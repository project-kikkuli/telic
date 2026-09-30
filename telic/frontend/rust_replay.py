"""Executing Rust counterexamples: the crate is copied, a function that
calls the target on the solver's values is placed next to it (in its
module), and the copy is compiled with a ``main`` that runs it (debug
semantics: overflow checks on). The panic, if any, is reported the way the
other harnesses report crashes."""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction
from typing import Any

from .. import ir

TIMEOUT_S = 10.0


class _Values:
    """Rust expressions for model values, with paths that resolve from
    anywhere in the crate."""

    def __init__(self, fe: Any):
        self.fe = fe

    def path(self, ir_name: str) -> str:
        for info in list(self.fe.structs.values()) + list(self.fe.data_enums.values()):
            if info.name == ir_name:
                return "crate::" + "::".join([*info.mod, info.src])
        for it in self.fe.crate.all_items():
            if self.fe.ir_names.get(id(it.node)) == ir_name:
                return "crate::" + "::".join([*it.mod, it.name])
        return ir_name

    def lit(self, v: Any, ty: ir.Type, rtype: str) -> str | None:
        """A Rust expression for model value ``v`` of type ``ty`` (Rust type text ``rtype``)."""
        rt = rtype.strip()
        ref = ""
        while rt.startswith("&"):
            ref += "&"
            rt = rt[1:].lstrip()
            if rt.startswith("'"):
                rt = rt.split(None, 1)[1] if " " in rt else rt
            if rt.startswith("mut "):
                ref += "mut "
                rt = rt[4:].lstrip()
        body = self._value(v, ty, rt)
        if body is None:
            return None
        if isinstance(ty, ir.TStr) and rt == "str":
            return body
        return ref + body

    def _value(self, v: Any, ty: ir.Type, rt: str) -> str | None:
        if isinstance(ty, ir.TInt):
            if not isinstance(v, int):
                v = 0
            suffix = rt if re.fullmatch(r"[iu](8|16|32|64|128|size)", rt) else ""
            return f"({v}{suffix})" if v < 0 else f"{v}{suffix}"
        if isinstance(ty, ir.TReal):
            if isinstance(v, dict) and "__real__" in v:
                v = Fraction(*v["__real__"])
            f = float(v or 0)
            return f"({f!r})" if f < 0 else repr(f)
        if isinstance(ty, ir.TBool):
            return "true" if v else "false"
        if isinstance(ty, ir.TStr):
            s = "" if v is None else str(v)
            esc = s.replace("\\", "\\\\").replace('"', '\\"')
            if rt == "str":
                return f'"{esc}"'
            if rt == "char":
                return f"'{esc[:1] or ' '}'"
            return f'String::from("{esc}")'
        if isinstance(ty, ir.TList):
            items = v if isinstance(v, list) else []
            inner = re.match(r"^(?:Vec<(.*)>|\[(.*?)(?:;\s*(\w+))?\])$", rt)
            et = (inner.group(1) or inner.group(2)) if inner else ""
            parts = [self.lit(x, ty.elem, et) for x in items]
            if any(p is None for p in parts):
                return None
            if inner and inner.group(3):  # [T; N]: an array of exactly N
                if not inner.group(3).isdigit() or int(inner.group(3)) != len(parts):
                    return None
                return f"[{', '.join(parts)}]"  # type: ignore[arg-type]
            return f"vec![{', '.join(parts)}]"  # type: ignore[arg-type]
        if isinstance(ty, ir.TOption):
            inner = re.match(r"^Option<(.*)>$", rt)
            if v is None:
                return "None"
            x = self.lit(v, ty.inner, inner.group(1) if inner else "")
            return None if x is None else f"Some({x})"
        if isinstance(ty, ir.TDict):
            m = re.match(r"^(?:HashMap|BTreeMap)<(.*)>$", rt)
            kt, vt = _split_generic(m.group(1)) if m else ("", "")
            items = v.items() if isinstance(v, dict) else []
            pairs = []
            for k, x in items:
                kl, xl = self.lit(k, ty.key, kt), self.lit(x, ty.val, vt)
                if kl is None or xl is None:
                    return None
                pairs.append(f"({kl}, {xl})")
            base = "HashMap" if not m or rt.startswith("HashMap") else "BTreeMap"
            return f"std::collections::{base}::from([{', '.join(pairs)}])"
        if isinstance(ty, ir.TEnum):
            if isinstance(v, dict) and "member" in v:
                v = v["member"]
            name = v if isinstance(v, str) and v in ty.members else ty.members[int(v) if isinstance(v, int) and 0 <= v < len(ty.members) else 0]
            return f"{self.path(ty.name)}::{name}"
        if isinstance(ty, ir.TRecord):
            return self._record(v, ty, rt)
        if isinstance(ty, ir.TClass):
            return self._struct(v, ty.name)
        return None

    def _record(self, v: Any, ty: ir.TRecord, rt: str) -> str | None:
        if isinstance(v, dict) and "__record__" in v:
            v = v.get("fields", {})
        if not isinstance(v, dict):
            return None
        if ty.fields[:1] and ty.fields[0][0] == "tag":
            tag = ty.fields[0][1]
            assert isinstance(tag, ir.TEnum)
            i = v.get("tag")
            vn = tag.members[i] if isinstance(i, int) and 0 <= i < len(tag.members) else tag.members[0]
            if tag.name == "Result$tag":
                m = re.match(r"^(?:[\w:]*::)?Result<(.*)>$", rt)
                parts = _split_generic(m.group(1)) if m else ("", "")
                ft = dict(ty.fields).get(f"{vn}_0")
                if ft is None:
                    return f"{vn}(())"
                x = self.lit(v.get(f"{vn}_0"), ft, parts[0] if vn == "Ok" else parts[1])
                return None if x is None else f"{vn}({x})"
            e = self.fe.data_enums.get(ty.name)
            if e is None:
                return None
            variant = e.variant(vn)
            assert variant is not None
            head = f"{self.path(ty.name)}::{vn}"
            vals = []
            for fname, rtext, _ in variant[2]:
                ft = dict(ty.fields).get(f"{vn}_{fname}")
                x = "()" if ft is None else self.lit(v.get(f"{vn}_{fname}"), ft, rtext)
                if x is None:
                    return None
                vals.append((fname, x))
            if variant[1] == "unit":
                return head
            if variant[1] == "tuple":
                return f"{head}({', '.join(x for _, x in vals)})"
            return f"{head} {{ {', '.join(f'{f}: {x}' for f, x in vals)} }}"
        return self._struct(v, ty.name)

    def _struct(self, v: Any, name: str) -> str | None:
        s = self.fe.structs.get(name)
        if isinstance(v, dict) and "__record__" in v:
            v = v.get("fields", {})
        if s is None or not isinstance(v, dict):
            return None
        saved = self.fe.cur_mod, self.fe.cur_generics, self.fe.cur_self, self.fe.cur_subst
        self.fe._in(s.mod, s.generics, s.name)
        try:
            parts = []
            for fname, rtext, tn in s.fields:
                t, _ = self.fe.ty(tn, name)
                x = self.lit(v.get(fname), t, rtext)
                if x is None:
                    return None
                parts.append((fname, x))
        finally:
            self.fe.cur_mod, self.fe.cur_generics, self.fe.cur_self, self.fe.cur_subst = saved
        if s.tuple:
            return f"{self.path(name)}({', '.join(x for _, x in parts)})"
        return f"{self.path(name)} {{ {', '.join(f'{f}: {x}' for f, x in parts)} }}"


def _split_generic(text: str) -> tuple[str, str]:
    depth = 0
    for i, ch in enumerate(text):
        if ch in "<([":
            depth += 1
        elif ch in ">)]":
            depth -= 1
        elif ch == "," and depth == 0:
            return text[:i].strip(), text[i + 1 :].strip()
    return text, ""


def _module_level(node: Any) -> Any:
    """The item holding ``node`` at module level (a method's impl block)."""
    while node.parent is not None:
        p = node.parent
        if p.type == "source_file" or (p.type == "declaration_list" and p.parent is not None and p.parent.type == "mod_item"):
            return node
        node = p
    return node


_MOD_DECL = re.compile(r"^(\s*)(?:pub(?:\s*\([^)]*\))?\s+)?mod\s+(\w+)\s*([;{])", re.M)


HOOK = (
    "std::panic::set_hook(Box::new(|info| {"
    " let msg = if let Some(s) = info.payload().downcast_ref::<&str>() { s.to_string() }"
    " else if let Some(s) = info.payload().downcast_ref::<String>() { s.clone() } else { String::new() };"
    ' let line = info.location().map(|l| l.line()).unwrap_or(0); let file = info.location().map(|l| l.file().to_string()).unwrap_or_default();'
    ' println!("TELIC_PANIC {} {} {}", line, file.replace(\' \', "%20"), msg.replace(\'\\n\', " ")); }));'
)


class _Target:
    """The function to run, with what building calls to it needs."""

    def __init__(self, path: str, fn: ir.Function):
        from .rust import RustFrontend

        self.fn = fn
        self.fe = RustFrontend(path, open(path).read(), path)
        self.fe.run()
        want = ir.source_name(fn.name)
        cands = [i for i in self.fe.fns.values() if i.file == self.fe.abs and not i.decl and ir.source_name(i.key) == want]
        self.info = next((i for i in cands if i.key == fn.name), cands[0] if cands else None)
        if self.info is None:
            return
        self.fe._enter(self.info)
        self.vals = _Values(self.fe)
        self.ptypes: dict[str, str] = {}
        ps = self.info.node.child_by_field_name("parameters")
        for c in ps.children if ps is not None else []:
            if c.type == "parameter":
                pat = c.child_by_field_name("pattern")
                self.ptypes[pat.text.decode().replace("mut ", "").strip()] = c.child_by_field_name("type").text.decode()

    def invocation(self, model: dict[str, Any]) -> tuple[str, str] | None:
        """(setup, call) running the function on a model's values."""
        assert self.info is not None
        args, setup = [], []
        recv = None
        for p in self.fn.params:
            v = model.get(p.name)
            if p.name == "self":
                lit = self.vals.lit(v, p.ty, "")
                if lit is None:
                    return None
                setup.append(f"let mut __self = {lit};")
                recv = "__self"
                continue
            a = self.vals.lit(v, p.ty, self.ptypes.get(p.name, ""))
            if a is None:
                return None
            # bind each argument to its parameter's name, so contracts can mention it
            if a.startswith("&mut "):
                setup.append(f"let mut {p.name} = {a[5:]};")
                args.append(f"&mut {p.name}")
            elif a.startswith("&"):
                setup.append(f"let {p.name} = {a[1:]};")
                args.append(f"&{p.name}")
            else:
                setup.append(f"let {p.name} = {a};")
                args.append(f"{p.name}.clone()")
        name = _text_name(self.info.node)
        owner = self.vals.path(self.info.owner) if self.info.owner else ""
        call = f"{recv}.{name}({', '.join(args)})" if recv else (f"{owner}::{name}({', '.join(args)})" if self.info.owner else f"{name}({', '.join(args)})")
        return " ".join(setup), call

    def checks(self) -> list[str]:
        """Postconditions as Rust, where their text is Rust the compiler accepts."""
        out = []
        for i, c in enumerate(self.fn.ensures):
            text = _rust_implies(c.text)
            if text is None or "old(" in text:
                continue
            cond = _receiver(re.sub(r"\bresult\b", "__v", text))
            out.append(f"if !({cond}) {{ println!(\"TELIC_VIOLATION ensures {i}\"); }}")
        return out

    def lifecycles(self) -> tuple[list[str], list[str], list[Any]]:
        """(snapshots taken before the call, checks after it, the lifecycles):
        objects passed in change only as their lifecycles allow."""
        if self.info is None:
            return [], [], []
        from ..runtime import _lifecycles

        pairs = [(p, lc) for p in self.fn.params if isinstance(p.ty, ir.TClass) for _, lc in _lifecycles(self.fe.classes, p.ty.name)]
        lcs = [lc for _, lc in pairs]
        snaps, checks = [], []
        for i, (p, lc) in enumerate(pairs):
            cond, olds = _extract_old(re.sub(r"\bself\b", "__self" if p.name == "self" else p.name, lc.code))
            for k, o in enumerate(olds):
                snaps.append(f"let __o{i}_{k} = ({o}).clone();")
                cond = cond.replace(f"__OLD{k}__", f"__o{i}_{k}")
            checks.append(f"if !({cond}) {{ println!(\"TELIC_VIOLATION lifecycle {i}\"); }}")
        return snaps, checks, lcs

    def run(self, bodies: list[str]) -> tuple[str, str] | dict[str, Any]:
        """Build the crate with each body in turn until one compiles; its
        output and the copied root file."""
        res: tuple[str, str] | dict[str, Any] = {"harness_error": "nothing to run"}
        for body in bodies:
            res = _run_many([(self, body)])
            if not (isinstance(res, dict) and "harness_error" in res):
                return res
        if isinstance(res, dict) and "harness_error" in res:
            return {"harness_error": f"rustc could not build the counterexample: {res['harness_error']}"}
        return res


def run_rust(path: str, fn: ir.Function, model: dict[str, Any]) -> dict[str, Any] | None:
    if shutil.which("rustc") is None:
        return None
    t = _Target(path, fn)
    if t.info is None:
        return None
    inv = t.invocation(model)
    if inv is None:
        return None
    setup, call = inv
    snaps, lc_checks, lcs = t.lifecycles()
    checks = t.checks() + lc_checks
    bodies = []
    if checks:
        bodies.append(f"let __r = std::panic::catch_unwind(move || {{ {setup} {' '.join(snaps)} let __v = {call}; {' '.join(checks)} format!(\"{{:?}}\", __v) }}); if let Ok(s) = __r {{ println!(\"TELIC_RETURNED {{}}\", s); }}")
    bodies += [
        f"let __r = std::panic::catch_unwind(move || {{ {setup} let __v = {call}; format!(\"{{:?}}\", __v) }}); if let Ok(s) = __r {{ println!(\"TELIC_RETURNED {{}}\", s); }}",
        f"let __r = std::panic::catch_unwind(move || {{ {setup} let _ = {call}; }}); if __r.is_ok() {{ println!(\"TELIC_RETURNED (value)\"); }}",
    ]
    res = t.run(bodies)
    if isinstance(res, dict):
        return res
    stdout, root_copy = res
    out = _parse(stdout, root_copy)
    for line in stdout.splitlines():
        if line.startswith("TELIC_VIOLATION ensures "):
            c2 = fn.ensures[int(line.split()[-1])]
            return {"violation": "ensures", "func": ir.source_name(fn.name), "text": c2.text, "detail": f"returned {out.get('returned_repr', '')}".strip()}
        if line.startswith("TELIC_VIOLATION lifecycle "):
            return {"violation": "lifecycle", "func": ir.source_name(fn.name), "text": lcs[int(line.split()[-1])].clause.text}
    return out


def run_rust_batch(path: str, fn: ir.Function, models: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Run the function on each model in one program: per model, what
    ``run_rust`` reports (without checking postconditions), or ``rejected``
    when the model breaks a @requires or cannot be written as Rust."""
    if shutil.which("rustc") is None:
        return [{"harness_error": "rustc is not installed"}] * len(models)
    t = _Target(path, fn)
    if t.info is None:
        return [{"harness_error": "function not found"}] * len(models)
    if any(r is None or "old(" in r for r in (_rust_implies(c.text) for c in fn.requires)):
        return [{"harness_error": "a @requires is not Rust the harness can evaluate"}] * len(models)
    usable = [i for i, m in enumerate(models) if t.invocation(m) is not None]
    got = run_rust_samples(path, [(fn, [models[i] for i in usable])], checks=False) if usable else {}
    if got is None:
        return [{"harness_error": "rustc could not build the batch"}] * len(models)
    rows = got.get(fn.name)
    if usable and rows is None:
        return [{"harness_error": "rustc could not build the batch"}] * len(models)
    out: list[dict[str, Any]] = [{"rejected": True}] * len(models)
    for i, row in zip(usable, rows or []):
        out[i] = {"rejected": True} if row.get("skipped") else row
    return out


def run_rust_samples(path: str, targets: list[tuple[ir.Function, list[dict[str, Any]]]], checks: bool = True) -> dict[str, list[dict[str, Any]]] | None:
    """Run functions of one file on several models each, in one build: per
    model, the panic or broken postcondition, or {"skipped": True} when the
    inputs do not meet the preconditions (checked where their text is Rust).
    Functions the harness cannot call are left out."""
    if shutil.which("rustc") is None:
        return None
    runs: list[tuple[_Target, list[str]]] = []
    for fn, models in targets:
        t = _Target(path, fn)
        reqs = [_rust_implies(c.text) for c in fn.requires]
        if t.info is None or any(r is None or "old(" in r for r in reqs):
            continue
        guard = " ".join(f"if !({_receiver(r)}) {{ return String::from(\"TELIC_SKIPPED\"); }}" for r in reqs)  # type: ignore[arg-type]
        invs = [t.invocation(m) for m in models]
        if any(x is None for x in invs):
            continue
        variants = []
        post = " ".join(t.checks()) if checks else ""
        for checks_, show in ((post, True), (post, False), ("", True), ("", False)):
            value = 'format!("{:?}", __v)' if show else "String::new()"
            variants.append(" ".join(f'println!("TELIC_SAMPLE {fn.name} {i}"); let __r = std::panic::catch_unwind(move || {{ {setup} {guard} let __v = {call}; {checks_} {value} }}); if let Ok(s) = __r {{ println!("TELIC_RETURNED {{}}", s); }}' for i, (setup, call) in enumerate(invs)))  # type: ignore[misc]
        runs.append((t, variants))
    if not runs:
        return {}
    # one build; a harness rustc rejects falls back to its next variant
    level = [0] * len(runs)
    while True:
        live = [k for k in range(len(runs)) if level[k] < len(runs[k][1])]
        if not live:
            return {}
        chosen = [(runs[k][0], runs[k][1][level[k]]) for k in live]
        res = _run_many(chosen)
        if not (isinstance(res, dict) and "harness_error" in res):
            break
        bad = res.get("bad") or set()
        if not bad:
            return None
        for j in bad:
            level[live[j]] += 1
    if isinstance(res, dict):
        return None
    stdout, root_copy = res
    chunks: dict[tuple[str, int], list[str]] = {}
    cur = None
    for line in stdout.splitlines():
        if line.startswith("TELIC_SAMPLE "):
            _, name, i = line.split()
            cur = (name, int(i))
            chunks[cur] = []
        elif cur is not None:
            chunks[cur].append(line)
    out: dict[str, list[dict[str, Any]]] = {}
    for t, _ in chosen:
        fn = t.fn
        models = next(ms for f, ms in targets if f is fn)
        rows = []
        for i in range(len(models)):
            lines = chunks.get((fn.name, i), [])
            if any(l.startswith("TELIC_RETURNED") and "TELIC_SKIPPED" in l for l in lines):
                rows.append({"skipped": True})
                continue
            v = next((l for l in lines if l.startswith("TELIC_VIOLATION ensures ")), None)
            if v is not None:
                rows.append({"violation": "ensures", "text": fn.ensures[int(v.split()[-1])].text})
                continue
            rows.append(_parse("\n".join(lines), root_copy))
        out[fn.name] = rows
    return out


def _run_many(chosen: list[tuple["_Target", str]]) -> tuple[str, str] | dict[str, Any]:
    """Build the crate with each target's harness placed after it, then run them all."""
    rustc = shutil.which("rustc")
    t0 = chosen[0][0]
    crate = t0.fe.crate
    top = os.path.dirname(crate.root_file)
    inserts: dict[str, list[tuple[int, str]]] = {}
    calls = []
    for k, (t, body) in enumerate(chosen):
        assert t.info is not None
        at = _module_level(t.info.node)
        inserts.setdefault(t.fe.abs, []).append((at.end_byte, f"\npub fn __telic_run{k}() {{ {HOOK} {body} }}\n"))
        calls.append("::".join(["crate", *t.info.mod, f"__telic_run{k}"]) + "();")
    key = hashlib.sha256(("\0".join(crate.sources[f] for f in sorted(crate.sources)) + repr(inserts)).encode()).hexdigest()[:16]
    work = os.path.join(tempfile.gettempdir(), f"telic-rs-{key}")
    where: dict[tuple[str, int], int] = {}  # (file, line) -> harness
    for f, src in crate.sources.items():
        b = src.encode("utf8")
        for pos, text in sorted(inserts.get(f, []), reverse=True):
            b = b[:pos] + text.encode() + b[pos:]
        text = _MOD_DECL.sub(lambda m: f"{m.group(1)}pub mod {m.group(2)}{m.group(3)}", b.decode("utf8"))
        if f == crate.root_file:
            text = re.sub(r"\bfn\s+main\s*\(", "fn __telic_user_main(", text)
            text = "#![allow(warnings)]\n" + text + f"\nfn main() {{ {' '.join(calls)} }}\n"
        rel = os.path.relpath(f, top)
        for n, line in enumerate(text.splitlines(), 1):
            m = re.match(r"pub fn __telic_run(\d+)\(\)", line)
            if m:
                where[(rel, n)] = int(m.group(1))
        dest = os.path.join(work, "src", rel)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "w") as fh:
            fh.write(text)
    root_copy = os.path.join(work, "src", os.path.relpath(crate.root_file, top))
    exe = os.path.join(work, "main")
    c = subprocess.run([rustc, "--edition", _edition(top), *_features(top), "-C", "overflow-checks=on", "-C", "debug-assertions=on", "-o", exe, root_copy], capture_output=True, text=True)  # type: ignore[list-item]
    if c.returncode != 0:
        bad = set()
        for m in re.finditer(r"--> (.+?):(\d+):\d+", c.stderr):
            path = os.path.relpath(m.group(1), os.path.join(work, "src")) if os.path.isabs(m.group(1)) else os.path.relpath(os.path.abspath(m.group(1)), os.path.join(work, "src"))
            k = where.get((path, int(m.group(2))))
            if k is not None:
                bad.add(k)
        return {"harness_error": next((l for l in c.stderr.splitlines() if l.startswith("error")), "compile error"), "bad": bad}
    try:
        r = subprocess.run([exe], capture_output=True, text=True, timeout=TIMEOUT_S * 4)
    except subprocess.TimeoutExpired:
        return {"timeout": True}
    return r.stdout, root_copy


def _extract_old(text: str) -> tuple[str, list[str]]:
    """``old(e)`` -> ``__OLDk__``, with the ``e`` texts in order."""
    out, olds, i = "", [], 0
    for m in re.finditer(r"\bold\(", text):
        if m.start() < i:
            continue
        depth, j = 1, m.end()
        while j < len(text) and depth:
            depth += {"(": 1, ")": -1}.get(text[j], 0)
            j += 1
        out += text[i : m.start()] + f"__OLD{len(olds)}__"
        olds.append(text[m.end() : j - 1])
        i = j
    return out + text[i:], olds


def _receiver(text: str) -> str:
    """Contract text about ``self``, about the harness's receiver instead."""
    return re.sub(r"\bself\b", "__self", re.sub(r"\*\s*self\b", "self", text))


def _rust_implies(text: str) -> str | None:
    """A contract's text as Rust: ``implies(a, b)`` becomes ``(!(a) || (b))``."""
    if "implies(" not in text:
        return text
    from .rust import parser

    src = "fn __f() { (" + text + "); }"
    tree = parser().parse(src.encode("utf8"))
    if tree.root_node.has_error:
        return None
    raw = src.encode("utf8")

    def render(n: Any) -> bytes:
        if n.type == "call_expression" and n.child_by_field_name("function").text == b"implies":
            args = [c for c in n.child_by_field_name("arguments").named_children]
            if len(args) == 2:
                return b"(!(" + render(args[0]) + b") || (" + render(args[1]) + b"))"
        out, pos = b"", n.start_byte
        for c in n.children:
            out += raw[pos : c.start_byte] + render(c)
            pos = c.end_byte
        return out + raw[pos : n.end_byte]

    body = render(tree.root_node).decode("utf8")
    return body[len("fn __f() { (") : -len("); }")]


def _manifest(src_dir: str) -> dict[str, Any]:
    path = os.path.join(os.path.dirname(src_dir), "Cargo.toml")
    if os.path.basename(src_dir) != "src" or not os.path.exists(path):
        return {}
    try:
        import tomllib
    except ImportError:  # pragma: no cover - Python 3.10
        import tomli as tomllib  # type: ignore[no-redef]
    try:
        with open(path, "rb") as f:
            return tomllib.load(f)
    except (OSError, ValueError):
        return {}


def _edition(src_dir: str) -> str:
    return str(_manifest(src_dir).get("package", {}).get("edition", "2021"))


def _features(src_dir: str) -> list[str]:
    """--cfg flags for the crate's default features (as cargo builds it)."""
    feats = _manifest(src_dir).get("features", {})
    on: set[str] = set()
    todo = list(feats.get("default", []))
    while todo:
        f = todo.pop()
        if f in on or "/" in f or f.startswith("dep:"):
            continue
        on.add(f)
        todo += feats.get(f, [])
    return [x for f in sorted(on) for x in ("--cfg", f'feature="{f}"')]


def _text_name(node: Any) -> str:
    return node.child_by_field_name("name").text.decode("utf8")


def _parse(out: str, root_copy: str = "") -> dict[str, Any]:
    for line in out.splitlines():
        if line.startswith("TELIC_PANIC "):
            rest = line[len("TELIC_PANIC "):]
            ln, _, rest = rest.partition(" ")
            file, _, msg = rest.partition(" ")
            crash = "panic"
            if "attempt to shift" in msg:
                crash = "AssertionError"
            elif "with overflow" in msg:
                crash = "overflow"
            elif "divide by zero" in msg or "divisor of zero" in msg:
                crash = "ZeroDivisionError"
            elif "index out of bounds" in msg:
                crash = "IndexError"
            elif "out of range for slice" in msg or "slice index starts" in msg:
                crash = "AssertionError"
            elif "no entry found for key" in msg:
                crash = "KeyError"
            elif "None` value" in msg or "on a `None`" in msg:
                crash = "unwrap on None"
            elif msg.startswith("assertion"):
                crash = "AssertionError"
            line_no = int(ln) if ln.isdigit() else None
            if line_no is not None and os.path.normpath(file.replace("%20", " ")) == os.path.normpath(root_copy):
                line_no -= 1  # (the root file has one extra line on top)
            return {"crash": crash, "msg": msg, "line": line_no}
        if line.startswith("TELIC_RETURNED "):
            return {"returned_repr": line[len("TELIC_RETURNED "):]}
    return {"harness_error": "the counterexample program printed nothing"}
