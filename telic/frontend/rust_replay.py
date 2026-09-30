"""Executing Rust counterexamples: the file is compiled with a generated
``main`` that calls the function on the solver's values (debug semantics:
overflow checks on), and the panic, if any, is reported the way the other
harnesses report crashes."""

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


def _lit(v: Any, ty: ir.Type, rtype: str) -> str | None:
    """A Rust expression for model value ``v`` of type ``ty`` (Rust type text ``rtype``)."""
    rt = rtype.strip()
    ref = ""
    while rt.startswith("&"):
        ref += "&"
        rt = rt[1:].lstrip()
        if rt.startswith("mut "):
            ref += "mut "
            rt = rt[4:].lstrip()
    if isinstance(ty, ir.TInt):
        if not isinstance(v, int):
            v = 0
        suffix = rt if re.fullmatch(r"[iu](8|16|32|64|128|size)", rt) else ""
        body = f"({v}{suffix})" if v < 0 else f"{v}{suffix}"
        return ref + body
    if isinstance(ty, ir.TReal):
        if isinstance(v, dict) and "__real__" in v:
            v = Fraction(*v["__real__"])
        f = float(v or 0)
        return ref + (f"({f!r})" if f < 0 else repr(f))
    if isinstance(ty, ir.TBool):
        return ref + ("true" if v else "false")
    if isinstance(ty, ir.TStr):
        s = "" if v is None else str(v)
        esc = s.replace("\\", "\\\\").replace('"', '\\"')
        if rt in ("str",):
            return f'"{esc}"'
        return ref + f'String::from("{esc}")'
    if isinstance(ty, ir.TList):
        items = v if isinstance(v, list) else []
        inner = re.match(r"^(?:Vec<(.*)>|\[(.*?)(?:;.*)?\])$", rt)
        et = (inner.group(1) or inner.group(2)) if inner else ""
        parts = [_lit(x, ty.elem, et) for x in items]
        if any(p is None for p in parts):
            return None
        return ref + f"vec![{', '.join(parts)}]"  # type: ignore[arg-type]
    if isinstance(ty, ir.TOption):
        inner = re.match(r"^Option<(.*)>$", rt)
        if v is None:
            return ref + "None"
        x = _lit(v, ty.inner, inner.group(1) if inner else "")
        return None if x is None else ref + f"Some({x})"
    if isinstance(ty, ir.TDict):
        m = re.match(r"^(?:HashMap|BTreeMap)<(.*)>$", rt)
        kt, vt = _split_generic(m.group(1)) if m else ("", "")
        items = v.items() if isinstance(v, dict) else []
        pairs = []
        for k, x in items:
            kl, xl = _lit(k, ty.key, kt), _lit(x, ty.val, vt)
            if kl is None or xl is None:
                return None
            pairs.append(f"({kl}, {xl})")
        base = "HashMap" if not m or rt.startswith("HashMap") else "BTreeMap"
        return ref + f"std::collections::{base}::from([{', '.join(pairs)}])"
    if isinstance(ty, ir.TEnum):
        if isinstance(v, dict) and "member" in v:
            v = v["member"]
        name = v if isinstance(v, str) and v in ty.members else ty.members[int(v) if isinstance(v, int) and 0 <= v < len(ty.members) else 0]
        return ref + f"{ty.name}::{name}"
    return None


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


def _struct_lit(v: Any, name: str, fe: Any, ref: str) -> str | None:
    s = fe.structs.get(name)
    if isinstance(v, dict) and "__record__" in v:
        v = v.get("fields", {})
    if s is None or not isinstance(v, dict):
        return None
    parts = []
    for fname, rtext, tn in s.fields:
        t, _ = fe.ty(tn, name)
        fv = v.get(fname)
        if isinstance(t, (ir.TClass, ir.TRecord)):
            x = _struct_lit(fv, t.name, fe, "")
        else:
            x = _lit(fv, t, rtext)
        if x is None:
            return None
        parts.append(f"{fname}: {x}")
    return ref + f"{name} {{ {', '.join(parts)} }}"


def _arg(v: Any, p: ir.Param, rtype: str, fe: Any) -> str | None:
    if isinstance(p.ty, (ir.TClass, ir.TRecord)):
        ref = "&mut " if rtype.startswith("&mut") else "&" if rtype.startswith("&") else ""
        return _struct_lit(v, p.ty.name, fe, ref)
    return _lit(v, p.ty, rtype)


def _prepare(path: str, fn: ir.Function) -> tuple[Any, Any, dict[str, str], str] | None:
    """(frontend, the function's info, parameter types as written, the source
    with its own ``main`` renamed), or None if the function is not found."""
    from .rust import RustFrontend

    source = open(path).read()
    fe = RustFrontend(path, source)
    fe.run()
    info = fe.fns.get(ir.source_name(fn.name))
    if info is None:
        return None
    ptypes: dict[str, str] = {}
    ps = info.node.child_by_field_name("parameters")
    for c in ps.children if ps is not None else []:
        if c.type == "parameter":
            pat = c.child_by_field_name("pattern")
            ptypes[pat.text.decode().replace("mut ", "").strip()] = c.child_by_field_name("type").text.decode()
        elif c.type == "self_parameter":
            ptypes["self"] = c.text.decode().replace("self", "Self").strip()
    return fe, info, ptypes, re.sub(r"\bfn\s+main\s*\(", "fn __telic_user_main(", source)


def _call(fn: ir.Function, fe: Any, info: Any, ptypes: dict[str, str], model: dict[str, Any]) -> tuple[list[str], str] | None:
    """(statements binding each argument to its parameter's name, the call)."""
    args = []
    setup = []
    recv = None
    for p in fn.params:
        v = model.get(p.name)
        if p.name == "self":
            lit = _struct_lit(v, info.owner or "", fe, "")
            if lit is None:
                return None
            setup.append(f"let mut __self = {lit};")
            recv = "__self"
            continue
        a = _arg(v, p, ptypes.get(p.name, ""), fe)
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
    name = fn.name.split(".")[-1]
    call = f"{recv}.{name}({', '.join(args)})" if recv else (f"{info.owner}::{name}({', '.join(args)})" if info.owner else f"{name}({', '.join(args)})")
    return setup, call


HOOK = (
    "std::panic::set_hook(Box::new(|info| {"
    " let msg = if let Some(s) = info.payload().downcast_ref::<&str>() { s.to_string() }"
    " else if let Some(s) = info.payload().downcast_ref::<String>() { s.clone() } else { String::new() };"
    ' let line = info.location().map(|l| l.line()).unwrap_or(0); println!("TELIC_PANIC {} {}", line, msg.replace(\'\\n\', " ")); }));'
)


def _build(rustc: str, body: str, main: str, key: str) -> tuple[str | None, str]:
    """(the executable, or None and the compiler's errors)."""
    work = os.path.join(tempfile.gettempdir(), f"telic-rs-{key}")
    os.makedirs(work, exist_ok=True)
    src = os.path.join(work, "main.rs")
    exe = os.path.join(work, "main")
    with open(src, "w") as f:
        f.write(f"#![allow(warnings)]\n{body}\nfn main() {{ {HOOK} {main} }}\n")
    c = subprocess.run([rustc, "--edition", "2021", "-C", "overflow-checks=on", "-C", "debug-assertions=on", "-o", exe, src], capture_output=True, text=True)
    return (exe, "") if c.returncode == 0 else (None, c.stderr)


def _compile_error(err: str) -> dict[str, Any]:
    first = next((l for l in err.splitlines() if l.startswith("error")), "compile error")
    return {"harness_error": f"rustc could not build the counterexample: {first}"}


def run_rust(path: str, fn: ir.Function, model: dict[str, Any]) -> dict[str, Any] | None:
    rustc = shutil.which("rustc")
    if rustc is None:
        return None
    prep = _prepare(path, fn)
    if prep is None:
        return None
    fe, info, ptypes, body = prep
    got = _call(fn, fe, info, ptypes, model)
    if got is None:
        return None
    setup, call = got
    # postconditions, checked at runtime where their text is Rust the compiler accepts
    checks = []
    for i, c in enumerate(fn.ensures):
        if "old(" in c.text or "implies(" in c.text:
            continue
        cond = re.sub(r"\bresult\b", "__v", c.text)
        checks.append(f"if !({cond}) {{ println!(\"TELIC_VIOLATION ensures {i}\"); }}")
    # the receiver changes only as its lifecycles allow
    lcs = []
    if any(p.name == "self" for p in fn.params):
        from ..runtime import _lifecycles

        lcs = _lifecycles(fe.module.classes, info.owner or "")
    snaps: list[str] = []
    lcs = [lc for _, lc in lcs]
    for i, lc in enumerate(lcs):
        cond, olds = _extract_old(re.sub(r"\bself\b", "__self", lc.code))
        for k, o in enumerate(olds):
            snaps.append(f"let __o{i}_{k} = ({o}).clone();")
            cond = cond.replace(f"__OLD{k}__", f"__o{i}_{k}")
        checks.append(f"if !({cond}) {{ println!(\"TELIC_VIOLATION lifecycle {i}\"); }}")
    if snaps:
        setup = setup + snaps
    variants = []
    if checks:
        variants.append(f"let __r = std::panic::catch_unwind(move || {{ {' '.join(setup)} let __v = {call}; {' '.join(checks)} format!(\"{{:?}}\", __v) }}); if let Ok(s) = __r {{ println!(\"TELIC_RETURNED {{}}\", s); }}")
        setup = setup[: len(setup) - len(snaps)]
    variants += [
        f"let __r = std::panic::catch_unwind(move || {{ {' '.join(setup)} let __v = {call}; format!(\"{{:?}}\", __v) }}); if let Ok(s) = __r {{ println!(\"TELIC_RETURNED {{}}\", s); }}",
        f"let __r = std::panic::catch_unwind(move || {{ {' '.join(setup)} let _ = {call}; }}); if __r.is_ok() {{ println!(\"TELIC_RETURNED (value)\"); }}",
    ]
    key = hashlib.sha256((body + call).encode()).hexdigest()[:16]
    err = ""
    for v in variants:
        exe, err = _build(rustc, body, v, key)
        if exe is None:
            continue
        try:
            r = subprocess.run([exe], capture_output=True, text=True, timeout=TIMEOUT_S)
        except subprocess.TimeoutExpired:
            return {"timeout": True}
        out = _parse(r.stdout)
        for line in r.stdout.splitlines():
            if line.startswith("TELIC_VIOLATION ensures "):
                c = fn.ensures[int(line.split()[-1])]
                return {"violation": "ensures", "func": ir.source_name(fn.name), "text": c.text, "detail": f"returned {out.get('returned_repr', '')}".strip()}
            if line.startswith("TELIC_VIOLATION lifecycle "):
                return {"violation": "lifecycle", "func": ir.source_name(fn.name), "text": lcs[int(line.split()[-1])].clause.text}
        return out
    return _compile_error(err)


def run_rust_batch(path: str, fn: ir.Function, models: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Run the function on each model in one program: per model, what
    ``run_rust`` reports, or ``rejected`` when the model breaks a @requires
    or cannot be written as Rust."""
    rustc = shutil.which("rustc")
    prep = _prepare(path, fn) if rustc else None
    if rustc is None or prep is None:
        return [{"harness_error": "rustc is not installed" if rustc is None else "function not found"}] * len(models)
    fe, info, ptypes, body = prep
    reqs = [re.sub(r"\bself\b", "__self", c.text) for c in fn.requires if "old(" not in c.text and "implies(" not in c.text]
    if len(reqs) != len(fn.requires):
        return [{"harness_error": "a @requires is not Rust the harness can evaluate"}] * len(models)
    guard = f"if !({' && '.join(f'({r})' for r in reqs)}) {{ println!(\"TELIC_REJECTED\"); return; }}" if reqs else ""
    calls = [_call(fn, fe, info, ptypes, m) for m in models]
    err = ""
    for show in ("let __v = {call}; println!(\"TELIC_RETURNED {{:?}}\", __v);", "let _ = {call}; println!(\"TELIC_RETURNED (value)\");"):
        cases = "".join(
            f"println!(\"TELIC_CASE {i}\"); let _ = std::panic::catch_unwind(move || {{ {' '.join(c[0])} {guard} {show.format(call=c[1])} }});"
            for i, c in enumerate(calls)
            if c is not None
        )
        exe, err = _build(rustc, body, cases, hashlib.sha256((body + cases).encode()).hexdigest()[:16])
        if exe is None:
            continue
        try:
            r = subprocess.run([exe], capture_output=True, text=True, timeout=TIMEOUT_S * 3)
        except subprocess.TimeoutExpired:
            return [{"timeout": True}] * len(models)
        chunks: dict[int, list[str]] = {}
        cur = None
        for line in r.stdout.splitlines():
            m = re.match(r"^TELIC_CASE (\d+)$", line)
            if m:
                cur = int(m.group(1))
                chunks[cur] = []
            elif cur is not None:
                chunks[cur].append(line)
        return [
            {"rejected": True} if calls[i] is None or "TELIC_REJECTED" in chunks.get(i, []) else _parse("\n".join(chunks.get(i, [])))
            for i in range(len(models))
        ]
    return [_compile_error(err)] * len(models)


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


def _parse(out: str) -> dict[str, Any]:
    for line in out.splitlines():
        if line.startswith("TELIC_PANIC "):
            rest = line[len("TELIC_PANIC "):]
            ln, _, msg = rest.partition(" ")
            crash = "panic"
            if "with overflow" in msg:
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
            return {"crash": crash, "msg": msg, "line": int(ln) - 1 if ln.isdigit() else None}  # (the generated file has one extra line on top)
        if line.startswith("TELIC_RETURNED "):
            return {"returned_repr": line[len("TELIC_RETURNED "):]}
    return {"harness_error": "the counterexample program printed nothing"}
