"""Execute counterexamples for real.

A solver model is a claim about a *model* of the program. telic does not ask
you to trust it: every counterexample is replayed against the actual code in
the actual runtime (CPython, Node) with contracts enforced, and reported as

* **confirmed**  -- the real program misbehaved on exactly these inputs, or
* **not reproduced** -- the real program was fine, which almost always means
  a loop invariant is too weak to rule out the state the solver picked (the
  report says which loop).
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from . import ir
from .program import Program

TIMEOUT_S = 5.0
PKG_ROOT = str(Path(__file__).resolve().parent.parent)


def _encode_any(v: Any) -> Any:
    """Encode a decoded model value whose static type is not at hand."""
    if isinstance(v, dict) and "__class__" in v:
        fields = None if v.get("__stub__") else {k: _encode_any(x) for k, x in v.items() if not k.startswith("__")}
        return {"__object__": v["__class__"], "ref": v.get("__ref__"), "fields": fields}
    if isinstance(v, Fraction):
        return {"__real__": [v.numerator, v.denominator]}
    if isinstance(v, list):
        return [_encode_any(x) for x in v]
    if isinstance(v, dict):
        return {"__dict__": [[k, _encode_any(x)] for k, x in v.items()]}
    return v


def encode_value(v: Any, ty: ir.Type) -> Any:
    if isinstance(ty, ir.TOption):
        return None if v is None else encode_value(v, ty.inner)
    if isinstance(ty, ir.TClass):
        if isinstance(v, dict) and "__class__" in v:
            return _encode_any(v)
        return {"__object__": ty.name, "ref": v, "fields": None}
    if isinstance(ty, ir.TDict):
        return {"__dict__": [[encode_value(k, ty.key), encode_value(x, ty.val)] for k, x in (v or {}).items()]}
    if isinstance(ty, ir.TList):
        return [encode_value(x, ty.elem) for x in (v or [])]
    if isinstance(ty, ir.TRecord):
        return {"__record__": ty.name, "fields": {n: encode_value((v or {}).get(n), t) for n, t in ty.fields}}
    if isinstance(ty, ir.TReal):
        if isinstance(v, Fraction):
            return {"__real__": [v.numerator, v.denominator]}
        return {"__real__": [int(v or 0), 1]}
    if isinstance(ty, ir.TInt):
        return int(v) if isinstance(v, (int, Fraction)) else 0
    if isinstance(ty, ir.TBool):
        return bool(v)
    if isinstance(ty, ir.TStr):
        return v if isinstance(v, str) else ""
    return v


def format_value(v: Any, ty: ir.Type | None = None, lang: str = "python", names: dict | None = None, label: str | None = None) -> str:
    """``names`` maps object references already shown to how to refer to
    them, so aliasing and cycles are visible: ``f(a=<Box v=0 next=a>, b=a)``."""
    if v is None:
        return "None" if lang == "python" else "null"
    if isinstance(v, dict) and "__object__" in v:
        names = {} if names is None else names
        key = (v["__object__"], v["ref"])
        if key in names:
            return names[key]
        if v["fields"] is None:
            return f"<{v['__object__']} #{v['ref']}>"
        names[key] = label or f"#{v['ref']}"
        tag = v["__object__"] if label else f"{v['__object__']} #{v['ref']}"
        inner = " ".join(f"{k}={format_value(x, None, lang, names)}" for k, x in v["fields"].items())
        return f"<{tag} {inner}>" if inner else f"<{tag}>"
    if isinstance(v, dict) and "__dict__" in v:
        inner = ", ".join(f"{format_value(k, None, lang)}: {format_value(x, None, lang)}" for k, x in v["__dict__"])
        return "{" + inner + "}"
    if isinstance(v, dict) and "__real__" in v:
        n, d = v["__real__"]
        return format_value(Fraction(n, d), ir.REAL, lang)
    if isinstance(v, dict) and "__record__" in v:
        inner = ", ".join(f"{k}={format_value(x, None, lang)}" if lang == "python" else f"{k}: {format_value(x, None, lang)}" for k, x in v["fields"].items())
        return f"{v['__record__']}({inner})" if lang == "python" else "{ " + inner + " }"
    if isinstance(v, Fraction):
        if v.denominator == 1:
            return f"{v.numerator}.0" if lang == "python" else str(v.numerator)
        f = float(v)
        s = repr(f)
        return s if Fraction(s) == v else f"{s} (={v.numerator}/{v.denominator})"
    if isinstance(v, bool):
        if lang == "python":
            return "True" if v else "False"
        return "true" if v else "false"
    if isinstance(v, list):
        inner_ty = ty.elem if isinstance(ty, ir.TList) else None
        return "[" + ", ".join(format_value(x, inner_ty, lang, names) for x in v) + "]"
    if isinstance(v, str):
        return json.dumps(v) if lang != "python" else repr(v)
    return str(v)


def call_text(fn: ir.Function, model: dict[str, Any], lang: str, names: bool = True) -> str:
    params = fn.params
    head = fn.name
    shown: dict = {}  # object reference -> how it is referred to

    def fmt(p: ir.Param) -> str:
        return format_value(encode_value(model.get(p.name), p.ty), p.ty, lang, shown, label=p.name)

    if "." in fn.name and params and isinstance(params[0].ty, ir.TClass) and params[0].ty.name == fn.name.split(".")[0]:
        # a method: show it called on the receiver
        head = f"{fmt(params[0])}.{fn.name.split('.', 1)[1]}"
        params = params[1:]
    args = []
    for p in params:
        v = fmt(p)
        if names and (len(params) > 1 or isinstance(p.ty, (ir.TClass, ir.TOption))):
            v = f"{p.name}={v}" if lang == "python" else f"{p.name}: {v}"
        args.append(v)
    return f"{head}({', '.join(args)})"


def type_desc(ty: ir.Type, classes: dict[str, ir.ClassDecl] | None = None, depth: int = 0) -> dict[str, Any]:
    if isinstance(ty, ir.TOption):
        return {"k": "option", "inner": type_desc(ty.inner, classes, depth)}
    if isinstance(ty, ir.TDict):
        return {"k": "dict", "key": type_desc(ty.key), "val": type_desc(ty.val, classes, depth + 1)}
    if isinstance(ty, ir.TClass):
        decl = (classes or {}).get(ty.name)
        fields = [[f, type_desc(t, classes, depth + 1)] for f, t in decl.fields] if decl is not None and depth < 3 else None
        return {"k": "class", "name": ty.name, "fields": fields}
    if isinstance(ty, ir.TList):
        return {"k": "list", "elem": type_desc(ty.elem, classes, depth + 1)}
    if isinstance(ty, ir.TRecord):
        return {"k": "record", "name": ty.name, "fields": [[n, type_desc(t)] for n, t in ty.fields]}
    return {"k": str(ty)}


def run_python(path: str, func: str, args: list[Any], timeout: float = TIMEOUT_S, extra: dict | None = None) -> dict[str, Any]:
    req = json.dumps({"path": os.path.abspath(path), "func": func, "args": args, **(extra or {})})
    env = dict(os.environ)
    env["PYTHONPATH"] = PKG_ROOT + os.pathsep + env.get("PYTHONPATH", "")
    try:
        p = subprocess.run(
            [sys.executable, "-m", "telic.replay_harness"],
            input=req,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=os.path.dirname(os.path.abspath(path)) or ".",
            env=env,
        )
    except subprocess.TimeoutExpired:
        return {"timeout": True}
    lines = [l for l in p.stdout.splitlines() if l.startswith("{")]
    if not lines:
        return {"harness_error": (p.stderr or p.stdout).strip()[-500:]}
    return json.loads(lines[-1])


def run_typescript(path: str, func: str, args: list[Any], timeout: float = TIMEOUT_S, extra: dict | None = None) -> dict[str, Any]:
    from .frontend.typescript import run_ts

    return run_ts(path, func, args, timeout, extra)


FUZZ_INPUTS = 400


def ts_contracts(module: ir.Module | None) -> dict[str, Any]:
    out: dict[str, Any] = {}
    if module is None:
        return out
    for f in module.functions.values():
        out[f.name] = {
            "params": [p.name for p in f.params],
            "lists": [i for i, p in enumerate(f.params) if isinstance(p.ty, ir.TList)],
            "requires": [c.text for c in f.requires],
            "ensures": [c.text for c in f.ensures],
        }
    return out


def fuzz(path: str, fn: ir.Function, lang: str, n: int = FUZZ_INPUTS, module: ir.Module | None = None) -> dict[str, Any]:
    classes = module.classes if module is not None else {}
    extra: dict[str, Any] = {"fuzz": n, "types": [type_desc(p.ty, classes) for p in fn.params]}
    if lang == "typescript":
        extra["contracts"] = ts_contracts(module)
    runner = run_python if lang == "python" else run_typescript
    return runner(path, fn.name, [], TIMEOUT_S * 3, extra)


EXPECTED = {
    "ensures": ("violation", "ensures"),
    "call": ("violation", "requires"),
    "inv.entry": ("violation", "invariant"),
    "inv.step": ("violation", "invariant"),
    "assert": ("violation", "assert"),
    "div": ("crash", "ZeroDivisionError"),
    "index": ("crash", "IndexError"),
    "none": ("crash", "TypeError"),
    "key": ("crash", "KeyError"),
    "class.inv": ("violation", "class.inv"),
}


def _same(text: str, clause) -> bool:
    return clause is not None and " ".join(str(text).split()) == clause.text


def matches(ob, out: dict[str, Any], fn: ir.Function, lang: str) -> bool:
    """Does what happened at runtime demonstrate *this* obligation failing?"""
    k = ob.kind
    v, crash = out.get("violation"), out.get("crash")
    if k == "ensures":
        return v == "ensures" and out.get("func") == fn.name and _same(out.get("text", ""), ob.clause)
    if k == "call":
        return v == "requires" and out.get("func") != fn.name and _same(out.get("text", ""), ob.clause)
    if k in ("inv.entry", "inv.step"):
        return v == "invariant" and _same(out.get("text", ""), ob.clause)
    if k == "assert":
        return (v in ("assert", "assume") and _same(out.get("text", ""), ob.clause)) or crash == "AssertionError"
    if k == "div":
        return crash == "ZeroDivisionError" or (lang == "typescript" and bool(out.get("nonfinite")))
    if k == "index":
        return crash == "IndexError" or bool(out.get("oob"))
    if k == "none":
        return crash in ("TypeError", "AttributeError") and ("NoneType" in str(out.get("msg", "")) or "None" in str(out.get("msg", "")))
    if k == "key":
        return crash == "KeyError" or bool(out.get("missing_key"))
    if k == "class.inv":
        return v == "class.inv" and out.get("func") == fn.name and _same(out.get("text", ""), ob.clause)
    if k == "raise":
        return crash is not None and crash not in ("RecursionError",)
    if k == "raises":
        return "returned_repr" in out
    if k == "return":
        return bool(out.get("returned_is_none")) and "returned_repr" in out
    return False


def describe(out: dict[str, Any], runtime: str) -> str:
    if "violation" in out:
        kind, text, where = out["violation"], out.get("text", ""), out.get("func", "")
        if kind == "ensures":
            return f"{runtime}: {out.get('detail') or 'returned'}; '{text}' is false"
        if kind == "requires":
            return f"{runtime}: called {where}() violating '@requires {text}'"
        if kind == "class.inv":
            return f"{runtime}: class invariant '{text}' is false when {where.split('.')[-1]}() returns"
        if kind == "invariant":
            return f"{runtime}: invariant '{text}' is false at runtime -- the invariant itself is wrong"
        return f"{runtime}: '@{kind} {text}' failed" + (f" at line {out.get('line')}" if out.get("line") else "")
    if "crash" in out:
        line = out.get("line")
        at = f" at line {line}" if line else ""
        msg = out.get("msg") or ""
        return f"{runtime}: {out['crash']}{': ' + msg if msg else ''}{at}"
    if out.get("returned_is_none"):
        return f"{runtime}: fell off the end and returned {out.get('returned_repr')}"
    return f"{runtime}: returned {out.get('returned_repr')}"


def classify(ob, out: dict[str, Any], fn: ir.Function, lang: str) -> tuple[bool, str, str | None]:
    """(confirmed, summary, violation). Confirmed only if the runtime failure
    is this obligation's failure: same clause, same kind of crash."""
    runtime = "node" if lang == "typescript" else "python"
    if out.get("timeout"):
        if ob.kind == "variant":
            return False, f"{runtime}: still running after {TIMEOUT_S:.0f}s (consistent with non-termination, not proof of it)", None
        return False, f"{runtime}: timed out after {TIMEOUT_S:.0f}s", None
    if "harness_error" in out:
        return False, f"could not run: {out['harness_error'].splitlines()[-1] if out['harness_error'] else 'unknown error'}", None
    if out.get("violation") == "requires" and out.get("func") == fn.name and ob.kind != "call":
        return False, f"{runtime}: the model violates '@requires {out.get('text', '')}' (telic model mismatch; please report)", None
    summary = describe(out, runtime)
    if matches(ob, out, fn, lang):
        what = out.get("violation") or out.get("crash") or ob.kind
        return True, summary, str(what)
    if "violation" in out or "crash" in out:
        return False, f"{summary} -- a real failure, but a different one from this obligation", None
    loop_state = any("@" in c.name for h in ob.hyps for c in _consts(h))
    if ob.kind in ("inv.step", "variant") or loop_state:
        return False, f"{summary} without violating anything -- the state behind this counterexample is unreachable; a loop invariant is too weak to rule it out", None
    return False, f"{summary} without violating anything", None


def _consts(t):
    from . import logic as L

    return L.consts(t)


def replay_verdicts(program: Program, rep) -> None:
    from .checker import Replay

    fn = rep.fn
    lang = rep.ref.module.language
    path = rep.ref.module.path
    root = getattr(program, "root", None)
    full = os.path.join(root, path) if root and not os.path.isabs(path) else path
    for v in rep.verdicts:
        if v.status != "refuted" or not v.model and fn.params:
            continue
        if v.reason.startswith("the model's list input is too large"):
            v.replay = Replay(False, False, v.reason)
            v.status = "unconfirmed"
            continue
        args = [encode_value(v.model.get(p.name), p.ty) for p in fn.params]
        try:
            if lang == "python":
                out = run_python(full, fn.name, args)
            else:
                out = run_typescript(full, fn.name, args, extra={"contracts": ts_contracts(rep.ref.module)})
        except Exception as e:  # pragma: no cover - defensive
            v.replay = Replay(False, False, f"could not replay: {e}")
            continue
        confirmed, summary, violation = classify(v.ob, out, fn, lang)
        v.replay = Replay(
            ran="harness_error" not in out,
            confirmed=confirmed,
            summary=summary,
            returned=out.get("returned_repr"),
            violation=violation,
            runtime="node" if lang == "typescript" else "python",
        )
    # The solver's state was unreachable? Search for a real failing input.
    pending = [v for v in rep.verdicts if v.status == "refuted" and v.replay is not None and v.replay.ran and not v.replay.confirmed]
    if pending:
        out = fuzz(full, fn, lang, module=rep.ref.module)
        if out.get("found"):
            what = out.get("violation") or out.get("crash")
            text = out.get("text", out.get("msg", ""))
            call = f"{fn.name}({out['args_repr']})"
            if out.get("violation"):
                desc = f"'@{what} {text}' fails"
            else:
                desc = f"raises {what}"
            for v in pending:
                v.replay.fuzz_witness = call  # type: ignore[attr-defined]
                v.replay.fuzz_desc = f"{v.replay.runtime}: {desc}"  # type: ignore[attr-defined]
                v.replay.fuzz_summary = f"but a real input breaks it: {call} -> {desc}"  # type: ignore[attr-defined]
                same_clause = v.ob.clause is not None and " ".join(str(text).split()) == v.ob.clause.text
                if same_clause and ((v.ob.kind in ("inv.entry", "inv.step") and what == "invariant") or (v.ob.kind == "ensures" and what == "ensures")):
                    v.replay.confirmed = True
        else:
            for v in pending:
                v.replay.fuzz_summary = f"{out.get('tried', 0)} random inputs found no failure"  # type: ignore[attr-defined]
    # A model the real program cannot reproduce is not a refutation.
    for v in rep.verdicts:
        if v.status == "refuted" and v.replay is not None and v.replay.ran and not v.replay.confirmed:
            v.status = "unconfirmed"
