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


def encode_value(v: Any, ty: ir.Type) -> Any:
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


def format_value(v: Any, ty: ir.Type | None = None, lang: str = "python") -> str:
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
        return "[" + ", ".join(format_value(x, inner_ty, lang) for x in v) + "]"
    if isinstance(v, str):
        return json.dumps(v) if lang != "python" else repr(v)
    return str(v)


def call_text(fn: ir.Function, model: dict[str, Any], lang: str, names: bool = True) -> str:
    args = []
    for p in fn.params:
        v = format_value(encode_value(model.get(p.name), p.ty), p.ty, lang)
        if names and len(fn.params) > 1:
            v = f"{p.name}={v}" if lang == "python" else f"{p.name}: {v}"
        args.append(v)
    return f"{fn.name}({', '.join(args)})"


def type_desc(ty: ir.Type) -> dict[str, Any]:
    if isinstance(ty, ir.TList):
        return {"k": "list", "elem": type_desc(ty.elem)}
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
    extra: dict[str, Any] = {"fuzz": n, "types": [type_desc(p.ty) for p in fn.params]}
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
}


def classify(ob, out: dict[str, Any], fn: ir.Function, lang: str, callee: str | None) -> tuple[bool, str, str | None]:
    """(confirmed, summary, violation)."""
    runtime = "node" if lang == "typescript" else "python"
    if out.get("timeout"):
        if ob.kind == "variant":
            return True, f"{runtime}: did not terminate within {TIMEOUT_S:.0f}s", "timeout"
        return False, f"{runtime}: timed out after {TIMEOUT_S:.0f}s", "timeout"
    if "harness_error" in out:
        return False, f"could not run: {out['harness_error'].splitlines()[-1] if out['harness_error'] else 'unknown error'}", None
    ret = out.get("returned_repr")
    if "violation" in out:
        kind, text, where = out["violation"], out.get("text", ""), out.get("func", "")
        detail = out.get("detail", "")
        if kind == "requires" and where == fn.name and ob.kind != "call":
            return False, f"{runtime}: the model violates '@requires {text}' (telic model mismatch; please report)", None
        what = f"@{kind} {text}"
        if kind == "ensures":
            msg = f"{runtime}: {detail or 'returned'}; '{text}' is false"
        elif kind == "requires":
            msg = f"{runtime}: called {where}() violating '@requires {text}'"
        elif kind == "invariant":
            msg = f"{runtime}: invariant '{text}' is false at runtime -- the invariant itself is wrong"
        else:
            msg = f"{runtime}: '{what}' failed at line {out.get('line')}"
        return True, msg, what
    if "crash" in out:
        exc = out["crash"]
        line = out.get("line")
        at = f" at line {line}" if line else ""
        if ob.kind == "raise":
            return True, f"{runtime}: raised {exc}{at}", exc
        if lang == "typescript" and ob.kind == "index":
            return True, f"{runtime}: {out.get('msg') or exc}{at}", exc
        return True, f"{runtime}: {exc}: {out.get('msg', '')}{at}".rstrip(": "), exc
    if "returned_repr" in out:
        if ob.kind == "return" and out.get("returned_is_none"):
            return True, f"{runtime}: fell off the end and returned {ret}", "missing return"
        if lang == "typescript" and out.get("oob"):
            return True, f"{runtime}: read past the end of an array (got undefined){'; returned ' + ret if ret else ''}", "undefined read"
        if lang == "typescript" and ob.kind == "div" and out.get("nonfinite"):
            return True, f"{runtime}: returned {ret}", "division by zero"
        loop_state = any("@" in c.name for h in ob.hyps for c in _consts(h))
        if ob.kind in ("inv.step", "variant") or loop_state:
            return False, f"{runtime}: returned {ret} without violating anything -- the state behind this counterexample is unreachable; a loop invariant is too weak to rule it out", None
        return False, f"{runtime}: returned {ret} without violating anything", None
    return False, "no result", None


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
        args = [encode_value(v.model.get(p.name), p.ty) for p in fn.params]
        try:
            if lang == "python":
                out = run_python(full, fn.name, args)
            else:
                out = run_typescript(full, fn.name, args, extra={"contracts": ts_contracts(rep.ref.module)})
        except Exception as e:  # pragma: no cover - defensive
            v.replay = Replay(False, False, f"could not replay: {e}")
            continue
        callee = None
        confirmed, summary, violation = classify(v.ob, out, fn, lang, callee)
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
