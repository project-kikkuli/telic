"""Subprocess entry point: run one function with contracts enforced.

Reads ``{"path", "func", "args"}`` as JSON on stdin, prints one JSON line.
"""

from __future__ import annotations

import copy
import json
import sys
import traceback
from fractions import Fraction
from typing import Any

from telic.runtime import settle, show


def decode(v: Any, module: Any, memo: dict | None = None) -> Any:
    """JSON -> Python values. Objects with the same reference decode to the
    same Python object, so aliasing in a counterexample is reproduced."""
    memo = {} if memo is None else memo
    if isinstance(v, list):
        return [decode(x, module, memo) for x in v]
    if isinstance(v, dict) and "__object__" in v:
        key = (v["__object__"], v.get("ref"))
        obj = memo.get(key)
        if obj is None:
            cls = getattr(module, v["__object__"])
            obj = object.__new__(cls)
            memo[key] = obj
        for k, x in (v.get("fields") or {}).items():
            object.__setattr__(obj, k, decode(x, module, memo))
        return obj
    if isinstance(v, dict) and "__json__" in v:
        return copy.deepcopy(v["__json__"])
    if isinstance(v, dict) and "__dict__" in v:
        return {decode(k, module, memo): decode(x, module, memo) for k, x in v["__dict__"]}
    if isinstance(v, dict) and "__enum__" in v:
        return getattr(getattr(module, v["__enum__"]), v["member"])
    if isinstance(v, dict) and "__opaque__" in v:
        s = _Stub()
        object.__setattr__(s, "_anything", bool(v.get("any")))
        return s
    if isinstance(v, dict) and "__real__" in v:
        n, d = v["__real__"]
        return float(Fraction(n, d))
    if isinstance(v, dict) and "__float__" in v:
        return float(v["__float__"])
    if isinstance(v, dict) and "__record__" in v:
        cls = getattr(module, v["__record__"])
        return cls(**{k: decode(x, module, memo) for k, x in v["fields"].items()})
    return v


def to_json(v: Any) -> Any:
    if isinstance(v, (list, tuple)):
        return [to_json(x) for x in v]
    if hasattr(v, "__dataclass_fields__"):
        return {k: to_json(getattr(v, k)) for k in v.__dataclass_fields__}
    if hasattr(v, "_asdict"):
        return {k: to_json(x) for k, x in v._asdict().items()}
    if isinstance(v, float) and v.is_integer():
        return int(v)
    return v


def gen(ty: dict, rnd, module: Any, depth: int = 0) -> Any:
    k = ty["k"]
    if k == "int":
        r = rnd.random()
        if r < 0.5:
            return rnd.choice([0, 1, -1, 2, 3, 4, 5, 7, 10, -2, 100])
        if r < 0.85:
            return rnd.randint(-20, 20)
        return rnd.randint(-1000, 1000)
    if k == "real":
        return rnd.choice([0.0, 0.5, 1.0, 1.5, 2.5, -0.5, 0.25, 3.0, 10.0]) if rnd.random() < 0.6 else round(rnd.uniform(-50, 50), 2)
    if k == "bool":
        return rnd.random() < 0.5
    if k == "str":
        return rnd.choice(["", "a", "b", "draft", "paid", "x"])
    if k == "list":
        n = rnd.choice([0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 8])
        return [gen(ty["elem"], rnd, module, depth + 1) for _ in range(n)]
    if k == "record":
        cls = getattr(module, ty["name"])
        return cls(**{f: gen(t, rnd, module, depth + 1) for f, t in ty["fields"]})
    if k == "option":
        return None if rnd.random() < 0.25 else gen(ty["inner"], rnd, module, depth)
    if k == "dict":
        n = rnd.choice([0, 1, 1, 2, 3])
        return {gen(ty["key"], rnd, module, depth + 1): gen(ty["val"], rnd, module, depth + 1) for _ in range(n)}
    if k == "enum":
        return getattr(getattr(module, ty["name"]), rnd.choice(ty["members"]))
    if k == "class":
        cls = getattr(module, ty["name"])
        obj = object.__new__(cls)
        for f, t in ty.get("fields") or []:
            object.__setattr__(obj, f, gen(t, rnd, module, depth + 1))
        return obj
    return None


REJECTED: dict = {}


def _outcome(fn: Any, args: list, module: Any, ContractViolation: Any, fname: str) -> dict | None:
    """None if the call passes, REJECTED if its own precondition rejects the
    input, otherwise a description of the failure."""
    STAND_IN.clear()
    out = _run(fn, args, module, ContractViolation, fname)
    return {**out, "stand_in": True} if out and out is not REJECTED and STAND_IN else out


def _run(fn: Any, args: list, module: Any, ContractViolation: Any, fname: str) -> dict | None:
    import copy

    try:
        settle(fn(*copy.deepcopy(args)))
        return None
    except ContractViolation as e:
        if e.kind == "requires" and e.func == fname:
            return REJECTED
        return {"violation": e.kind, "text": e.text, "line": e.line, "func": e.func, "detail": e.detail}
    except RecursionError:
        return {"crash": "RecursionError"}
    except Exception as e:
        line = None
        for fr in traceback.extract_tb(e.__traceback__):
            if fr.filename == getattr(module, "__file__", None):
                line = fr.lineno
        return {"crash": type(e).__name__, "msg": str(e), "line": line}


def _smaller(v: Any):
    if isinstance(v, bool):
        if v:
            yield False
        return
    if isinstance(v, int):
        if v != 0:
            yield 0
            yield v // 2 if v > 0 else -((-v) // 2)
            yield v - 1 if v > 0 else v + 1
        return
    if isinstance(v, float):
        if v != 0.0:
            yield 0.0
            yield float(int(v))
            yield v / 2
        return
    if isinstance(v, list):
        for i in range(len(v)):
            yield v[:i] + v[i + 1:]
        for i, x in enumerate(v):
            for y in _smaller(x):
                yield v[:i] + [y] + v[i + 1:]


def shrink(fn: Any, args: list, found: dict, module: Any, ContractViolation: Any, fname: str) -> tuple[list, dict]:
    key = (found.get("violation"), found.get("text"), found.get("crash"))
    for _ in range(200):
        progress = False
        for i, a in enumerate(args):
            for b in _smaller(a):
                cand = args[:i] + [b] + args[i + 1:]
                out = _outcome(fn, cand, module, ContractViolation, fname)
                if out and (out.get("violation"), out.get("text"), out.get("crash")) == key:
                    args, found, progress = cand, out, True
                    break
            if progress:
                break
        if not progress:
            break
    return args, found


def fuzz(fn: Any, types: list, n: int, module: Any, ContractViolation: Any, fname: str) -> dict:
    rnd = __import__("random").Random(0xC0FFEE)
    accepted = 0
    for _ in range(n * 20):
        if accepted >= n:
            break
        args = [gen(t, rnd, module) for t in types]
        out = _outcome(fn, args, module, ContractViolation, fname)
        if out is REJECTED:
            continue
        if out is None:
            accepted += 1
            continue
        accepted += 1
        args, out = shrink(fn, args, out, module, ContractViolation, fname)
        out.update({"found": True, "args_repr": ", ".join(show(a) for a in args), "tried": accepted})
        return out
    return {"found": False, "tried": accepted}


STUBBED: list[str] = []
# set once a run looks inside a stub: it computed with made-up values
STAND_IN: list[bool] = []


class _Stub:
    """Stands in for anything from a module that is not installed, or for an
    input telic does not model; ``_anything`` if that input's type admits
    every value (then the stub is a real input, not a made-up one)."""

    _anything = False

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        for k, v in kwargs.items():
            object.__setattr__(self, k, v)

    def __init_subclass__(cls, **kwargs: Any) -> None:
        pass

    def __call__(self, *args: Any, **kwargs: Any) -> Any:
        return self._derived()

    def __getattr__(self, name: str) -> Any:
        if name.startswith("__"):
            raise AttributeError(name)
        return self._derived()

    def _derived(self) -> "_Stub":
        if not self._anything:
            STAND_IN.append(True)
        s = _Stub()
        object.__setattr__(s, "_anything", self._anything)
        return s


class _StubFinder:
    """Last on sys.meta_path: an import that would fail yields a stub module,
    so counterexamples can run without the app's dependencies installed."""

    def find_spec(self, fullname: str, path: Any, target: Any = None) -> Any:
        import importlib.machinery

        return importlib.machinery.ModuleSpec(fullname, self, is_package=True)

    def create_module(self, spec: Any) -> Any:
        import types

        mod = types.ModuleType(spec.name)
        mod.__path__ = []  # type: ignore[attr-defined]
        mod.__getattr__ = lambda name: type(name, (_Stub,), {})  # type: ignore[attr-defined]
        STUBBED.append(spec.name)
        return mod

    def exec_module(self, module: Any) -> None:
        pass


def main() -> None:
    req = json.loads(sys.stdin.read())
    sys.meta_path.append(_StubFinder())
    from telic.runtime import ContractViolation, load_instrumented

    path = req["path"]
    sys.path.insert(0, __import__("os").path.dirname(path))
    try:
        mod = load_instrumented(path, "__telic_target__", root=req.get("root"))
        fn = mod
        for part in req["func"].split("."):
            fn = getattr(fn, part)
        memo: dict = {}
        args = [decode(a, mod, memo) for a in req.get("args", [])]
    except Exception as e:
        print(json.dumps({"harness_error": f"{type(e).__name__}: {e}"}))
        return
    if "batch" in req:
        results = []
        for raw in req["batch"]:
            memo = {}
            args = [decode(a, mod, memo) for a in raw]
            try:
                r = settle(fn(*args))
                results.append({"ok": True, "value": to_json(r), "repr": show(r)})
            except ContractViolation as e:
                if e.kind == "requires" and e.func == req["func"]:
                    results.append({"rejected": True})
                else:
                    results.append({"error": f"@{e.kind} {e.text} failed"})
            except Exception as e:
                results.append({"error": f"{type(e).__name__}: {e}"})
        print(json.dumps({"results": results}))
        return
    if "fuzz" in req:
        print(json.dumps(fuzz(fn, req["types"], req["fuzz"], mod, ContractViolation, req["func"])))
        return
    def emit(d: dict) -> None:
        print(json.dumps({**d, "stand_in": True} if STAND_IN else d))

    STAND_IN.clear()
    try:
        r = settle(fn(*args))
        emit({"returned_repr": show(r), "returned_is_none": r is None, "stubbed": STUBBED})
    except ContractViolation as e:
        emit({"violation": e.kind, "text": e.text, "line": e.line, "func": e.func, "detail": e.detail})
    except RecursionError:
        emit({"crash": "RecursionError", "msg": "maximum recursion depth exceeded"})
    except Exception as e:
        line = None
        for fr in traceback.extract_tb(e.__traceback__):
            if fr.filename == path:
                line = fr.lineno
        emit({"crash": type(e).__name__, "msg": str(e), "line": line})


if __name__ == "__main__":
    main()
