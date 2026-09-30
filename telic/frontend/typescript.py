"""TypeScript -> telic IR, via the official TypeScript compiler (Node).

The lowering itself lives in ``ts/lower.mjs``; this module runs it and turns
its JSON into IR dataclasses. ``run_ts`` executes a TypeScript function for
counterexample replay and fuzzing, with contracts enforced at runtime.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any

from .. import ir

HERE = Path(__file__).resolve().parent / "ts"


class FrontendUnavailable(RuntimeError):
    pass


def _node() -> str:
    node = shutil.which("node")
    if node is None:
        raise FrontendUnavailable("TypeScript support needs Node.js >= 18 on PATH")
    return node


def ensure_installed() -> None:
    if (HERE / "node_modules" / "typescript" / "package.json").exists():
        return
    npm = shutil.which("npm")
    if npm is None:
        raise FrontendUnavailable("TypeScript support needs npm to install the 'typescript' package")
    subprocess.run([npm, "install", "--silent", "--no-audit", "--no-fund"], cwd=HERE, check=True, capture_output=True)


# ---------------------------------------------------------------------------
# JSON -> IR


def _type(t: dict[str, Any]) -> ir.Type:
    k = t["k"]
    if k == "int":
        return ir.INT
    if k == "real":
        return ir.REAL
    if k == "bool":
        return ir.BOOL
    if k == "str":
        return ir.STR
    if k == "none":
        return ir.NONE
    if k == "list":
        return ir.TList(_type(t["elem"]))
    if k == "record":
        return ir.TRecord(t["name"], tuple((n, _type(ft)) for n, ft in t["fields"]))
    if k == "option":
        return ir.TOption(_type(t["inner"]))
    if k == "dict":
        return ir.TDict(_type(t["key"]), _type(t["val"]), t.get("js", "object"))
    if k == "class":
        return ir.TClass(t["name"])
    if k == "opaque":
        return ir.TOpaque(t.get("why", ""))
    if k == "enum":
        return ir.TEnum(t["name"], tuple(t["members"]), tuple(t.get("values") or ()))
    raise ValueError(f"unknown type {t}")


def _loc(l: Any) -> ir.Loc:
    if isinstance(l, list):
        return ir.Loc(int(l[0]), int(l[1]) if len(l) > 1 else 0, int(l[2]) if len(l) > 2 else 0)
    return ir.Loc(int(l or 0))


def _expr(d: dict[str, Any]) -> ir.Expr:
    kind = d["e"]
    ty = _type(d["ty"])
    loc = _loc(d.get("loc"))
    if kind == "Lit":
        if d.get("frac"):
            n, den = d["frac"]
            return ir.Lit(ty, loc, Fraction(n, den))
        v = d["value"]
        if isinstance(ty, ir.TReal) and isinstance(v, (int, float)) and not isinstance(v, bool):
            return ir.Lit(ty, loc, Fraction(v))
        if isinstance(ty, ir.TInt) and isinstance(v, float):
            v = int(v)
        return ir.Lit(ty, loc, v)
    if kind == "Var":
        return ir.Var(ty, loc, d["name"])
    if kind == "Result":
        return ir.Result(ty, loc)
    if kind == "Old":
        return ir.Old(ty, loc, _expr(d["expr"]))
    if kind == "Unary":
        return ir.Unary(ty, loc, d["op"], _expr(d["arg"]))
    if kind == "Binary":
        return ir.Binary(ty, loc, d["op"], _expr(d["left"]), _expr(d["right"]))
    if kind == "Ite":
        return ir.Ite(ty, loc, _expr(d["cond"]), _expr(d["then"]), _expr(d["orelse"]))
    if kind == "Call":
        return ir.Call(ty, loc, d["func"], tuple(_expr(a) for a in d["args"]))
    if kind == "Builtin":
        return ir.Builtin(ty, loc, d["name"], tuple(_expr(a) for a in d["args"]))
    if kind == "Index":
        return ir.Index(ty, loc, _expr(d["seq"]), _expr(d["idx"]), bool(d["wrap"]))
    if kind == "Field":
        return ir.Field(ty, loc, _expr(d["obj"]), d["name"])
    if kind == "Quant":
        return ir.Quant(
            ty,
            loc,
            d["kind"],
            d["idx"],
            _expr(d["lo"]),
            _expr(d["hi"]),
            _expr(d["body"]),
            d.get("elem"),
            _expr(d["seq"]) if d.get("seq") else None,
        )
    if kind == "ListLit":
        return ir.ListLit(ty, loc, tuple(_expr(a) for a in d["elems"]))
    if kind == "RecordLit":
        return ir.RecordLit(ty, loc, tuple((n, _expr(v)) for n, v in d["fields"]))
    if kind == "New":
        return ir.New(ty, loc, d["cls"], tuple(_expr(a) for a in d["args"]))
    if kind == "Extern":
        return ir.Extern(ty, loc, d["name"], tuple(_expr(a) for a in d["args"]))
    raise ValueError(f"unknown expression {kind}")


def _clause(d: dict[str, Any] | None) -> ir.Clause | None:
    if d is None:
        return None
    return ir.Clause(d["kind"], _expr(d["expr"]), _loc(d["loc"]), d["text"], tuple(d.get("aims") or ()))


def _stmts(xs: list[dict[str, Any]]) -> tuple[ir.Stmt, ...]:
    return tuple(_stmt(x) for x in xs)


def _stmt(d: dict[str, Any]) -> ir.Stmt:
    k = d["s"]
    loc = _loc(d.get("loc"))
    if k == "Assign":
        return ir.Assign(loc, d["name"], _expr(d["value"]))
    if k == "IndexAssign":
        return ir.IndexAssign(loc, d["name"], _expr(d["idx"]), _expr(d["value"]), bool(d["wrap"]))
    if k == "Append":
        return ir.Append(loc, d["name"], _expr(d["value"]))
    if k == "If":
        return ir.If(loc, _expr(d["cond"]), _stmts(d["then"]), _stmts(d["orelse"]))
    if k == "While":
        return ir.While(loc, _expr(d["cond"]), tuple(_clause(c) for c in d["invariants"]), _clause(d.get("decreases")), _stmts(d["body"]), _stmts(d.get("step") or []))  # type: ignore[arg-type]
    if k == "ForRange":
        return ir.ForRange(loc, d["var"], _expr(d["lo"]), _expr(d["hi"]), tuple(_clause(c) for c in d["invariants"]), _stmts(d["body"]), bool(d.get("reeval")))  # type: ignore[arg-type]
    if k == "ForEach":
        return ir.ForEach(loc, d["elem"], d["idx"], _expr(d["seq"]), tuple(_clause(c) for c in d["invariants"]), _stmts(d["body"]), bool(d.get("idx_visible")))  # type: ignore[arg-type]
    if k == "Return":
        return ir.Return(loc, _expr(d["value"]) if d.get("value") else None)
    if k == "Break":
        return ir.Break(loc)
    if k == "Continue":
        return ir.Continue(loc)
    if k == "AssertStmt":
        return ir.AssertStmt(loc, _clause(d["clause"]), bool(d.get("native")))  # type: ignore[arg-type]
    if k == "AssumeStmt":
        return ir.AssumeStmt(loc, _clause(d["clause"]))  # type: ignore[arg-type]
    if k == "Raise":
        return ir.Raise(loc, d.get("what", "exception"), bool(d.get("caught")))
    if k == "FieldAssign":
        return ir.FieldAssign(loc, _expr(d["obj"]), d["cls"], d["field"], _expr(d["value"]))
    if k == "DictDel":
        return ir.DictDel(loc, d["name"], _expr(d["key"]), bool(d.get("strict", False)))
    if k == "Try":
        return ir.Try(loc, _stmts(d["body"]), tuple(_stmts(h) for h in d["handlers"]), _stmts(d.get("orelse") or []), _stmts(d.get("finalbody") or []))
    if k == "ExprStmt":
        return ir.ExprStmt(loc, _expr(d["expr"]))
    if k == "Unsupported":
        return ir.Unsupported(loc, d["reason"])
    raise ValueError(f"unknown statement {k}")


def _function(d: dict[str, Any]) -> ir.Function:
    return ir.Function(
        name=d["name"],
        loc=_loc(d["loc"]),
        end_line=int(d["end_line"]),
        params=[ir.Param(n, _type(t)) for n, t in d["params"]],
        ret=_type(d["ret"]),
        requires=[_clause(c) for c in d["requires"]],  # type: ignore[misc]
        ensures=[_clause(c) for c in d["ensures"]],  # type: ignore[misc]
        decreases=_clause(d.get("decreases")),
        raises=[_clause(c) for c in d["raises"]],  # type: ignore[misc]
        body=list(_stmts(d["body"])),
        aims=list(d.get("aims") or []),
        mirrors=[(m, ir.Loc(int(line))) for m, line in d.get("mirrors") or []],
        unsupported=[(m, ir.Loc(int(line))) for m, line in d.get("unsupported") or []],
        trusted=bool(d.get("trusted")),
        exported=bool(d.get("exported", True)),
        source=d.get("source", ""),
        locals={n: _type(t) for n, t in (d.get("locals") or {}).items()},
        escaped=set(d.get("escaped") or []),
    )


def _module(d: dict[str, Any]) -> ir.Module:
    m = ir.Module(path=d["path"], language="typescript", source=d["source"])
    m.records = {n: _type(t) for n, t in d.get("records", {}).items()}  # type: ignore[misc]
    for f in d["functions"]:
        fn = _function(f)
        m.functions[fn.name] = fn
    for cname, c in (d.get("classes") or {}).items():
        m.classes[cname] = ir.ClassDecl(cname, [(n, _type(t)) for n, t in c["fields"]], [_clause(x) for x in c.get("invariants", [])], _loc(c.get("loc")))  # type: ignore[misc]
    m.imports = {k: (v[0], v[1]) for k, v in (d.get("imports") or {}).items()}
    m.class_origin = dict(d.get("class_origin") or {})
    m.aims = [ir.AimDecl(i["id"], i["text"], ir.Loc(int(i["line"]), int(i.get("col", 0)))) for i in d.get("aims", [])]
    m.problems = [(msg, ir.Loc(int(line))) for msg, line in d.get("problems", [])]
    m.notes = [(msg, ir.Loc(int(line))) for msg, line in d.get("notes", [])]
    m.assumptions = list(d.get("assumptions", []))
    return m


_IMPORT = re.compile(r"""(?:\bfrom|\bimport|\brequire\s*\()\s*["'](\.[^"']*)["']""")


def project_imports(path: str, root: str) -> list[str]:
    """TypeScript files under ``root`` that ``path`` imports by relative
    specifier, resolved as ``lower.mjs`` resolves them."""
    try:
        src = Path(path).read_text()
    except OSError:
        return []
    out = []
    for spec in _IMPORT.findall(src):
        base = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(path)), spec))
        for cand in (base, base + ".ts", base + ".tsx", os.path.join(base, "index.ts"), os.path.join(base, "index.tsx"), re.sub(r"\.js$", ".ts", base)):
            if os.path.isfile(cand) and cand.startswith(os.path.abspath(root) + os.sep) and cand != os.path.abspath(path):
                out.append(cand)
                break
    return sorted(set(out))


def lower_typescript_files(files: list[str], root: str) -> dict[str, ir.Module]:
    ensure_installed()
    p = subprocess.run(
        [_node(), str(HERE / "lower.mjs"), os.path.abspath(root)] + [os.path.abspath(f) for f in files],
        capture_output=True,
        text=True,
    )
    if p.returncode != 0:
        raise FrontendUnavailable(f"TypeScript frontend failed:\n{p.stderr.strip()}")
    docs = json.loads(p.stdout)
    out: dict[str, ir.Module] = {}
    for f, d in zip(files, docs):
        out[f] = _module(d)
    return out


def lower_typescript(path: str, source: str | None = None, root: str | None = None) -> ir.Module:
    root = root or os.path.dirname(os.path.abspath(path))
    return lower_typescript_files([path], root)[path]


# ---------------------------------------------------------------------------
# Execution


def run_ts(path: str, func: str, args: list[Any], timeout: float, extra: dict | None = None) -> dict[str, Any]:
    ensure_installed()
    req = json.dumps({"path": os.path.abspath(path), "func": func, "args": args, **(extra or {})})
    try:
        p = subprocess.run(
            [_node(), str(HERE / "harness.mjs")],
            input=req,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return {"timeout": True}
    lines = [l for l in p.stdout.splitlines() if l.startswith("{")]
    if not lines:
        return {"harness_error": (p.stderr or p.stdout).strip()[-500:]}
    return json.loads(lines[-1])
