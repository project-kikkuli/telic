"""Contract clauses in words.

Drafted intents start as a deterministic rendering of a proved clause:
``ensures result <= a`` on ``saturating`` reads "WHEN saturating returns,
the result shall be at most a." The rendering is plain and literal; a
generative oracle may rephrase it, and a person always edits it."""

from __future__ import annotations

import ast
import re

_CMP = {
    ast.Lt: "less than", ast.LtE: "at most", ast.Gt: "greater than", ast.GtE: "at least",
    ast.Eq: "equal to", ast.NotEq: "different from", ast.In: "in", ast.NotIn: "not in",
    ast.Is: "", ast.IsNot: "not",
}
_BIN = {ast.Add: "plus", ast.Sub: "minus", ast.Mult: "times", ast.Div: "divided by", ast.FloorDiv: "divided by", ast.Mod: "modulo", ast.Pow: "to the power of"}


def pythonish(text: str) -> str:
    """Rust/TypeScript clause syntax, rewritten to Python so one renderer reads all three."""
    t = text.strip()
    t = re.sub(r"\|\s*(\w+)\s*\|", r"lambda \1:", t)  # Rust closure |x| e
    t = re.sub(r"\((\w+)\)\s*=>", r"lambda \1:", t)
    t = re.sub(r"\b(\w+)\s*=>", r"lambda \1:", t)
    t = t.replace("&&", " and ").replace("||", " or ").replace("===", "==").replace("!==", "!=")
    t = re.sub(r"!(?!=)", " not ", t)
    t = re.sub(r"(\w+(?:\.\w+|\[[^\]]*\])*)\.len\(\)", r"len(\1)", t)
    t = re.sub(r"(\w+(?:\.\w+|\[[^\]]*\])*)\.length\b", r"len(\1)", t)
    t = re.sub(r"(\w+(?:\.\w+)*)\.is_empty\(\)", r"(len(\1) == 0)", t)
    t = re.sub(r"(\w+(?:\.\w+)*)\.is_none\(\)", r"(\1 is None)", t)
    t = re.sub(r"(\w+(?:\.\w+)*)\.is_some\(\)", r"(\1 is not None)", t)
    t = re.sub(r"\.unwrap\(\)", "", t)
    t = re.sub(r"\s+as\s+[iuf](8|16|32|64|128|size)\b", "", t)
    t = re.sub(r"\.iter\(\)", "", t)
    t = re.sub(r"\b(null|undefined)\b", "None", t)
    t = re.sub(r"\btrue\b", "True", t)
    t = re.sub(r"\bfalse\b", "False", t)
    return t


def clause_words(text: str) -> str | None:
    """The clause as a phrase ("the result is at most a"), or None when it
    has a shape the renderer does not know."""
    try:
        node = ast.parse(pythonish(text), mode="eval").body
        return _say(node)
    except (SyntaxError, _Unknown, ValueError, RecursionError):
        return None


def requirement(func: str, clause: str) -> str:
    """An EARS sentence for one proved clause (``ensures ...`` or ``requires ...``)."""
    kind, _, body = clause.partition(" ")
    name = func.split(".")[-1]
    if kind == "requires":
        said = clause_words(body)
        return f"The callers of {name} shall ensure that {said or '`' + body + '`'}."
    try:
        node = ast.parse(pythonish(body), mode="eval").body
        response = _shall(node)
    except (SyntaxError, _Unknown, ValueError, RecursionError):
        response = None
    return f"WHEN {name} returns, {response or f'the result shall satisfy `{body}`'}."


class _Unknown(Exception):
    pass


def _shall(n: ast.expr) -> str:
    """The clause as an EARS response: exactly one 'shall'."""
    if isinstance(n, ast.Compare) and len(n.ops) == 1:
        left, op, right = _say(n.left), n.ops[0], _say(n.comparators[0])
        if isinstance(op, (ast.Is, ast.Eq)) and _none(n.comparators[0]):
            return f"{left} shall be absent"
        if isinstance(op, (ast.IsNot, ast.NotEq)) and _none(n.comparators[0]):
            return f"{left} shall be present"
        if isinstance(op, ast.Eq) and _boolish(n.comparators[0]):
            return f"{left} shall be true exactly when {right}"
        if isinstance(op, ast.Eq):
            return f"{left} shall equal {right}"
        return f"{left} shall be {_CMP[type(op)]} {right}"
    if isinstance(n, ast.BoolOp) and isinstance(n.op, ast.Or) and len(n.values) == 2:
        # a or b  ==  if not a then b; the common shape is "x is None or <fact about x>"
        first, second = n.values
        return f"{_shall(second)} whenever {_say(_negate(first))}"
    if isinstance(n, ast.Call) and _name(n.func) == "implies" and len(n.args) == 2:
        return f"{_shall(n.args[1])} whenever {_say(n.args[0])}"
    return f"it shall hold that {_say(n)}"


def _negate(n: ast.expr) -> ast.expr:
    if isinstance(n, ast.Compare) and len(n.ops) == 1:
        flip = {ast.Is: ast.IsNot, ast.IsNot: ast.Is, ast.Eq: ast.NotEq, ast.NotEq: ast.Eq, ast.Lt: ast.GtE, ast.GtE: ast.Lt, ast.Gt: ast.LtE, ast.LtE: ast.Gt, ast.In: ast.NotIn, ast.NotIn: ast.In}
        return ast.Compare(left=n.left, ops=[flip[type(n.ops[0])]()], comparators=n.comparators)
    if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.Not):
        return n.operand
    return ast.UnaryOp(op=ast.Not(), operand=n)


def _boolish(n: ast.expr) -> bool:
    return isinstance(n, (ast.Compare, ast.BoolOp)) or (isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.Not))


def _none(n: ast.expr) -> bool:
    return isinstance(n, ast.Constant) and n.value is None


def _name(n: ast.expr) -> str:
    return n.id if isinstance(n, ast.Name) else n.attr if isinstance(n, ast.Attribute) else ""


def _say(n: ast.expr) -> str:
    if isinstance(n, ast.Name):
        return {"result": "the result", "self": "it", "True": "true", "False": "false"}.get(n.id, n.id)
    if isinstance(n, ast.Constant):
        if n.value is None:
            return "nothing"
        if isinstance(n.value, bool):
            return "true" if n.value else "false"
        return repr(n.value) if isinstance(n.value, str) else str(n.value)
    if isinstance(n, ast.Attribute):
        if isinstance(n.value, ast.Name) and n.value.id == "self":
            return f"the {n.attr.replace('_', ' ')}"
        return f"{_say(n.value)}'s {n.attr.replace('_', ' ')}"
    if isinstance(n, ast.Subscript):
        return f"{_say(n.value)}[{ast.unparse(n.slice)}]"
    if isinstance(n, ast.UnaryOp):
        if isinstance(n.op, ast.Not):
            if isinstance(n.operand, ast.Compare):
                return _say(_negate(n.operand))
            return f"not {_say(n.operand)}"
        if isinstance(n.op, ast.USub):
            return f"-{_say(n.operand)}"
    if isinstance(n, ast.BinOp) and type(n.op) in _BIN:
        return f"{_say(n.left)} {_BIN[type(n.op)]} {_say(n.right)}"
    if isinstance(n, ast.BoolOp):
        joiner = " and " if isinstance(n.op, ast.And) else " or "
        return joiner.join(_say(v) for v in n.values)
    if isinstance(n, ast.Compare):
        parts, left = [], n.left
        for op, right in zip(n.ops, n.comparators):
            if isinstance(op, (ast.Is, ast.IsNot, ast.Eq, ast.NotEq)) and _none(right):
                parts.append(f"{_say(left)} is {'absent' if isinstance(op, (ast.Is, ast.Eq)) else 'present'}")
            else:
                parts.append(f"{_say(left)} is {_CMP[type(op)]} {_say(right)}")
            left = right
        return " and ".join(parts)
    if isinstance(n, ast.IfExp):
        return f"{_say(n.body)} if {_say(n.test)}, else {_say(n.orelse)}"
    if isinstance(n, ast.Call):
        f = _name(n.func)
        args = n.args
        if f == "len" and len(args) == 1:
            return f"the length of {_say(args[0])}"
        if f == "old" and len(args) == 1:
            return f"{_say(args[0])} before the call"
        if f == "abs" and len(args) == 1:
            return f"the absolute value of {_say(args[0])}"
        if f in ("sum", "min", "max") and len(args) == 1:
            return f"the {'total' if f == 'sum' else f + 'imum'} of {_say(args[0])}"
        if f in ("all", "any", "every", "some") and args:
            return _quant(f, n)
        if f == "implies" and len(args) == 2:
            return f"{_say(args[1])} whenever {_say(args[0])}"
        if f in ("sorted", "is_sorted") and len(args) == 1:
            return f"{_say(args[0])} is sorted"
    raise _Unknown(ast.dump(n))


def _quant(f: str, n: ast.Call) -> str:
    every = f in ("all", "every")
    # Python: all(p(x) for x in xs); Rust/TS after rewriting: all(xs, lambda x: p) or xs.all(lambda x: p)
    if isinstance(n.func, ast.Attribute) and n.args and isinstance(n.args[0], ast.Lambda):
        coll, lam = n.func.value, n.args[0]
        var, body = lam.args.args[0].arg, lam.body
    elif n.args and isinstance(n.args[0], ast.GeneratorExp) and len(n.args[0].generators) == 1:
        g = n.args[0].generators[0]
        if not isinstance(g.target, ast.Name) or g.ifs:
            raise _Unknown("quantifier")
        coll, var, body = g.iter, g.target.id, n.args[0].elt
    else:
        raise _Unknown("quantifier")
    if isinstance(coll, ast.Call) and _name(coll.func) == "range" and len(coll.args) in (1, 2):
        lo = _say(coll.args[0]) if len(coll.args) == 2 else "0"
        hi = _say(coll.args[-1])
        where = f"every {var} from {lo} below {hi}" if every else f"some {var} from {lo} below {hi}"
    else:
        where = f"every {var} in {_say(coll)}" if every else f"some {var} in {_say(coll)}"
    return f"for {where}, {_say(body)}"
