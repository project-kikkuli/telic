"""Swift expressions as a small tree with Swift's own operator structure.

tree-sitter-swift parses a sequence of binary operators with the wrong
grouping whenever precedences mix (``a && b || c`` comes back as
``a && (b || c)``), attaches prefix operators to the first operand of a
postfix chain (``!a.isEmpty`` as ``(!a).isEmpty``) and ``try`` to the first
operand of a sequence. Swift itself parses an operator sequence flat and
folds it by precedence group afterwards; this module does the same: it
flattens what tree-sitter built back into source order and refolds it with
the standard library's precedence groups, so the lowering never sees a
misgrouped expression.
"""

from __future__ import annotations

from typing import Any

_PARSER: Any = None


class SwiftUnavailable(Exception):
    pass


def parser() -> Any:
    global _PARSER
    if _PARSER is None:
        try:
            import tree_sitter
            import tree_sitter_swift
        except ImportError as e:  # pragma: no cover - depends on the install
            raise SwiftUnavailable("Swift support needs the 'tree-sitter' and 'tree-sitter-swift' packages (pip install 'telic[swift]')") from e
        _PARSER = tree_sitter.Parser(tree_sitter.Language(tree_sitter_swift.language()))
    return _PARSER


def text(n: Any) -> str:
    return n.text.decode("utf8")


def named(n: Any) -> list[Any]:
    return [c for c in n.children if c.is_named and c.type not in ("comment", "multiline_comment")]


class X:
    """One normalized expression. ``at`` is the tree-sitter node it came
    from (for locations); the other attributes depend on ``kind``."""

    def __init__(self, kind: str, at: Any, **kw: Any):
        self.kind = kind
        self.at = at
        self.__dict__.update(kw)

    @property
    def start_point(self) -> tuple[int, int]:
        return self.at.start_point

    @property
    def end_point(self) -> tuple[int, int]:
        return self.at.end_point

    @property
    def src(self) -> str:
        return text(self.at)

    def __repr__(self) -> str:  # debugging aid
        fields = {k: v for k, v in self.__dict__.items() if k not in ("at", "kind")}
        return f"X({self.kind}, {fields})"


class Unsupported(Exception):
    def __init__(self, msg: str, node: Any):
        super().__init__(msg)
        self.node = node


# Precedence groups of the standard library, tightest first.
PREC = {
    **dict.fromkeys(("<<", ">>", "&<<", "&>>"), 10),
    **dict.fromkeys(("*", "/", "%", "&", "&*"), 9),
    **dict.fromkeys(("+", "-", "|", "^", "&+", "&-"), 8),
    **dict.fromkeys(("...", "..<"), 7),
    **dict.fromkeys(("as", "as?", "as!", "is"), 6),
    "??": 5,
    **dict.fromkeys(("<", "<=", ">", ">=", "==", "!=", "===", "!==", "~="), 4),
    "&&": 3,
    "||": 2,
    "?:": 1,
}
RIGHT = {"??", "?:"}
CASTS = {"as", "as?", "as!", "is"}

BINARY = {
    "additive_expression",
    "multiplicative_expression",
    "comparison_expression",
    "equality_expression",
    "conjunction_expression",
    "disjunction_expression",
    "infix_expression",
    "nil_coalescing_expression",
    "bitwise_operation",
    "range_expression",
    "ternary_expression",
    "as_expression",
    "check_expression",
}


class Op:
    """An operator in a flattened sequence: binary, a cast (with its type
    node), or the ``? t :`` of a ternary (with its middle operand)."""

    def __init__(self, op: str, at: Any, type_node: Any = None, mid: X | None = None):
        self.op = op
        self.at = at
        self.type_node = type_node
        self.mid = mid


def _operator(n: Any) -> tuple[str, Any]:
    """The operator token of a binary node: the child that is neither operand."""
    fields = {"lhs", "rhs", "value", "if_nil", "start", "end"}
    for i, c in enumerate(n.children):
        f = n.field_name_for_child(i)
        if f in fields or c.type in ("comment", "multiline_comment"):
            continue
        return text(c), c
    raise Unsupported(f"cannot find the operator of '{text(n)}'", n)


def _operands(n: Any) -> tuple[Any, Any]:
    left = n.child_by_field_name("lhs") or n.child_by_field_name("value") or n.child_by_field_name("start")
    right = n.child_by_field_name("rhs") or n.child_by_field_name("if_nil") or n.child_by_field_name("end")
    if left is None or right is None:
        raise Unsupported(f"unsupported operator expression '{text(n)}'", n)
    return left, right


def flatten(n: Any) -> list[Any]:
    """An operator sequence in source order: operands (X) and operators (Op)."""
    t = n.type
    if t == "ternary_expression":
        c, a, b = n.child_by_field_name("condition"), n.child_by_field_name("if_true"), n.child_by_field_name("if_false")
        return flatten(c) + [Op("?:", n, mid=norm(a))] + flatten(b)
    if t in ("as_expression", "check_expression"):
        kids = named(n)
        e = n.child_by_field_name("expr") or kids[0]
        ty = kids[-1]
        op = "is" if t == "check_expression" else next(text(c) for c in n.children if c.type == "as_operator").replace(" ", "")
        return flatten(e) + [Op(op, n, type_node=ty)]
    if t in BINARY:
        left, right = _operands(n)
        op, at = _operator(n)
        return flatten(left) + [Op(op, at)] + flatten(right)
    if t == "prefix_expression":
        op = n.child_by_field_name("operation")
        target = n.child_by_field_name("target")
        if op is not None and target is not None and text(op) != "." and _leads_sequence(target):
            seq = flatten(target)  # '-a * b' is (-a) * b: the prefix binds to the first operand
            seq[0] = _prefix(text(op), seq[0], n)
            return seq
    if t in ("-", "+", "~", "bang") and not n.named_children:
        # '-(a)' after an operator comes back as the operator, then a call
        return [X("prefixop", n, op="!" if t == "bang" else t)]
    if t == "try_expression":
        e = n.child_by_field_name("expr")
        if e is not None and _leads_sequence(e):
            seq = flatten(e)
            seq[0] = X("try", n, op=_try_kind(n), e=seq[0], lead=True)
            return seq
    r = norm(n, as_seq=True)
    return r if isinstance(r, list) else [r]


def _leads_sequence(n: Any) -> bool:
    while n.type in ("prefix_expression", "try_expression", "await_expression"):
        if n.type == "prefix_expression" and n.child_by_field_name("operation") is not None and text(n.child_by_field_name("operation")) == ".":
            return False
        n = n.child_by_field_name("target") or n.child_by_field_name("expr") or (named(n)[-1] if named(n) else n)
        if n is None:
            return False
    return n.type in BINARY


def _prefix(op: str, e: X, at: Any) -> X:
    return X("prefix", at, op=op, e=e)


def _try_kind(n: Any) -> str:
    op = next((c for c in n.children if c.type == "try_operator"), None)
    return text(op).replace(" ", "") if op is not None else "try"


def fold(seq: list[Any]) -> X:
    """Fold an operator sequence by precedence (Swift's sequence folding)."""
    lead: list[X] = []
    while isinstance(seq[0], X) and seq[0].kind in ("try", "await") and len(seq) > 1:
        # 'try' and 'await' cover everything to their right
        lead.append(seq[0])
        seq = [seq[0].e] + seq[1:]
    pos = [0]

    def operand() -> X:
        e = seq[pos[0]]
        if not isinstance(e, X):
            raise Unsupported(f"unexpected operator '{e.op}'", e.at)
        pos[0] += 1
        return e

    def climb(min_prec: int) -> X:
        lhs = operand()
        while pos[0] < len(seq):
            o = seq[pos[0]]
            assert isinstance(o, Op)
            p = PREC.get(o.op)
            if p is None:
                raise Unsupported(f"operator '{o.op}' is not supported", o.at)
            if p < min_prec:
                break
            pos[0] += 1
            if o.op in CASTS:
                lhs = X("cast", o.at, op=o.op, e=lhs, type_node=o.type_node, whole=o.at)
                continue
            rhs = climb(p if o.op in RIGHT else p + 1)
            if o.op == "?:":
                lhs = X("ternary", o.at, c=lhs, t=o.mid, f=rhs)
            elif o.op in ("...", "..<"):
                lhs = X("range", o.at, op=o.op, lo=lhs, hi=rhs)
            else:
                lhs = X("binop", o.at, op=o.op, l=lhs, r=rhs)
        return lhs

    out = climb(0)
    if pos[0] != len(seq):
        raise Unsupported("cannot fold this operator sequence", seq[pos[0]].at)
    for t in reversed(lead):
        out = X("try", t.at, op=t.op, e=out) if t.kind == "try" else X("await", t.at, e=out)
    return out


def _span(e: X, whole: Any) -> X:
    e.at = whole
    return e


def norm(n: Any, as_seq: bool = False) -> Any:
    """Normalize a tree-sitter expression node. With ``as_seq``, a postfix
    operation tree-sitter attached to an operator sequence comes back as
    that sequence (for the enclosing fold)."""
    t = n.type
    if t in BINARY or t == "prefix_expression" and _leads_sequence(n) or t == "try_expression" and _leads_sequence(n):
        return _span(fold(flatten(n)), n)
    if t == "simple_identifier":
        return X("name", n, id=text(n))
    if not n.is_named and t in ("+", "-", "*", "/", "<", ">", "<=", ">=", "==", "&&", "||"):
        return X("name", n, id=t)  # an operator passed as a function: reduce(0, +)
    if t == "integer_literal" or t in ("hex_literal", "oct_literal", "bin_literal"):
        return X("int", n, text=text(n))
    if t == "real_literal":
        return X("real", n, text=text(n))
    if t == "boolean_literal":
        return X("bool", n, value=text(n) == "true")
    if t in ("line_string_literal", "multi_line_string_literal"):
        parts: list[Any] = []
        raw = False
        for c in n.children:
            if c.type in ("line_str_text", "multi_line_str_text"):
                parts.append(text(c))
            elif c.type == "str_escaped_char":
                parts.append(_escape(text(c), c))
            elif c.type == "interpolated_expression":
                inner = named(c)
                if len(inner) != 1:
                    raise Unsupported("string interpolation with labels or formats", c)
                parts.append(norm(inner[0]))
            elif c.type in ('"', '"""', "\\(", ")"):
                continue
            elif c.is_named:
                raw = True
        if raw:
            raise Unsupported("this string literal form is not supported", n)
        return X("str", n, parts=parts)
    if t == "raw_string_literal":
        raise Unsupported("raw string literals are not supported", n)
    if text(n) == "nil" and t in ("nil", "simple_identifier") or t == "nil":
        return X("nil", n)
    if t == "self_expression":
        return X("self", n)
    if t == "super_expression":
        return X("super", n)
    if t == "tuple_expression":
        items = _tuple_items(n)
        if len(items) == 1 and items[0][0] is None:
            return X("paren", n, e=norm(items[0][1]))
        return X("tuple", n, items=[(lbl, norm(v)) for lbl, v in items])
    if t == "prefix_expression":
        op = n.child_by_field_name("operation")
        target = n.child_by_field_name("target")
        if op is None or target is None:
            raise Unsupported(f"unsupported prefix expression '{text(n)}'", n)
        if text(op) == ".":
            return X("implicit", n, name=text(target))
        return X("prefix", n, op=text(op), e=norm(target))
    if t == "try_expression":
        return X("try", n, op=_try_kind(n), e=norm(n.child_by_field_name("expr") or named(n)[-1]))
    if t == "await_expression":
        return X("await", n, e=norm(named(n)[-1]))
    if t == "navigation_expression":
        target = n.child_by_field_name("target")
        suffix = n.child_by_field_name("suffix")
        opt = any(c.type == "?" for c in n.children)
        name_n = suffix.child_by_field_name("suffix") if suffix is not None else None
        if name_n is None:
            raise Unsupported(f"unsupported member access '{text(n)}'", n)
        if target is None:  # '.member' after a type (Int.max) is still a target; this is not
            raise Unsupported(f"unsupported member access '{text(n)}'", n)
        return _suffixed(target, lambda b: X("member", n, base=b, name=text(name_n), opt=opt), n, as_seq)
    if t == "call_expression" and n.children and n.children[0].type in ("-", "+", "~", "bang"):
        # '-(a * b)' and '!(a && b)' come back as calls of the operator
        va = next((c for s in n.children if s.type == "call_suffix" for c in s.children if c.type == "value_arguments"), None)
        args = _arguments(va) if va is not None else []
        if len(args) != 1 or args[0][0] is not None:
            raise Unsupported(f"unsupported expression '{text(n)}'", n)
        op = "!" if n.children[0].type == "bang" else n.children[0].type
        return X("prefix", n, op=op, e=X("paren", n, e=args[0][1]))
    if t == "call_expression":
        kids = named(n)
        suffix = next((c for c in kids if c.type == "call_suffix"), None)
        callee_n = kids[0]
        opt = any(c.type == "?" for c in n.children)
        if suffix is None:
            raise Unsupported(f"unsupported call '{text(n)}'", n)
        va = next((c for c in suffix.children if c.type == "value_arguments"), None)
        trailing = [norm(c) for c in suffix.children if c.type == "lambda_literal"]
        subscript = va is not None and any(c.type == "[" for c in va.children)
        args = _arguments(va) if va is not None else []
        if subscript:
            return _suffixed(callee_n, lambda b: X("subscript", n, base=b, args=args, opt=opt), n, as_seq)
        return _suffixed(callee_n, lambda b: X("call", n, callee=b, args=args, trailing=trailing, opt=opt), n, as_seq)
    if t == "postfix_expression":
        op = n.child_by_field_name("operation")
        target = n.child_by_field_name("target")
        o = text(op) if op is not None else text(n.children[-1])
        if target is None:
            target = named(n)[0]
        if o == "!":
            return _suffixed(target, lambda b: X("force", n, e=b), n, as_seq)
        if o in ("++", "--"):
            raise Unsupported(f"'{o}' does not exist in Swift", n)
        raise Unsupported(f"unsupported postfix operator '{o}'", n)
    if t == "array_literal":
        return X("array", n, elems=[norm(c) for c in n.children_by_field_name("element")])
    if t == "dictionary_literal":
        keys = n.children_by_field_name("key")
        vals = n.children_by_field_name("value")
        return X("dict", n, pairs=[(norm(k), norm(v)) for k, v in zip(keys, vals)])
    if t == "lambda_literal":
        return X("closure", n, params=_closure_params(n), body=next((c for c in n.children if c.type == "statements"), None))
    if t in ("open_end_range_expression", "open_start_range_expression"):
        kids = named(n)
        e = norm(kids[0]) if kids else None
        op = "..<" if "..<" in text(n) else "..."
        return X("range", n, op=op, lo=e if t == "open_end_range_expression" else None, hi=e if t == "open_start_range_expression" else None)
    if t in ("user_type", "type_identifier"):
        return X("name", n, id=text(n))
    if t == "key_path_expression":
        raise Unsupported("key paths are not supported", n)
    if t == "if_statement" or t == "switch_statement":
        return X("stmt_expr", n, node=n)
    raise Unsupported(f"unsupported expression: {t.replace('_', ' ')}", n)


def _suffixed(target: Any, make: Any, whole: Any, as_seq: bool = False) -> Any:
    """A postfix operation (call, member, subscript, '!') on ``target``. When
    tree-sitter hands it an operator sequence (``a && xs.allSatisfy { ... }``
    comes back as a call of ``a && xs.allSatisfy``), it belongs to the
    sequence's last operand."""
    if target.type in BINARY or _leads_sequence(target):
        seq = flatten(target)
    else:
        r = norm(target, as_seq=True)  # a chain whose own target was a sequence
        if not isinstance(r, list):
            return _postfix(r, make)
        seq = r
    if not isinstance(seq[-1], X):
        raise Unsupported(f"unsupported expression '{text(whole)}'", whole)
    if seq[-1].kind == "prefixop":
        probe = make(X("name", whole, id="_"))
        if probe.kind != "call" or len(probe.args) != 1 or probe.args[0][0] is not None or probe.trailing:
            raise Unsupported(f"unsupported expression '{text(whole)}'", whole)
        seq[-1] = X("prefix", whole, op=seq[-1].op, e=X("paren", whole, e=probe.args[0][1]))
    else:
        seq[-1] = _postfix(seq[-1], make)
    return seq if as_seq else _span(fold(seq), whole)


def _postfix(base: X, make: Any) -> X:
    """Apply a postfix operation. A prefix operator or 'try' that
    tree-sitter attached to the chain's first operand covers the whole chain."""
    if base.kind == "prefix":
        return X("prefix", base.at, op=base.op, e=_postfix(base.e, make))
    if base.kind == "try":
        return X("try", base.at, op=base.op, e=_postfix(base.e, make))
    if base.kind == "await":
        return X("await", base.at, e=_postfix(base.e, make))
    return make(base)


def _tuple_items(n: Any) -> list[tuple[str | None, Any]]:
    out: list[tuple[str | None, Any]] = []
    label = None
    for c in n.children:
        if c.type in ("(", ")", ",", "comment"):
            continue
        if c.type == ":":
            continue
        if c.type == "simple_identifier" and c.next_sibling is not None and c.next_sibling.type == ":":
            label = text(c)
            continue
        if c.is_named or c.type == "nil":
            out.append((label, c))
            label = None
    return out


def _arguments(va: Any) -> list[tuple[str | None, X]]:
    out: list[tuple[str | None, X]] = []
    for a in va.children:
        if a.type != "value_argument":
            continue
        lbl = a.child_by_field_name("name")
        val = a.child_by_field_name("value")
        if val is None:
            raise Unsupported(f"unsupported argument '{text(a)}'", a)
        out.append((text(lbl).rstrip(":").strip() if lbl is not None else None, norm(val)))
    return out


def _closure_params(n: Any) -> list[str] | None:
    """Explicit closure parameter names, or None for '$0'-style closures."""
    ty = n.child_by_field_name("type")
    if ty is None:
        ty = next((c for c in n.children if c.type == "lambda_function_type"), None)
    if ty is None:
        return None
    ps = next((c for c in ty.children if c.type == "lambda_function_type_parameters"), None)
    if ps is None:
        return []
    out = []
    for p in ps.children:
        if p.type == "lambda_parameter":
            nm = p.child_by_field_name("name")
            out.append(text(nm) if nm is not None else text(p).split(":")[0].strip())
    return out


_ESC = {"\\n": "\n", "\\t": "\t", "\\r": "\r", "\\0": "\0", '\\"': '"', "\\'": "'", "\\\\": "\\"}


def _escape(s: str, n: Any) -> str:
    if s in _ESC:
        return _ESC[s]
    if s.startswith("\\u{") and s.endswith("}"):
        try:
            return chr(int(s[3:-1], 16))
        except ValueError:
            pass
    raise Unsupported(f"unsupported escape {s}", n)


def parse_expression(src: str) -> tuple[Any, Any]:
    """Parse ``src`` as one Swift expression: (tree, node), or (tree, None)."""
    wrapped = f"let __telic = (\n{src}\n)"
    tree = parser().parse(wrapped.encode("utf8"))
    if tree.root_node.has_error:
        return tree, None
    decl = tree.root_node.children[0]
    val = decl.child_by_field_name("value")
    return tree, val
