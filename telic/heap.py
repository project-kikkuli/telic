"""Versioned symbolic heap layout shared with ``core/``."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from . import ir, logic as L
from .py_number import PyNumber


ABI_VERSION = 1
LANGUAGE_TAGS = {"python": 1, "typescript": 2, "rust": 3, "swift": 4}
VALUE_TAGS = {
    "none": 0,
    "integer": 1,
    "real": 2,
    "boolean": 3,
    "text": 4,
    "reference": 5,
    "opaque": 6,
    "python_number": 7,
}
CELL_TAGS = {"free": 0, "list": 1, "dict": 2, "record": 3, "class": 4}


@dataclass(frozen=True)
class Layout:
    class_tags: tuple[tuple[str, int], ...]
    field_slots: tuple[tuple[str, str, int], ...]

    def json(self) -> dict[str, Any]:
        return {
            "version": ABI_VERSION,
            "language_tags": LANGUAGE_TAGS,
            "value_tags": VALUE_TAGS,
            "cell_tags": CELL_TAGS,
            "class_tags": [[name, tag] for name, tag in self.class_tags],
            "field_slots": [[owner, name, slot] for owner, name, slot in self.field_slots],
            "records": {
                "number": ["PythonNumber", [["is_int", "Bool"], ["integer", "Int"], ["floating", "Float64"]]],
                "box": "TelicValueV1",
                "key": "TelicKeyV1",
                "cell": "TelicCellV1",
            },
        }


def layout(program) -> Layout:
    names = sorted(program.classes)
    owners = {
        (program.field_storage_owner(c, name), name)
        for c, decl in program.classes.items()
        for name, _ in decl.fields
    }

    def add_record(owner: str, record: ir.TRecord) -> None:
        owners.update((owner, name) for name, _ in record.fields)

    def visit_type(language: str, ty: ir.Type) -> None:
        if isinstance(ty, ir.TRecord):
            add_record(record_field_owner(language, ty.name), ty)
            for _, field_ty in ty.fields:
                visit_type(language, field_ty)
        elif isinstance(ty, ir.TList):
            visit_type(language, ty.elem)
        elif isinstance(ty, ir.TDict):
            visit_type(language, ty.key)
            visit_type(language, ty.val)
        elif isinstance(ty, ir.TOption):
            visit_type(language, ty.inner)

    for module in program.modules:
        for record in module.records.values():
            owner = record_field_owner(module.language, record.name)
            add_record(owner, record)
        for fn in module.functions.values():
            for ty in [*(param.ty for param in fn.params), fn.ret, *fn.locals.values()]:
                visit_type(module.language, ty)
            for stmt in ir.walk_stmts(fn.body):
                for expr in ir.stmt_exprs(stmt):
                    for expr_node in ir.walk_expr(expr):
                        visit_type(module.language, expr_node.ty)
        for decl in module.classes.values():
            for _, ty in decl.fields:
                visit_type(module.language, ty)
    owners = sorted(owners)
    return Layout(
        tuple((name, i + 1) for i, name in enumerate(names)),
        tuple((owner, name, i + 1) for i, (owner, name) in enumerate(owners)),
    )


def record_field_owner(language: str, record_name: str) -> str:
    if language in ("python", "typescript"):
        return "property"
    return f"record:{record_name}"


def field_slot(program, owner: str, name: str) -> int:
    slots = {(slot_owner, field_name): slot for slot_owner, field_name, slot in layout(program).field_slots}
    try:
        return slots[(owner, name)]
    except KeyError as exc:
        raise KeyError(f"no heap field slot for {owner}.{name}") from exc


def number_sort() -> L.Sort:
    """The numeric lane is the public numeric ABI, not a heap-local copy."""
    return L.REC("PythonNumber", (("is_int", L.BOOL), ("integer", L.INT), ("floating", L.FLOAT64)))


REF = L.INT
KEY = L.REC("TelicKeyV1", (("tag", L.INT), ("numeric", L.REAL), ("text", L.STR)))
BOX = L.REC("TelicValueV1", (
    ("tag", L.INT), ("integer", L.INT), ("real", L.FLOAT64), ("python_number", number_sort()),
    ("boolean", L.BOOL), ("text", L.STR), ("reference", REF), ("opaque", L.OPAQUE),
))
CELL = L.REC("TelicCellV1", (
    ("allocated", L.BOOL), ("kind", L.INT), ("class", L.INT), ("len", L.INT), ("key_count", L.INT),
    ("seq", L.ARRAY(BOX)), ("map", L.ARRAY(BOX, KEY)), ("has", L.ARRAY(L.BOOL, KEY)),
    ("keys", L.ARRAY(KEY)), ("key_live", L.ARRAY(L.BOOL)),
    ("key_position", L.ARRAY(L.INT, KEY)), ("fields", L.ARRAY(BOX)),
))
HEAP = L.ARRAY(CELL)


def default(sort: L.Sort) -> L.Term:
    if sort == L.INT:
        return L.ZERO
    if sort in (L.FLOAT32, L.FLOAT64):
        return L.fval(0.0, sort)
    if sort == L.REAL:
        return L.RealV(0)
    if sort == L.BOOL:
        return L.FALSE
    if sort == L.STR:
        return L.StrV("")
    if sort == L.OPAQUE:
        return L.Const("opaque!default", L.OPAQUE)
    if sort.name == "Array":
        return L.const_array(sort, default(sort.elem))
    if sort.name == "Rec":
        return L.mkrec(sort, tuple(default(s) for _, s in sort.fields))
    raise TypeError(f"no heap default for {sort}")


def blank_cell() -> L.Term:
    return L.mkrec(CELL, tuple(default(s) for _, s in CELL.fields))


def blank_box(tag: int) -> L.Term:
    fields = [default(s) for _, s in BOX.fields]
    fields[0] = L.IntV(tag)
    return L.mkrec(BOX, tuple(fields))


def with_fields(record: L.Term, updates: dict[str, L.Term]) -> L.Term:
    return L.mkrec(record.sort, tuple(updates.get(name, L.field(record, name)) for name, _ in record.sort.fields))


def cell(heap: L.Term, ref: L.Term) -> L.Term:
    return L.select(heap, ref)


def read_len(heap: L.Term, ref: L.Term) -> L.Term:
    return L.field(cell(heap, ref), "len")


def read_list(heap: L.Term, ref: L.Term, index: L.Term) -> L.Term:
    return L.select(L.field(cell(heap, ref), "seq"), index)


def _cell_update(heap: L.Term, ref: L.Term, **updates: L.Term) -> L.Term:
    return L.store(heap, ref, with_fields(cell(heap, ref), updates))


def write_list(heap: L.Term, ref: L.Term, index: L.Term, value: L.Term) -> L.Term:
    current = cell(heap, ref)
    seq = L.store(L.field(current, "seq"), index, value)
    return L.store(heap, ref, with_fields(current, {"seq": seq}))


def append_list(heap: L.Term, ref: L.Term, value: L.Term) -> L.Term:
    current = cell(heap, ref)
    length = L.field(current, "len")
    seq = L.store(L.field(current, "seq"), length, value)
    return L.store(heap, ref, with_fields(current, {"seq": seq, "len": L.add(length, L.ONE)}))


def read_dict(heap: L.Term, ref: L.Term, key: L.Term) -> L.Term:
    return L.select(L.field(cell(heap, ref), "map"), key)


def write_dict(heap: L.Term, ref: L.Term, key: L.Term, value: L.Term, original_key: L.Term) -> L.Term:
    current = cell(heap, ref)
    entries = L.field(current, "has")
    existed = L.select(entries, key)
    new_len = L.ite(existed, L.field(current, "len"), L.add(L.field(current, "len"), L.ONE))
    count = L.field(current, "key_count")
    keys = L.field(current, "keys")
    live = L.field(current, "key_live")
    positions = L.field(current, "key_position")
    seq = L.field(current, "seq")
    keys = L.ite(existed, keys, L.store(keys, count, key))
    live = L.ite(existed, live, L.store(live, count, L.TRUE))
    positions = L.ite(existed, positions, L.store(positions, key, count))
    seq = L.ite(existed, seq, L.store(seq, count, original_key))
    return L.store(heap, ref, with_fields(current, {
        "map": L.store(L.field(current, "map"), key, value),
        "has": L.store(entries, key, L.TRUE), "keys": keys, "key_live": live,
        "key_position": positions, "seq": seq,
        "key_count": L.ite(existed, count, L.add(count, L.ONE)), "len": new_len,
    }))


def delete_dict(heap: L.Term, ref: L.Term, key: L.Term) -> L.Term:
    current = cell(heap, ref)
    has = L.field(current, "has")
    present = L.select(has, key)
    keys = L.field(current, "keys")
    live = L.field(current, "key_live")
    position = L.select(L.field(current, "key_position"), key)
    live = L.ite(present, L.store(live, position, L.FALSE), live)
    return L.store(heap, ref, with_fields(current, {
        "has": L.store(has, key, L.FALSE),
        "len": L.ite(present, L.sub(L.field(current, "len"), L.ONE), L.field(current, "len")),
        "keys": keys, "key_live": live,
    }))


@dataclass(frozen=True)
class RefVal:
    ref: L.Term
    ty: ir.Type


@dataclass(frozen=True)
class ListView:
    heap: L.Term
    ref: L.Term
    offset: L.Term
    length: L.Term
    elem_type: ir.Type

    def at(self, index: L.Term, ctx: Any, loc: ir.Loc):
        return unbox(read_list(self.heap, self.ref, L.add(self.offset, index)), self.elem_type, ctx, loc)


def key(value: Any, key_type: ir.Type, language: str = "python") -> tuple[L.Term, L.Term]:
    """Return a source-equality key and the condition that it is admissible.

    Python bool, integer and finite float keys share exact rational values;
    text remains in a distinct lane. Non-finite floats are rejected by the
    caller until Python's NaN dictionary identity behavior is modelled.
    """
    admissible = L.TRUE
    if isinstance(key_type, ir.TBool):
        number = L.ite(value, L.RealV(1), L.RealV(0))
        tag = 1
    elif isinstance(key_type, ir.TInt):
        number = L.to_real(value)
        tag = 1
    elif isinstance(key_type, ir.TPythonNumber):
        from .py_number import PyNumber

        py = PyNumber(L.field(value, "is_int"), L.field(value, "integer"), L.field(value, "floating")) if isinstance(value, L.Term) else value
        assert isinstance(py, PyNumber)
        number = L.ite(py.is_int, L.to_real(py.integer), L.fto_real(py.floating))
        admissible = L.or_(py.is_int, L.is_finite(py.floating))
        tag = 1
    elif isinstance(key_type, ir.TReal):
        if value.sort == L.REAL:
            number = value
        else:
            number = L.fto_real(value)
            admissible = L.is_finite(value)
        tag = 1
    elif isinstance(key_type, ir.TStr):
        number = L.RealV(0)
        tag = 2
        return L.mkrec(KEY, (L.IntV(tag), number, value)), L.TRUE
    else:
        raise TypeError(f"unsupported dictionary key type {key_type}")
    return L.mkrec(KEY, (L.IntV(tag), number, L.StrV(""))), admissible


def list_cell(items: list[L.Term], language: str = "python") -> L.Term:
    c = blank_cell()
    seq = L.const_array(L.ARRAY(BOX), blank_box(VALUE_TAGS["none"]))
    for i, item in enumerate(items):
        seq = L.store(seq, L.IntV(i), item)
    return with_fields(c, {
        "kind": L.IntV(CELL_TAGS["list"]), "len": L.IntV(len(items)), "seq": seq,
    })


def dict_cell(language: str = "python") -> L.Term:
    c = blank_cell()
    return with_fields(c, {
        "kind": L.IntV(CELL_TAGS["dict"]), "len": L.ZERO, "key_count": L.ZERO,
        "map": L.const_array(L.ARRAY(BOX, KEY), blank_box(VALUE_TAGS["none"])),
        "has": L.const_array(L.ARRAY(L.BOOL, KEY), L.FALSE),
        "key_live": L.const_array(L.ARRAY(L.BOOL), L.FALSE),
        "key_position": L.const_array(L.ARRAY(L.INT, KEY), L.ZERO),
    })


def class_cell(class_tag: int) -> L.Term:
    return with_fields(blank_cell(), {"kind": L.IntV(CELL_TAGS["class"]), "class": L.IntV(class_tag)})


def record_cell() -> L.Term:
    return with_fields(blank_cell(), {"kind": L.IntV(CELL_TAGS["record"])})


def read_field(heap: L.Term, ref: L.Term, slot: int) -> L.Term:
    return L.select(L.field(cell(heap, ref), "fields"), L.IntV(slot))


def write_field(heap: L.Term, ref: L.Term, slot: int, value: L.Term) -> L.Term:
    current = cell(heap, ref)
    fields = L.store(L.field(current, "fields"), L.IntV(slot), value)
    return L.store(heap, ref, with_fields(current, {"fields": fields}))


def allocate(heap: L.Term, contents: L.Term, fresh_ref: L.Term) -> tuple[L.Term, list[L.Term]]:
    allocated = L.field(cell(heap, fresh_ref), "allocated")
    contents = with_fields(contents, {"allocated": L.TRUE})
    return L.store(heap, fresh_ref, contents), [L.not_(allocated)]


def box(value: Any, static_type: ir.Type, language: str) -> L.Term:
    if language == "python" and isinstance(value, L.BoolV):
        static_type = ir.TBool()
    if language == "python" and isinstance(static_type, ir.TReal) and isinstance(value, PyNumber):
        return box(value, ir.TPythonNumber(), language)
    fields = {name: default(sort) for name, sort in BOX.fields}
    if isinstance(static_type, ir.TOption):
        if value is None or isinstance(static_type.inner, ir.TNone):
            return blank_box(VALUE_TAGS["none"])
        some = getattr(value, "some", None)
        inner = getattr(value, "val", value)
        if some is None and isinstance(value, L.Term) and value.sort.name == "Rec":
            some = L.field(value, "some")
            inner = L.field(value, "val")
        if some is None:
            some, inner = L.TRUE, value
        return L.ite(some, box(inner, static_type.inner, language), blank_box(VALUE_TAGS["none"]))
    if value is None or isinstance(static_type, ir.TNone):
        fields["tag"] = L.IntV(VALUE_TAGS["none"])
    elif isinstance(static_type, ir.TPythonNumber):
        number = value if isinstance(value, PyNumber) else L.field(value, "python_number")
        fields["tag"] = L.IntV(VALUE_TAGS["python_number"])
        fields["python_number"] = number if isinstance(number, L.Term) else L.mkrec(number_sort(), number.parts())
    elif isinstance(static_type, ir.TBool):
        fields.update(tag=L.IntV(VALUE_TAGS["boolean"]), boolean=value)
    elif isinstance(static_type, ir.TInt):
        fields.update(tag=L.IntV(VALUE_TAGS["integer"]), integer=value)
    elif isinstance(static_type, ir.TReal):
        fields.update(tag=L.IntV(VALUE_TAGS["real"]), real=L.to_float(value, L.FLOAT64) if value.sort != L.FLOAT64 else value)
    elif isinstance(static_type, ir.TStr):
        fields.update(tag=L.IntV(VALUE_TAGS["text"]), text=value)
    elif isinstance(static_type, (ir.TList, ir.TDict, ir.TClass, ir.TRecord)):
        ref = getattr(value, "ref", value)
        fields.update(tag=L.IntV(VALUE_TAGS["reference"]), reference=ref)
    elif isinstance(static_type, ir.TOpaque):
        fields.update(tag=L.IntV(VALUE_TAGS["opaque"]), opaque=value)
    else:
        raise TypeError(f"cannot box {static_type} for {language}")
    return L.mkrec(BOX, tuple(fields[name] for name, _ in BOX.fields))


def unbox(value: L.Term, view_type: ir.Type, ctx: Any, loc: ir.Loc):
    tag = L.field(value, "tag")
    if isinstance(view_type, ir.TOption):
        from .vcgen import OptVal

        return OptVal(L.ne(tag, L.IntV(VALUE_TAGS["none"])), unbox(value, view_type.inner, ctx, loc), view_type)
    if isinstance(view_type, ir.TPythonNumber):
        tagged = L.field(value, "python_number")
        is_number = L.eq(tag, L.IntV(VALUE_TAGS["python_number"]))
        is_int = L.eq(tag, L.IntV(VALUE_TAGS["integer"]))
        is_bool = L.eq(tag, L.IntV(VALUE_TAGS["boolean"]))
        integer = L.ite(is_bool, L.ite(L.field(value, "boolean"), L.ONE, L.ZERO), L.field(value, "integer"))
        converted = L.mkrec(number_sort(), (L.TRUE, integer, L.fval(0.0, L.FLOAT64)))
        as_real = L.mkrec(number_sort(), (L.FALSE, L.ZERO, L.field(value, "real")))
        return L.ite(is_number, tagged, L.ite(is_int, converted, L.ite(is_bool, converted, as_real)))
    if isinstance(view_type, ir.TBool):
        return L.field(value, "boolean")
    if isinstance(view_type, ir.TInt):
        is_bool = L.eq(tag, L.IntV(VALUE_TAGS["boolean"]))
        is_python_number = L.eq(tag, L.IntV(VALUE_TAGS["python_number"]))
        number = L.field(value, "python_number")
        return L.ite(is_bool, L.ite(L.field(value, "boolean"), L.ONE, L.ZERO), L.ite(is_python_number, L.field(number, "integer"), L.field(value, "integer")))
    if isinstance(view_type, ir.TReal):
        is_integer = L.eq(tag, L.IntV(VALUE_TAGS["integer"]))
        is_boolean = L.eq(tag, L.IntV(VALUE_TAGS["boolean"]))
        is_python_number = L.eq(tag, L.IntV(VALUE_TAGS["python_number"]))
        number = L.field(value, "python_number")
        boolean = L.to_float(L.ite(L.field(value, "boolean"), L.ONE, L.ZERO), L.FLOAT64)
        return L.ite(is_python_number, L.ite(L.field(number, "is_int"), L.to_float(L.field(number, "integer"), L.FLOAT64), L.field(number, "floating")), L.ite(is_integer, L.to_float(L.field(value, "integer"), L.FLOAT64), L.ite(is_boolean, boolean, L.field(value, "real"))))
    if isinstance(view_type, ir.TStr):
        return L.field(value, "text")
    if isinstance(view_type, (ir.TList, ir.TDict, ir.TClass, ir.TRecord)):
        return L.field(value, "reference")
    if isinstance(view_type, ir.TNone):
        return L.eq(tag, L.IntV(VALUE_TAGS["none"]))
    if isinstance(view_type, ir.TOpaque):
        return L.field(value, "opaque")
    raise TypeError(f"cannot view box as {view_type}")


def accepts(value: L.Term, view_type: ir.Type) -> L.Term:
    tag = L.field(value, "tag")
    if isinstance(view_type, ir.TOption):
        return L.or_(L.eq(tag, L.IntV(VALUE_TAGS["none"])), accepts(value, view_type.inner))
    if isinstance(view_type, ir.TPythonNumber):
        return L.or_(*[L.eq(tag, L.IntV(VALUE_TAGS[n])) for n in ("integer", "real", "boolean", "python_number")])
    if isinstance(view_type, ir.TBool):
        return L.eq(tag, L.IntV(VALUE_TAGS["boolean"]))
    if isinstance(view_type, ir.TInt):
        is_python_int = L.and_(L.eq(tag, L.IntV(VALUE_TAGS["python_number"])), L.field(L.field(value, "python_number"), "is_int"))
        return L.or_(L.eq(tag, L.IntV(VALUE_TAGS["integer"])), L.eq(tag, L.IntV(VALUE_TAGS["boolean"])), is_python_int)
    if isinstance(view_type, ir.TReal):
        return L.or_(*[L.eq(tag, L.IntV(VALUE_TAGS[n])) for n in ("real", "python_number", "integer", "boolean")])
    if isinstance(view_type, ir.TStr):
        return L.eq(tag, L.IntV(VALUE_TAGS["text"]))
    if isinstance(view_type, ir.TNone):
        return L.eq(tag, L.IntV(VALUE_TAGS["none"]))
    if isinstance(view_type, (ir.TList, ir.TDict, ir.TClass, ir.TRecord)):
        return L.eq(tag, L.IntV(VALUE_TAGS["reference"]))
    if isinstance(view_type, ir.TOpaque):
        return L.eq(tag, L.IntV(VALUE_TAGS["opaque"]))
    raise TypeError(f"cannot view boxed item as {view_type}")
