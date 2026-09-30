"""JavaScript regular expressions as SMT-LIB regular languages.

Only a subset is translated: characters, escapes (``\\d \\s \\w`` and
escaped punctuation), classes with ranges, ``.``, groups, alternation,
the quantifiers ``* + ? {n} {n,} {n,m}`` (lazy or not: the same language),
and ``^``/``$`` at the ends. Anything else (backreferences, lookaround,
flags other than ``u``) is not translated, and the call stays unchecked.
"""

from __future__ import annotations

from dataclasses import dataclass, field

_WS = " \t\n\r\x0b\x0c\u00a0\u1680\u2028\u2029\u202f\u205f\u3000\ufeff"


class Untranslatable(Exception):
    pass


def _lit(s: str) -> str:
    out = []
    for ch in s:
        if ch == '"':
            out.append('""')
        elif 32 <= ord(ch) < 127 and ch != "\\":
            out.append(ch)
        else:
            out.append("\\u{%x}" % ord(ch))
    return f'(str.to_re "{"".join(out)}")'


def _range(a: str, b: str) -> str:
    return f'(re.range "{_lit(a)[12:-2]}" "{_lit(b)[12:-2]}")'


def _union(parts: list[str]) -> str:
    return parts[0] if len(parts) == 1 else f"(re.union {' '.join(parts)})"


def _concat(parts: list[str]) -> str:
    if not parts:
        return '(str.to_re "")'
    return parts[0] if len(parts) == 1 else f"(re.++ {' '.join(parts)})"


_DIGIT = _range("0", "9")
_WORD = _union([_range("a", "z"), _range("A", "Z"), _DIGIT, _lit("_")])
_SPACE = _union([_lit(c) for c in _WS] + [_range("\u2000", "\u200a")])  # JavaScript's \s, exactly
_ANY_BUT_NEWLINE = "(re.diff re.allchar (re.union (str.to_re \"\\u{a}\") (str.to_re \"\\u{d}\") (str.to_re \"\\u{2028}\") (str.to_re \"\\u{2029}\")))"


@dataclass
class Group:
    index: int
    regex: str
    mandatory: bool  # takes part in every match


@dataclass
class Translation:
    search: str  # the strings exec finds a match in
    whole: str  # what a match itself is
    groups: list[Group] = field(default_factory=list)


class _Parser:
    def __init__(self, src: str):
        self.s = src
        self.i = 0
        self.groups: list[Group] = []
        self.count = 0

    def peek(self) -> str | None:
        return self.s[self.i] if self.i < len(self.s) else None

    def take(self) -> str:
        ch = self.s[self.i]
        self.i += 1
        return ch

    def alternation(self, mandatory: bool) -> str:
        before = self.count
        branches = [self.sequence(mandatory)]
        while self.peek() == "|":
            self.take()
            branches.append(self.sequence(False))
        if len(branches) > 1:  # a group in one branch takes no part in a match by another
            for g in self.groups:
                if g.index > before:
                    g.mandatory = False
        return _union(branches)

    def sequence(self, mandatory: bool) -> str:
        parts = []
        while self.peek() is not None and self.peek() not in "|)":
            parts.append(self.quantified(mandatory))
        return _concat(parts)

    def quantified(self, mandatory: bool) -> str:
        first = len(self.groups)
        atom = self.atom(mandatory)
        ch = self.peek()
        lo, hi = 1, 1
        if ch in ("*", "+", "?"):
            self.take()
            lo, hi = {"*": (0, None), "+": (1, None), "?": (0, 1)}[ch]
        elif ch == "{" and self._counted():
            lo, hi = self._counted_take()
        else:
            return atom
        if self.peek() == "?":
            self.take()  # lazy: the same language
        if lo == 0:
            for g in self.groups[first:]:
                g.mandatory = False
        if hi is None:
            return f"(re.* {atom})" if lo == 0 else f"(re.+ {atom})" if lo == 1 else f"(re.++ ((_ re.loop {lo} {lo}) {atom}) (re.* {atom}))"
        if (lo, hi) == (0, 1):
            return f"(re.opt {atom})"
        return f"((_ re.loop {lo} {hi}) {atom})"

    def _counted(self) -> bool:
        j = self.s.find("}", self.i)
        body = self.s[self.i + 1 : j] if j > 0 else ""
        parts = body.split(",")
        return j > 0 and 1 <= len(parts) <= 2 and parts[0].isdigit() and (len(parts) == 1 or parts[1] == "" or parts[1].isdigit())

    def _counted_take(self) -> tuple[int, int | None]:
        j = self.s.find("}", self.i)
        parts = self.s[self.i + 1 : j].split(",")
        self.i = j + 1
        lo = int(parts[0])
        hi: int | None = lo if len(parts) == 1 else (None if parts[1] == "" else int(parts[1]))
        if hi is not None and hi < lo:
            raise Untranslatable("a count whose maximum is below its minimum")
        return lo, hi

    def atom(self, mandatory: bool) -> str:
        ch = self.take()
        if ch == "(":
            capture = True
            if self.s.startswith("?:", self.i):
                self.i += 2
                capture = False
            elif self.peek() == "?":
                raise Untranslatable("lookaround or a named group")
            if capture:
                self.count += 1
                g = Group(self.count, "", mandatory)
                self.groups.append(g)
            inner = self.alternation(mandatory)
            if self.peek() != ")":
                raise Untranslatable("an unclosed group")
            self.take()
            if capture:
                g.regex = inner
            return inner
        if ch == "[":
            return self.klass()
        if ch == ".":
            return _ANY_BUT_NEWLINE
        if ch == "\\":
            return self.escape(in_class=False)
        if ch in "^$":
            raise Untranslatable("an anchor inside the pattern")
        if ch in "*+?{}":
            if ch == "{" or ch == "}":
                return _lit(ch)
            raise Untranslatable("a quantifier with nothing to repeat")
        return _lit(ch)

    def escape(self, in_class: bool) -> str:
        if self.peek() is None:
            raise Untranslatable("a trailing backslash")
        ch = self.take()
        if ch == "d":
            return _DIGIT
        if ch == "w":
            return _WORD
        if ch == "s":
            return _SPACE
        if ch in "DWS":
            base = {"D": _DIGIT, "W": _WORD, "S": _SPACE}[ch]
            return f"(re.diff re.allchar {base})"
        if ch in "nrtfv0":
            return _lit({"n": "\n", "r": "\r", "t": "\t", "f": "\f", "v": "\v", "0": "\0"}[ch])
        if ch.isalnum():
            raise Untranslatable(f"the escape \\{ch}")
        return _lit(ch)

    def klass(self) -> str:
        negate = self.peek() == "^"
        if negate:
            self.take()
        parts: list[str] = []
        first = True
        while True:
            ch = self.peek()
            if ch is None:
                raise Untranslatable("an unclosed class")
            if ch == "]" and not first:
                self.take()
                break
            first = False
            self.take()
            if ch == "\\":
                a = self.escape(in_class=True)
                single = a.startswith("(str.to_re")
            else:
                a, single = _lit(ch), True
            if single and self.peek() == "-" and self.i + 1 < len(self.s) and self.s[self.i + 1] != "]":
                self.take()
                b = self.take()
                if b == "\\":
                    b_re = self.escape(in_class=True)
                    if not b_re.startswith("(str.to_re"):
                        raise Untranslatable("a range to a class escape")
                    b = _unlit(b_re)
                lo = _unlit(a)
                if len(lo) != 1 or len(b) != 1 or ord(b) < ord(lo):
                    raise Untranslatable("an odd range")
                parts.append(_range(lo, b))
            else:
                parts.append(a)
        body = _union(parts) if parts else "re.none"
        return f"(re.diff re.allchar {body})" if negate else body


def _unlit(t: str) -> str:
    inner = t[len('(str.to_re "') : -2]
    if inner.startswith("\\u{"):
        return chr(int(inner[3:-1], 16))
    return inner.replace('""', '"')


def translate(literal: str) -> Translation:
    """``/pattern/flags`` as SMT-LIB regular languages, or Untranslatable."""
    if not literal.startswith("/") or literal.rfind("/") == 0:
        raise Untranslatable("not a regular expression literal")
    end = literal.rfind("/")
    src, flags = literal[1:end], literal[end + 1 :]
    if set(flags) - {"u"}:
        raise Untranslatable(f"the flags {flags}")
    head = src.startswith("^")
    tail = src.endswith("$") and not src.endswith("\\$")
    body = src[1 if head else 0 : len(src) - 1 if tail else len(src)]
    p = _Parser(body)
    whole = p.alternation(True)
    if p.i != len(body):
        raise Untranslatable("an unmatched parenthesis")
    search = _concat(([] if head else ["re.all"]) + [whole] + ([] if tail else ["re.all"]))
    return Translation(search, whole, p.groups)
