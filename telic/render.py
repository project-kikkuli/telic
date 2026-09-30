"""Terminal rendering. Quiet when things are proved, exact when they are not."""

from __future__ import annotations

import os
import sys
from typing import Any

from . import ir
from . import logic as L
from .checker import FunctionReport, Report, Verdict
from .replay import call_text

# ---------------------------------------------------------------------------
# Paint


class Paint:
    def __init__(self, enabled: bool | None = None):
        if enabled is None:
            enabled = sys.stdout.isatty() and not os.environ.get("NO_COLOR") and os.environ.get("TERM") != "dumb"
            if os.environ.get("FORCE_COLOR") or os.environ.get("CLICOLOR_FORCE"):
                enabled = True
        self.on = enabled

    def _c(self, code: str, s: str) -> str:
        return f"\033[{code}m{s}\033[0m" if self.on else s

    def bold(self, s: str) -> str:
        return self._c("1", s)

    def dim(self, s: str) -> str:
        return self._c("2", s)

    def red(self, s: str) -> str:
        return self._c("31", s)

    def green(self, s: str) -> str:
        return self._c("32", s)

    def yellow(self, s: str) -> str:
        return self._c("33", s)

    def blue(self, s: str) -> str:
        return self._c("34", s)

    def magenta(self, s: str) -> str:
        return self._c("35", s)

    def cyan(self, s: str) -> str:
        return self._c("36", s)

    def gray(self, s: str) -> str:
        return self._c("90", s)

    def bred(self, s: str) -> str:
        return self._c("1;31", s)

    def bgreen(self, s: str) -> str:
        return self._c("1;32", s)

    def byellow(self, s: str) -> str:
        return self._c("1;33", s)


def visible_len(s: str) -> int:
    import re

    return len(re.sub(r"\033\[[0-9;]*m", "", s))


def pad(s: str, width: int) -> str:
    return s + " " * max(0, width - visible_len(s))


# ---------------------------------------------------------------------------
# Vocabulary

STATUS_MARK = {
    "proved": ("✓", "green"),
    "trusted": ("◇", "blue"),
    "refuted": ("✗", "red"),
    "vacuous": ("∅", "red"),
    "open": ("?", "yellow"),
    "unsupported": ("⊘", "gray"),
    "error": ("!", "red"),
    "unformalized": ("○", "gray"),
    "undeclared": ("!", "yellow"),
}

KIND_HEADLINE = {
    "ensures": "postcondition can be false",
    "call": "precondition of the callee may not hold",
    "inv.entry": "loop invariant may not hold before the loop",
    "inv.step": "loop invariant may not survive an iteration",
    "variant": "may not terminate",
    "div": "division by zero is possible",
    "index": "index can be out of bounds",
    "raise": "exception is reachable",
    "raises": "returns normally where it should raise",
    "return": "can fall off the end without returning",
    "assert": "assertion can fail",
}

KIND_NOUN = {
    "ensures": "postcondition",
    "call": "call precondition",
    "inv.entry": "invariant (entry)",
    "inv.step": "invariant (step)",
    "variant": "termination",
    "div": "division",
    "index": "bounds",
    "raise": "raise",
    "raises": "raises",
    "return": "return",
    "assert": "assertion",
}


def mark(p: Paint, status: str) -> str:
    sym, color = STATUS_MARK.get(status, ("·", "dim"))
    return getattr(p, color)(sym)


# ---------------------------------------------------------------------------
# Source snippets


def snippet(p: Paint, module: ir.Module, marks: list[tuple[ir.Loc, str, str]], context: int = 0) -> list[str]:
    """Render source lines with underlines.

    ``marks`` is a list of (loc, label, color). Lines between marks that are
    far apart are elided.
    """
    lines = module.source.splitlines()
    wanted: dict[int, list[tuple[ir.Loc, str, str]]] = {}
    for loc, label, color in marks:
        if loc.line <= 0 or loc.line > len(lines):
            continue
        wanted.setdefault(loc.line, []).append((loc, label, color))
    if not wanted:
        return []
    show: set[int] = set()
    for ln in wanted:
        for k in range(ln - context, ln + context + 1):
            if 1 <= k <= len(lines):
                show.add(k)
    width = len(str(max(show)))
    out = [p.dim(" " * width + " │")]
    prev = None
    for ln in sorted(show):
        if prev is not None and ln > prev + 1:
            if ln == prev + 2:
                out.append(p.dim(f"{prev + 1:>{width}} │ ") + p.dim(lines[prev]))
            else:
                out.append(p.dim(" " * width + " ┆"))
        text = lines[ln - 1]
        out.append(p.dim(f"{ln:>{width}} │ ") + text)
        for loc, label, color in wanted.get(ln, []):
            start = loc.col
            end = loc.end_col if loc.end_col > loc.col else len(text.rstrip())
            if loc.end_col <= loc.col or start >= len(text) or end <= start:
                start = len(text) - len(text.lstrip())
                end = len(text.rstrip())
            under = " " * start + "━" * max(1, end - start)
            paint = getattr(p, color)
            out.append(p.dim(" " * width + " │ ") + paint(under + (" " + label if label else "")))
        prev = ln
    out.append(p.dim(" " * width + " │"))
    return out


def _empty(f) -> bool:
    """Proved, but vacuously: no obligation and no claim."""
    return f.status == "proved" and not f.verdicts and not f.fn.has_contract and not f.open_deps


def fn_loc(rep: FunctionReport) -> str:
    return f"{rep.ref.module.path}:{rep.fn.loc.line}"


def fmt_state_value(v: Any) -> str:
    from fractions import Fraction

    if isinstance(v, Fraction):
        return str(v.numerator) if v.denominator == 1 else f"{float(v):g}"
    if isinstance(v, bool):
        return "true" if v else "false"
    return str(v)


# ---------------------------------------------------------------------------


class Renderer:
    def __init__(self, report: Report, paint: Paint | None = None, verbose: bool = False, width: int | None = None):
        self.r = report
        self.p = paint or Paint()
        self.verbose = verbose
        self.width = width or min(100, max(72, _term_width()))
        self.aim_text = {i.id: i.text for i in report.aims}

    def rule(self, title: str, right: str = "", color: str = "bold") -> str:
        p = self.p
        left = getattr(p, color)(title)
        fill = self.width - visible_len(left) - visible_len(right) - 4
        return f"{left} {p.dim('─' * max(3, fill))} {p.dim(right)}"

    # -- whole report -----------------------------------------------------

    def render(self) -> str:
        out: list[str] = []
        out.append(self.header())
        out.append("")
        problems = [(m, msg, loc) for m in self.r.modules for (msg, loc) in m.problems]
        for m, msg, loc in problems:
            out += self.problem(m, msg, loc)
        for f in self.r.functions:
            if f.status in ("refuted", "vacuous", "open", "error") or (self.verbose and f.status != "proved"):
                out += self.function_detail(f)
        for mr in self.r.mirrors:
            if mr.status != "proved" or self.verbose:
                out += self.mirror_detail(mr)
        out += self.ui_section()
        out += self.aim_table()
        out += self.function_table()
        out += self.trust_section()
        out.append(self.footer())
        return "\n".join(out)

    def header(self) -> str:
        p = self.p
        r = self.r
        nfun = len(r.functions)
        nob = sum(len(f.verdicts) for f in r.functions) + sum(len(m.verdicts) for m in r.mirrors)
        files = sum(1 for m in r.modules if m.language != "aims")
        stats = f"{files} file{'s' * (files != 1)} · {nfun} function{'s' * (nfun != 1)} · {nob} obligation{'s' * (nob != 1)}"
        if r.ui is not None and r.ui.results:
            n = len(r.ui.results)
            stats += f" · {n} ui lemma{'s' * (n != 1)}"
        if r.cache_hits:
            stats += f" · {r.cache_hits} cached"
        stats += f" · {r.seconds:.1f}s"
        return f"{p.bold('telic')}  {p.dim(stats)}"

    def footer(self) -> str:
        p = self.p
        r = self.r
        refuted = [f for f in r.functions if f.status == "refuted"] + [m for m in r.mirrors if m.status == "refuted"]
        vacuous = [f for f in r.functions if f.status == "vacuous"]
        open_ = [f for f in r.functions if f.status in ("open", "error")] + [m for m in r.mirrors if m.status == "open"]
        proved = [f for f in r.functions if f.status == "proved" and not _empty(f)]
        empty = [f for f in r.functions if _empty(f)]
        problems = sum(len(m.problems) for m in r.modules)
        parts = []
        if refuted:
            parts.append(p.bred(f"{len(refuted)} refuted"))
        if vacuous:
            parts.append(p.bred(f"{len(vacuous)} vacuous"))
        if open_:
            parts.append(p.byellow(f"{len(open_)} open"))
        if problems:
            parts.append(p.byellow(f"{problems} problem{'s' * (problems != 1)}"))
        parts.append(p.bgreen(f"{len(proved)} proved"))
        if r.ui is not None and r.ui.results:
            us = [x.status for x in r.ui.results]
            bits = [f"{us.count(k)} {k}" for k in ("proved", "refuted", "open", "vacuous") if us.count(k)]
            color = p.bred if "refuted" in us or "vacuous" in us else p.byellow if "open" in us else p.bgreen
            parts.append(color("ui: " + ", ".join(bits)))
        if empty:
            parts.append(p.gray(f"{len(empty)} with nothing to check"))
        unsup = [f for f in r.functions if f.status == "unsupported"]
        if unsup:
            parts.append(p.gray(f"{len(unsup)} unsupported"))
        return "\n" + "  ".join(parts)

    def problem(self, m: ir.Module, msg: str, loc: ir.Loc) -> list[str]:
        p = self.p
        out = [self.rule(p.byellow("! PROBLEM"), f"{m.path}:{loc.line}"), "   " + msg]
        out += ["   " + x for x in snippet(p, m, [(loc, "", "yellow")])]
        out.append("")
        return out

    # -- functions ----------------------------------------------------------

    def function_detail(self, f: FunctionReport) -> list[str]:
        p = self.p
        out: list[str] = []
        if f.status == "error":
            out.append(self.rule(p.bred("! ERROR") + " " + p.bold(f.fn.name), fn_loc(f)))
            for msg, loc in f.problems:
                out.append("   " + msg)
                out += ["   " + x for x in snippet(p, f.ref.module, [(loc, "", "red")])]
            out.append("")
            return out
        if f.status == "unsupported":
            out.append(self.rule(p.gray("⊘ UNSUPPORTED") + " " + p.bold(f.fn.name), fn_loc(f)))
            for msg, loc in f.problems:
                out.append(f"   {p.dim(f'line {loc.line}:')} {msg}")
            out.append("")
            return out
        bad = [v for v in f.verdicts if v.status in ("refuted", "unconfirmed", "unknown")]
        # refuted first, then unconfirmed, then unknown
        order = {"refuted": 0, "unconfirmed": 1, "unknown": 2}
        bad.sort(key=lambda v: (order[v.status], v.ob.loc.line))
        shown = 0
        for v in bad:
            if shown >= 3 and not self.verbose:
                break
            out += self.verdict_detail(f, v)
            shown += 1
        rest = len(bad) - shown
        if rest > 0:
            out.append(p.dim(f"   … and {rest} more for {f.fn.name} (telic explain {f.fn.name})"))
            out.append("")
        tag = p.bred("∅ VACUOUS") if f.status == "vacuous" else p.byellow("? OPEN")
        for msg, loc in f.problems:
            out.append(self.rule(tag + " " + p.bold(f.fn.name), f"{f.ref.module.path}:{loc.line}"))
            out.append("   " + msg)
            out += ["   " + x for x in snippet(p, f.ref.module, [(loc, "", "yellow")])]
            out.append("")
        return out

    def verdict_detail(self, f: FunctionReport, v: Verdict) -> list[str]:
        p = self.p
        ob = v.ob
        mod = f.ref.module
        race = v.replay is not None and v.replay.violation == "race"
        if race:
            tag = p.bred("⚡ RACE")
        elif v.status == "refuted":
            tag = p.bred("✗ REFUTED")
        elif v.status == "unconfirmed":
            tag = p.byellow("? UNPROVEN")
        else:
            tag = p.byellow("? UNKNOWN")
        head = KIND_HEADLINE.get(ob.kind, ob.kind)
        if v.status == "unknown":
            head = f"{KIND_NOUN.get(ob.kind, ob.kind)} not proved"
        where = f"{mod.path}:{(ob.site or ob.loc).line}"
        out = [self.rule(f"{tag} {p.bold(f.fn.name)} {p.dim('·')} {head}", where)]
        for iid in ob.aims:
            txt = self.aim_text.get(iid)
            out.append(f"   {p.cyan(iid)}  {txt or p.dim('(undeclared aim)')}")
        marks: list[tuple[ir.Loc, str, str]] = []
        color = "red" if v.status == "refuted" else "yellow"
        if ob.kind == "ensures":
            marks.append((ob.loc, "can be false" if v.status == "refuted" else "not proved", color))
            if ob.site and ob.site.line != ob.loc.line:
                marks.append((ob.site, "when it returns here", "blue"))
        elif ob.kind in ("inv.entry", "inv.step"):
            marks.append((ob.loc, "", color))
            if ob.site and ob.site.line != ob.loc.line:
                marks.append((ob.site, "for this loop", "blue"))
        elif ob.kind == "call":
            marks.append((ob.loc, ob.message, color))
        elif ob.kind == "raises":
            marks.append((ob.loc, "", color))
            if ob.site:
                marks.append((ob.site, "returns normally here", "blue"))
        else:
            marks.append((ob.loc, ob.message if ob.kind not in ("div", "index", "return") else "", color))
        out.append("")
        out += ["   " + x for x in snippet(p, mod, marks)]
        if ob.kind == "call" and ob.clause is not None:
            callee_mod = self._module_for_clause(ob.clause)
            if callee_mod is not None:
                out.append(p.dim(f"   required by {callee_mod.path}:{ob.clause.loc.line}"))
                out += ["   " + x for x in snippet(p, callee_mod, [(ob.clause.loc, "", "blue")])]
        if ob.inferred:
            out.append(p.dim("   (about an inferred invariant or measure)"))
        lang = mod.language
        rp = v.replay
        solver_cex = call_text(f.fn, v.model, lang) if v.model is not None and (v.model or not f.fn.params) else None
        if rp is not None and rp.fuzz_witness and rp.confirmed:
            # The solver's candidate was unreachable; testing found a real one.
            out.append(f"   {p.bold(pad('counterexample', 16))}{rp.fuzz_witness}")
            out.append(f"   {p.bold(pad('replayed', 16))}{p.green('✓')} {rp.fuzz_desc}")
            if solver_cex:
                out.append(p.dim(f"   {pad('', 16)}found by testing; the solver's candidate {solver_cex} was unreachable,"))
                out.append(p.dim(f"   {pad('', 16)}which means a loop invariant is also missing"))
        else:
            if solver_cex and v.status in ("refuted", "unconfirmed"):
                out.append(f"   {p.bold(pad('counterexample', 16))}{solver_cex}")
                interesting = {k: val for k, val in v.state.items() if "@" in k and not k.endswith("()") and "@new" not in k and not k.startswith(("alloc@",))}
                if interesting and v.status == "unconfirmed" and not race:
                    st = ", ".join(f"{k.split('@')[0]}={fmt_state_value(val)}" for k, val in list(interesting.items())[:6])
                    out.append(f"   {p.dim(pad('loop state', 16))}{p.dim(st)}")
            if rp is not None:
                if rp.confirmed and v.status == "refuted":
                    out.append(f"   {p.bold(pad('replayed', 16))}{p.green('✓')} {rp.summary}")
                else:
                    out.append(f"   {p.bold(pad('replayed', 16))}{p.dim('·')} {rp.summary}")
                if rp.fuzz_summary and not race:
                    sym = p.red("✗") if rp.fuzz_witness else p.dim("·")
                    out.append(f"   {p.bold(pad('tested', 16))}{sym} {rp.fuzz_summary}")
        if v.status == "unknown":
            out.append(f"   {p.bold(pad('solver', 16))}{p.dim(v.reason or 'gave up')}")
            if v.lean is not None:
                out.append(f"   {p.bold(pad('lean', 16))}{v.lean.summary}")
        hint = self.hint(f, v)
        if hint:
            out.append(f"   {p.magenta(pad('hint', 16))}{hint}")
        out.append("")
        return out

    def _module_for_clause(self, clause: ir.Clause) -> ir.Module | None:
        for m in self.r.modules:
            for fn in m.functions.values():
                if any(c is clause for c in fn.requires):
                    return m
        return None

    def hint(self, f: FunctionReport, v: Verdict) -> str:
        ob = v.ob
        if v.replay is not None and v.replay.violation == "race":
            return "re-check the state after the await, or keep other tasks from changing it meanwhile (a lock, a version check)"
        if v.status == "unconfirmed":
            if ob.kind == "variant":
                return "add or fix '@decreases' on this loop"
            if v.replay is not None and "too weak to rule this out" in v.replay.summary:
                return "add the missing fact to the callee's '@ensures'"
            return "strengthen the loop invariant(s) so the solver cannot pick an unreachable state"
        if v.status == "unknown":
            return "prove it in Lean: telic lean " + ob.id
        if v.status == "refuted":
            if ob.kind in ("div", "index", "call") and not f.fn.requires:
                return "fix the code, or state when it may be called with '@requires'"
            if ob.kind == "ensures" and v.replay and v.replay.confirmed:
                return "the code and the contract disagree: fix whichever one is wrong"
        return ""

    # -- mirrors -------------------------------------------------------------

    def mirror_detail(self, mr) -> list[str]:
        p = self.p
        out: list[str] = []
        a, b = mr.a, mr.b
        if mr.status == "proved":
            tag = p.bgreen("✓ EQUIVALENT")
        elif mr.status == "refuted":
            tag = p.bred("✗ DIVERGES")
        else:
            tag = p.byellow("? UNKNOWN")
        out.append(self.rule(f"{tag} {p.bold(a.fn.name)} {p.dim('≡')} {p.bold(b.fn.name)}", f"{a.module.path} ⇄ {b.module.path}"))
        for iid in mr.aims:
            out.append(f"   {p.cyan(iid)}  {self.aim_text.get(iid) or ''}")
        if mr.status == "refuted" and mr.witness is not None:
            out.append("")
            w = mr.witness
            col = max(16, len(a.module.path) + 2, len(b.module.path) + 2)
            out.append(f"   {p.bold(pad('input', col))}{w['args_text']}")
            out.append(f"   {p.bold(pad(a.module.path, col))}{w['a_text']}")
            out.append(f"   {p.bold(pad(b.module.path, col))}{w['b_text']}")
            if w.get("replay"):
                ok = w["replay"].get("confirmed")
                sym = p.green("✓") if ok else p.dim("·")
                out.append(f"   {p.bold(pad('replayed', col))}{sym} {w['replay']['summary']}")
            if mr.explanation:
                out.append(f"   {p.magenta(pad('why', col))}{mr.explanation}")
            how = "found by the solver" if mr.method == "smt" else "found by differential testing"
            out.append(p.dim(f"   {pad('', col)}{how}; both functions satisfy their own contracts"))
        elif mr.status == "proved":
            out.append(p.dim("   proved: equal results for every input both accept"))
        elif mr.reason:
            out.append(f"   {p.dim(mr.reason)}")
        out.append("")
        return out

    # -- ui ----------------------------------------------------------------

    def ui_section(self) -> list[str]:
        """The apps, the models learned from them, and each ui lemma: one
        line when it holds, the replayed trace when it does not."""
        ui = self.r.ui
        if ui is None or not (ui.results or ui.problems):
            return []
        p = self.p
        out: list[str] = []
        for path, line, msg in ui.problems:
            out += [self.rule(p.byellow("! PROBLEM"), f"{path}:{line}"), "   " + msg, ""]
        by_app: dict[str, list] = {}
        for r in ui.results:
            by_app.setdefault(r.app, []).append(r)
        apps = {a.config: a for a in ui.apps}
        for cfg, results in by_app.items():
            a = apps.get(cfg)
            out.append(self.rule("ui", cfg or "no app configured"))
            if a is not None:
                if a.error:
                    out.append(f"  {p.red('app')}    {a.error}")
                elif a.url:
                    out.append(f"  {p.dim('app')}    {a.url}" + p.dim("  (verdicts cached: nothing the app is built from has changed)" if a.cached else f"  ({a.seconds:.0f}s)"))
                for m in a.models:
                    out.append(f"  {p.dim('model')}  {model_line(m, p)}")
                    for note in m.get("notes", []):
                        out.append(f"         {p.dim(note)}")
            nw = max(len(r.lemma.name) for r in results) + 2
            for r in results:
                lem = r.lemma
                where = p.dim(f"{lem.path}:{lem.line}")
                out.append(f"  {mark(p, r.status)} {pad(lem.name, nw)}{lem.text}  {where}")
                how = {"proved": p.green, "refuted": p.red, "vacuous": p.red}.get(r.status, p.yellow)
                label = ui_label(r.status, r.method)
                text = f"{label} · {r.detail}" if r.detail else label
                for k, line in enumerate(_wrap(text, self.width - nw - 6)):
                    if k == 0 and line.startswith(label):
                        line = how(label) + (p.dim(line[len(label):]) if r.status == "proved" else line[len(label):])
                    elif r.status == "proved":
                        line = p.dim(line)
                    out.append(f"    {pad('', nw)}{line}")
                if r.status != "proved" and r.trace:
                    for k, step in enumerate(r.trace, 1):
                        out.append(f"    {pad('', nw)}{p.dim(f'{k:>2}.')} {step}")
                if r.status != "proved" and r.replay:
                    sym = p.green("✓") if r.replay.get("confirmed") else p.dim("·")
                    out.append(f"    {pad('', nw)}{p.bold('replayed')} {sym} {r.replay.get('summary', '')}")
            out.append("")
        return out

    # -- tables --------------------------------------------------------------

    def aim_table(self) -> list[str]:
        """Requirements first: each aim, what backs it, and whether its
        links and wording hold up. Lemmas are listed under it."""
        p = self.p
        if not self.r.aims:
            return []
        out = [self.rule("aims", f"{len(self.r.aims)}"), ""]
        label = {
            "backed": p.green("backed"),
            "broken": p.red("broken"),
            "vacuous": p.red("vacuous"),
            "partial": p.yellow("partial"),
            "unbacked": p.gray("unbacked"),
            "undeclared": p.yellow("undeclared"),
        }
        glyph = {"backed": p.green("●"), "broken": p.red("✗"), "vacuous": p.red("∅"), "partial": p.yellow("◐"), "unbacked": p.gray("○"), "undeclared": p.yellow("!")}
        for i in self.r.aims:
            n = len(i.lemmas)
            ok = sum(1 for x in i.lemmas if x.status in ("proved", "trusted"))
            summary = [label[i.status]]
            if n:
                summary.append(f"{ok}/{n} lemma{'s' * (n != 1)} proved")
            cov = i.coverage
            if cov is not None and cov.get("kind") == "reviewed":
                summary.append(p.green(f"reviewed by {cov.get('by') or 'a person'}") if cov.get("fresh") else p.yellow("review stale (lemmas or wording changed)"))
            elif cov is not None and cov.get("kind") == "judged":
                v = cov.get("verdict")
                who = cov.get("model") or "oracle"
                prob = f" p={cov['p']:.2f}" if isinstance(cov.get("p"), (int, float)) else ""
                word = p.cyan("judged sufficient") if v == "sufficient" else p.yellow(f"judged {v}")
                summary.append(word + p.dim(f" ({who}{prob})"))
            elif i.status == "backed":
                summary.append(p.dim("coverage not reviewed"))
            where = f"{i.loc[0]}:{i.loc[1]}" if i.loc else ""
            out.append(f"  {glyph[i.status]} {p.bold(p.cyan(i.id))}  {'  ·  '.join(summary)}  {p.dim(where)}")
            text = i.text or p.dim("cited, but never declared with '@aim ID: sentence'")
            for line in _wrap(text, self.width - 6):
                out.append(f"    {line}")
            nw = max((len(x.name) for x in i.lemmas), default=0) + 2
            for x in i.lemmas:
                m = {"proved": p.green("✓"), "trusted": p.blue("◇"), "refuted": p.red("✗"), "vacuous": p.red("∅")}.get(x.status, p.yellow("?"))
                body = x.text if x.kind == "mirror" else f"{x.kind} {x.text}"
                room = self.width - nw - 12
                if visible_len(body) > room:
                    body = body[: max(10, room - 1)] + "…"
                out.append(f"    {m} {pad(x.name, nw)}{p.dim(body)}")
                if x.detail:
                    d = x.detail if visible_len(x.detail) <= room else x.detail[: max(10, room - 1)] + "…"
                    out.append(f"      {pad('', nw)}{p.dim(d)}")
            if cov is not None and cov.get("kind") == "judged" and cov.get("verdict") != "sufficient" and cov.get("missing"):
                out.append(f"    {p.yellow('judge')}  {p.dim('missing: ' + cov['missing'])}")
            for msg in i.pointers:
                out.append(f"    {p.yellow('link')}   {msg}")
            for msg in i.ears:
                out.append(f"    {p.dim('ears')}   {p.dim('the sentence ' + msg)}")
            for msg in i.advice:
                out.append(f"    {p.dim('note')}   {p.dim(msg)}")
            if i.status == "unbacked" and i.scope is not None:
                out.append(f"    {p.yellow('orphan')} {p.dim('declared in an aims/ file and nothing backs it: cite it from the code, or remove it')}")
            out.append("")
        return out

    def function_table(self) -> list[str]:
        p = self.p
        fs = self.r.functions
        if not fs:
            return []
        out = [self.rule("functions", f"{len(fs)}"), ""]
        # functions with nothing to check make no claim: listed only with --verbose
        empty = [f for f in fs if _empty(f)]
        if not self.verbose and len(empty) > 3:
            fs = [f for f in fs if not _empty(f)]
        if not fs:
            fs = empty[:0]
        nw = max([len(f.fn.name) for f in fs] + [8]) + 2
        lw = max([len(fn_loc(f)) for f in fs] + [8]) + 2
        for f in fs:
            n = len(f.verdicts)
            if _empty(f):
                out.append(f"  {p.dim('·')} {pad(f.fn.name, nw)}{pad(p.dim(fn_loc(f)), lw)}{p.dim('nothing to check')}")
                continue
            if f.status == "proved":
                desc = p.dim(f"{n} obligation{'s' * (n != 1)}")
            elif f.status == "refuted":
                k = f.count("refuted")
                desc = p.red(f"{k} refuted") + p.dim(f" of {n}")
            elif f.status == "open":
                k = sum(1 for v in f.verdicts if v.status != "proved")
                desc = p.yellow(f"{k} open" if k else "termination open") + p.dim(f" of {n}")
            elif f.status == "unsupported":
                msg, loc = f.problems[0] if f.problems else ("", f.fn.loc)
                desc = p.gray(f"line {loc.line}: {msg}")
            elif f.status == "vacuous":
                desc = p.red("vacuous") + p.dim(" · what it assumes on entry can never hold")
            elif f.status == "trusted":
                desc = p.blue("trusted") + p.dim(" · contract assumed, body not checked")
            else:
                desc = p.red("error")
            extras = []
            if f.inferred:
                ni = sum(len(v) for v in f.inferred.invariants.values())
                if ni:
                    extras.append(f"{ni} inferred invariant{'s' * (ni != 1)}")
                if f.inferred.variants or f.inferred.measure:
                    extras.append("inferred termination")
            lean = sum(1 for v in f.verdicts if v.method.startswith("lean") or (v.method == "cache" and v.reason.startswith("lean")))
            if lean:
                extras.append(f"{lean} by Lean")
            if f.context_deps and f.status == "proved" and not f.open_deps:
                deps = ", ".join(sorted(d.split("::")[-1] for d in f.context_deps))
                extras.append(f"uses the contracts of {deps}")
            if f.open_deps and f.status == "proved":
                deps = ", ".join(sorted(d.split("::")[-1] for d in f.open_deps))
                extras.append(p.yellow(f"assumes unproved {deps}"))
            ex = p.dim("  ·  " + "  ·  ".join(extras)) if extras else ""
            out.append(f"  {mark(p, f.status)} {pad(f.fn.name, nw)}{pad(p.dim(fn_loc(f)), lw)}{desc}{ex}")
        if len(fs) < len(self.r.functions) and empty and not self.verbose:
            out.append(p.dim(f"  · {len(empty)} more with nothing to check: no contract and no operation that can fail (add '@ensures' to make a claim; --verbose lists them)"))
        out.append("")
        return out

    def trust_section(self) -> list[str]:
        p = self.p
        trusted = [f for f in self.r.functions if f.status == "trusted"]
        assumes = [(f, loc, t) for f in self.r.functions for loc, t in f.assumptions]
        langs = sorted({m.language for m in self.r.modules})
        if not (trusted or assumes or self.verbose):
            return []
        out = [self.rule("trusted base", ""), ""]
        for f in trusted:
            out.append(f"  {p.blue('◇')} {f.fn.name} {p.dim(fn_loc(f))} {p.dim('@trusted')}")
        groups: dict[str, list[tuple[str, int]]] = {}
        calls: dict[str, list[tuple[str, int]]] = {}
        for f, loc, text in assumes:
            if text.startswith("assumed: call:"):
                calls.setdefault(text[len("assumed: call:"):], []).append((f.ref.module.path, loc.line))
            elif text.startswith("assumed: "):
                groups.setdefault(text[len("assumed: "):], []).append((f.ref.module.path, loc.line))
            else:
                out.append(f"  {p.blue('◇')} {p.dim('@assume')} {text} {p.dim(f'{f.ref.module.path}:{loc.line}')}")

        brief = not self.verbose

        def where(locs: list[tuple[str, int]]) -> str:
            by: dict[str, list[int]] = {}
            for path, line in locs:
                by.setdefault(path, [])
                if line not in by[path]:
                    by[path].append(line)
            items = [f"{path}:{','.join(str(x) for x in sorted(ls))}" for path, ls in by.items()]
            if brief and len(items) > 3:
                n = sum(len(ls) for ls in by.values())
                return "  ".join(items[:3]) + f"  … {n} places in {len(items)} files"
            return "  ".join(items)

        if calls:
            names = sorted(calls, key=lambda k: (-len(calls[k]), k))
            shown = ", ".join(names[:8] if brief else sorted(names))
            more = f", … {len(names) - 8} more" if brief and len(names) > 8 else ""
            out.append(f"  {p.blue('◇')} unchecked calls do not raise: {shown}{more}  {p.dim(where([x for v in calls.values() for x in v]))}")
        for text, locs in groups.items():
            out.append(f"  {p.blue('◇')} {text}  {p.dim(where(locs))}")
        if brief and (calls or groups) and sum(len(v) for v in calls.values()) + sum(len(v) for v in groups.values()) > 12:
            out.append(p.dim("  (--verbose lists every assumption and where it is made)"))
        if self.verbose:
            for lang in langs:
                mod = next(m for m in self.r.modules if m.language == lang)
                for a in mod.assumptions:
                    out.append(f"  {p.dim('·')} {p.dim(lang + ': ' + a)}")
        out.append("")
        return out


def ui_label(status: str, method: str) -> str:
    """What a ui verdict rests on, in its own words."""
    if status == "proved":
        return {"learned model": "proved on the learned model", "witness replayed": "proved by a replayed witness", "hit-tested": "unobscured wherever it renders", "tested": "passed the test"}.get(method, "proved")
    if status == "refuted":
        return "refuted" + (" on the learned model" if method == "learned model" else "")
    return status


def model_line(m: dict[str, Any], p: Paint) -> str:
    """One learned model: size, whether exploration finished, conformance."""
    bits = [f"{m['states']} states", f"{m['transitions']} transitions"]
    bits.append(p.green("complete") if m.get("complete") else p.yellow(f"incomplete: stopped at the {m.get('stop')}"))
    if m.get("walks"):
        conf = f"conformance: {m['walks']} walks of ≤{m['walk_length']} steps, {m['agreed']} steps as predicted"
        if m.get("disagreed"):
            conf += f", {len(m['disagreed'])} not (added)"
        bits.append(conf)
    if m.get("nondeterministic"):
        bits.append(p.yellow(f"{m['nondeterministic']} nondeterministic"))
    if m.get("seeded"):
        sd = m["seeded"]
        bits.append(f"oracle seed: {sd.get('steps_agreed', 0)} steps right, {sd.get('steps_wrong', 0)} wrong")
    return f"{p.bold(m['viewport'])}  " + p.dim(" · ").join(bits)


def _wrap(text: str, width: int) -> list[str]:
    import textwrap

    return textwrap.wrap(text, max(30, width)) or [""]


def _term_width() -> int:
    try:
        return os.get_terminal_size().columns
    except OSError:
        return 88


# ---------------------------------------------------------------------------
# explain


def explain(report: Report, target: str, paint: Paint | None = None) -> str:
    p = paint or Paint()
    out: list[str] = []
    for f in report.functions:
        if f.fn.name != target and not any(v.ob.id == target for v in f.verdicts):
            continue
        verdicts = [v for v in f.verdicts if v.ob.id == target] or f.verdicts
        out.append(f"{mark(p, f.status)} {p.bold(f.fn.name)}  {p.dim(fn_loc(f))}  {f.status}")
        if f.inferred:
            for line, cs in sorted(f.inferred.invariants.items()):
                for c in cs:
                    out.append(f"  {p.dim('inferred invariant')}  {c.text}  {p.dim(f'(loop at line {line})')}")
            for line, v in sorted(f.inferred.variants.items()):
                out.append(f"  {p.dim('inferred measure  ')}  {v}  {p.dim(f'(loop at line {line})')}")
            if f.inferred.measure:
                out.append(f"  {p.dim('inferred measure  ')}  {f.inferred.measure}  {p.dim('(recursion)')}")
        out.append("")
        for v in verdicts:
            ob = v.ob
            out.append(f"  {mark(p, 'proved' if v.status == 'proved' else 'refuted' if v.status == 'refuted' else 'open')} {p.bold(ob.id)}  {p.dim(v.status + ' · ' + v.method)}")
            out.append(f"    {ob.message}")
            if len(verdicts) == 1 or v.status != "proved":
                hyps = [h for h in ob.hyps if h != L.TRUE]
                for h in hyps[-12:]:
                    out.append(p.dim("    │ ") + _short(L.show(h)))
                if len(hyps) > 12:
                    out.append(p.dim(f"    │ … {len(hyps) - 12} earlier facts"))
                out.append(p.dim("    ⊢ ") + _short(L.show(ob.goal)))
                if v.model:
                    out.append(p.dim("    counterexample ") + call_text(f.fn, v.model, f.ref.module.language))
            out.append("")
    if not out:
        return f"no function or obligation named '{target}'"
    return "\n".join(out)


def _short(s: str, n: int = 160) -> str:
    return s if len(s) <= n else s[: n - 1] + "…"
