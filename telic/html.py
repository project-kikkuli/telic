"""`telic report`: the proof ledger as one self-contained HTML page.

Aims first (the summary a reader wants), then every function with its
source and a proof gutter: each line that carries an obligation shows what was
proved there, how, or what broke.
"""

from __future__ import annotations

import html
import os
from datetime import datetime, timezone

from . import ir
from .checker import FunctionReport, Report, Verdict
from .render import KIND_NOUN
from .replay import call_text

ORDER = {"refuted": 0, "unconfirmed": 1, "unknown": 2, "proved": 3}
STATUS_WORD = {
    "proved": "proved",
    "refuted": "refuted",
    "vacuous": "vacuous",
    "open": "open",
    "unsupported": "unsupported",
    "trusted": "trusted",
    "error": "error",
    "unformalized": "unformalized",
    "undeclared": "undeclared",
    "backed": "backed",
    "broken": "broken",
    "partial": "partial",
    "vacuous-risk": "vacuous risk",
    "unbacked": "unbacked",
}
MARK = {"proved": "✓", "refuted": "✗", "vacuous": "∅", "open": "?", "unconfirmed": "?", "unknown": "?", "unsupported": "⊘", "trusted": "◇", "error": "!", "unformalized": "○", "undeclared": "!", "backed": "●", "broken": "✗", "partial": "◐", "vacuous-risk": "∅", "unbacked": "○"}

CSS = """
/* Layout: a ledger. Aims summary on top, then one panel per function:
   source with a proof gutter, evidence table beneath. */
:root {
  --ground: #f4f6f5;
  --paper: #ffffff;
  --ink: #17201c;
  --muted: #5d6b65;
  --rule: #d9e0dc;
  --code-bg: #f8faf9;
  --accent: #2f4f8f;
  --proved: #1c7a4b;
  --proved-bg: #e3f3ea;
  --refuted: #b3261e;
  --refuted-bg: #fbe6e4;
  --open: #9a6200;
  --open-bg: #fbf0da;
  --quiet: #7b8782;
  --quiet-bg: #eceff0;
  --font-display: "IBM Plex Sans Condensed", "Arial Narrow", system-ui, sans-serif;
  --font-body: "IBM Plex Sans", system-ui, -apple-system, "Segoe UI", sans-serif;
  --font-mono: "IBM Plex Mono", ui-monospace, "SF Mono", Menlo, Consolas, monospace;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --ground: #0f1312; --paper: #161b19; --ink: #e3ebe7; --muted: #93a39c; --rule: #2a332f;
    --code-bg: #121715; --accent: #8fb0f0; --proved: #5fcf95; --proved-bg: #173026;
    --refuted: #f2877f; --refuted-bg: #3a1a18; --open: #e9b456; --open-bg: #352a14;
    --quiet: #8a9691; --quiet-bg: #222927; color-scheme: dark;
  }
}
:root[data-theme="dark"] {
  --ground: #0f1312; --paper: #161b19; --ink: #e3ebe7; --muted: #93a39c; --rule: #2a332f;
  --code-bg: #121715; --accent: #8fb0f0; --proved: #5fcf95; --proved-bg: #173026;
  --refuted: #f2877f; --refuted-bg: #3a1a18; --open: #e9b456; --open-bg: #352a14;
  --quiet: #8a9691; --quiet-bg: #222927; color-scheme: dark;
}
* { box-sizing: border-box; }
body { background: var(--ground); color: var(--ink); font: 15px/1.55 var(--font-body); margin: 0; }
.wrap { max-width: 1080px; margin: 0 auto; padding-inline: 20px; padding-block: 36px 64px; display: grid; gap: 40px; }
h1, h2, h3 { font-family: var(--font-display); font-weight: 600; margin: 0; text-wrap: balance; letter-spacing: 0.005em; }
h1 { font-size: 2.1rem; line-height: 1.1; }
h2 { font-size: 1.35rem; }
h3 { font-size: 1.1rem; }
code, .mono { font-family: var(--font-mono); font-size: 0.86em; }
.muted { color: var(--muted); }
.eyebrow { font: 600 0.72rem/1 var(--font-body); letter-spacing: 0.12em; text-transform: uppercase; color: var(--muted); }
header.top { display: grid; gap: 10px; }
.tally { display: flex; flex-wrap: wrap; gap: 8px 18px; font-variant-numeric: tabular-nums; color: var(--muted); }
.tally b { color: var(--ink); font-weight: 600; }
.pill { display: inline-flex; align-items: center; gap: 6px; padding: 2px 10px 2px 8px; border-radius: 999px; font: 600 0.78rem/1.6 var(--font-body); white-space: nowrap; }
.pill.proved { color: var(--proved); background: var(--proved-bg); }
.pill.refuted { color: var(--refuted); background: var(--refuted-bg); }
.pill.open, .pill.unknown, .pill.unconfirmed, .pill.undeclared { color: var(--open); background: var(--open-bg); }
.pill.backed { color: var(--proved); background: var(--proved-bg); }
.pill.broken, .pill.vacuous { color: var(--refuted); background: var(--refuted-bg); }
.pill.partial, .pill.unbacked, .pill.vacuous-risk { color: var(--open); background: var(--open-bg); }
.aim ul { margin: 6px 0 0; padding-left: 1.1rem; list-style: none; }
.pill.unsupported, .pill.trusted, .pill.unformalized, .pill.error { color: var(--quiet); background: var(--quiet-bg); }
section { display: grid; gap: 14px; }
.aims { display: grid; gap: 0; border-top: 1px solid var(--rule); }
.aim { display: grid; grid-template-columns: minmax(0, 11rem) minmax(0, 1fr) auto; gap: 6px 18px; padding: 14px 2px; border-bottom: 1px solid var(--rule); align-items: baseline; }
.aim .id { font: 600 0.9rem var(--font-mono); color: var(--accent); overflow-wrap: anywhere; }
.aim .text { min-width: 0; }
.aim .evidence { grid-column: 2 / 4; color: var(--muted); font-size: 0.86rem; }
@media (max-width: 640px) {
  .aim { grid-template-columns: minmax(0, 1fr) auto; }
  .aim .text, .aim .evidence { grid-column: 1 / 3; }
}
.fn { background: var(--paper); border: 1px solid var(--rule); border-radius: 6px; overflow: hidden; }
.fn > header { display: flex; flex-wrap: wrap; gap: 8px 14px; align-items: center; padding: 14px 18px; border-bottom: 1px solid var(--rule); }
.fn > header h3 { font-family: var(--font-mono); font-size: 1rem; font-weight: 600; }
.fn > header .where { margin-left: auto; color: var(--muted); font-size: 0.82rem; font-family: var(--font-mono); }
.fn .tags { display: flex; flex-wrap: wrap; gap: 6px; padding: 10px 18px 0; }
.tag { font: 0.78rem var(--font-mono); color: var(--accent); }
.tag.inferred { color: var(--muted); }
.src { overflow-x: auto; background: var(--code-bg); margin: 12px 0 0; border-block: 1px solid var(--rule); }
.src table { border-collapse: collapse; width: 100%; font: 0.82rem/1.6 var(--font-mono); }
.src td { padding: 0 12px 0 0; white-space: pre; vertical-align: top; }
.src td.n { color: var(--quiet); text-align: right; padding: 0 10px 0 12px; user-select: none; width: 1%; }
.src td.g { width: 1%; padding: 0 10px 0 2px; font-weight: 700; text-align: center; }
.src tr.proved td.g { color: var(--proved); }
.src tr.refuted td.g { color: var(--refuted); }
.src tr.refuted td.c { background: var(--refuted-bg); }
.src tr.open td.g { color: var(--open); }
.src tr.open td.c { background: var(--open-bg); }
.src td.c .contract { color: var(--accent); }
.obs { width: 100%; border-collapse: collapse; font-size: 0.86rem; }
.obs-wrap { overflow-x: auto; padding: 4px 18px 16px; }
.obs th { text-align: left; font: 600 0.7rem var(--font-body); letter-spacing: 0.1em; text-transform: uppercase; color: var(--muted); padding: 10px 12px 6px 0; border-bottom: 1px solid var(--rule); }
.obs td { padding: 7px 12px 7px 0; border-bottom: 1px solid var(--rule); vertical-align: top; }
.obs tr:last-child td { border-bottom: 0; }
.obs td.k { white-space: nowrap; color: var(--muted); }
.obs td.l { font-variant-numeric: tabular-nums; color: var(--muted); font-family: var(--font-mono); font-size: 0.8rem; }
.obs td.m { white-space: nowrap; font-family: var(--font-mono); font-size: 0.8rem; color: var(--muted); }
.cex { display: grid; gap: 2px; margin-top: 6px; font-size: 0.82rem; }
.cex .mono { overflow-wrap: anywhere; }
.problem { padding: 10px 18px 14px; color: var(--muted); font-size: 0.88rem; }
.mirror ol { margin: 0; padding-left: 1.4rem; font-family: var(--font-mono); font-size: 0.84rem; }
.mirror { background: var(--paper); border: 1px solid var(--rule); border-radius: 6px; padding: 14px 18px; display: grid; gap: 10px; }
.mirror .pair { display: flex; flex-wrap: wrap; gap: 6px 14px; align-items: center; font-family: var(--font-mono); font-size: 0.9rem; }
.mirror dl { display: grid; grid-template-columns: minmax(0, max-content) minmax(0, 1fr); gap: 4px 16px; margin: 0; font-size: 0.88rem; }
.mirror dt { color: var(--muted); font-family: var(--font-mono); font-size: 0.82rem; }
.mirror dd { margin: 0; min-width: 0; overflow-wrap: anywhere; }
.trust { font-size: 0.88rem; color: var(--muted); display: grid; gap: 4px; }
footer { color: var(--muted); font-size: 0.82rem; }
.filters { display: flex; flex-wrap: wrap; gap: 8px; }
.filters button { font: 600 0.8rem var(--font-body); border: 1px solid var(--rule); background: var(--paper); color: var(--ink); border-radius: 999px; padding: 4px 12px; cursor: pointer; }
.filters button[aria-pressed="true"] { border-color: var(--accent); color: var(--accent); }
.filters button:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }
"""

JS = """
(function () {
  var buttons = document.querySelectorAll('.filters button');
  function apply(which) {
    document.querySelectorAll('.fn').forEach(function (el) {
      el.hidden = which !== 'all' && el.dataset.status !== which;
    });
    buttons.forEach(function (b) { b.setAttribute('aria-pressed', String(b.dataset.show === which)); });
  }
  buttons.forEach(function (b) { b.addEventListener('click', function () { apply(b.dataset.show); }); });
})();
"""


def e(s: object) -> str:
    return html.escape(str(s), quote=True)


def pill(status: str, label: str | None = None) -> str:
    return f'<span class="pill {e(status)}">{MARK.get(status, "·")} {e(label or STATUS_WORD.get(status, status))}</span>'


def verdict_status(v: Verdict) -> str:
    return v.status


def _span(fn: ir.Function, source_lines: list[str]) -> tuple[int, int]:
    """Function lines plus the contract/comment block directly above it."""
    start = fn.loc.line
    k = start - 1
    while k >= 1 and source_lines[k - 1].strip().startswith(("#", "//", "@")):
        k -= 1
    return k + 1, fn.end_line


def _line_status(f: FunctionReport) -> dict[int, str]:
    worst: dict[int, str] = {}
    for v in f.verdicts:
        #@ invariant all(worst[k] == "refuted" or worst[k] == "open" or worst[k] == "proved" for k in worst)
        st = "refuted" if v.status == "refuted" else "open" if v.status in ("unknown", "unconfirmed") else "proved"
        for ln in {v.ob.loc.line, (v.ob.site or v.ob.loc).line}:
            #@ invariant all(worst[k] == "refuted" or worst[k] == "open" or worst[k] == "proved" for k in worst)
            cur = worst.get(ln)
            rank = {"refuted": 0, "open": 1, "proved": 2}
            if cur is None or rank[st] < rank[cur]:
                worst[ln] = st
    for msg, loc in f.problems:
        worst[loc.line] = "open" if worst.get(loc.line) != "refuted" else "refuted"
    return worst


def _method(v: Verdict) -> str:
    if v.method == "cache":
        return (v.reason or "cached").replace("lean:", "lean · ") + " · cached"
    return v.method.replace("lean:", "lean · ")


def function_panel(f: FunctionReport) -> str:
    from .evidence import evidence_status

    evidence = evidence_status(f)
    mod = f.ref.module
    lines = mod.source.splitlines()
    lo, hi = _span(f.fn, lines)
    marks = _line_status(f)
    rows = []
    for n in range(lo, hi + 1):
        text = lines[n - 1] if n <= len(lines) else ""
        st = marks.get(n, "")
        g = {"proved": "✓", "refuted": "✗", "open": "?"}.get(st, "")
        stripped = text.lstrip()
        body = e(text)
        if stripped.startswith(("#@", "//@")):
            body = f'<span class="contract">{body}</span>'
        rows.append(f'<tr class="{st}"><td class="n">{n}</td><td class="g">{g}</td><td class="c">{body}</td></tr>')
    tags = []
    for i in f.fn.aims:
        tags.append(f'<span class="tag">{e(i)}</span>')
    if f.inferred:
        for line, cs in sorted(f.inferred.invariants.items()):
            for c in cs:
                tags.append(f'<span class="tag inferred">inferred @invariant {e(c.text)}</span>')
        for line, v in sorted(f.inferred.variants.items()):
            tags.append(f'<span class="tag inferred">inferred @decreases {e(v)}</span>')
        if f.inferred.measure:
            tags.append(f'<span class="tag inferred">inferred @decreases {e(f.inferred.measure)}</span>')
    obs = []
    for v in sorted(f.verdicts, key=lambda v: (ORDER.get(v.status, 9), v.ob.loc.line)):
        detail = e(v.ob.message)
        extra = []
        if v.status in ("refuted", "unconfirmed") and v.model is not None and (v.model or not f.fn.params):
            rp = v.replay
            if rp is not None and rp.fuzz_witness and rp.confirmed:
                extra.append(f'<span class="mono">{e(rp.fuzz_witness)}</span><span>{e(rp.fuzz_desc or "")}</span>')
            else:
                extra.append(f'<span class="mono">{e(call_text(f.fn, v.model, mod.language))}</span>')
                if rp is not None:
                    extra.append(f"<span>{'✓ ' if rp.confirmed else ''}{e(rp.summary)}</span>")
        if v.status == "unknown":
            extra.append(f"<span>solver: {e(v.reason or 'gave up')}</span>")
            if v.lean is not None:
                extra.append(f"<span>lean: {e(v.lean.summary)}</span>")
        cex = f'<div class="cex">{"".join(extra)}</div>' if extra else ""
        site = f"{v.ob.loc.line}" + (f" → {v.ob.site.line}" if v.ob.site and v.ob.site.line != v.ob.loc.line else "")
        obs.append(
            f"<tr><td>{pill('open' if v.status == 'unconfirmed' else v.status, 'unproven' if v.status == 'unconfirmed' else None)}</td>"
            f'<td class="k">{e(KIND_NOUN.get(v.ob.kind, v.ob.kind))}</td><td class="l">{site}</td>'
            f"<td>{detail}{cex}</td><td class=\"m\">{e(_method(v)) if v.status == 'proved' else ''}</td></tr>"
        )
    problems = "".join(f'<div class="problem">line {loc.line}: {e(msg)}</div>' for msg, loc in f.problems)
    conditional = []
    conditional.extend(f"unchecked context contract {d}" for d in sorted(f.context_deps))
    conditional.extend(f"unproved dependency {d}" for d in sorted(f.open_deps))
    conditional.extend(f"trusted dependency {d}" for d in sorted(f.trusted_deps))
    conditional.extend(f"line {loc.line}: {text}" for loc, text in f.assumptions)
    assumptions = f'<div class="problem">{e("; ".join(conditional))}</div>' if conditional else ""
    count = f"{len(f.verdicts)} obligation{'s' * (len(f.verdicts) != 1)}"
    table = (
        '<div class="obs-wrap"><table class="obs"><thead><tr><th>result</th><th>kind</th><th>line</th><th>obligation</th><th>evidence</th></tr></thead>'
        f'<tbody>{"".join(obs)}</tbody></table></div>'
        if obs
        else ""
    )
    return (
        f'<article class="fn" id="fn-{e(f.fn.name)}" data-status="{e(evidence)}">'
        f"<header>{pill(evidence)}<h3>{e(f.fn.name)}</h3><span class=\"muted\">{count}</span>"
        f'<span class="where">{e(mod.path)}:{f.fn.loc.line}</span></header>'
        f'{"<div class=tags>" + "".join(tags) + "</div>" if tags else ""}'
        f'<div class="src"><table>{"".join(rows)}</table></div>{problems}{assumptions}{table}</article>'
    )


def mirror_card(m) -> str:
    parts = [
        f'<div class="pair">{pill(m.status, "equivalent" if m.status == "proved" else "diverges" if m.status == "refuted" else "vacuous" if m.status == "vacuous" else "not proved")}'
        f"<span>{e(m.a.module.path)}::{e(m.a.fn.name)}</span><span class=\"muted\">≡</span><span>{e(m.b.module.path)}::{e(m.b.fn.name)}</span></div>"
    ]
    if m.status == "proved":
        parts.append('<div class="muted">Equal results for every input both preconditions accept (proved by the solver).</div>')
    elif m.witness:
        w = m.witness
        parts.append(
            "<dl>"
            f"<dt>input</dt><dd>{e(w['args_text'])}</dd>"
            f"<dt>{e(m.a.module.path)}</dt><dd>{e(w['a_text'])}</dd>"
            f"<dt>{e(m.b.module.path)}</dt><dd>{e(w['b_text'])}</dd>"
            f"<dt>replayed</dt><dd>{e(w['replay']['summary'])}</dd>"
            + (f"<dt>why</dt><dd>{e(m.explanation)}</dd>" if m.explanation else "")
            + "</dl>"
        )
    elif m.reason:
        parts.append(f'<div class="muted">{e(m.reason)}</div>')
    return f'<div class="mirror">{"".join(parts)}</div>'


def ui_card(r) -> str:
    """One ui lemma: its verdict, what the verdict rests on, and the replayed trace."""
    from .render import ui_label

    lem = r.lemma
    parts = [
        f'<div class="pair">{pill(r.status, ui_label(r.status, r.method))}<span>{e(lem.name)}</span>'
        f'<span class="muted">{e(lem.text)}</span><span class="where">{e(lem.path)}:{lem.line}</span></div>',
        f'<div class="muted">{e(r.detail)}</div>',
    ]
    if r.status != "proved" and r.trace:
        parts.append("<ol>" + "".join(f"<li>{e(step)}</li>" for step in r.trace) + "</ol>")
    if r.status != "proved" and r.replay:
        parts.append(f"<dl><dt>replayed</dt><dd>{'✓ ' if r.replay.get('confirmed') else ''}{e(r.replay.get('summary', ''))}</dd></dl>")
    return f'<div class="mirror">{"".join(parts)}</div>'


def ui_section(rep: Report) -> str:
    ui = getattr(rep, "ui", None)
    if ui is None or not ui.results:
        return ""
    from .render import Paint, model_line

    plain = Paint(False)
    apps = []
    for a in ui.apps:
        rows = "".join(f"<dt>model</dt><dd>{e(model_line(m, plain))}</dd>" for m in a.models)
        head = f"<dt>app</dt><dd>{e(a.config)} · {e(a.error or a.url)}{' (cached)' if a.cached else ''}</dd>"
        apps.append(f'<div class="mirror"><dl>{head}{rows}</dl></div>')
    return "<section><h2>UI</h2>" + "".join(apps) + "".join(ui_card(r) for r in ui.results) + "</section>"


def _p(part: dict) -> str:
    p = part.get("p")
    return f"p={p:.2f}" + (f" by {part['by']}" if part.get("by") else "") if isinstance(p, (int, float)) else "not answered"


def render_html(rep: Report, title: str = "Proof ledger", standalone: bool = True) -> str:
    fs = rep.functions
    from .evidence import evidence_status

    counts = {s: sum(1 for f in fs if evidence_status(f) == s) for s in ("proved", "refuted", "vacuous", "open", "unsupported", "trusted", "error")}
    nob = sum(len(f.verdicts) for f in fs)
    lean = sum(1 for f in fs for v in f.verdicts if v.method.startswith("lean") or (v.method == "cache" and v.reason.startswith("lean")))
    inferred = sum(sum(len(c) for c in f.inferred.invariants.values()) for f in fs if f.inferred)
    nfiles = sum(1 for m in rep.modules if m.language != "aims")
    tally = [
        f"<span><b>{nfiles}</b> file{'s' * (nfiles != 1)}</span>",
        f"<span><b>{len(fs)}</b> function{'s' * (len(fs) != 1)}</span>",
        f"<span><b>{nob}</b> obligation{'s' * (nob != 1)}</span>",
        f"<span><b>{counts['proved']}</b> proved</span>",
    ]
    if counts["refuted"]:
        tally.append(f"<span><b>{counts['refuted']}</b> refuted</span>")
    if counts["vacuous"]:
        tally.append(f"<span><b>{counts['vacuous']}</b> vacuous</span>")
    if counts["open"] + counts["error"]:
        tally.append(f"<span><b>{counts['open'] + counts['error']}</b> open</span>")
    if lean:
        tally.append(f"<span><b>{lean}</b> by Lean</span>")
    if inferred:
        tally.append(f"<span><b>{inferred}</b> inferred invariant{'s' * (inferred != 1)}</span>")
    aims = []
    for i in rep.aims:
        ok = sum(1 for x in i.lemmas if x.status == "proved")
        ev = [f"{ok}/{len(i.lemmas)} lemmas proved"] if i.lemmas else ["no lemma cites this aim yet"]
        if i.trusted:
            ev.append(f"assuming trusted {', '.join(i.trusted)}")
        cov = i.coverage or {}
        if cov.get("kind") == "reviewed":
            ev.append(f"reviewed by {cov.get('by') or 'a person'}" if cov.get("fresh") else "review stale")
        elif cov.get("kind") == "judged":
            prob = f" p={cov['p']:.2f}" if isinstance(cov.get("p"), (int, float)) else ""
            ev.append(f"judged {cov.get('verdict', '')} by {cov.get('model') or 'an oracle'}{prob}, not proof" + (f" (missing: {cov['missing']})" if cov.get("verdict") != "sufficient" and cov.get("missing") else ""))
        lemmas = "".join(
            f"<li>{MARK.get(x.status, '?')} <code>{e(x.name)}</code> {e(x.text if x.kind == 'mirror' else x.kind + ' ' + x.text)}{' · ' + e(x.detail) if x.detail else ''}</li>" for x in i.lemmas
        )
        if i.loc:
            ev.append(f"declared in {i.loc[0]}:{i.loc[1]}")
        judged = "".join(
            f"<li>{'✓' if (x.get('p') or 0) >= 0.5 else '?'} judged <q>{e(x['condition'])}</q> {e(_p(x))}</li>" for x in (cov.get("parts") or []) if cov.get("kind") == "judged"
        )
        issues = judged + "".join(f"<li>∅ {e(m)}; add a lemma that says what it still does</li>" for m in i.stubs) + "".join(f"<li>⚠ {e(m)}</li>" for m in i.assumes) + "".join(f"<li>⚠ {e(m)}</li>" for m in i.pointers) + "".join(f"<li>EARS: the sentence {e(m)}</li>" for m in i.ears) + "".join(f"<li>{e(m)}</li>" for m in i.advice)
        aims.append(
            f'<div class="aim"><span class="id">{e(i.id)}</span><span class="text">{e(i.text or "cited but never declared")}</span>'
            f"{pill(i.status)}<span class=\"evidence\">{e(' · '.join(ev))}<ul>{lemmas}{issues}</ul></span></div>"
        )
    trust = []
    for f in fs:
        if f.status == "trusted":
            trust.append(f"<div>◇ {e(f.fn.name)} is @trusted: its contract is assumed, its body unchecked</div>")
        for loc, text in f.assumptions:
            trust.append(f"<div>◇ @assume {e(text)} <span class=\"mono\">{e(f.ref.module.path)}:{loc.line}</span></div>")
    for lang in sorted({m.language for m in rep.modules}):
        mod = next(m for m in rep.modules if m.language == lang)
        for a in mod.assumptions:
            trust.append(f"<div>· {e(lang)}: {e(a)}</div>")
    when = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    body = f"""
<div class="wrap">
  <header class="top">
    <span class="eyebrow">telic · proof ledger</span>
    <h1>{e(title)}</h1>
    <div class="tally">{"".join(tally)}</div>
  </header>
  {"<section><h2>Aims</h2><div class='aims'>" + "".join(aims) + "</div></section>" if aims else ""}
  {"<section><h2>Mirrors</h2>" + "".join(mirror_card(m) for m in rep.mirrors) + "</section>" if rep.mirrors else ""}
  {ui_section(rep)}
  <section>
    <h2>Functions</h2>
    <div class="filters" role="group" aria-label="Show functions">
      <button type="button" data-show="all" aria-pressed="true">All</button>
      <button type="button" data-show="proved" aria-pressed="false">Proved</button>
      <button type="button" data-show="refuted" aria-pressed="false">Refuted</button>
      <button type="button" data-show="open" aria-pressed="false">Open</button>
    </div>
    {"".join(function_panel(f) for f in fs)}
  </section>
  <section>
    <h2>Trusted base</h2>
    <div class="trust">{"".join(trust) or "<div>Nothing beyond Z3, the Lean kernel and the language models.</div>"}</div>
  </section>
  <footer>Generated by telic on {e(when)}. Every ✓ is a proof (Z3 or a kernel-checked Lean proof); every ✗ is a counterexample that was executed and reproduced.</footer>
</div>
<script>{JS}</script>
"""
    head = (
        f"<title>{e(title)}</title>\n"
        '<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans+Condensed:wght@600&family=IBM+Plex+Sans:wght@400;600&display=swap">\n'
        f"<style>{CSS}</style>\n"
    )
    if standalone:
        return f'<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n<meta name="viewport" content="width=device-width, initial-scale=1">\n{head}</head>\n<body>{body}</body>\n</html>\n'
    return head + body


def cmd_report(args) -> int:
    from .checker import check

    root = os.path.abspath(args.root or os.getcwd())
    rep = check(args.paths, args._options(args, root), root=root)
    out = args.output
    title = args.title or os.path.basename(root) or "Proof ledger"
    with open(out, "w") as fh:
        fh.write(render_html(rep, title=title, standalone=not args.fragment))
    print(f"wrote {out}")
    return 0 if rep.ok else 1


def add_commands(sub, common, options) -> None:
    r = sub.add_parser("report", help="write the proof ledger as an HTML page")
    common(r)
    r.add_argument("-o", "--output", default="telic-report.html")
    r.add_argument("--title", default=None)
    r.add_argument("--fragment", action="store_true", help="omit <html>/<head>/<body> (for embedding)")
    r.set_defaults(func=cmd_report, _options=options)
