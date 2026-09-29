"""telic command line.

    telic check [PATH...]          verify every function; exit 1 on a refutation
    telic explain NAME             show the obligations (and their formulas) for a function
    telic lean ID                  print the Lean 4 goal for an obligation
    telic prove [PATH...]          discharge open obligations in Lean (auto tactics / --agent)
    telic gaps [PATH...]           attack the specs: find wrong code the contracts still accept
    telic run SCRIPT [ARGS...]     run a Python program with every contract enforced
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from typing import Any

from . import __version__
from .checker import CheckOptions, Report, check


def _cache_path(root: str) -> str:
    return os.path.join(root, ".telic", "cache.json")


def _options(args: argparse.Namespace, root: str) -> CheckOptions:
    return CheckOptions(
        timeout_ms=int(args.timeout * 1000),
        replay=not args.no_replay,
        lean=not args.no_lean,
        cache_path=None if args.no_cache else _cache_path(root),
        only=set(args.only) if args.only else None,
        jobs=getattr(args, "jobs", None),
        engine=getattr(args, "engine", None) or os.environ.get("TELIC_ENGINE", "python"),
    )


def _common(ap: argparse.ArgumentParser) -> None:
    ap.add_argument("paths", nargs="*", default=["."], help="files or directories (default: .)")
    ap.add_argument("--timeout", type=float, default=8.0, help="solver timeout per obligation, seconds (default 8)")
    ap.add_argument("--no-replay", action="store_true", help="do not execute counterexamples")
    ap.add_argument("--no-lean", action="store_true", help="do not escalate unknown obligations to Lean")
    ap.add_argument("--no-cache", action="store_true", help="ignore and do not write .telic/cache.json")
    ap.add_argument("--only", action="append", metavar="FUNC", help="check only these functions")
    ap.add_argument("--root", default=None, help="project root for relative paths and the cache (default: cwd)")
    ap.add_argument("-j", "--jobs", type=int, default=None, help="solver threads (default: every core)")
    ap.add_argument("--engine", choices=["python", "ox"], default=None, help="'ox': the native OxCaml engine (core/), where it applies")


def report_json(rep: Report) -> dict[str, Any]:
    from .replay import call_text

    fns = []
    for f in rep.functions:
        obs = []
        for v in f.verdicts:
            d: dict[str, Any] = {
                "id": v.ob.id,
                "kind": v.ob.kind,
                "status": v.status,
                "method": v.method,
                "message": v.ob.message,
                "file": f.ref.module.path,
                "line": v.ob.loc.line,
                "site_line": v.ob.site.line if v.ob.site else None,
                "intents": list(v.ob.intents),
            }
            if v.status != "proved":
                if v.model:
                    d["counterexample"] = call_text(f.fn, v.model, f.ref.module.language)
                if v.replay:
                    d["replay"] = {"confirmed": v.replay.confirmed, "summary": v.replay.summary, "fuzz": v.replay.fuzz_summary}
                if v.reason:
                    d["reason"] = v.reason
            obs.append(d)
        fns.append(
            {
                "function": f.fn.name,
                "file": f.ref.module.path,
                "line": f.fn.loc.line,
                "status": f.status,
                "problems": [{"message": m, "line": loc.line} for m, loc in f.problems],
                "intents": f.fn.intents,
                "obligations": obs,
                "assumes_unproved": sorted(f.open_deps),
                "inferred": {
                    "invariants": {str(k): [c.text for c in v] for k, v in (f.inferred.invariants.items() if f.inferred else [])},
                    "variants": {str(k): v for k, v in (f.inferred.variants.items() if f.inferred else [])},
                    "measure": f.inferred.measure if f.inferred else None,
                },
            }
        )
    return {
        "version": __version__,
        "ok": rep.ok,
        "seconds": round(rep.seconds, 3),
        "cache_hits": rep.cache_hits,
        "problems": [{"file": m.path, "line": loc.line, "message": msg} for m in rep.modules for msg, loc in m.problems],
        "intents": [
            {"id": i.id, "status": i.status, "text": i.text, "functions": i.functions, "proved": i.proved, "refuted": i.refuted, "open": i.open}
            for i in rep.intents
        ],
        "functions": fns,
        "mirrors": [m.to_json() for m in rep.mirrors],
    }


def cmd_check(args: argparse.Namespace) -> int:
    from .render import Paint, Renderer

    root = os.path.abspath(args.root or os.getcwd())
    rep = check(args.paths, _options(args, root), root=root)
    if args.json:
        print(json.dumps(report_json(rep), indent=2))
    else:
        paint = Paint(True if args.color == "always" else False if args.color == "never" else None)
        print(Renderer(rep, paint, verbose=args.verbose).render())
    if args.strict:
        return 0 if rep.ok and all(f.status in ("proved", "trusted") for f in rep.functions) else 1
    return 0 if rep.ok else 1


def cmd_explain(args: argparse.Namespace) -> int:
    from .render import Paint, explain

    root = os.path.abspath(args.root or os.getcwd())
    name = args.name.split("/")[0]
    args.only = [name]
    opts = _options(args, root)
    opts.receipts = False  # explain needs the formulas, not just the verdicts
    rep = check(args.paths, opts, root=root)
    print(explain(rep, args.name, Paint()))
    return 0


def cmd_run(args: argparse.Namespace) -> int:
    from .frontend.python import lower_python
    from .runtime import ContractViolation, install, instrument_source

    script = os.path.abspath(args.script)
    root = os.path.dirname(script)
    install([root])
    sys.argv = [script] + args.args
    sys.path.insert(0, root)
    try:
        src = open(script).read()
        tree = instrument_source(src, lower_python(script, src), script)
        code = compile(tree, script, "exec")
        g = {"__name__": "__main__", "__file__": script}
        exec(code, g)
    except ContractViolation as e:
        print(f"telic: contract violated: {e}", file=sys.stderr)
        return 1
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="telic", description="Contracts in comments. Proofs, not vibes.")
    ap.add_argument("--version", action="version", version=f"telic {__version__}")
    sub = ap.add_subparsers(dest="cmd")

    c = sub.add_parser("check", help="verify functions against their contracts")
    _common(c)
    c.add_argument("--json", action="store_true", help="machine-readable output (for agents and CI)")
    c.add_argument("-v", "--verbose", action="store_true")
    c.add_argument("--strict", action="store_true", help="also fail when anything is open or unsupported")
    c.add_argument("--color", choices=["auto", "always", "never"], default="auto")
    c.set_defaults(func=cmd_check)

    e = sub.add_parser("explain", help="show obligations and formulas for a function or obligation id")
    e.add_argument("name")
    _common(e)
    e.set_defaults(func=cmd_explain)

    r = sub.add_parser("run", help="run a Python script with contracts enforced (C0's -d)")
    r.add_argument("script")
    r.add_argument("args", nargs=argparse.REMAINDER)
    r.set_defaults(func=cmd_run)

    from .lean import add_commands as add_lean

    add_lean(sub, _common, _options)
    from .gaps import add_commands as add_gaps

    add_gaps(sub, _common, _options)
    from .html import add_commands as add_report

    add_report(sub, _common, _options)
    from .intent import add_commands as add_intents

    add_intents(sub, _common, _options)
    from .ledger import add_commands as add_ledger

    add_ledger(sub, _common, _options)
    from .demo import add_commands as add_demo

    add_demo(sub)

    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or (argv[0] not in sub.choices and argv[0] not in ("-h", "--help", "--version")):
        argv = ["check"] + argv
    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
