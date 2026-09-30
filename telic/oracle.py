"""Oracles: the one place telic delegates a judgment to a model.

telic proves things; a few steps need judgment that no proof gives: whether
an aim's lemmas cover its words, and which proved facts read like
requirements (or like bugs). Those steps go through this module and nowhere
else, and their answers are always labelled with the oracle that gave them
and never count as proof.

The protocol is typed questions about a state, the shape of a System One
classifier (TypeSafe's Jev): the caller sends

    {"task": "coverage", "state": <any JSON>,
     "questions": {"covers": {"type": "noul", "instructions": "...",
                              "criteria": {"true": "...", "false": "..."}}}}

and gets back ``{"answers": {"covers": {"type": "noul", "noul": 0.93}}}``.
Question types:

- ``noul``   yes/no, answered with a probability ``noul`` in [0, 1];
- ``choice`` one of ``criteria``'s keys: ``choice``, ``probabilities``, ``confidence``;
- ``score``  a rating over a list of levels: ``score`` (a number), ``confidence``;
- ``text``   free text (``text``), answered only by generative backends.

An oracle may leave a question out: that is an abstention, and the caller
falls back (to the next oracle in the chain, or to not deciding).

Backends, chosen with ``--oracle`` or ``TELIC_ORACLE`` (``TELIC_ORACLE_<TASK>``
for one task):

    builtin              deterministic classifiers, local and free (the fallback)
    jev[:MODEL]          TypeSafe System One (JEV_API_KEY or TYPESAFE_API_KEY)
    http:URL             POSTs the request above, reads {"answers": ...}
    cmd:COMMAND          the request on stdin, {"answers": ...} on stdout
    py:MODULE:FUNC       FUNC(task, state, questions) -> answers
    anthropic[:MODEL]    an LLM prompted for the typed answers (ANTHROPIC_API_KEY)
    llm-cmd:COMMAND      the same prompt on stdin, the LLM's reply on stdout
    NAME[:ARG]           a plugin registered under the ``telic.oracles`` entry point

Specs can be chained with `` then ``, e.g. ``jev then anthropic``: questions
one oracle leaves unanswered go to the next, and ``builtin`` always ends the
chain. Judgments default to Jev when its key is set, with ``claude -p`` as
the fallback for what Jev leaves unanswered. The generative tasks
(``GENERATIVE``: writing mutants, proposing contracts), which Jev can't
answer, default to ``llm-cmd:claude -p`` when the ``claude`` CLI is on the
PATH.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import urllib.request
from dataclasses import dataclass, field
from typing import Any, Callable

KINDS = ("noul", "choice", "score", "text")
JEV_URL = "https://api.typesafe.ai/v1/systemone"
JEV_MODEL = "jev-latest"
LLM_MODEL = "claude-haiku-4-5-20251001"
TIMEOUT_S = 90
CLAUDE_CMD = "claude -p"
GENERATIVE = ("mutate", "strengthen")

Questions = dict[str, dict[str, Any]]
Answers = dict[str, dict[str, Any]]


class OracleError(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# Backends


@dataclass
class Oracle:
    name: str
    kinds: frozenset[str] = frozenset(KINDS)

    def ask(self, task: str, state: Any, questions: Questions) -> Answers:  # pragma: no cover - interface
        raise NotImplementedError


@dataclass
class Builtin(Oracle):
    """Deterministic classifiers, one per task (see ``BUILTIN_TASKS``). They
    abstain on tasks and questions they have no rule for."""

    name: str = "builtin"

    def ask(self, task: str, state: Any, questions: Questions) -> Answers:
        fn = BUILTIN_TASKS.get(task)
        return fn(state, questions) if fn else {}


@dataclass
class Http(Oracle):
    url: str = ""
    token: str | None = None
    model: str | None = None
    wire: str = "telic"  # "telic" sends the task; "jev" sends only what Jev reads

    def ask(self, task: str, state: Any, questions: Questions) -> Answers:
        body: dict[str, Any] = {"state": state, "questions": questions}
        if self.wire == "telic":
            body["task"] = task
        else:  # only the fields Jev defines
            body["questions"] = {k: {f: q[f] for f in ("type", "instructions", "criteria") if f in q} for k, q in questions.items()}
        if self.model:
            body["model"] = self.model
        headers = {"content-type": "application/json"}
        if self.token:
            headers["authorization"] = f"Bearer {self.token}"
        req = urllib.request.Request(self.url, data=json.dumps(body).encode(), headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT_S) as resp:
                data = json.loads(resp.read())
        except urllib.error.HTTPError as e:
            detail = e.read().decode(errors="replace")[:200]
            raise OracleError(f"{self.name}: HTTP {e.code} {detail}") from None
        except (urllib.error.URLError, TimeoutError) as e:
            raise OracleError(f"{self.name}: {e}") from None
        return _answers(data, questions)


def jev(model: str | None = None) -> Http:
    key = os.environ.get("JEV_API_KEY") or os.environ.get("TYPESAFE_API_KEY")
    if not key:
        raise OracleError("jev needs JEV_API_KEY (or TYPESAFE_API_KEY) in the environment")
    return Http(
        name=f"jev:{model}" if model else "jev",
        kinds=frozenset(("noul", "choice", "score")),
        url=os.environ.get("JEV_URL", JEV_URL),
        token=key,
        model=model or JEV_MODEL,
        wire="jev",
    )


@dataclass
class Command(Oracle):
    command: str = ""

    def ask(self, task: str, state: Any, questions: Questions) -> Answers:
        req = json.dumps({"task": task, "state": state, "questions": questions})
        out = _run(self.command, req, self.name)
        try:
            data = json.loads(out)
        except ValueError:
            raise OracleError(f"{self.name}: expected JSON on stdout, got {out.strip()[:120]!r}") from None
        return _answers(data, questions)


@dataclass
class Python(Oracle):
    fn: Callable[..., Any] | None = None

    def ask(self, task: str, state: Any, questions: Questions) -> Answers:
        assert self.fn is not None
        return _answers(self.fn(task, state, questions), questions)


@dataclass
class Llm(Oracle):
    """A generative model asked for the typed answers as JSON. ``send`` takes
    a prompt and returns the model's reply."""

    send: Callable[[str], str] | None = None

    def ask(self, task: str, state: Any, questions: Questions) -> Answers:
        assert self.send is not None
        reply = self.send(llm_prompt(task, state, questions))
        m = re.search(r"\{.*\}", reply, re.S)
        if not m:
            raise OracleError(f"{self.name}: the reply had no JSON object")
        try:
            data = json.loads(m.group(0))
        except ValueError as e:
            raise OracleError(f"{self.name}: the reply's JSON did not parse ({e})") from None
        return _answers(data, questions)


def llm_prompt(task: str, state: Any, questions: Questions) -> str:
    fmt = {
        "noul": 'a probability that the answer is yes, e.g. {"noul": 0.9}',
        "choice": 'one of the listed keys, e.g. {"choice": "KEY", "confidence": 0.8}',
        "score": 'a number on the listed scale (0 = first level), e.g. {"score": 2}',
        "text": 'free text, e.g. {"text": "..."}',
    }
    qs = []
    for key, q in questions.items():
        crit = q.get("criteria")
        crit_s = f"\n  criteria: {json.dumps(crit)}" if crit else ""
        qs.append(f"- {key} ({q['type']}): {_instr(q)}{crit_s}\n  answer with {fmt[q['type']]}")
    role = ROLES.get(task, f"You are a careful classifier for a program verifier (task: {task}).")
    return (
        f"{role} Read the state and answer every "
        "question. Answer with one JSON object mapping each question key to its answer, and nothing else.\n\n"
        f"State:\n{json.dumps(state, indent=1)}\n\nQuestions:\n" + "\n".join(qs)
    )


ROLES = {
    "mutate": "You are a mutation testing expert working for a program verifier (task: mutate).",
    "strengthen": "You are a specification expert working for a program verifier (task: strengthen).",
}


def anthropic(model: str | None = None) -> Llm:
    key = os.environ.get("ANTHROPIC_API_KEY")
    if not key:
        raise OracleError("anthropic needs ANTHROPIC_API_KEY in the environment")
    model = model or os.environ.get("TELIC_JUDGE_MODEL") or LLM_MODEL

    def send(prompt: str) -> str:
        body = json.dumps({"model": model, "max_tokens": 4000, "messages": [{"role": "user", "content": prompt}]}).encode()
        req = urllib.request.Request(
            "https://api.anthropic.com/v1/messages",
            data=body,
            headers={"x-api-key": key, "anthropic-version": "2023-06-01", "content-type": "application/json"},
        )
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT_S) as resp:
                data = json.loads(resp.read())
        except urllib.error.HTTPError as e:
            raise OracleError(f"anthropic: HTTP {e.code} {e.read().decode(errors='replace')[:200]}") from None
        return "".join(part.get("text", "") for part in data.get("content", []))

    return Llm(name=f"anthropic:{model}", send=send)


def llm_command(command: str) -> Llm:
    return Llm(name=f"llm-cmd:{command}", send=lambda prompt: _run(command, prompt, "llm-cmd"))


@dataclass
class Chain(Oracle):
    """Each question goes to the first oracle that answers it. An oracle that
    fails is skipped, and the failure is kept in ``notes``."""

    oracles: list[Oracle] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    def ask(self, task: str, state: Any, questions: Questions) -> Answers:
        got: Answers = {}
        for o in self.oracles:
            todo = {k: q for k, q in questions.items() if k not in got and q["type"] in o.kinds}
            if not todo:
                continue
            try:
                ans = o.ask(task, state, todo)
            except Exception as e:  # noqa: BLE001 - a failing oracle is a note, the next one answers
                self.notes.append(str(e) if isinstance(e, OracleError) else f"{o.name}: {e}")
                continue
            for k, a in ans.items():
                if k in todo:
                    got[k] = {**a, "by": o.name}
        return got


# ---------------------------------------------------------------------------
# Choosing an oracle


def resolve(spec: str | None = None, task: str | None = None) -> Chain:
    """The oracle chain for ``task``: ``spec``, else ``TELIC_ORACLE_<TASK>``,
    else ``TELIC_ORACLE``, else whatever credentials are present (Jev, then an
    LLM), always ending with the builtin classifiers."""
    if spec is None and task:
        spec = os.environ.get("TELIC_ORACLE_" + re.sub(r"\W", "_", task).upper())
    spec = spec or os.environ.get("TELIC_ORACLE")
    chain = Chain(name="")
    parts: list[str]
    if spec:
        parts = [p.strip() for p in re.split(r"\s+then\s+", spec) if p.strip()]
    else:
        parts = []
        claude = shutil.which(CLAUDE_CMD.split()[0]) is not None
        if os.environ.get("TELIC_JUDGE_CMD"):
            parts.append("llm-cmd:" + os.environ["TELIC_JUDGE_CMD"])
        elif task in GENERATIVE and claude:
            parts.append("llm-cmd:" + CLAUDE_CMD)
        if task not in GENERATIVE and (os.environ.get("JEV_API_KEY") or os.environ.get("TYPESAFE_API_KEY")):
            parts.append("jev")
            if claude and not os.environ.get("TELIC_JUDGE_CMD"):
                parts.append("llm-cmd:" + CLAUDE_CMD)  # only for what Jev leaves unanswered
        if os.environ.get("ANTHROPIC_API_KEY"):
            parts.append("anthropic")
    for p in parts:
        try:
            chain.oracles.append(backend(p))
        except OracleError as e:
            chain.notes.append(str(e))
    if not any(isinstance(o, Builtin) for o in chain.oracles):
        chain.oracles.append(Builtin())
    chain.name = " then ".join(o.name for o in chain.oracles)
    return chain


def backend(spec: str) -> Oracle:
    head, _, arg = spec.partition(":")
    if head == "builtin":
        return Builtin()
    if head == "jev":
        return jev(arg or None)
    if head in ("http", "https"):
        url = spec if head == "https" or arg.startswith("//") else arg
        if url.startswith("//"):
            url = "http:" + url
        return Http(name=f"http:{url}", url=url, token=os.environ.get("TELIC_ORACLE_TOKEN"))
    if head == "cmd":
        return Command(name=f"cmd:{arg}", command=arg)
    if head == "py":
        mod, _, fn = arg.rpartition(":")
        if not mod:
            raise OracleError(f"py oracle needs MODULE:FUNC, got {arg!r}")
        import importlib

        return Python(name=f"py:{arg}", fn=getattr(importlib.import_module(mod), fn))
    if head == "anthropic":
        return anthropic(arg or None)
    if head == "llm-cmd":
        return llm_command(arg)
    plugin = _plugin(head)
    if plugin is not None:
        o = plugin(arg or None)
        if not isinstance(o, Oracle):
            o = Python(name=spec, fn=o)
        return o
    raise OracleError(f"unknown oracle {spec!r} (builtin, jev, http:URL, cmd:COMMAND, py:MODULE:FUNC, anthropic, llm-cmd:COMMAND)")


def _plugin(name: str) -> Callable[..., Any] | None:
    try:
        from importlib.metadata import entry_points

        for ep in entry_points(group="telic.oracles"):
            if ep.name == name:
                return ep.load()
    except Exception:  # noqa: BLE001 - a broken plugin is the same as none
        return None
    return None


# ---------------------------------------------------------------------------
# Asking, with a cache


CACHE = os.path.join(".telic", "oracle.json")


@dataclass
class Consultation:
    answers: Answers
    oracle: str
    notes: list[str]


def consult(task: str, state: Any, questions: Questions, *, spec: str | None = None, root: str | None = None) -> Consultation:
    """Ask the configured oracle chain. Answers are cached under ``root`` by
    the chain's name and a hash of the request, so a CI run asks once."""
    for k, q in questions.items():
        if q.get("type") not in KINDS:
            raise ValueError(f"question {k}: unknown type {q.get('type')!r}")
    chain = resolve(spec, task)
    digest = hashlib.sha256(json.dumps([chain.name, task, state, questions], sort_keys=True).encode()).hexdigest()[:24]
    path = os.path.join(root, CACHE) if root else None
    cache: dict[str, Any] = {}
    if path:
        try:
            with open(path) as fh:
                cache = json.load(fh)
        except (OSError, ValueError):
            cache = {}
        if digest in cache:
            return Consultation(cache[digest], chain.name, [])
    answers = chain.ask(task, state, questions)
    if path and not chain.notes:
        cache[digest] = answers
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as fh:
            json.dump(cache, fh, indent=1, sort_keys=True)
    return Consultation(answers, chain.name, chain.notes)


def noul(a: dict[str, Any] | None) -> float | None:
    return None if a is None else a.get("noul")


# ---------------------------------------------------------------------------
# Normalising answers from any backend


def _answers(data: Any, questions: Questions) -> Answers:
    if isinstance(data, dict) and isinstance(data.get("answers"), dict):
        data = data["answers"]
    if not isinstance(data, dict):
        raise OracleError("answers must be a JSON object keyed by question")
    out: Answers = {}
    for key, q in questions.items():
        if key not in data or data[key] is None:
            continue
        a = _one(data[key], q)
        if a is not None:
            out[key] = a
    return out


def _one(raw: Any, q: dict[str, Any]) -> dict[str, Any] | None:
    kind = q["type"]
    a = raw if isinstance(raw, dict) else {kind: raw}
    v = a.get(kind)
    if kind == "noul":
        if isinstance(v, bool):
            v = 1.0 if v else 0.0
        if isinstance(v, str):
            v = {"yes": 1.0, "true": 1.0, "no": 0.0, "false": 0.0}.get(v.strip().lower())
        if not isinstance(v, (int, float)):
            return None
        return {"type": "noul", "noul": min(1.0, max(0.0, float(v)))}
    if kind == "choice":
        keys = list((q.get("criteria") or {}).keys())
        if v not in keys:
            return None
        probs = a.get("probabilities") or {}
        conf = a.get("confidence", probs.get(v) if isinstance(probs, dict) else None)
        return {"type": "choice", "choice": v, "probabilities": probs, "confidence": conf}
    if kind == "score":
        if not isinstance(v, (int, float)) or isinstance(v, bool):
            return None
        return {"type": "score", "score": float(v), "confidence": a.get("confidence")}
    if kind == "text":
        return {"type": "text", "text": str(v)} if v is not None else None
    return None


def _instr(q: dict[str, Any]) -> str:
    i = q.get("instructions", "")
    return i if isinstance(i, str) else json.dumps(i)


def _run(command: str, stdin: str, who: str) -> str:
    try:
        p = subprocess.run(command, shell=True, input=stdin, capture_output=True, text=True, timeout=TIMEOUT_S)
    except subprocess.TimeoutExpired:
        raise OracleError(f"{who}: timed out") from None
    if p.returncode != 0:
        raise OracleError(f"{who}: exit {p.returncode}: {p.stderr.strip()[-200:]}")
    return p.stdout


# ---------------------------------------------------------------------------
# Builtin classifiers
#
# Deterministic, cheap and conservative. They are heuristics over words and
# clause shapes, labelled as such wherever their answers are shown.

BUILTIN_TASKS: dict[str, Callable[[Any, Questions], Answers]] = {}


def builtin(task: str) -> Callable[[Callable[[Any, Questions], Answers]], Callable[[Any, Questions], Answers]]:
    def reg(fn: Callable[[Any, Questions], Answers]) -> Callable[[Any, Questions], Answers]:
        BUILTIN_TASKS[task] = fn
        return fn

    return reg


_STOP = set(
    """a an the and or of to in on at by for with from into be is are was were been being it its this that these those
    shall must should will would can could may might do does did not no than then when while if where whenever each
    every any all some system user users value values which who whom whose as so such only also ever never""".split()
)

# words that name a relation, and the clause tokens that express it
_RELATIONS = {
    "most": {"<="}, "exceed": {"<=", "<"}, "exceeds": {"<=", "<"}, "above": {">", ">="}, "below": {"<", "<="},
    "least": {">="}, "less": {"<", "<="}, "more": {">", ">="}, "greater": {">", ">="}, "fewer": {"<", "<="},
    "equal": {"=="}, "equals": {"=="}, "same": {"=="}, "unchanged": {"old", "=="}, "previous": {"old"},
    "negative": {"<", ">="}, "positive": {">", ">="}, "empty": {"len", "is_empty", "not"}, "length": {"len"},
    "count": {"len"}, "size": {"len"}, "absent": {"none", "is_none"}, "missing": {"none", "is_none", "not"},
    "present": {"none", "is_some", "is_none"}, "sorted": {"<="}, "zero": {"0"}, "unique": {"len", "set"},
}


def words(text: str) -> list[str]:
    """Lower-case content words, with identifiers split at ``_`` and case changes."""
    text = re.sub(r"([a-z])([A-Z])", r"\1 \2", text)
    return [w for w in re.findall(r"[a-z]+|\d+", text.lower().replace("_", " ")) if w not in _STOP]


def _tokens(text: str) -> set[str]:
    out = set(words(text))
    out |= set(re.findall(r"<=|>=|==|!=|<|>", text))
    out |= {m.lower() for m in re.findall(r"[A-Za-z_]+", text)}
    return out


def _matches(word: str, toks: set[str]) -> bool:
    if word in toks:
        return True
    if word in _RELATIONS and _RELATIONS[word] & toks:
        return True
    stem = word[:5] if len(word) > 5 else word.rstrip("s")
    return len(stem) >= 4 and any(t.startswith(stem) or (len(t) >= 4 and word.startswith(t)) for t in toks)


@builtin("coverage")
def _coverage(state: Any, questions: Questions) -> Answers:
    """Each condition of the requirement is covered in proportion to its
    content words that proved facts (their functions and clauses) mention."""
    facts = [f for f in state.get("facts", []) if f.get("status") == "proved"]
    toks: set[str] = set()
    for f in facts:
        toks |= _tokens(f.get("function", "")) | _tokens(f.get("clause", ""))
    conds: dict[str, float] = {}
    for key, q in questions.items():
        cond = q.get("condition")
        if cond is None or q["type"] != "noul":
            continue
        ws = words(cond)
        if not ws or not facts:
            conds[key] = 0.0
            continue
        hit = sum(_matches(w, toks) for w in ws)
        conds[key] = round(hit / len(ws), 2)
    out: Answers = {k: {"type": "noul", "noul": 0.7 if p >= 0.75 else 0.5 if p >= 0.5 else 0.1} for k, p in conds.items()}
    if "covers" in questions:
        out["covers"] = {"type": "noul", "noul": min((a["noul"] for a in out.values()), default=0.1) if facts else 0.0}
    return out


@builtin("classify-facts")
def _classify(state: Any, questions: Questions) -> Answers:
    """Frame conditions and type-level ranges are details; a fact the code
    could not avoid is a requirement candidate. The builtin never calls a fact
    a bug: that needs a reader."""
    out: Answers = {}
    cands = state.get("candidates", {})
    for key, q in questions.items():
        if q["type"] != "choice" or not key.endswith("_kind"):
            continue
        c = cands.get(key[: -len("_kind")], {})
        clause = c.get("clause", "")
        body = re.sub(r"^(ensures|requires)\s+", "", clause).strip()
        frame = re.fullmatch(r"(.+?)\s*==\s*old\((.+)\)", body)
        detail = bool(
            (frame and frame.group(1).strip() == frame.group(2).strip())
            or re.fullmatch(r"(result|len\(.*\)|.*\.len\(\)|.*\.length)\s*>=\s*0", body)
            or re.fullmatch(r"isinstance\(.*\)", body)
            or body in ("True", "true")
        )
        if detail:
            out[key] = {"type": "choice", "choice": "detail", "probabilities": {"requirement": 0.2, "detail": 0.8, "bug": 0.0}, "confidence": 0.8}
        else:
            out[key] = {"type": "choice", "choice": "requirement", "probabilities": {"requirement": 0.6, "detail": 0.4, "bug": 0.0}, "confidence": 0.6}
    return out


# ---------------------------------------------------------------------------
# CLI: telic oracle

TASKS = ("coverage", "classify-facts", *GENERATIVE)


def cmd_oracle(args: Any) -> int:
    for task in TASKS:
        chain = resolve(args.oracle, task)
        print(f"{task:15} {chain.name}")
        for n in chain.notes:
            print(f"{'':15} note: {n}")
    if not args.probe:
        return 0
    q = {
        "covers": {
            "type": "noul",
            "instructions": "Do the proved facts establish the requirement?",
            "criteria": {"true": "every condition is established", "false": "some condition is not established"},
        },
        "part1": {
            "type": "noul",
            "instructions": "Is 'the shop shall refund at most what was paid' established by a proved fact?",
            "criteria": {"true": "yes", "false": "no"},
            "condition": "the shop shall refund at most what was paid",
        },
    }
    state = {
        "requirement": "WHEN a refund is requested, the shop shall refund at most what was paid.",
        "facts": [{"function": "refund", "clause": "ensures result <= paid", "status": "proved"}],
    }
    got = consult("coverage", state, q, spec=args.oracle)
    print(json.dumps({"oracle": got.oracle, "answers": got.answers, "notes": got.notes}, indent=2))
    return 0 if got.answers else 1


def add_command(sub: Any) -> None:
    o = sub.add_parser("oracle", help="which oracle answers each judgment task (and --probe it)")
    o.add_argument("--oracle", default=None, help="oracle spec to resolve instead of TELIC_ORACLE")
    o.add_argument("--probe", action="store_true", help="ask one sample coverage question")
    o.set_defaults(func=cmd_oracle)
