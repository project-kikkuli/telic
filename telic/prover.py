"""Provers: where ``telic prove`` gets candidate Lean proofs.

A prover sees one open obligation and returns a candidate proof. Lean checks
every candidate, so a prover is trusted for nothing: a wrong answer costs an
attempt, never a verdict.

Backends, chosen with ``telic prove --agent SPEC`` or ``TELIC_PROVER``:

    COMMAND / cmd:COMMAND   the prompt on stdin, a reply on stdout ("claude -p")
    http:URL / https://...  POSTs the request below as JSON (TELIC_PROVER_TOKEN
                            is sent as a bearer token)
    py:MODULE:FUNC          FUNC(request) -> reply
    NAME[:ARG]              a plugin registered under the ``telic.provers``
                            entry point: NAME(ARG) -> FUNC(request) -> reply

The request is

    {"prompt": <the full instructions for an LLM>,
     "document": <the complete Lean file, ending in the theorem with `sorry`>,
     "theorem": <its name>, "statement": <its statement>,
     "lean_version": "4.34.1", "obligation": <id>, "message": <what it claims>,
     "attempt": 1, "feedback": <Lean's errors on the previous attempt, or "">}

and the reply is text holding a ```lean block with the tactic proof, or JSON
``{"proof": <tactics>}`` or ``{"lean": <the document with sorry filled in>}``.
A prover that fills in whole files (Harmonic's Aristotle, for instance) can
take ``document`` and answer with ``lean``.
"""

from __future__ import annotations

import importlib
import json
import os
import re
import shlex
import subprocess
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any, Callable

TIMEOUT_S = 600

Request = dict[str, Any]


class ProverError(RuntimeError):
    pass


@dataclass
class Prover:
    name: str
    send: Callable[[Request], str]

    def prove(self, request: Request) -> str | None:
        return extract_proof(self.send(request), request["theorem"])


def resolve(spec: str | None) -> Prover | None:
    spec = spec or os.environ.get("TELIC_PROVER")
    if not spec:
        return None
    head, _, arg = spec.partition(":")
    if head in ("http", "https"):
        url = spec if head == "https" or arg.startswith("//") else arg
        if url.startswith("//"):
            url = "http:" + url
        return Prover(f"http:{url}", lambda r: _post(url, r))
    if head == "cmd":
        return Prover(spec, lambda r: _run(arg, r["prompt"]))
    if head == "py":
        mod, _, fn = arg.rpartition(":")
        if not mod:
            raise ProverError(f"py prover needs MODULE:FUNC, got {arg!r}")
        return Prover(spec, getattr(importlib.import_module(mod), fn))
    plugin = _plugin(head) if re.fullmatch(r"[\w.-]+", head) else None
    if plugin is not None:
        return Prover(spec, plugin(arg or None))
    return Prover(f"cmd:{spec}", lambda r: _run(spec, r["prompt"]))


def extract_proof(reply: str, theorem: str) -> str | None:
    text = reply
    try:
        data = json.loads(reply)
    except ValueError:
        data = None
    if isinstance(data, dict):
        if isinstance(data.get("proof"), str):
            return _dedent(data["proof"]) or None
        if isinstance(data.get("lean"), str):
            m = re.search(rf"theorem {re.escape(theorem)}\b.*?:= by\n(.*)", data["lean"], re.S)
            return _dedent(m.group(1)) if m else None
        text = str(data.get("text", ""))
    blocks = re.findall(r"```(?:lean4?|)\s*\n(.*?)```", text, re.S)
    if not blocks:
        return None
    proof = blocks[-1].strip("\n")
    # Accept a full theorem by mistake: keep only what follows its ':= by'
    if re.match(r"\s*(theorem|lemma|example)\b", proof) and ":= by" in proof:
        proof = proof.split(":= by", 1)[1]
    return _dedent(proof)


def _dedent(proof: str) -> str:
    lines = proof.strip("\n").splitlines()
    indents = [len(l) - len(l.lstrip()) for l in lines if l.strip()]
    cut = min(indents) if indents else 0
    return "\n".join(l[cut:] for l in lines).strip("\n")


def _run(command: str, stdin: str) -> str:
    try:
        p = subprocess.run(shlex.split(command), input=stdin, capture_output=True, text=True, timeout=TIMEOUT_S)
    except subprocess.TimeoutExpired:
        raise ProverError(f"{command}: timed out after {TIMEOUT_S}s") from None
    except OSError as e:
        raise ProverError(f"{command}: {e}") from None
    if p.returncode != 0 and not p.stdout.strip():
        raise ProverError(f"{command}: exit {p.returncode}: {p.stderr.strip()[-200:]}")
    return p.stdout


def _post(url: str, request: Request) -> str:
    headers = {"content-type": "application/json"}
    token = os.environ.get("TELIC_PROVER_TOKEN")
    if token:
        headers["authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, data=json.dumps(request).encode(), headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT_S) as resp:
            return resp.read().decode()
    except urllib.error.HTTPError as e:
        raise ProverError(f"http:{url}: HTTP {e.code} {e.read().decode(errors='replace')[:200]}") from None
    except (urllib.error.URLError, TimeoutError) as e:
        raise ProverError(f"http:{url}: {e}") from None


def _plugin(name: str) -> Callable[[str | None], Callable[[Request], str]] | None:
    from importlib.metadata import entry_points

    for ep in entry_points(group="telic.provers"):
        if ep.name == name:
            return ep.load()
    return None
