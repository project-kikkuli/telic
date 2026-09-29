"""Oracles: one typed-question protocol, any backend, never proof."""

import json
import sys
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer

import pytest

from telic import oracle
from telic.oracle import consult, resolve

NOUL = {"type": "noul", "instructions": "is it?", "criteria": {"true": "yes", "false": "no"}}
CHOICE = {"type": "choice", "instructions": "which?", "criteria": {"a": "first", "b": "second"}}
TEXT = {"type": "text", "instructions": "say something"}

CREDENTIALS = ("TELIC_ORACLE", "TELIC_ORACLE_COVERAGE", "TELIC_ORACLE_T", "JEV_API_KEY", "TYPESAFE_API_KEY", "ANTHROPIC_API_KEY", "TELIC_JUDGE_CMD")


@pytest.fixture(autouse=True)
def clean_env(monkeypatch):
    for v in CREDENTIALS:
        monkeypatch.delenv(v, raising=False)


def test_default_is_builtin_and_builtin_ends_every_chain(monkeypatch):
    assert resolve().name == "builtin"
    monkeypatch.setenv("JEV_API_KEY", "k")
    assert resolve().name == "jev then builtin"
    monkeypatch.setenv("TELIC_ORACLE_COVERAGE", "cmd:true")
    assert resolve(task="coverage").name == "cmd:true then builtin"
    assert resolve(task="other").name == "jev then builtin"
    assert resolve("anthropic").notes  # no key: a note, not a crash
    assert resolve("anthropic").name == "builtin"


def test_answers_are_normalised_and_bad_ones_abstain():
    qs = {"n": NOUL, "c": CHOICE, "t": TEXT, "missing": NOUL}
    got = oracle._answers({"answers": {"n": True, "c": {"choice": "zzz"}, "t": "hi"}}, qs)
    assert got == {"n": {"type": "noul", "noul": 1.0}, "t": {"type": "text", "text": "hi"}}


def test_a_failing_oracle_falls_through_with_a_note(tmp_path):
    bad = f"cmd:{sys.executable} -c 'import sys; sys.exit(3)'"
    got = consult("t", {}, {"n": NOUL}, spec=bad)
    assert got.answers == {}  # builtin has no rule for task "t": it abstains
    assert got.notes and "exit 3" in got.notes[0]


def test_questions_go_to_the_first_oracle_that_answers(tmp_path):
    first = tmp_path / "a.py"
    first.write_text("import json, sys; json.load(sys.stdin); print(json.dumps({'answers': {'n': {'noul': 0.2}}}))")
    second = tmp_path / "b.py"
    second.write_text("import json, sys; req = json.load(sys.stdin); print(json.dumps({'answers': {k: {'choice': 'b'} for k in req['questions']}}))")
    got = consult("t", {}, {"n": NOUL, "c": CHOICE}, spec=f"cmd:{sys.executable} {first} then cmd:{sys.executable} {second}")
    assert got.answers["n"]["noul"] == 0.2 and got.answers["n"]["by"].endswith("a.py")
    assert got.answers["c"]["choice"] == "b" and got.answers["c"]["by"].endswith("b.py")


def plugin(task, state, questions):
    return {k: {"noul": 0.75} for k in questions}


def test_python_plugin_and_cache(tmp_path):
    spec = f"py:{__name__}:plugin"
    got = consult("t", {"x": 1}, {"n": NOUL}, spec=spec, root=str(tmp_path))
    assert got.answers["n"]["noul"] == 0.75
    cached = json.loads((tmp_path / ".telic" / "oracle.json").read_text())
    assert len(cached) == 1


def test_llm_backends_get_a_prompt_and_may_wrap_json_in_prose(tmp_path):
    script = tmp_path / "llm.py"
    script.write_text(
        "import sys\n"
        "p = sys.stdin.read()\n"
        "assert 'n (noul)' in p and 't (text)' in p\n"
        "print('Sure! {\"n\": {\"noul\": 0.6}, \"t\": {\"text\": \"ok\"}} hope that helps')\n"
    )
    got = consult("t", {}, {"n": NOUL, "t": TEXT}, spec=f"llm-cmd:{sys.executable} {script}")
    assert got.answers["n"]["noul"] == 0.6 and got.answers["t"]["text"] == "ok"


def test_the_jev_wire_format(monkeypatch):
    seen = {}

    class H(BaseHTTPRequestHandler):
        def do_POST(self):
            seen["auth"] = self.headers.get("authorization")
            seen["body"] = json.loads(self.rfile.read(int(self.headers["content-length"])))
            out = {"model": "jev-x", "answers": {"n": {"type": "noul", "noul": 0.9}, "c": {"type": "choice", "choice": "a", "confidence": 0.8, "probabilities": {"a": 0.9, "b": 0.1}}}}
            data = json.dumps(out).encode()
            self.send_response(200)
            self.send_header("content-length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def log_message(self, *a):
            pass

    srv = HTTPServer(("127.0.0.1", 0), H)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    try:
        monkeypatch.setenv("JEV_API_KEY", "secret")
        monkeypatch.setenv("JEV_URL", f"http://127.0.0.1:{srv.server_port}/v1/systemone")
        monkeypatch.setenv("NO_PROXY", "127.0.0.1")
        monkeypatch.setenv("no_proxy", "127.0.0.1")
        got = consult("t", "state", {"n": NOUL, "c": CHOICE, "t": TEXT}, spec="jev")
    finally:
        srv.shutdown()
    assert seen["auth"] == "Bearer secret"
    body = seen["body"]
    assert body["model"] == "jev-latest" and body["state"] == "state" and "task" not in body
    assert set(body["questions"]) == {"n", "c"}  # Jev answers no free text: never asked
    assert got.answers["n"]["noul"] == 0.9 and got.answers["c"]["confidence"] == 0.8
    assert "t" not in got.answers


def test_builtin_coverage_needs_proved_facts_that_mention_the_requirement():
    q = {"covers": NOUL, "part1": {**NOUL, "condition": "the shop shall refund at most what was paid"}}
    facts = [{"function": "refund", "clause": "ensures result <= paid", "status": "proved"}]
    good = consult("coverage", {"facts": facts}, q, spec="builtin").answers
    assert good["covers"]["noul"] >= 0.5
    unproved = consult("coverage", {"facts": [{**facts[0], "status": "refuted"}]}, q, spec="builtin").answers
    assert unproved["covers"]["noul"] == 0.0
    other = [{"function": "log_event", "clause": "ensures len(result) > 0", "status": "proved"}]
    assert consult("coverage", {"facts": other}, q, spec="builtin").answers["covers"]["noul"] < 0.5
