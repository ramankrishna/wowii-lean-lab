"""Solver loop: LLM proposes a full Lean file -> verifier checks -> errors fed back.

Pre-registration: on first run, targets + success criteria are frozen into
preregistration.json (with a hash). Later runs refuse to start if the target
list changed. Every attempt is appended to attempts.jsonl, pass or fail.

Usage:
  export ANTHROPIC_API_KEY=...      # your key, never commit it
  python3 solve_loop.py --project ~/rh-lean/formal-conjectures --targets targets.json
targets.json: [{"file": "FormalConjectures/WrittenOnTheWallII/GraphConjecture84.lean",
                "theorem": "conjecture84", "mode": "prove"}, ...]
"""
import argparse
import datetime as dt
import hashlib
import json
import os
import re
import sys

from verifier import verify

MODEL = os.environ.get("SOLVER_MODEL", "claude-opus-5-5")
CRITERIA = ("PASS = compiles with lake env lean, statement and prefix byte-locked to the original, "
            "no sorry/admit/axiom/unsafe, #print axioms within {propext, Classical.choice, Quot.sound}. "
            "Disproofs additionally need human review of the negated statement.")

SYSTEM = """You are a Lean 4 + Mathlib prover working inside the google-deepmind/formal-conjectures repo.
Return the COMPLETE Lean file in one ```lean block.
Hard rules (a verifier enforces them, violations are rejected without compiling):
- Keep everything before the target theorem byte-identical. You may insert helper `lemma`s
  directly above the target theorem's docstring; no new def/abbrev/instance/notation/options.
- Do not change the target theorem's statement. Replace only its `sorry`.
- No sorry, admit, axiom, native_decide, unsafe.
If you believe the statement is FALSE, say so plainly, give the explicit counterexample,
and still return your best file. Honest failure beats a fake proof."""


def sha(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode()).hexdigest()[:16]


def preregister(path, targets, max_iters):
    reg = {"targets": targets, "max_iters_per_target": max_iters, "model": MODEL,
           "criteria": CRITERIA}
    h = sha(reg)
    if os.path.exists(path):
        old = json.load(open(path))
        if old["hash"] != h:
            sys.exit(f"Preregistration mismatch ({old['hash']} != {h}). "
                     "Targets/settings changed after registration. Start a new run dir.")
        return old
    reg.update(hash=h, registered_at=dt.datetime.now(dt.timezone.utc).isoformat())
    json.dump(reg, open(path, "w"), indent=2)
    return reg


def context_files(project, statement_src):
    """Pull definition files for identifiers used in the conjecture."""
    idents = set(re.findall(r"\b([a-zA-Z_][\w']*)\b", statement_src))
    root = os.path.join(project, "FormalConjecturesForMathlib")
    out = []
    for dp, _, fns in os.walk(root):
        for fn in fns:
            if not fn.endswith(".lean"):
                continue
            p = os.path.join(dp, fn)
            src = open(p).read()
            defs = set(re.findall(r"\bdef\s+([\w']+)|\babbrev\s+([\w']+)", src))
            names = {a or b for a, b in defs}
            if names & idents:
                out.append((os.path.relpath(p, project), src[:12000]))
    return out[:6]


def extract_lean(text):
    m = re.findall(r"```lean\s*\n(.*?)```", text, flags=re.S)
    return m[-1] if m else None


def run_target(client, project, t, max_iters, log):
    original = open(os.path.join(project, t["file"])).read()
    ctx = context_files(project, original)
    ctx_txt = "\n\n".join(f"--- {p} ---\n{s}" for p, s in ctx)
    msgs = [{"role": "user", "content":
             f"Target theorem: `{t['theorem']}` (mode: {t.get('mode','prove')}).\n\n"
             f"File {t['file']}:\n```lean\n{original}\n```\n\nRelevant definitions:\n{ctx_txt}"}]
    for i in range(1, max_iters + 1):
        r = client.messages.create(model=MODEL, max_tokens=16000, system=SYSTEM, messages=msgs)
        reply = "".join(b.text for b in r.content if b.type == "text")
        cand = extract_lean(reply)
        if cand is None:
            result = {"ok": False, "stage": "format", "errors": ["no ```lean block"]}
        else:
            result = verify(project, original, cand, t["theorem"], t.get("mode", "prove"))
        claims_false = bool(re.search(r"\b(false|counterexample)\b", reply, flags=re.I))
        rec = {"ts": dt.datetime.now(dt.timezone.utc).isoformat(), "target": t, "iter": i,
               "result": result, "model_claims_false": claims_false,
               "usage": {"in": r.usage.input_tokens, "out": r.usage.output_tokens}}
        log.write(json.dumps(rec) + "\n")
        log.flush()
        print(f"[{t['theorem']}] iter {i}: {result['stage']} ok={result['ok']}")
        if result["ok"]:
            os.makedirs("proofs", exist_ok=True)
            open(f"proofs/{t['theorem']}.lean", "w").write(cand)
            return {"status": "proved" if t.get("mode", "prove") == "prove" else "disproved*",
                    "iters": i, "claims_false": claims_false}
        msgs.append({"role": "assistant", "content": reply})
        msgs.append({"role": "user", "content":
                     "Verifier rejected it.\n" + json.dumps(result, indent=1)[:6000] +
                     "\nFix and return the full file."})
    return {"status": "failed", "iters": max_iters, "claims_false": claims_false}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--project", required=True)
    ap.add_argument("--targets", required=True)
    ap.add_argument("--max-iters", type=int, default=15)
    a = ap.parse_args()
    project = os.path.expanduser(a.project)
    targets = json.load(open(a.targets))
    preregister("preregistration.json", targets, a.max_iters)

    import anthropic
    client = anthropic.Anthropic()
    summary = []
    with open("attempts.jsonl", "a") as log:
        for t in targets:
            out = run_target(client, project, t, a.max_iters, log)
            summary.append((t["theorem"], out))
    with open("results_agent.md", "w") as f:
        f.write(f"# Solver run ({MODEL})\n\nCriteria: {CRITERIA}\n\n")
        f.write("| theorem | status | iters | model claimed false |\n|---|---|---|---|\n")
        for name, o in summary:
            f.write(f"| {name} | {o['status']} | {o['iters']} | {o['claims_false']} |\n")
        f.write("\nAny pass still needs a literature check before calling it new.\n")
    print(open("results_agent.md").read())


if __name__ == "__main__":
    main()
