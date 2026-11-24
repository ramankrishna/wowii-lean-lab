"""Full calibration pack for verifier.py. Every rejection stage gets one real-Lean case,
and the positive controls use repo proofs neither we nor Claude Code wrote.

Run:  export PATH=$HOME/.elan/bin:$PATH
      cd ~/rh-lean/verifier && python3 run_controls.py
Writes controls.md. Exit code 1 if any case disagrees with its expectation.
Does not modify verifier.py or any repo file (tampered candidates are temp files).
"""
import json
import os
import sys
import tempfile

from verifier import verify

ROOT = os.path.expanduser(os.environ.get("WOWII_ROOT", "~/rh-lean"))
P = os.path.join(ROOT, "formal-conjectures")
W = "FormalConjectures/WrittenOnTheWallII"
PROOF96 = os.path.join(ROOT, "proofs", "GraphConjecture96.lean")


def rd(rel):
    return open(os.path.join(P, rel)).read()


def must_replace(text, old, new):
    assert text.count(old) == 1, f"anchor not unique/found: {old!r}"
    return text.replace(old, new)


p96 = open(PROOF96).read()
o96 = rd(f"{W}/GraphConjecture96.lean")
anchor = "/--\nWOWII [Conjecture 96]"

CASES = [
    # name, original rel, candidate text, theorem, expected (ok, stage)
    ("P1 repo proof C141 (external)", f"{W}/GraphConjecture141.lean",
     rd(f"{W}/GraphConjecture141.lean"), "conjecture141", (True, "passed")),
    ("P2 repo proof C143 (external)", f"{W}/GraphConjecture143.lean",
     rd(f"{W}/GraphConjecture143.lean"), "conjecture143", (True, "passed")),
    ("N1 C84 original has sorry", f"{W}/GraphConjecture84.lean",
     rd(f"{W}/GraphConjecture84.lean"), "conjecture84", (False, "static")),
    ("N2 repo native_decide theorem (C36)", f"{W}/GraphConjecture36.lean",
     rd(f"{W}/GraphConjecture36.lean"), "wowii36Counterexample_no_inducedPath6",
     (False, "axioms")),
    ("N3 C96 proof, final tactic broken", f"{W}/GraphConjecture96.lean",
     must_replace(p96, "  linarith\n", "  exact trivial\n"), "conjecture96", (False, "compile")),
    ("N4 C96 proof, statement weakened 1+ -> 2+", f"{W}/GraphConjecture96.lean",
     must_replace(p96, "≤ 1 + (minDistEven", "≤ 2 + (minDistEven"), "conjecture96",
     (False, "lock")),
    ("N5 C96 proof, helper def inserted", f"{W}/GraphConjecture96.lean",
     must_replace(p96, anchor, "noncomputable def trickyBound : ℕ := 1000\n\n" + anchor),
     "conjecture96", (False, "lock")),
    ("N6 C96 proof, axiom smuggled in", f"{W}/GraphConjecture96.lean",
     must_replace(p96, anchor, "axiom cheat : False\n\n" + anchor), "conjecture96",
     (False, "static")),
    ("N7 C96 proof, change hidden inside let (min' -> max')", f"{W}/GraphConjecture96.lean",
     must_replace(p96, ".image (distEven G)).min' (by simp)\n    let maxL",
                  ".image (distEven G)).max' (by simp)\n    let maxL"),
     "conjecture96", (False, "lock")),
    ("P3 C96 proof (Claude Code's)", f"{W}/GraphConjecture96.lean", p96, "conjecture96",
     (True, "passed")),
    # Defense in depth: text lock switched OFF, the Lean type lock alone must catch N4.
    ("N8 N4 again, text lock disabled -> type lock", f"{W}/GraphConjecture96.lean",
     must_replace(p96, "≤ 1 + (minDistEven", "≤ 2 + (minDistEven"), "conjecture96",
     (False, "type_lock")),
]

import verifier as _v
_real_match = _v.statement_matches

rows, bad = [], 0
for name, orig_rel, cand, thm, (want_ok, want_stage) in CASES:
    _v.statement_matches = (lambda *a: (True, "", "")) if name.startswith("N8") else _real_match
    r = verify(P, rd(orig_rel), cand, thm)
    match = r["ok"] == want_ok and r["stage"] == want_stage
    bad += not match
    rows.append((name, f"{want_ok}/{want_stage}", f"{r['ok']}/{r['stage']}",
                 "OK" if match else "MISMATCH", r))
    print(f"{'OK      ' if match else 'MISMATCH'} {name}: got {r['ok']}/{r['stage']} {r['errors'][:1]}",
          flush=True)

with open("controls.md", "w") as f:
    f.write("# Verifier control pack\n\n| case | expected | got | |\n|---|---|---|---|\n")
    for name, e, g, m, _ in rows:
        f.write(f"| {name} | {e} | {g} | {m} |\n")
    f.write(f"\n**{len(rows) - bad}/{len(rows)} as expected.**\n\n## Raw results\n")
    for name, *_, r in rows:
        f.write(f"\n### {name}\n```json\n{json.dumps(r, indent=1)}\n```\n")
sys.exit(1 if bad else 0)
