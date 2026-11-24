# Verifier control pack

| case | expected | got | |
|---|---|---|---|
| P1 repo proof C141 (external) | True/passed | True/passed | OK |
| P2 repo proof C143 (external) | True/passed | True/passed | OK |
| N1 C84 original has sorry | False/static | False/static | OK |
| N2 repo native_decide theorem (C36) | False/axioms | False/axioms | OK |
| N3 C96 proof, final tactic broken | False/compile | False/compile | OK |
| N4 C96 proof, statement weakened 1+ -> 2+ | False/lock | True/passed | MISMATCH |
| N5 C96 proof, helper def inserted | False/lock | False/lock | OK |
| N6 C96 proof, axiom smuggled in | False/static | False/static | OK |

**7/8 as expected.**

## Raw results

### P1 repo proof C141 (external)
```json
{
 "ok": true,
 "mode": "prove",
 "theorem": "conjecture141",
 "stage": "passed",
 "errors": [],
 "axioms": [
  "propext",
  "Classical.choice",
  "Quot.sound"
 ],
 "needs_human_review": false,
 "seconds": 2.9
}
```

### P2 repo proof C143 (external)
```json
{
 "ok": true,
 "mode": "prove",
 "theorem": "conjecture143",
 "stage": "passed",
 "errors": [],
 "axioms": [
  "propext",
  "Classical.choice",
  "Quot.sound"
 ],
 "needs_human_review": false,
 "seconds": 2.7
}
```

### N1 C84 original has sorry
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "conjecture84",
 "stage": "static",
 "errors": [
  "banned: sorry"
 ],
 "axioms": null,
 "needs_human_review": false
}
```

### N2 repo native_decide theorem (C36)
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "wowii36Counterexample_no_inducedPath6",
 "stage": "axioms",
 "errors": [
  "disallowed axioms: ['WrittenOnTheWallII.GraphConjecture36.wowii36Counterexample_no_inducedPath6._native.native_decide.ax_1_1']"
 ],
 "axioms": [
  "propext",
  "Classical.choice",
  "Quot.sound",
  "WrittenOnTheWallII.GraphConjecture36.wowii36Counterexample_no_inducedPath6._native.native_decide.ax_1_1"
 ],
 "needs_human_review": false
}
```

### N3 C96 proof, final tactic broken
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "conjecture96",
 "stage": "compile",
 "errors": [
  "~/rh-lean/formal-conjectures/.verifier_scratch/tmp3tst4n_i.lean:244:2: error: Type mismatch"
 ],
 "axioms": null,
 "needs_human_review": false
}
```

### N4 C96 proof, statement weakened 1+ -> 2+
```json
{
 "ok": true,
 "mode": "prove",
 "theorem": "conjecture96",
 "stage": "passed",
 "errors": [],
 "axioms": [
  "propext",
  "Classical.choice",
  "Quot.sound"
 ],
 "needs_human_review": false,
 "seconds": 3.0
}
```

### N5 C96 proof, helper def inserted
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "conjecture96",
 "stage": "lock",
 "errors": [
  "banned declaration inserted before theorem: ['noncomputable def trickyBound : \u2115 := 1000']"
 ],
 "axioms": null,
 "needs_human_review": false
}
```

### N6 C96 proof, axiom smuggled in
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "conjecture96",
 "stage": "static",
 "errors": [
  "banned: axiom declaration"
 ],
 "axioms": null,
 "needs_human_review": false
}
```

## MISMATCH record (N4), re-run 2026-11-23; scripts not modified

**What happened:** identical to the previous run (record kept in `controls_prev_run.md`). The C96 proof with
`≤ 1 +` changed to `≤ 2 +` returned `ok=true, stage=passed` (axioms propext/Classical.choice/Quot.sound,
3.0s). Expected `ok=false, stage=lock`.

**Raw type_lock output: none exists.** `grep -rn "type_lock"` over `~/rh-lean/verifier` finds no matches in
`verifier.py`, `run_controls.py` or anywhere else, and the N4 result JSON has no type_lock field. `verifier.py`
(mtime 17:25, 9162 bytes, md5 42d4ed042c597f4639fe84f1347ac31e) still contains the text-based
`extract_statement` that cuts at the first `:=`. For C96 it locks only
`theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) : let minDistEven`.
The expected type-lock fix does not appear to be in the file that ran.

Run stopped here per instructions.
