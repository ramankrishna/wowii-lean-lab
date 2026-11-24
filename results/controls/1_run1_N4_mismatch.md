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
 "seconds": 3.0
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
  "~/rh-lean/formal-conjectures/.verifier_scratch/tmpoflk6_9c.lean:244:2: error: Type mismatch"
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

## MISMATCH record (N4), added after the run; scripts not modified

**What happened:** the C96 proof with its statement weakened from `≤ 1 + (minDistEven` to `≤ 2 + (minDistEven`
passed every stage (`ok=true, stage=passed`, allowed axioms only). Expected: `ok=false, stage=lock`.

**Why (read-only diagnosis):** `extract_statement` cuts the statement at the first `:=` after
`theorem <name>`. The C96 statement contains `let minDistEven := ...`, so the locked text is only
`theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) : let minDistEven`.
Nothing after the first `let ... :=` is compared, and `prefix_lock` checks only the text *before* the theorem.
The weakened statement is also genuinely provable: the unchanged proof's final `linarith` closes it. So the case
compiled and passed.

**Scope:** the statement lock is unreliable for any target whose statement contains `:=`
before the proof. Among the 8 targets, C72, C96 and C133 use `let ... :=`.
The earlier calibration pass for `proofs/GraphConjecture96.lean` should not rest on the verifier's lock.
Statement identity for that file was checked separately (byte-identical statement; a diff against
the repo file shows only the removed `sorry` line), but the verifier itself did not establish it.

Run stopped here per instructions. No further cases or fixes attempted.
