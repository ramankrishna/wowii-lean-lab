# Verifier control pack

| case | expected | got | |
|---|---|---|---|
| P1 repo proof C141 (external) | True/passed | True/passed | OK |
| P2 repo proof C143 (external) | True/passed | True/passed | OK |
| N1 C84 original has sorry | False/static | False/static | OK |
| N2 repo native_decide theorem (C36) | False/axioms | False/axioms | OK |
| N3 C96 proof, final tactic broken | False/compile | False/compile | OK |
| N4 C96 proof, statement weakened 1+ -> 2+ | False/lock | False/lock | OK |
| N5 C96 proof, helper def inserted | False/lock | False/lock | OK |
| N6 C96 proof, axiom smuggled in | False/static | False/static | OK |
| N7 C96 proof, change hidden inside let (min' -> max') | False/lock | False/lock | OK |
| P3 C96 proof (Claude Code's) | True/passed | True/passed | OK |
| N8 N4 again, text lock disabled -> type lock | False/type_lock | False/type_lock | OK |

**11/11 as expected.**

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
 "type_lock": {
  "original_found": true,
  "candidate_found": true
 },
 "seconds": 5.7
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
 "type_lock": {
  "original_found": true,
  "candidate_found": true
 },
 "seconds": 5.4
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
 "needs_human_review": false,
 "type_lock": {
  "original_found": true,
  "candidate_found": true
 }
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
  "~/rh-lean/formal-conjectures/.verifier_scratch/tmpadfvsyte.lean:244:2: error: Type mismatch"
 ],
 "axioms": null,
 "needs_human_review": false
}
```

### N4 C96 proof, statement weakened 1+ -> 2+
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "conjecture96",
 "stage": "lock",
 "errors": [
  "statement differs from original",
  "original:  theorem conjecture96 (G : SimpleGraph \u03b1) (h : G.Connected) : let minDistEven := (Finset.univ.image (distEven G)).min' (by simp) let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp) (G.indepNum : \u211d) \u2264 1 + (minDistEven : \u211d) * ((maxL : \u211d) - 1)",
  "candidate: theorem conjecture96 (G : SimpleGraph \u03b1) (h : G.Connected) : let minDistEven := (Finset.univ.image (distEven G)).min' (by simp) let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp) (G.indepNum : \u211d) \u2264 2 + (minDistEven : \u211d) * ((maxL : \u211d) - 1) := by classical intro minDistEven maxL "
 ],
 "axioms": null,
 "needs_human_review": false
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

### N7 C96 proof, change hidden inside let (min' -> max')
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "conjecture96",
 "stage": "lock",
 "errors": [
  "statement differs from original",
  "original:  theorem conjecture96 (G : SimpleGraph \u03b1) (h : G.Connected) : let minDistEven := (Finset.univ.image (distEven G)).min' (by simp) let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp) (G.indepNum : \u211d) \u2264 1 + (minDistEven : \u211d) * ((maxL : \u211d) - 1)",
  "candidate: theorem conjecture96 (G : SimpleGraph \u03b1) (h : G.Connected) : let minDistEven := (Finset.univ.image (distEven G)).max' (by simp) let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp) (G.indepNum : \u211d) \u2264 1 + (minDistEven : \u211d) * ((maxL : \u211d) - 1) := by classical intro minDistEven maxL "
 ],
 "axioms": null,
 "needs_human_review": false
}
```

### P3 C96 proof (Claude Code's)
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
 "type_lock": {
  "original_found": true,
  "candidate_found": true
 },
 "seconds": 5.7
}
```

### N8 N4 again, text lock disabled -> type lock
```json
{
 "ok": false,
 "mode": "prove",
 "theorem": "conjecture96",
 "stage": "type_lock",
 "errors": [
  "elaborated statement type differs or could not be read",
  "original:  @WrittenOnTheWallII.GraphConjecture96.conjecture96.{u_1} : \u2200 {\u03b1 : Type u_1} [inst : Fintype.{u_1} \u03b1] [DecidableEq.{u_1 + 1} \u03b1] [inst_2 : Nontrivial.{u_1} \u03b1] (G : SimpleGraph.{u_1} \u03b1) (h : @SimpleGraph.Connected.{u_1} \u03b1 G), have minDistEven : Nat := @Finset.min'.{0} Nat Nat.instLinearOrder (@Finset.image.{u_1, 0} \u03b1 Nat instDecidableEqNat (@SimpleGraph.distEven.{u_1} \u03b1 inst G) (@Finset.univ.{u_1} \u03b1 inst)) (@WrittenOnTheWallII.GraphConjecture96.conjecture96._proof_1.{u_1} \u03b1 inst inst_2 G); have maxL : Nat := @Finset.max'.{0} Nat Nat.instLinearOrder (@Finset.image.{u_1, 0} \u03b1 Nat instDecidableEqNat",
  "candidate: @WrittenOnTheWallII.GraphConjecture96.conjecture96.{u_1} : \u2200 {\u03b1 : Type u_1} [inst : Fintype.{u_1} \u03b1] [DecidableEq.{u_1 + 1} \u03b1] [inst_2 : Nontrivial.{u_1} \u03b1] (G : SimpleGraph.{u_1} \u03b1) (h : @SimpleGraph.Connected.{u_1} \u03b1 G), have minDistEven : Nat := @Finset.min'.{0} Nat Nat.instLinearOrder (@Finset.image.{u_1, 0} \u03b1 Nat instDecidableEqNat (@SimpleGraph.distEven.{u_1} \u03b1 inst G) (@Finset.univ.{u_1} \u03b1 inst)) (@WrittenOnTheWallII.GraphConjecture96.conjecture96._proof_1.{u_1} \u03b1 inst inst_2 G); have maxL : Nat := @Finset.max'.{0} Nat Nat.instLinearOrder (@Finset.image.{u_1, 0} \u03b1 Nat instDecidableEqNat"
 ],
 "axioms": null,
 "needs_human_review": false,
 "type_lock": {
  "original_found": true,
  "candidate_found": true
 }
}
```
