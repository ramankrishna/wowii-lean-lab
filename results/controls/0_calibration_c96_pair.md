# Verifier calibration

Date: 2026-11-23. `verifier.py` was not modified. Run from `~/rh-lean/verifier` with
`~/.elan/bin` on PATH (the verifier shells out to `lake`), project `~/rh-lean/formal-conjectures`,
original `FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean`, theorem `conjecture96`.

## Positive control: `~/rh-lean/proofs/GraphConjecture96.lean` (expect ok=true)

Command: `python3 verifier.py --project $P --original $F --candidate ~/rh-lean/proofs/GraphConjecture96.lean --theorem conjecture96`
Exit code 0. Result: **as expected**.

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
  "seconds": 10.9
}
```

## Negative control: original `GraphConjecture96.lean` (expect ok=false, stage=static)

Command: `python3 verifier.py --project $P --original $F --candidate $P/$F --theorem conjecture96`
Exit code 0. Result: **as expected**.

```json
{
  "ok": false,
  "mode": "prove",
  "theorem": "conjecture96",
  "stage": "static",
  "errors": [
    "banned: sorry"
  ],
  "axioms": null,
  "needs_human_review": false
}
```

## Notes

- Neither check misbehaved.
- The candidate proof file already ends with its own `#print axioms` line, and the verifier
  appends a second one. The duplicate is harmless: the parsed axioms match the expected set.
- The verifier leaves an empty `.verifier_scratch/` directory in the project; each temp file is deleted after its run.
- These controls differ from the README's suggested pair (a negative control on conjecture84, and
  a positive control on an existing repo proof). They use the C96 pair as requested. Running the
  conjecture84 control and the repo-proof control would add coverage.
