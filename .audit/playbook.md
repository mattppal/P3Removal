# P3-removal playbook

Designed under figure-it-out. Rigor is high on novelty and statement fidelity.
Architect is skipped. The Palomar shape and Zhang's proof are already concrete.

## Done when

All of the following hold on the real artifacts, not a self-report.

1. `NOVELTY.md` records that Zhang arXiv:2409.15504 Theorem 1.10 is absent from
   `ShengtongZhang-alt/Sq` and `ShengtongZhang-alt/SqOmega`, with file-level
   evidence.
2. `Challenge.lean` states Theorem 1.10 for both signs, quoting the paper.
3. `lake build` succeeds.
4. Proof modules contain no `sorry` or `admit`. `Challenge.lean` may keep the
   Palomar statement `sorry`.
5. `formalization.yaml` and `comparator.json` are present and free of
   `TEMPLATE` sentinels.

Failure writes `Failure.md` instead.

## Out of scope

- Theorem 1.6 (superadditivity). A sister package owns that statement.
- Corollaries 1.11 and 1.12.
- The 1+1/16 quantitative refinement.

## Units

Each unit ends in a check. Do not start the next unit until the current one
is VERIFIED.

1. Palomar scaffold and this playbook. Check: required files exist.
2. Lean toolchain and mathlib cache. Check: `lean --version`, `lake exe cache get`.
3. Definitions and Challenge statement. Check: `lake build Challenge`.
4. Spectral parts and Lemma 3.1. Check: `lake build P3Removal.Spectral`.
5. Row-column mass and deletion. Check: `lake build P3Removal.RowCol`.
6. Numerical coincidence polynomial. Check: `lake build P3Removal.Numerics`.
7. Lemma 4.1. Check: `lake build P3Removal.Lemma41`.
8. Theorem 1.10 and Solution. Check: `lake build`.
9. Metadata and novelty note. Check: validator, sorry scan, `NOVELTY.md`.

## Verification harness

`scripts/verify.sh` rebuilds the library, rejects `sorry` in the proof
development, and rejects leftover `TEMPLATE` metadata.

## Verification record

| Unit | Check | Result |
|---|---|---|
| 1 scaffold | required Palomar files | VERIFIED |
| 2 toolchain | `lean --version` = 4.32.0 | VERIFIED |
| 3 definitions | `lake build Challenge` | VERIFIED |
| 4 Lemma 3.1 | `lake build P3Removal.Spectral` | VERIFIED |
| 5 row-col | `lake build P3Removal.RowCol` | VERIFIED |
| 6 numerics | `lake build P3Removal.Numerics` | VERIFIED |
| 7 Lemma 4.1 | `lake build P3Removal.Lemma41` | VERIFIED |
| 8 Theorem 1.10 | `lake build` | VERIFIED |
| 9 metadata | `verify.sh --skip-build`, `NOVELTY.md` | VERIFIED |

## Lessons

- Elan rustls failed TLS to GitHub; curl plus a manual toolchain extract worked.
- `omit` must precede `@[simp]`. `NLinArith` is not a Mathlib import; use `Linarith`.
- Lemma 4.1's A+M case is the A−M case after conjugating the middle vertex.
