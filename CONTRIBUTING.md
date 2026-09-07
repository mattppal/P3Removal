# Contributing

This is a Palomar submission for Zhang Theorem 1.10, not a general
library. Keep `Challenge.lean` as the statement-only surface. Put proofs
in `P3Removal/` and wire them through `Solution.lean`.

Do not add Theorem 1.6 (superadditivity). That statement belongs to a
sister package.

Replace metadata only with independently checkable facts. Run
`./scripts/verify.sh` before proposing a change.
