# Novelty check: Zhang Theorem 1.10 is not in Sq or SqOmega

Checked before the formalization, against the published Lean sources
`ShengtongZhang-alt/Sq` and `ShengtongZhang-alt/SqOmega`.

## Target

Zhang, *Extremal values for the square energies of graphs*,
arXiv:2409.15504v2, Theorem 1.10:

> Let G be any graph. Suppose U is a set of three vertices in G such that
> G[U] is isomorphic to the three-vertex path P₃. Then there exists a
> vertex u ∈ U such that s⁻(G) > s⁻(G\{u}) + 1. The same holds if we
> replace s⁻ with s⁺.

## What those repositories prove

| Repository | Main theorem | File |
|---|---|---|
| `ShengtongZhang-alt/Sq` | `min(s⁺(G), s⁻(G)) ≥ n−1` for connected finite simple graphs | `Sq/Main.lean`, `card_sub_one_le_min_squareEnergy` |
| `ShengtongZhang-alt/SqOmega` | `√s±(G) ≤ (1 − 1/ω(G)) n` | `SqOmega/Main.lean`, `sqrt_squareEnergies_le_cliqueNum` |

`Sq` has a `deleteVertex` helper used in the connected-graph induction
(`Sq/Sparse/Cut.lean`). That is vertex deletion for the `n−1` bound. It is
not the P₃-removal statement.

## Search evidence

Local clones at `/tmp/novelty/Sq` and `/tmp/novelty/SqOmega`, searched for
`1.10`, `P3-removal`, `p3_removal`, `InducedP3`, and `Theorem 1.10`. No
matches for the target theorem. The only `P3` / `s⁻` hits in `SqOmega` are
the clique-bound docstring.

GitHub code search for `InducedP3` and `p3_removal` in Lean returned no
hits in those repositories. Re-checked the live READMEs: `Sq` advertises
`card_sub_one_le_min_squareEnergy`; `SqOmega` advertises
`sqrt_squareEnergies_le_cliqueNum`. Neither states Theorem 1.10.

## Out of scope here

Theorem 1.6 (superadditivity) is owned by a sister package and is not
duplicated.

## Conclusion

Novelty is not blocked. This package formalizes leftover Theorem 1.10.
