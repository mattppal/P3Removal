# Novelty check: Zhang Theorem 1.10 is not already formalized

Checked **2026-09-07** (UTC), before submission, against published Lean
sources and the paper. Re-run on this date; earlier notes are superseded.

## Target

Zhang, *Extremal values for the square energies of graphs*,
arXiv:2409.15504v2, Theorem 1.10. Quote from the HTML source on 2026-09-07
(`https://arxiv.org/html/2409.15504v2`):

> Let G be any graph. Suppose U is a set of three vertices in G such that
> G[U] is isomorphic to the three-vertex path P₃. Then there exists a
> vertex u ∈ U such that s⁻(G) > s⁻(G\{u}) + 1. The same holds if we
> replace s⁻ with s⁺.

## What the Zhang Lean repositories prove

| Repository | Main theorem | File | Checked |
|---|---|---|---|
| `ShengtongZhang-alt/Sq` | `min(s⁺(G), s⁻(G)) ≥ n−1` for connected finite simple graphs | `Sq/Main.lean`, `card_sub_one_le_min_squareEnergy` | 2026-09-07 |
| `ShengtongZhang-alt/SqOmega` | `√s±(G) ≤ (1 − 1/ω(G)) n` | `SqOmega/Main.lean`, `sqrt_squareEnergies_le_cliqueNum` | 2026-09-07 |

`Sq` has a `deleteVertex` helper used in the connected-graph induction
(`Sq/Sparse/Cut.lean`). That is vertex deletion for the `n−1` bound. It is
not the P₃-removal statement.

Other public Lean repos under `ShengtongZhang-alt` on 2026-09-07 (`BN`,
`Nikodym`, `three-uniform-vc-lean`) are different theorems.

## GitHub code search (2026-09-07)

Queries via the GitHub code-search API, Lean or unrestricted:

| Query | Hits for Theorem 1.10 |
|---|---|
| `p3_removal language:Lean` | 0 |
| `InducedP3 language:Lean` | 0 |
| `"Theorem 1.10" Zhang square energy language:Lean` | 0 |
| `zhang_theorem_1_10 language:Lean` | 0 |
| `rowColMass language:Lean` | 0 |
| `p3_removal_negative` | 0 |
| `P3-removal palomar` | 0 |
| `2409.15504 language:Lean` | 0 |

`repo:ShengtongZhang-alt/Sq` and `repo:ShengtongZhang-alt/SqOmega` searches
for `p3_removal` returned 0 items (one Sq query reported
`incomplete_results: true` with an empty item list). Live READMEs of both
repos still advertise the `n−1` bound and the clique bound only.

This package is not yet on public GitHub, so those zeros do not include
the present source.

## arXiv (2026-09-07)

- `2409.15504v2` states Theorem 1.10 as quoted above. It is a mathematics
  paper, not a Lean development.
- Later papers *cite* the P₃-removal lemma (e.g. arXiv:2608.17329v1,
  Lemma 2.3). Citation is not a formalization.
- No arXiv abstract claims a Lean proof of Theorem 1.10.

## X / Twitter (2026-09-07)

- The X MCP namespace required authentication and exposed no tools.
- The X-API MCP namespace was listed as ready but exposed no tools.
- A web search of `site:x.com` for a Lean P3-removal formalization
  returned no results.

Treat the X check as **inconclusive for MCP**, **empty for public web
search**. It does not block novelty: no Lean source was found.

## Out of scope here

Theorem 1.6 (superadditivity) is owned by a sister package and is not
duplicated.

## Conclusion

Novelty is not blocked. This package formalizes leftover Theorem 1.10.
