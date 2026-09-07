# P3-removal

Lean 4 formalization of Zhang, *Extremal values for the square energies of
graphs*, [arXiv:2409.15504v2](https://arxiv.org/abs/2409.15504), Theorem 1.10.

> Let G be any graph. Suppose U is a set of three vertices in G such that
> G[U] is isomorphic to the three-vertex path P₃. Then there exists a
> vertex u ∈ U such that s⁻(G) > s⁻(G\{u}) + 1. The same holds if we
> replace s⁻ with s⁺.

`s⁺` and `s⁻` are the sums of squares of the strictly positive and strictly
negative adjacency eigenvalues.

This is a [Palomar](https://palomar-registry.org/) package. It does **not**
formalize Theorem 1.6 (superadditivity). Related formalizations of other
theorems from the same paper are
[`ShengtongZhang-alt/Sq`](https://github.com/ShengtongZhang-alt/Sq) and
[`ShengtongZhang-alt/SqOmega`](https://github.com/ShengtongZhang-alt/SqOmega);
see `NOVELTY.md`.

## Repository map

- `Challenge.lean` is the statement surface. Each advertised theorem ends in
  `sorry`.
- `Solution.lean` proves the same declarations.
- `P3Removal/` is the proof development: definitions, Lemma 3.1, the
  numerical coincidence, Lemma 4.1, and Theorem 1.10.
- `comparator.json` lists the declarations Comparator must match.
- `formalization.yaml` is the Palomar metadata.
- `NOVELTY.md` records the check against `Sq` and `SqOmega`.

## Build

Lean 4.32.0 and Mathlib are pinned in `lean-toolchain` and
`lake-manifest.json`.

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify.sh --skip-build
```

`scripts/verify.sh` rebuilds (unless `--skip-build`), rejects `sorry` in the
proof modules, and rejects leftover `TEMPLATE` metadata.

Comparator, if the verifier toolchain is installed:

```text
./scripts/verify-comparator.sh
```

Documentation:

```text
cd docbuild && lake build P3Removal:docs
```

## Proof sketch

Lemma 3.1 writes `s⁻(G)` as the squared Frobenius distance from the
adjacency matrix to the positive-semidefinite cone, and likewise for `s⁺`.
Deleting a vertex splits that squared norm into the principal submatrix plus
the row-column mass of the deleted index. Restricting to the induced `P₃`
and applying Lemma 4.1 produces a vertex in the path whose row-column mass
strictly exceeds 1, which is the claimed drop.

The paper checks a cubic inequality in Lemma 4.1 on a calculator. This
development expands the same polynomial and estimates signs.

## Submit

Read the current
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and open the
[submission form](https://submit.palomar-registry.org/)
with the full 40-character commit SHA.
