import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Advertised statement

Zhang, *Extremal values for the square energies of graphs*,
arXiv:2409.15504v2, Theorem 1.10.

Quote from the paper:

> Let G be any graph. Suppose U is a set of three vertices in G such that
> G[U] is isomorphic to the three-vertex path P₃. Then there exists a
> vertex u ∈ U such that s⁻(G) > s⁻(G\{u}) + 1. The same holds if we
> replace s⁻ with s⁺.

`positiveSquareEnergy` and `negativeSquareEnergy` are Zhang's `s⁺` and `s⁻`.
`deleteVertex G u` is the induced subgraph `G \ {u}`. An `InducedP3` is a
set of three vertices whose induced subgraph is exactly `P₃`.

This file is the Palomar statement surface. It imports Mathlib only.
-/

open scoped BigOperators

universe u

namespace P3Removal

section SquareEnergyDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency eigenvalues of a finite simple graph, indexed with algebraic
multiplicity by the vertex type. -/
noncomputable def adjacencyEigenvalues
    (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues

/-- The sum of squares of the strictly positive adjacency eigenvalues. This is
Zhang's `s⁺(G)`. -/
noncomputable def positiveSquareEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ i with 0 < adjacencyEigenvalues G i, (adjacencyEigenvalues G i) ^ 2

/-- The sum of squares of the strictly negative adjacency eigenvalues. This is
Zhang's `s⁻(G)`. -/
noncomputable def negativeSquareEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ i with adjacencyEigenvalues G i < 0, (adjacencyEigenvalues G i) ^ 2

/-- The graph obtained by deleting `v`. Vertices remember that they differ
from `v`. -/
def deleteVertex (G : SimpleGraph V) (v : V) :
    SimpleGraph {x : V // x ≠ v} :=
  G.induce {x | x ≠ v}

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (deleteVertex G v).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x.1 y.1))

/-- Three distinct vertices that induce a copy of the path `P₃`. The edges are
`a—b` and `b—c`, and `a` is not adjacent to `c`. -/
structure InducedP3 (G : SimpleGraph V) where
  /-- An endpoint of the induced path. -/
  a : V
  /-- The middle vertex of the induced path. -/
  b : V
  /-- The other endpoint of the induced path. -/
  c : V
  a_ne_b : a ≠ b
  b_ne_c : b ≠ c
  a_ne_c : a ≠ c
  adj_ab : G.Adj a b
  adj_bc : G.Adj b c
  not_adj_ac : ¬ G.Adj a c

/-- The three vertices of an induced `P₃`, as a finite set. -/
def InducedP3.verts {G : SimpleGraph V} (U : InducedP3 G) : Finset V :=
  {U.a, U.b, U.c}

end SquareEnergyDefs

/-- Zhang arXiv:2409.15504 Theorem 1.10, negative square energy. -/
theorem p3_removal_negative
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      negativeSquareEnergy G > negativeSquareEnergy (deleteVertex G u) + 1 := by
  sorry

/-- Zhang arXiv:2409.15504 Theorem 1.10, positive square energy. -/
theorem p3_removal_positive
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      positiveSquareEnergy G > positiveSquareEnergy (deleteVertex G u) + 1 := by
  sorry

/-- Zhang arXiv:2409.15504 Theorem 1.10, both signs. -/
theorem p3_removal
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    (∃ u ∈ U.verts,
        negativeSquareEnergy G > negativeSquareEnergy (deleteVertex G u) + 1) ∧
      (∃ u ∈ U.verts,
        positiveSquareEnergy G > positiveSquareEnergy (deleteVertex G u) + 1) := by
  sorry

end P3Removal
