/-
Copyright (c) 2026 Matt Palmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Palmer
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Square energy and vertex deletion

Positive and negative square energies follow Zhang, arXiv:2409.15504, §1.
Eigenvalues are indexed by the vertex type, so algebraic multiplicity is
recorded. Zero eigenvalues contribute to neither energy.

`deleteVertex` is the induced subgraph on `V \ {v}`, matching the paper's
`G \ {u}`.
-/

open scoped BigOperators

namespace P3Removal

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

omit [Fintype V] [DecidableEq V] in
@[simp]
lemma deleteVertex_adj (G : SimpleGraph V) (v : V)
    (x y : {x : V // x ≠ v}) :
    (deleteVertex G v).Adj x y ↔ G.Adj x.1 y.1 :=
  Iff.rfl

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

omit [Fintype V] in
lemma InducedP3.mem_verts {G : SimpleGraph V} (U : InducedP3 G) {u : V} :
    u ∈ U.verts ↔ u = U.a ∨ u = U.b ∨ u = U.c := by
  simp [InducedP3.verts]

end P3Removal
