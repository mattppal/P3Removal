import P3Removal.Definition

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
-/

namespace P3Removal

/-- Zhang arXiv:2409.15504 Theorem 1.10, negative square energy. -/
theorem p3_removal_negative
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      negativeSquareEnergy G > negativeSquareEnergy (deleteVertex G u) + 1 := by
  sorry

/-- Zhang arXiv:2409.15504 Theorem 1.10, positive square energy. -/
theorem p3_removal_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      positiveSquareEnergy G > positiveSquareEnergy (deleteVertex G u) + 1 := by
  sorry

/-- Zhang arXiv:2409.15504 Theorem 1.10, both signs. -/
theorem p3_removal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    (∃ u ∈ U.verts,
        negativeSquareEnergy G > negativeSquareEnergy (deleteVertex G u) + 1) ∧
      (∃ u ∈ U.verts,
        positiveSquareEnergy G > positiveSquareEnergy (deleteVertex G u) + 1) := by
  sorry

end P3Removal
