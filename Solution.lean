import P3Removal

/-!
# Proved solution

Comparator checks that each declaration below has exactly the same
statement as its counterpart in `Challenge.lean` and uses only the
permitted axioms.
-/

namespace P3Removal

theorem p3_removal_negative
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      negativeSquareEnergy G > negativeSquareEnergy (deleteVertex G u) + 1 :=
  zhang_theorem_1_10_negative U

theorem p3_removal_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      positiveSquareEnergy G > positiveSquareEnergy (deleteVertex G u) + 1 :=
  zhang_theorem_1_10_positive U

theorem p3_removal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : InducedP3 G) :
    (∃ u ∈ U.verts,
        negativeSquareEnergy G > negativeSquareEnergy (deleteVertex G u) + 1) ∧
      (∃ u ∈ U.verts,
        positiveSquareEnergy G > positiveSquareEnergy (deleteVertex G u) + 1) :=
  zhang_theorem_1_10 U

end P3Removal
