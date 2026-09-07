/-
Copyright (c) 2026 Matt Palmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Palmer
-/

import P3Removal.Definition
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Spectral parts and Zhang Lemma 3.1

The adjacency matrix splits as `A = A₊ - A₋` with both parts positive
semidefinite and orthogonal. Lemma 3.1 of the paper then writes each square
energy as a semidefinite least-squares program. This file proves that lemma
and does not prove Theorem 1.6.
-/

open scoped BigOperators MatrixOrder

namespace P3Removal

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive spectral part of the adjacency matrix. -/
noncomputable def adjacencyPosPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℝ :=
  (G.isHermitian_adjMatrix ℝ).cfc (fun x ↦ max x 0)

/-- The absolute value of the negative spectral part of the adjacency matrix. -/
noncomputable def adjacencyNegPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℝ :=
  (G.isHermitian_adjMatrix ℝ).cfc (fun x ↦ max (-x) 0)

lemma positiveSquareEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ positiveSquareEnergy G := by
  classical
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma negativeSquareEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ negativeSquareEnergy G := by
  classical
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [DecidableEq V] in
lemma sum_sq_posPart_eq_filter (f : V → ℝ) :
    (∑ i, (max (f i) 0) ^ 2) = ∑ i with 0 < f i, (f i) ^ 2 := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < f i
  · simp [hi, hi.le]
  · have hi' : f i ≤ 0 := le_of_not_gt hi
    simp [hi, hi']

omit [DecidableEq V] in
lemma sum_sq_negPart_eq_filter (f : V → ℝ) :
    (∑ i, (max (-f i) 0) ^ 2) = ∑ i with f i < 0, (f i) ^ 2 := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f i < 0
  · have hneg : 0 < -f i := neg_pos.mpr hi
    rw [if_pos hi, max_eq_left hneg.le]
    ring
  · have hi' : 0 ≤ f i := le_of_not_gt hi
    simp [hi, hi']

lemma adjacencyPosPart_eq_posPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyPosPart G = (G.adjMatrix ℝ)⁺ := by
  rw [adjacencyPosPart, CFC.posPart_def, cfcₙ_eq_cfc,
    (G.isHermitian_adjMatrix ℝ).cfc_eq]
  congr 1

lemma adjacencyNegPart_eq_negPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyNegPart G = (G.adjMatrix ℝ)⁻ := by
  rw [adjacencyNegPart, CFC.negPart_def, cfcₙ_eq_cfc,
    (G.isHermitian_adjMatrix ℝ).cfc_eq]
  congr 1

lemma adjacencyPosPart_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyPosPart G).PosSemidef := by
  rw [adjacencyPosPart_eq_posPart]
  exact (CFC.posPart_nonneg (G.adjMatrix ℝ)).posSemidef

lemma adjacencyNegPart_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyNegPart G).PosSemidef := by
  rw [adjacencyNegPart_eq_negPart]
  exact (CFC.negPart_nonneg (G.adjMatrix ℝ)).posSemidef

lemma adjacency_eq_posPart_sub_negPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.adjMatrix ℝ = adjacencyPosPart G - adjacencyNegPart G := by
  rw [adjacencyPosPart_eq_posPart, adjacencyNegPart_eq_negPart]
  exact (CFC.posPart_sub_negPart (G.adjMatrix ℝ)
    (G.isHermitian_adjMatrix ℝ).isSelfAdjoint).symm

lemma adjacencyPosPart_mul_negPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyPosPart G * adjacencyNegPart G = 0 := by
  rw [adjacencyPosPart_eq_posPart, adjacencyNegPart_eq_negPart]
  exact CFC.posPart_mul_negPart (G.adjMatrix ℝ)

lemma adjacencyNegPart_mul_posPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyNegPart G * adjacencyPosPart G = 0 := by
  rw [adjacencyPosPart_eq_posPart, adjacencyNegPart_eq_negPart]
  exact CFC.negPart_mul_posPart (G.adjMatrix ℝ)

lemma trace_hermitianCfc {A : Matrix V V ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (hA.cfc f) = ∑ i, f (hA.eigenvalues i) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp

lemma trace_sq_hermitianCfc {A : Matrix V V ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (hA.cfc f ^ 2) = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
  have hf : ContinuousOn f (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_restrict]
    fun_prop
  calc
    Matrix.trace (hA.cfc f ^ 2) =
        Matrix.trace (hA.cfc (fun x ↦ f x * f x)) := by
      rw [pow_two, ← hA.cfc_eq f, ← cfc_mul f f A hf hf, hA.cfc_eq]
    _ = ∑ i, f (hA.eigenvalues i) * f (hA.eigenvalues i) :=
      trace_hermitianCfc hA _
    _ = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
      simp only [pow_two]

lemma trace_sq_adjacencyPosPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (adjacencyPosPart G ^ 2) = positiveSquareEnergy G := by
  rw [adjacencyPosPart, trace_sq_hermitianCfc, sum_sq_posPart_eq_filter]
  rfl

lemma trace_sq_adjacencyNegPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (adjacencyNegPart G ^ 2) = negativeSquareEnergy G := by
  rw [adjacencyNegPart, trace_sq_hermitianCfc, sum_sq_negPart_eq_filter]
  rfl

/-- Squared Frobenius norm of a real matrix. -/
def frobeniusSq {n : Type*} [Fintype n] (M : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, M i j ^ 2

lemma frobeniusSq_nonneg {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    0 ≤ frobeniusSq M :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma frobeniusSq_neg {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    frobeniusSq (-M) = frobeniusSq M := by
  simp [frobeniusSq]

omit [Fintype V] [DecidableEq V] in
lemma isHermitian_apply_comm {A : Matrix V V ℝ} (hA : A.IsHermitian) (i j : V) :
    A j i = A i j := by
  have h := congr_fun (congr_fun hA.eq i) j
  simpa [Matrix.conjTranspose_apply] using h

omit [DecidableEq V] in
lemma sum_sum_two_mul (f : V → V → ℝ) :
    ∑ i, ∑ j, 2 * f i j = 2 * ∑ i, ∑ j, f i j := by
  simp [← Finset.mul_sum]

omit [DecidableEq V] in
lemma frobeniusSq_add (A B : Matrix V V ℝ) :
    frobeniusSq (A + B) =
      frobeniusSq A + frobeniusSq B + 2 * ∑ i, ∑ j, A i j * B i j := by
  unfold frobeniusSq
  simp only [Matrix.add_apply]
  have hterm (i j : V) :
      (A i j + B i j) ^ 2 = A i j ^ 2 + B i j ^ 2 + 2 * (A i j * B i j) := by
    ring
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, sum_sum_two_mul]

lemma frobeniusSq_eq_trace_sq_of_hermitian {A : Matrix V V ℝ}
    (hA : A.IsHermitian) :
    frobeniusSq A = Matrix.trace (A ^ 2) := by
  unfold frobeniusSq
  rw [pow_two, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [isHermitian_apply_comm hA i j, pow_two]

omit [DecidableEq V] in
lemma trace_mul_eq_sum_mul {A B : Matrix V V ℝ} :
    Matrix.trace (A * B) = ∑ i, ∑ j, A i j * B j i := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

omit [DecidableEq V] in
lemma inner_eq_trace_of_hermitian {A B : Matrix V V ℝ}
    (hB : B.IsHermitian) :
    ∑ i, ∑ j, A i j * B i j = Matrix.trace (A * B) := by
  rw [trace_mul_eq_sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [isHermitian_apply_comm hB j i]

/-- The Frobenius pairing of two real positive-semidefinite matrices is nonnegative. -/
lemma trace_mul_posSemidef_nonneg {A B : Matrix V V ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [← mul_assoc, Matrix.trace_mul_cycle, star_eq_conjTranspose]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

lemma adjacencyPosPart_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyPosPart G).IsHermitian :=
  (adjacencyPosPart_posSemidef G).isHermitian

lemma adjacencyNegPart_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyNegPart G).IsHermitian :=
  (adjacencyNegPart_posSemidef G).isHermitian

lemma frobeniusSq_adjacencyPosPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    frobeniusSq (adjacencyPosPart G) = positiveSquareEnergy G := by
  rw [frobeniusSq_eq_trace_sq_of_hermitian (adjacencyPosPart_isHermitian G),
    trace_sq_adjacencyPosPart]

lemma frobeniusSq_adjacencyNegPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    frobeniusSq (adjacencyNegPart G) = negativeSquareEnergy G := by
  rw [frobeniusSq_eq_trace_sq_of_hermitian (adjacencyNegPart_isHermitian G),
    trace_sq_adjacencyNegPart]

lemma trace_posPart_mul_negPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (adjacencyPosPart G * adjacencyNegPart G) = 0 := by
  rw [adjacencyPosPart_mul_negPart, Matrix.trace_zero]

/-- Zhang Lemma 3.1, lower bound for `s⁺`. -/
lemma le_frobeniusSq_add_of_posSemidef
    (G : SimpleGraph V) [DecidableRel G.Adj] {M : Matrix V V ℝ}
    (hM : M.PosSemidef) :
    positiveSquareEnergy G ≤ frobeniusSq (G.adjMatrix ℝ + M) := by
  have hAp := adjacencyPosPart_posSemidef G
  have hdecomp : G.adjMatrix ℝ + M =
      adjacencyPosPart G + (M - adjacencyNegPart G) := by
    rw [adjacency_eq_posPart_sub_negPart]
    abel
  rw [hdecomp, frobeniusSq_add, frobeniusSq_adjacencyPosPart]
  have hinner :
      0 ≤ ∑ i, ∑ j,
        (adjacencyPosPart G) i j * (M - adjacencyNegPart G) i j := by
    have htr :
        Matrix.trace (adjacencyPosPart G * (M - adjacencyNegPart G)) =
          Matrix.trace (adjacencyPosPart G * M) -
            Matrix.trace (adjacencyPosPart G * adjacencyNegPart G) := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    have hpos : 0 ≤ Matrix.trace (adjacencyPosPart G * M) :=
      trace_mul_posSemidef_nonneg hAp hM
    have hzero := trace_posPart_mul_negPart G
    have hB : (M - adjacencyNegPart G).IsHermitian :=
      hM.isHermitian.sub (adjacencyNegPart_isHermitian G)
    rw [inner_eq_trace_of_hermitian hB, htr, hzero, sub_zero]
    exact hpos
  nlinarith [frobeniusSq_nonneg (M - adjacencyNegPart G), hinner]

/-- Zhang Lemma 3.1, lower bound for `s⁻`. -/
lemma le_frobeniusSq_sub_of_posSemidef
    (G : SimpleGraph V) [DecidableRel G.Adj] {M : Matrix V V ℝ}
    (hM : M.PosSemidef) :
    negativeSquareEnergy G ≤ frobeniusSq (G.adjMatrix ℝ - M) := by
  have hAn := adjacencyNegPart_posSemidef G
  have hdecomp : G.adjMatrix ℝ - M =
      -(adjacencyNegPart G + (M - adjacencyPosPart G)) := by
    rw [adjacency_eq_posPart_sub_negPart]
    abel
  rw [hdecomp, frobeniusSq_neg, frobeniusSq_add, frobeniusSq_adjacencyNegPart]
  have hinner :
      0 ≤ ∑ i, ∑ j,
        (adjacencyNegPart G) i j * (M - adjacencyPosPart G) i j := by
    have htr :
        Matrix.trace (adjacencyNegPart G * (M - adjacencyPosPart G)) =
          Matrix.trace (adjacencyNegPart G * M) -
            Matrix.trace (adjacencyNegPart G * adjacencyPosPart G) := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    have hpos : 0 ≤ Matrix.trace (adjacencyNegPart G * M) :=
      trace_mul_posSemidef_nonneg hAn hM
    have hzero : Matrix.trace (adjacencyNegPart G * adjacencyPosPart G) = 0 := by
      rw [adjacencyNegPart_mul_posPart, Matrix.trace_zero]
    have hB : (M - adjacencyPosPart G).IsHermitian :=
      hM.isHermitian.sub (adjacencyPosPart_isHermitian G)
    rw [inner_eq_trace_of_hermitian hB, htr, hzero, sub_zero]
    exact hpos
  nlinarith [frobeniusSq_nonneg (M - adjacencyPosPart G), hinner]

/-- Zhang Lemma 3.1, equality case for `s⁻`. -/
lemma frobeniusSq_sub_posPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    frobeniusSq (G.adjMatrix ℝ - adjacencyPosPart G) = negativeSquareEnergy G := by
  have h : G.adjMatrix ℝ - adjacencyPosPart G = -adjacencyNegPart G := by
    rw [adjacency_eq_posPart_sub_negPart]
    abel
  rw [h, frobeniusSq_neg, frobeniusSq_adjacencyNegPart]

/-- Zhang Lemma 3.1, equality case for `s⁺`. -/
lemma frobeniusSq_add_negPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    frobeniusSq (G.adjMatrix ℝ + adjacencyNegPart G) = positiveSquareEnergy G := by
  have h : G.adjMatrix ℝ + adjacencyNegPart G = adjacencyPosPart G := by
    rw [adjacency_eq_posPart_sub_negPart]
    abel
  rw [h, frobeniusSq_adjacencyPosPart]

end P3Removal
