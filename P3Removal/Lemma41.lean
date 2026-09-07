/-
Copyright (c) 2026 Matt Palmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Palmer
-/

import P3Removal.Numerics
import P3Removal.RowCol
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.FinCases

/-!
# Zhang Lemma 4.1

If `A` is the adjacency matrix of `P₃` and `M` is any real `3 × 3`
positive-semidefinite matrix, then some row-column mass of `A - M` (and of
`A + M`) strictly exceeds `1`.
-/

open scoped BigOperators

namespace P3Removal

open Matrix

/-- Adjacency matrix of the path on three vertices, in the paper's labeling. -/
def p3Adj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then
      (1 : ℝ)
    else
      0

lemma erase0 : Finset.univ.erase (0 : Fin 3) = {1, 2} := by decide
lemma erase1 : Finset.univ.erase (1 : Fin 3) = {0, 2} := by decide
lemma erase2 : Finset.univ.erase (2 : Fin 3) = {0, 1} := by decide

lemma posSemidef_quadratic' {n : Type*} [Fintype n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) (x : n → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * M i j * x j := by
  have h := hM.dotProduct_mulVec_nonneg x
  have hx : star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
    simp only [dotProduct, mulVec]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hstar : star x i = x i := by
      rw [Pi.star_apply]
      simp
    rw [hstar]
    ring
  rw [hx] at h
  exact h

lemma disc_offdiag {α β γ : ℝ}
    (h : ∀ t : ℝ, 0 ≤ α * (t * t) + (2 * β) * t + γ) :
    β ^ 2 ≤ α * γ := by
  have hdisc := discrim_le_zero h
  have : (2 * β) ^ 2 - 4 * α * γ ≤ 0 := by
    simpa [discrim] using hdisc
  nlinarith

lemma posSemidef_quad01 (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosSemidef) (t : ℝ) :
    0 ≤ M 0 0 * (t * t) + (2 * M 0 1) * t + M 1 1 := by
  have hsym : M 1 0 = M 0 1 := isHermitian_apply_comm hM.isHermitian 0 1
  have hx := posSemidef_quadratic' hM ![t, 1, 0]
  simp [Fin.sum_univ_three, hsym] at hx
  nlinarith [hx]

lemma posSemidef_quad12 (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosSemidef) (t : ℝ) :
    0 ≤ M 1 1 * (t * t) + (2 * M 1 2) * t + M 2 2 := by
  have hsym : M 2 1 = M 1 2 := isHermitian_apply_comm hM.isHermitian 1 2
  have hx := posSemidef_quadratic' hM ![0, t, 1]
  simp [Fin.sum_univ_three, hsym] at hx
  nlinarith [hx]

lemma posSemidef_offdiag_01 (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosSemidef) :
    M 0 1 ^ 2 ≤ M 0 0 * M 1 1 :=
  disc_offdiag (posSemidef_quad01 M hM)

lemma posSemidef_offdiag_12 (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosSemidef) :
    M 1 2 ^ 2 ≤ M 1 1 * M 2 2 :=
  disc_offdiag (posSemidef_quad12 M hM)

lemma cauchy_afd (a f d : ℝ) :
    (a + f + 2 * d) ^ 2 ≤ 3 * (a ^ 2 + f ^ 2 + 4 * d ^ 2) := by
  nlinarith [sq_nonneg (a - f), sq_nonneg (a - 2 * d), sq_nonneg (f - 2 * d)]

lemma amgm_be (b e : ℝ) :
    2 * (1 - (b + e) / 2) ^ 2 ≤ (1 - b) ^ 2 + (1 - e) ^ 2 := by
  nlinarith [sq_nonneg (b - e)]

lemma le_one_of_sq {x : ℝ} (h : x ^ 2 ≤ 1) : x ≤ 1 :=
  (abs_le.mp ((sq_le_one_iff_abs_le_one x).mp h)).2

lemma half_le_of_sq_le_quarter {y : ℝ} (h : y ^ 2 ≤ 1 / 4) : |y| ≤ 1 / 2 := by
  have hsq : |y| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simp [sq_abs]
    nlinarith [h]
  exact (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 hsq

lemma rowColMass_p3_sub_zero (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ i j : Fin 3, M j i = M i j) :
    rowColMass (p3Adj - M) 0 =
      M 0 0 ^ 2 + 2 * (1 - M 0 1) ^ 2 + 2 * (M 0 2) ^ 2 := by
  unfold rowColMass
  simp [p3Adj, erase0, hsym 0 1, hsym 0 2]
  ring

lemma rowColMass_p3_sub_one (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ i j : Fin 3, M j i = M i j) :
    rowColMass (p3Adj - M) 1 =
      M 1 1 ^ 2 + 2 * (1 - M 0 1) ^ 2 + 2 * (1 - M 1 2) ^ 2 := by
  unfold rowColMass
  simp [p3Adj, erase1, hsym 0 1, hsym 1 2]
  ring

lemma rowColMass_p3_sub_two (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ i j : Fin 3, M j i = M i j) :
    rowColMass (p3Adj - M) 2 =
      M 2 2 ^ 2 + 2 * (1 - M 1 2) ^ 2 + 2 * (M 0 2) ^ 2 := by
  unfold rowColMass
  simp [p3Adj, erase2, hsym 0 2, hsym 1 2]
  ring

lemma quad_form_v (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ i j : Fin 3, M j i = M i j) (t : ℝ) :
    ∑ i, ∑ j, (![1, -t, 1] i) * M i j * (![1, -t, 1] j) =
      M 1 1 * (t * t) + (-2 * (M 0 1 + M 1 2)) * t +
        (M 0 0 + M 2 2 + 2 * M 0 2) := by
  simp [Fin.sum_univ_three, hsym 0 1, hsym 0 2, hsym 1 2]
  ring

def signFlip (i : Fin 3) : ℝ := if i = 1 then -1 else 1

def dConj (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => signFlip i * M i j * signFlip j

lemma dConj_eq_congr (M : Matrix (Fin 3) (Fin 3) ℝ) :
    dConj M = diagonal signFlip * M * diagonal signFlip := by
  ext i j
  simp [dConj, mul_apply, diagonal]

lemma dConj_posSemidef {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosSemidef) :
    (dConj M).PosSemidef := by
  rw [dConj_eq_congr]
  have hD : (diagonal signFlip : Matrix (Fin 3) (Fin 3) ℝ)ᴴ = diagonal signFlip :=
    (isHermitian_diagonal signFlip).eq
  have : diagonal signFlip * M * diagonal signFlip =
      (diagonal signFlip)ᴴ * M * diagonal signFlip := by
    rw [hD]
  rw [this]
  exact hM.conjTranspose_mul_mul_same _

lemma p3_add_entry_sq (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    ((p3Adj + M) i j) ^ 2 = ((p3Adj - dConj M) i j) ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [p3Adj, dConj, signFlip, Matrix.add_apply, Matrix.sub_apply]

lemma rowColMass_p3_add_eq_sub_dConj (M : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3) :
    rowColMass (p3Adj + M) k = rowColMass (p3Adj - dConj M) k := by
  unfold rowColMass
  simp only [p3_add_entry_sq]

lemma c_sq_bound {b e c x : ℝ}
    (hx : x = (b + e) / 2)
    (h1 : c ^ 2 + 2 * (1 - b) ^ 2 + 2 * (1 - e) ^ 2 ≤ 1) :
    c ^ 2 ≤ 1 - 4 * (1 - x) ^ 2 := by
  have hamgm := amgm_be b e
  have : 4 * (1 - x) ^ 2 ≤ 2 * (1 - b) ^ 2 + 2 * (1 - e) ^ 2 := by
    rw [hx]
    nlinarith [hamgm]
  nlinarith

lemma afd_bound {a f d b e x : ℝ}
    (hx : x = (b + e) / 2)
    (h0 : a ^ 2 + 2 * (1 - b) ^ 2 + 2 * d ^ 2 ≤ 1)
    (h2 : f ^ 2 + 2 * (1 - e) ^ 2 + 2 * d ^ 2 ≤ 1) :
    a ^ 2 + f ^ 2 + 4 * d ^ 2 ≤ 2 * (1 - 2 * (1 - x) ^ 2) := by
  have hamgm := amgm_be b e
  rw [hx]
  nlinarith [hamgm, h0, h2]

lemma cs_bound {a f d b e x : ℝ}
    (hx : x = (b + e) / 2)
    (h0 : a ^ 2 + 2 * (1 - b) ^ 2 + 2 * d ^ 2 ≤ 1)
    (h2 : f ^ 2 + 2 * (1 - e) ^ 2 + 2 * d ^ 2 ≤ 1) :
    (a + f + 2 * d) ^ 2 ≤ 6 * (1 - 2 * (1 - x) ^ 2) := by
  have := cauchy_afd a f d
  have := afd_bound hx h0 h2
  nlinarith

lemma x_ge_half {x : ℝ} (h : 0 ≤ 1 - 4 * (1 - x) ^ 2) : (1 / 2 : ℝ) ≤ x := by
  have hsq : (1 - x) ^ 2 ≤ 1 / 4 := by nlinarith
  have habs := half_le_of_sq_le_quarter hsq
  nlinarith [(abs_le.mp habs).right]

lemma chain_poly {c a f d x : ℝ}
    (hc2 : c ^ 2 ≤ 1 - 4 * (1 - x) ^ 2)
    (hcs : (a + f + 2 * d) ^ 2 ≤ 6 * (1 - 2 * (1 - x) ^ 2))
    (hprod : 4 * x ^ 2 ≤ c * (a + f + 2 * d)) :
    16 * x ^ 4 ≤ 6 * (1 - 4 * (1 - x) ^ 2) * (1 - 2 * (1 - x) ^ 2) := by
  have hprod_sq : (4 * x ^ 2) ^ 2 ≤ (c * (a + f + 2 * d)) ^ 2 :=
    sq_le_sq' (by nlinarith [hprod]) hprod
  have hleft : 16 * x ^ 4 ≤ c ^ 2 * (a + f + 2 * d) ^ 2 := by
    nlinarith [hprod_sq]
  nlinarith [hc2, hcs, hleft]

/-- The `A - M` half of Zhang Lemma 4.1. -/
lemma exists_rowColMass_p3_sub_gt_one {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M.PosSemidef) :
    ∃ i, 1 < rowColMass (p3Adj - M) i := by
  by_contra! hle
  have hsym (i j : Fin 3) : M j i = M i j :=
    isHermitian_apply_comm hM.isHermitian i j
  have h0 := (rowColMass_p3_sub_zero M hsym).symm ▸ hle 0
  have h1 := (rowColMass_p3_sub_one M hsym).symm ▸ hle 1
  have h2 := (rowColMass_p3_sub_two M hsym).symm ▸ hle 2
  set a := M 0 0
  set b := M 0 1
  set d := M 0 2
  set c := M 1 1
  set e := M 1 2
  set f := M 2 2
  set x := (b + e) / 2
  have hx : x = (b + e) / 2 := rfl
  have ha0 : 0 ≤ a := hM.diag_nonneg (i := 0)
  have hc0 : 0 ≤ c := hM.diag_nonneg (i := 1)
  have hf0 : 0 ≤ f := hM.diag_nonneg (i := 2)
  have hc2 := c_sq_bound hx h1
  have hx_bound : 0 ≤ 1 - 4 * (1 - x) ^ 2 := le_trans (sq_nonneg c) hc2
  have hx_ge := x_ge_half hx_bound
  have ha1 : a ≤ 1 := le_one_of_sq (by nlinarith [h0, sq_nonneg (1 - b), sq_nonneg d])
  have hc1 : c ≤ 1 := le_one_of_sq (by nlinarith [h1, sq_nonneg (1 - b), sq_nonneg (1 - e)])
  have hf1 : f ≤ 1 := le_one_of_sq (by nlinarith [h2, sq_nonneg (1 - e), sq_nonneg d])
  have hb2 : b ^ 2 ≤ a * c := posSemidef_offdiag_01 M hM
  have he2 : e ^ 2 ≤ c * f := posSemidef_offdiag_12 M hM
  have hac : a * c ≤ 1 := mul_le_one₀ ha1 hc0 hc1
  have hcf : c * f ≤ 1 := mul_le_one₀ hc1 hf0 hf1
  have hb_le : b ≤ 1 := le_one_of_sq (le_trans hb2 hac)
  have he_le : e ≤ 1 := le_one_of_sq (le_trans he2 hcf)
  have hx_le : x ≤ 1 := by nlinarith [hb_le, he_le]
  have hcs := cs_bound hx h0 h2
  have hquad (t : ℝ) :
      0 ≤ c * (t * t) + (-2 * (b + e)) * t + (a + f + 2 * d) := by
    have this := posSemidef_quadratic' hM ![1, -t, 1]
    rw [quad_form_v M hsym t] at this
    simpa [a, b, d, c, e, f, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
      using this
  have hdisc := discrim_le_zero hquad
  have hprod : 4 * x ^ 2 ≤ c * (a + f + 2 * d) := by
    have : (-2 * (b + e)) ^ 2 - 4 * c * (a + f + 2 * d) ≤ 0 := by
      simpa [discrim] using hdisc
    nlinarith
  have hchain := chain_poly hc2 hcs hprod
  have hstrict := zhangPoly_pos_x hx_ge hx_le
  exact (not_le_of_gt hstrict) hchain

/-- Zhang Lemma 4.1. -/
lemma lemma_4_1 {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosSemidef) :
    (∃ i, 1 < rowColMass (p3Adj - M) i) ∧
      (∃ j, 1 < rowColMass (p3Adj + M) j) := by
  refine ⟨exists_rowColMass_p3_sub_gt_one hM, ?_⟩
  obtain ⟨i, hi⟩ := exists_rowColMass_p3_sub_gt_one (dConj_posSemidef hM)
  refine ⟨i, ?_⟩
  rwa [rowColMass_p3_add_eq_sub_dConj]

end P3Removal
