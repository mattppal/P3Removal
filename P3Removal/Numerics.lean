/-
Copyright (c) 2026 Matt Palmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Palmer
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The numerical coincidence in Zhang Lemma 4.1

Zhang reduces the `3 × 3` estimate to the strict polynomial inequality

`16 (1-t)⁴ > 6 (1-4t²)(1-2t²)`

on `t ∈ [0, 1/2]`. The paper checks this on a calculator. The identity

`16(1-t)⁴ - 6(1-4t²)(1-2t²) = (1-2t)²(10-24t-8t²) + 4t²`

turns the check into elementary sign estimates.
-/

namespace P3Removal

/-- Algebraic expansion of the Zhang polynomial in the coordinate `t = 1 - x`. -/
lemma zhangPoly_identity (t : ℝ) :
    16 * (1 - t) ^ 4 - 6 * (1 - 4 * t ^ 2) * (1 - 2 * t ^ 2) =
      (1 - 2 * t) ^ 2 * (10 - 24 * t - 8 * t ^ 2) + 4 * t ^ 2 := by
  ring

/-- On `[0, 1/2]` the quadratic `10 - 24t - 8t²` is at least `-4`. -/
lemma zhangQuad_ge_neg_four {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    -4 ≤ 10 - 24 * t - 8 * t ^ 2 := by
  nlinarith [sq_nonneg t, h0, h1]

/-- If `10 - 24t - 8t²` is negative and `t ≥ 0`, then `t > 1/3`. -/
lemma zhangQuad_neg_imp_gt_one_third {t : ℝ} (h0 : 0 ≤ t)
    (hneg : 10 - 24 * t - 8 * t ^ 2 < 0) : 1 / 3 < t := by
  by_contra hle
  have ht : t ≤ 1 / 3 := le_of_not_gt hle
  have hsq : t ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    have := sq_le_sq' (by nlinarith) ht
    simpa using this
  nlinarith [hsq, h0]

/-- Zhang's numerical coincidence: the polynomial is strictly positive on
the closed interval `[0, 1/2]`. -/
lemma zhangPoly_pos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    0 < 16 * (1 - t) ^ 4 - 6 * (1 - 4 * t ^ 2) * (1 - 2 * t ^ 2) := by
  have hident := zhangPoly_identity t
  rw [hident]
  have hsq : 0 ≤ (1 - 2 * t) ^ 2 := sq_nonneg _
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  by_cases hquad : 0 ≤ 10 - 24 * t - 8 * t ^ 2
  · have hmain : 0 ≤ (1 - 2 * t) ^ 2 * (10 - 24 * t - 8 * t ^ 2) :=
      mul_nonneg hsq hquad
    by_cases ht0 : t = 0
    · subst ht0
      norm_num
    · have htpos : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht0)
      nlinarith [pow_pos htpos 2]
  · have hneg : 10 - 24 * t - 8 * t ^ 2 < 0 := lt_of_not_ge hquad
    have ht13 : (1 / 3 : ℝ) < t := zhangQuad_neg_imp_gt_one_third h0 hneg
    have hbound := zhangQuad_ge_neg_four h0 h1
    have hlower :
        (1 - 2 * t) ^ 2 * (-4) + 4 * t ^ 2 ≤
          (1 - 2 * t) ^ 2 * (10 - 24 * t - 8 * t ^ 2) + 4 * t ^ 2 := by
      nlinarith [hsq, hbound]
    have hrewrite :
        (1 - 2 * t) ^ 2 * (-4) + 4 * t ^ 2 = 4 * (3 * t - 1) * (1 - t) := by
      ring
    have hpos : 0 < 4 * (3 * t - 1) * (1 - t) := by
      have h3 : 0 < 3 * t - 1 := by nlinarith [ht13]
      have hone : 0 < 1 - t := by nlinarith [h1]
      positivity
    nlinarith [hlower, hrewrite, hpos]

/-- The same inequality in the paper's original coordinate `x ∈ [1/2, 1]`. -/
lemma zhangPoly_pos_x {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 1) :
    6 * (1 - 4 * (1 - x) ^ 2) * (1 - 2 * (1 - x) ^ 2) < 16 * x ^ 4 := by
  have ht0 : 0 ≤ 1 - x := by nlinarith
  have ht1 : 1 - x ≤ 1 / 2 := by nlinarith
  have := zhangPoly_pos ht0 ht1
  have hx : (1 - (1 - x)) = x := by ring
  simpa [hx] using this

end P3Removal
