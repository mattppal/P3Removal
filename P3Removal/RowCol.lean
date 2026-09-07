/-
Copyright (c) 2026 Matt Palmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Palmer
-/

import P3Removal.Spectral

/-!
# Row-column mass

Zhang writes `sᵢ(M)` for the sum of squares of every entry of `M` that lies
on the `i`-th row or the `i`-th column. For any matrix this splits the
squared Frobenius norm into the principal submatrix on `V \ {i}` plus that
row-column mass.
-/

open scoped BigOperators

namespace P3Removal

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Sum of squares of the entries of `M` on row `i` or column `i`. The
diagonal entry is counted once. -/
def rowColMass (M : Matrix n n ℝ) (i : n) : ℝ :=
  M i i ^ 2 + ∑ j ∈ Finset.univ.erase i, (M i j ^ 2 + M j i ^ 2)

lemma rowColMass_nonneg (M : Matrix n n ℝ) (i : n) :
    0 ≤ rowColMass M i :=
  add_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The principal submatrix obtained by deleting row and column `i`. -/
def deleteIndex (M : Matrix n n ℝ) (i : n) :
    Matrix {x : n // x ≠ i} {x : n // x ≠ i} ℝ :=
  M.submatrix Subtype.val Subtype.val

lemma sum_ne_eq_sum_erase (f : n → ℝ) (i : n) :
    ∑ a : {x : n // x ≠ i}, f a.1 = ∑ a ∈ Finset.univ.erase i, f a := by
  refine Finset.sum_nbij (fun a : {x : n // x ≠ i} ↦ a.1)
    (s := (Finset.univ : Finset {x : n // x ≠ i}))
    (t := Finset.univ.erase i) (f := fun a ↦ f a.1) (g := f) ?_ ?_ ?_ ?_
  · intro a _
    simp [a.property]
  · intro a _ b _ h
    exact Subtype.ext h
  · intro a ha
    refine ⟨⟨a, ?_⟩, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_erase.mp ha).1
  · intro _ _
    rfl

lemma sum_sum_ne_eq_sum_erase (f : n → n → ℝ) (i : n) :
    ∑ a : {x : n // x ≠ i}, ∑ b : {x : n // x ≠ i}, f a.1 b.1 =
      ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, f a b := by
  rw [sum_ne_eq_sum_erase (fun a ↦ ∑ b : {x : n // x ≠ i}, f a b.1) i]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact sum_ne_eq_sum_erase (fun b ↦ f a b) i

lemma frobeniusSq_eq_delete_add_rowCol (M : Matrix n n ℝ) (i : n) :
    frobeniusSq M = frobeniusSq (deleteIndex M i) + rowColMass M i := by
  unfold frobeniusSq deleteIndex rowColMass
  simp only [submatrix_apply]
  have hsplit (g : n → ℝ) :
      ∑ a, g a = g i + ∑ a ∈ Finset.univ.erase i, g a :=
    (Finset.add_sum_erase _ g (Finset.mem_univ i)).symm
  have hrow :
      ∑ b, M i b ^ 2 =
        M i i ^ 2 + ∑ b ∈ Finset.univ.erase i, M i b ^ 2 :=
    hsplit _
  have hrest :
      ∑ a ∈ Finset.univ.erase i, ∑ b, M a b ^ 2 =
        ∑ a ∈ Finset.univ.erase i, M a i ^ 2 +
          ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, M a b ^ 2 := by
    have := Finset.sum_congr (s₁ := Finset.univ.erase i) rfl
      (fun a _ ↦ hsplit (fun b ↦ M a b ^ 2))
    simpa [Finset.sum_add_distrib] using this
  have hleft :
      ∑ a, ∑ b, M a b ^ 2 =
        M i i ^ 2 + ∑ b ∈ Finset.univ.erase i, M i b ^ 2 +
          ∑ a ∈ Finset.univ.erase i, M a i ^ 2 +
            ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, M a b ^ 2 := by
    rw [hsplit (fun a ↦ ∑ b, M a b ^ 2), hrow, hrest]
    ac_rfl
  have hsub := sum_sum_ne_eq_sum_erase (fun a b ↦ M a b ^ 2) i
  have hmass :
      ∑ b ∈ Finset.univ.erase i, M i b ^ 2 +
          ∑ a ∈ Finset.univ.erase i, M a i ^ 2 =
        ∑ j ∈ Finset.univ.erase i, (M i j ^ 2 + M j i ^ 2) := by
    simp [Finset.sum_add_distrib]
  rw [hleft, ← hsub, ← hmass]
  ac_rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restricting to a subset of columns cannot increase the row-column mass. -/
lemma rowColMass_submatrix_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix V V ℝ) (e : ι → V) (he : Function.Injective e) (i : ι) :
    rowColMass (M.submatrix e e) i ≤ rowColMass M (e i) := by
  classical
  let s := (Finset.univ.erase i).image e
  let f : V → ℝ := fun k ↦ M (e i) k ^ 2 + M k (e i) ^ 2
  have hmap :
      ∑ j ∈ Finset.univ.erase i, f (e j) = ∑ k ∈ s, f k := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact he hxy
  have hsubset : s ⊆ Finset.univ.erase (e i) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
    exact he.ne hj
  have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase (e i) \ s, f k :=
    Finset.sum_nonneg fun _ _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsplit : ∑ k ∈ Finset.univ.erase (e i) \ s, f k + ∑ k ∈ s, f k =
      ∑ k ∈ Finset.univ.erase (e i), f k :=
    Finset.sum_sdiff hsubset
  unfold rowColMass
  simp only [submatrix_apply]
  change M (e i) (e i) ^ 2 + ∑ j ∈ Finset.univ.erase i, f (e j) ≤
    M (e i) (e i) ^ 2 + ∑ k ∈ Finset.univ.erase (e i), f k
  nlinarith [hmap, hsplit, hrest]

omit [Fintype V] [DecidableEq V] in
lemma deleteVertex_adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (deleteVertex G v).adjMatrix ℝ =
      (G.adjMatrix ℝ).submatrix Subtype.val Subtype.val := by
  ext x y
  simp [deleteVertex_adj, SimpleGraph.adjMatrix_apply]

omit [Fintype V] [DecidableEq V] in
lemma deleteIndex_sub (A B : Matrix V V ℝ) (v : V) :
    deleteIndex (A - B) v = deleteIndex A v - deleteIndex B v := by
  ext i j
  simp [deleteIndex]

omit [Fintype V] [DecidableEq V] in
lemma deleteIndex_add (A B : Matrix V V ℝ) (v : V) :
    deleteIndex (A + B) v = deleteIndex A v + deleteIndex B v := by
  ext i j
  simp [deleteIndex]

omit [Fintype V] [DecidableEq V] in
lemma deleteIndex_adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    deleteIndex (G.adjMatrix ℝ) v = (deleteVertex G v).adjMatrix ℝ :=
  (deleteVertex_adjMatrix G v).symm

omit [Fintype V] [DecidableEq V] in
lemma deleteIndex_posSemidef {M : Matrix V V ℝ} (hM : M.PosSemidef) (v : V) :
    (deleteIndex M v).PosSemidef :=
  hM.submatrix _

end P3Removal
