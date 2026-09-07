/-
Copyright (c) 2026 Matt Palmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Palmer
-/

import P3Removal.Lemma41

/-!
# Zhang Theorem 1.10

An induced `P₃` forces a vertex whose deletion drops the negative (resp.
positive) square energy by more than `1`. The argument is Lemma 3.1 plus
Lemma 4.1, as in arXiv:2409.15504v2 §4. Superadditivity (Theorem 1.6) is
not used.
-/

open scoped BigOperators

namespace P3Removal

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's labeling of an induced `P₃`: endpoints, then the middle vertex. -/
def InducedP3.embed {G : SimpleGraph V} (U : InducedP3 G) : Fin 3 → V :=
  ![U.a, U.b, U.c]

omit [Fintype V] [DecidableEq V] in
lemma InducedP3.embed_injective {G : SimpleGraph V} (U : InducedP3 G) :
    Function.Injective U.embed := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [InducedP3.embed] at h ⊢
  · exact (U.a_ne_b h).elim
  · exact (U.a_ne_c h).elim
  · exact (U.a_ne_b h.symm).elim
  · exact (U.b_ne_c h).elim
  · exact (U.a_ne_c h.symm).elim
  · exact (U.b_ne_c h.symm).elim

omit [Fintype V] in
lemma InducedP3.embed_mem_verts {G : SimpleGraph V} (U : InducedP3 G) (i : Fin 3) :
    U.embed i ∈ U.verts := by
  fin_cases i <;> simp [InducedP3.embed, InducedP3.mem_verts]

omit [Fintype V] [DecidableEq V] in
lemma InducedP3.adjMatrix_submatrix {G : SimpleGraph V} [DecidableRel G.Adj]
    (U : InducedP3 G) :
    (G.adjMatrix ℝ).submatrix U.embed U.embed = p3Adj := by
  ext i j
  have hab := U.adj_ab
  have hbc := U.adj_bc
  have hac := U.not_adj_ac
  have hba := hab.symm
  have hcb := hbc.symm
  have hca : ¬ G.Adj U.c U.a := fun h ↦ hac h.symm
  fin_cases i <;> fin_cases j <;>
    simp [submatrix_apply, SimpleGraph.adjMatrix_apply, p3Adj, InducedP3.embed,
      hab, hbc, hac, hba, hcb, hca]

omit [Fintype V] [DecidableEq V] in
lemma InducedP3.posSemidef_submatrix {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : M.PosSemidef) (U : InducedP3 G) :
    (M.submatrix U.embed U.embed).PosSemidef :=
  hM.submatrix _

lemma rowColMass_submatrix_p3 {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : Matrix V V ℝ) (U : InducedP3 G) (i : Fin 3) :
    rowColMass ((G.adjMatrix ℝ - M).submatrix U.embed U.embed) i ≤
      rowColMass (G.adjMatrix ℝ - M) (U.embed i) :=
  rowColMass_submatrix_le (G.adjMatrix ℝ - M) U.embed U.embed_injective i

lemma rowColMass_submatrix_p3_add {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : Matrix V V ℝ) (U : InducedP3 G) (i : Fin 3) :
    rowColMass ((G.adjMatrix ℝ + M).submatrix U.embed U.embed) i ≤
      rowColMass (G.adjMatrix ℝ + M) (U.embed i) :=
  rowColMass_submatrix_le (G.adjMatrix ℝ + M) U.embed U.embed_injective i

lemma submatrix_sub {n ι : Type*} (A B : Matrix n n ℝ) (e : ι → n) :
    (A - B).submatrix e e = A.submatrix e e - B.submatrix e e := by
  ext i j
  simp

lemma submatrix_add {n ι : Type*} (A B : Matrix n n ℝ) (e : ι → n) :
    (A + B).submatrix e e = A.submatrix e e + B.submatrix e e := by
  ext i j
  simp

/-- Zhang Theorem 1.10 for negative square energy. -/
theorem zhang_theorem_1_10_negative {G : SimpleGraph V} [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      negativeSquareEnergy G >
        negativeSquareEnergy (deleteVertex G u) + 1 := by
  let M := adjacencyPosPart G
  have hM : M.PosSemidef := adjacencyPosPart_posSemidef G
  have heq : frobeniusSq (G.adjMatrix ℝ - M) = negativeSquareEnergy G :=
    frobeniusSq_sub_posPart G
  have hMU := InducedP3.posSemidef_submatrix hM U
  have hA : (G.adjMatrix ℝ).submatrix U.embed U.embed = p3Adj :=
    U.adjMatrix_submatrix
  have hblock : (G.adjMatrix ℝ - M).submatrix U.embed U.embed =
      p3Adj - M.submatrix U.embed U.embed := by
    rw [submatrix_sub, hA]
  obtain ⟨i, hi⟩ := (lemma_4_1 hMU).1
  set u := U.embed i
  refine ⟨u, U.embed_mem_verts i, ?_⟩
  have hmass : 1 < rowColMass (G.adjMatrix ℝ - M) u :=
    lt_of_lt_of_le (by
      simpa [hblock] using hi) (rowColMass_submatrix_p3 M U i)
  have hsplit := frobeniusSq_eq_delete_add_rowCol (G.adjMatrix ℝ - M) u
  have hdel :
      frobeniusSq (deleteIndex (G.adjMatrix ℝ - M) u) =
        frobeniusSq
          ((deleteVertex G u).adjMatrix ℝ - deleteIndex M u) := by
    rw [deleteIndex_sub, deleteIndex_adjMatrix]
  have hMdel : (deleteIndex M u).PosSemidef := deleteIndex_posSemidef hM u
  have hlower :=
    le_frobeniusSq_sub_of_posSemidef (deleteVertex G u) hMdel
  have : negativeSquareEnergy G =
      frobeniusSq (deleteIndex (G.adjMatrix ℝ - M) u) +
        rowColMass (G.adjMatrix ℝ - M) u := by
    rw [← heq, hsplit]
  nlinarith [hlower, hmass, this, hdel,
    negativeSquareEnergy_nonneg (deleteVertex G u)]

/-- Zhang Theorem 1.10 for positive square energy. -/
theorem zhang_theorem_1_10_positive {G : SimpleGraph V} [DecidableRel G.Adj]
    (U : InducedP3 G) :
    ∃ u ∈ U.verts,
      positiveSquareEnergy G >
        positiveSquareEnergy (deleteVertex G u) + 1 := by
  let M := adjacencyNegPart G
  have hM : M.PosSemidef := adjacencyNegPart_posSemidef G
  have heq : frobeniusSq (G.adjMatrix ℝ + M) = positiveSquareEnergy G :=
    frobeniusSq_add_negPart G
  have hMU := InducedP3.posSemidef_submatrix hM U
  have hA : (G.adjMatrix ℝ).submatrix U.embed U.embed = p3Adj :=
    U.adjMatrix_submatrix
  have hblock : (G.adjMatrix ℝ + M).submatrix U.embed U.embed =
      p3Adj + M.submatrix U.embed U.embed := by
    rw [submatrix_add, hA]
  obtain ⟨j, hj⟩ := (lemma_4_1 hMU).2
  set u := U.embed j
  refine ⟨u, U.embed_mem_verts j, ?_⟩
  have hmass : 1 < rowColMass (G.adjMatrix ℝ + M) u :=
    lt_of_lt_of_le (by
      simpa [hblock] using hj) (rowColMass_submatrix_p3_add M U j)
  have hsplit := frobeniusSq_eq_delete_add_rowCol (G.adjMatrix ℝ + M) u
  have hdel :
      frobeniusSq (deleteIndex (G.adjMatrix ℝ + M) u) =
        frobeniusSq
          ((deleteVertex G u).adjMatrix ℝ + deleteIndex M u) := by
    rw [deleteIndex_add, deleteIndex_adjMatrix]
  have hMdel : (deleteIndex M u).PosSemidef := deleteIndex_posSemidef hM u
  have hlower :=
    le_frobeniusSq_add_of_posSemidef (deleteVertex G u) hMdel
  have : positiveSquareEnergy G =
      frobeniusSq (deleteIndex (G.adjMatrix ℝ + M) u) +
        rowColMass (G.adjMatrix ℝ + M) u := by
    rw [← heq, hsplit]
  nlinarith [hlower, hmass, this, hdel,
    positiveSquareEnergy_nonneg (deleteVertex G u)]

/-- Zhang arXiv:2409.15504 Theorem 1.10, both signs. -/
theorem zhang_theorem_1_10 {G : SimpleGraph V} [DecidableRel G.Adj]
    (U : InducedP3 G) :
    (∃ u ∈ U.verts,
        negativeSquareEnergy G > negativeSquareEnergy (deleteVertex G u) + 1) ∧
      (∃ u ∈ U.verts,
        positiveSquareEnergy G > positiveSquareEnergy (deleteVertex G u) + 1) :=
  ⟨zhang_theorem_1_10_negative U, zhang_theorem_1_10_positive U⟩

end P3Removal
