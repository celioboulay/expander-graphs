/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

module

public import ExpanderGraphs.Basic
public import Mathlib.Analysis.Matrix.Order

/-!
# Expander Mixing Lemma

TODO: write doc
-/


@[expose] public section


variable {α β : Type*}
variable {G : Graph α β} [Fintype α]


open Classical in
/-- Eigenvalues of the adjMatrix in non-increasing order. -/
noncomputable def adjEigvals : Fin (Fintype.card α) → ℝ :=
  (Matrix.isHermitian G).eigenvalues₀


/-- The indicator vector of a subset `S` of vertices.
For any vertex `v`, `setIndicator S v` is `1` if `v ∈ S` and `0` otherwise. -/
noncomputable def setIndicator (S : Set α) : α → ℝ :=
  Set.indicator S (fun _ => 1)


open Matrix

namespace Graph

variable [∀ s, Fintype (G.incidenceSet s)]
variable {d : ℕ}


lemma degree_mulVec_adj (i : G.vertexSet) (hG : G.IsRegularOfDegree d) :
  ∑ x, adjMultiplicity G i x = d := by classical
    unfold adjMultiplicity
    unfold IsRegularOfDegree degree incidenceSet at hG
    have hG_i := hG i; rw [← hG_i];
    sorry



theorem adjMatrix_mulVec_one_eq_degree (i : α) (hi : i ∈ G.vertexSet) (hG : G.IsRegularOfDegree d) :
  (adjMatrixMulti G *ᵥ 1) i = (d : ℝ) := by
    unfold adjMatrixMulti
    simp only [mulVec, dotProduct, Pi.one_apply, mul_one]
    rw [← Nat.cast_sum]
    norm_cast
    exact degree_mulVec_adj ⟨i, hi⟩ hG


open GraphPartitioning

variable {l : ℝ} -- max eigenvalue of the graph
variable {d : ℕ}
variable {n : ℝ} [Fact (n = G.vertexSet.ncard)] [Fact (1 < n)]


/-- Number of edges -/
noncomputable def EOS (S T : Set α) : ℝ := (orderedEdgeSet G S T).ncard


/-- The indicator vector of a subset `S` of vertices.
For any vertex `v`, `setIndicator S v` is `1` if `v ∈ S` and `0` otherwise. -/
noncomputable def setIndicator (S : Set α) : α → ℝ :=
  Set.indicator S (fun _ => 1)


theorem ExpanderMixingLemma (S T : Set α) (_ : G.IsRegularOfDegree d) :
  let e := G.EOS S T
  let nS := (S.ncard); let nT := (T.ncard)
  abs (e - d * (nS * nT) / n) ≤ l * d * Real.sqrt (nS * nT) := sorry



end Graph

end
