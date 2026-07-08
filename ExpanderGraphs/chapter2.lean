/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

module

public import ExpanderGraphs.chapter1


/-!
# Isoperimetric problems

## References
* [Spectral Graph Theory, Fan Chung][Chung]
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section


variable {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
variable {G : WeightedGraph α β} [DecidableRel G.Adj]
variable (hα : G.vertexSet = Set.univ)
variable (hβ : G.edgeSet = Set.univ)

open Graph
open NNReal


namespace WeightedGraph

/-- We define the edge boundary ∂S of S to consist of all edges with exactly one endpoint in S. -/
def edgeBoundary (S : Set α) : Set β :=
  {e ∈ G.edgeSet | ∃ a ∈ S, ∃ b ∈ Sᶜ, G.IsLink e a b}


/-- E(A, B) denotes the set of edges with one endpoint in A and one endpoint in B. -/
def edgeConnection (A B : Set α) : Set β :=
  {e ∈ G.edgeSet | ∃ a ∈ A, ∃ b ∈ B, G.IsLink e a b}


namespace Isoperimetry

noncomputable section

/-- It is easy to see that ∂S = ∂Sᶜ. -/
lemma edgeBoundaryComplement (S : Set α) :
    G.edgeBoundary S = G.edgeBoundary Sᶜ := by
  ext e; unfold edgeBoundary;
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
  compl_compl, and_congr_right_iff]
  intro he;
  constructor <;> rintro ⟨a, ha, b, hb, h⟩ <;> exact ⟨b, hb, a, ha, h.symm⟩


/-- ∂S = E(S, Sᶜ). -/
lemma self_connection_eq_boundary (S : Set α) :
  G.edgeBoundary S = G.edgeConnection S Sᶜ := rfl


open Classical in
/-- For a vertex set S, we define hG(S) = |E(S, Sᶜ)| / min(vol S , vol Sᶜ). -/
def hG (S : Set α) : ℝ :=
  (G.edgeBoundary S).ncard / (min (G.vol S) (G.vol Sᶜ))


open Classical in
/-- The Cheeger constant of a graph G is defined as the
minimum of hG (s) for every set of vertices s. -/
def cheeger (G : WeightedGraph α β) : ℝ :=
  ⨅ (S : Set α), hG (G := G) S


open Classical in
/-- cheger * vol S ≤ |∂S|. -/
lemma cheeger_mul_volume_le_volume_frontier (S : Set α) (hPb1 : G.vol S ≤ G.vol Sᶜ) :
  (cheeger G) * (G.vol S) ≤ (G.edgeBoundary S).ncard := by
    unfold cheeger hG; norm_cast;
    have h1 : (⨅ i, ↑(G.edgeBoundary i).ncard / min (G.vol i) (G.vol iᶜ)) * G.vol S ≤
      ↑(G.edgeBoundary S).ncard / min (G.vol S) (G.vol Sᶜ) * G.vol S := by
        · by_cases h0 : G.vol S = 0
          · rw [h0]; simp;
          · simp_all; push Not at h0; field_simp;
            have h_min : min (vol S) (vol Sᶜ) = vol S := min_eq_left hPb1
            have h_pos : 0 < G.vol S := by positivity;
            rw [← le_div_iff₀ h_pos, ← h_min]
            apply ciInf_le
            · use 0; rintro _ ⟨i, rfl⟩; positivity;
    have h2 :
      (G.edgeBoundary S).ncard / min (G.vol S) (G.vol Sᶜ) * G.vol S ≤ (G.edgeBoundary S).ncard := by
        rw [min_eq_left hPb1]; ring_nf;
        by_cases h0 : G.vol S = 0
        · rw [h0]; norm_cast; simp;
        · push Not at h0; refine mul_inv_right_le ?_; norm_cast; simp;
    grind;


-- TODO: write statements of lemmas
-- redefine what it means for a graph to be connected for the following statements.

/-- A graph is connected iff its cheeger constant is positive. -/
lemma connected_iff_cheeger_pos : True := sorry


/-- We first derive a simple upper bound for the eigenvalue λ1
in terms of the Cheeger constant of a connected graph. -/
lemma two_cheeger_ge_first_eigval : True := sorry

end

end Isoperimetry
