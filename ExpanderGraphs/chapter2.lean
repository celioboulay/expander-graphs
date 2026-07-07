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

namespace Isoperimetry

noncomputable section

def edgeBoundary (G : WeightedGraph α β) (S : Set α) : Set β :=
  {e ∈ G.edgeSet | ∃ a ∈ S, ∃ b ∈ Sᶜ, G.IsLink e a b}


lemma edgeBoundaryComplement (S : Set α) :
    edgeBoundary G S = edgeBoundary G Sᶜ := by
  ext e; unfold edgeBoundary;
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
  compl_compl, and_congr_right_iff]
  intro he;
  constructor <;> rintro ⟨a, ha, b, hb, h⟩ <;> exact ⟨b, hb, a, ha, h.symm⟩


/-- E(A, B) denotes the set of edges with one endpoint in A and one endpoint in B. -/
def edgeConnection (G : WeightedGraph α β) (A B : Set α) : Set β :=
  {e ∈ G.edgeSet | ∃ a ∈ A, ∃ b ∈ B, G.IsLink e a b}


/-- ∂S = E(S, Sᶜ). -/
lemma self_connection_eq_boundary (S : Set α) :
  edgeBoundary G S = edgeConnection G S Sᶜ := rfl


/-- We define vol S, the volume of S, to be the sum of the degrees of the vertices in S. -/
def vol (G : WeightedGraph α β) (S : Set α) [Fintype S] : ℝ≥0 := ∑ v : S, G.degree v
-- may move that into chapter 1 though


open Classical in
/-- For a vertex set S, we define hG(S) = |E(S, Sᶜ)| / min(vol S , vol Sᶜ). -/
def hG (G : WeightedGraph α β) (S : Set α) [Fintype S] [Fintype ↑Sᶜ] : ℝ :=
  (edgeBoundary G S).ncard / (min (vol G S) (vol G Sᶜ))


open Classical in
/-- The Cheeger constant of a graph G is defined as the
minimum of hG (s) for every set of vertices s. -/
def cheeger (G : WeightedGraph α β) : ℝ := ⨅ (S : Set α), hG G S


-- TODO: write statements of lemmas

/-- |∂S| ≥ cheger * vol S. -/
lemma find_name : True := sorry


/-- A graph is connected iff its cheeger constant is positive. -/
lemma connected_iff_cheeger_pos : True := sorry


/-- We first derive a simple upper bound for the eigenvalue λ1
in terms of the Cheeger constant of a connected graph. -/
lemma two_cheeger_ge_first_eigval : True := sorry

end

end Isoperimetry
