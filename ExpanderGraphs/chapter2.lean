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
variable {S : Set α} [Fintype S] -- [Fintype Sᶜ]

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
def vol (S : Set α) [Fintype S] : ℝ≥0 := ∑ v : S, G.degree v


-- For a vertex set S, we define hG(S) = |E(S, Sᶜ)| / min(vol S , vol Sᶜ). -/
-- def hG := (edgeBoundary G S).ncard / (min (vol S) (vol Sᶜ))

-- We will only consider connected graphs

end

end Isoperimetry
