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
variable {S : Set α} [Fintype S]

open Graph

namespace Isoperimetry

def edgeBoundary (G : WeightedGraph α β) (S : Set α) : Set β :=
  {e ∈ G.edgeSet | ∃ a ∈ S, ∃ b ∈ Sᶜ, G.IsLink e a b}


lemma edgeBoundaryComplement (S : Set α) :
    edgeBoundary G S = edgeBoundary G Sᶜ := by
  ext e; unfold edgeBoundary;
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
  compl_compl, and_congr_right_iff]
  intro he;
  constructor <;> rintro ⟨a, ha, b, hb, h⟩ <;> exact ⟨b, hb, a, ha, h.symm⟩



end Isoperimetry
