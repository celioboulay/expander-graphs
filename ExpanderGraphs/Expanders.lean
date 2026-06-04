/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import ExpanderGraphs.Basic

/-!
# Expander Graphs

An expander graph is a sparse graph that has strong connectivity properties.
This file states the main general definitions and early results.

## References
* [M. Cencelj, J. Dydak and A. Vavpetič. Large Scale Versus Small Scale.][Cencelj2014]
* [S. Hoory, N. Linial and A. Wigderson. Expander graphs and their applications.][Expander2006]
-/

namespace ExpanderGraphs

variable {α β : Type*}
variable (G : Graph α β)


/-- The Edge Boundary of a set S, denoted ∂S, is `∂S = E(S, Sᶜ)`.\
This is the set of edges emanating from the set S to its complement. -/
def edgeBoundary (S : Set α) : Set β :=
  {e | ∃ u ∈ S, ∃ v ∈ Sᶜ, G.IsLink e u v}


/-- The Edge Expansion of a graph is defined as `min |∂S| / |S|`
over all subsets `S` such that `0 < |S| ≤ n / 2`. -/
noncomputable def cheegerConstant (G : Graph α β) : ℝ :=
  let n : ℝ := (Set.ncard G.vertexSet : ℝ)
  sInf (
    ((fun S : Set α ↦ (Set.ncard (edgeBoundary G S) : ℝ) / (Set.ncard S : ℝ)) ''
    {S : Set α | S ⊆ G.vertexSet ∧ 0 < Set.ncard S ∧ (Set.ncard S : ℝ) ≤ n / 2} : Set ℝ)
  )


/-- If `G` if connected, every non empty proper subset `S` of its vertices has `∂S ≠ ∅` -/
lemma connected_edgeBoundary_nonempty :
  G.Connected →
    (∀ S ⊆ G.vertexSet, S.Nonempty → S ≠ G.vertexSet → (edgeBoundary G S).Nonempty) := by
  sorry


/-- The Cheeger constant is strictly positive if and only if `G` is connected. -/
theorem cheeger_positive_iff_connected {G : Graph α β} (_ : G.IsFinite) :
  0 < cheegerConstant G ↔ G.Connected := by
  -- can use le_sInf at some point
  sorry


/-- A finite graph `G` is a (k, ε)-expander
  if each vertex of `G` has valency at most `k`, and `h(G) ≥  ε > 0`. -/
def IsExpander (k : ℕ) (ε : ℝ) (_ : G.IsFinite) : Prop :=
  ∀ v ∈ G.vertexSet, (G.incidenceSet v).ncard ≤ k ∧ ε ≤ cheegerConstant G ∧ 0 < ε


/-- A sequence of finite graphs `{Gi}` is called an expander sequence if `|Gi| → ∞`
and there exists `k, ε` such that each `Gi` is a `(k, ε)-expander`. -/
def expanderSequence (g : ℕ → Graph α β) (hF : ∀ i, (g i).IsFinite) : Prop :=
  ∃ ε : ℝ, ∃ k : ℕ, ∀ i : ℕ, IsExpander (g i) k ε (hF i)


end ExpanderGraphs
