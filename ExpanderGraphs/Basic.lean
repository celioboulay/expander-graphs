/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Setoid.Partition
import Mathlib.Combinatorics.Graph.Basic

/-!
# Expander Graphs

TODO: write documentation :)

## References
* [Irit Dinur. The PCP theorem by gap amplification. ECCC, 2005.][Dinur2005]

-/

namespace ExpanderGraphs

universe u
variable {α : Type u_3} {β : Type u_4}
variable (G : Graph α β) [Fintype G.vertexSet]

/-- The Edge Boundary of a set S, denoted ∂S, is `∂S = E(S, Sᶜ)`.\
This is the set of edges emanating from the set S to its complement. -/
def edgeBoundary (S : Set α) : Set β :=
  {e | ∃ u ∈ S, ∃ v ∈ Sᶜ, G.IsLink e u v}


/-- The Edge Expansion is defined as: `min{frac{|∂S| / |S|, 0<|S|≤n/2}` -/
noncomputable def edgeExpansion : ℝ :=
  let n : ℝ := (Set.ncard G.vertexSet : ℝ)
  sInf (
    ((fun S : Set α ↦ (Set.ncard (edgeBoundary G S) : ℝ) / (Set.ncard S : ℝ)) ''
    {S : Set α | 0 < Set.ncard S ∧ (Set.ncard S : ℝ) ≤ n / 2} : Set ℝ)
  )


/-- A sequence of k-regular graphs `{Gi}` of size increasing with i
is a family of Expander Graphs if `∃ ε > 0` s.t. `h(Gi) ≥ ε`, for all i -/
def expanderFamily (g : ℕ → Graph α β) (ε : ℝ) : Prop :=
  ε > 0 ∧ ∀ i : ℕ, ε ≤ edgeExpansion (g i)


/- TODO: Better adjacency matrix cf slides -/


end ExpanderGraphs
