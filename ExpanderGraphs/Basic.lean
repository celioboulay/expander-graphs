import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace ExpanderGraphs

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)


/-- The Edge Boundary of a set S, denoted ∂S, is `∂S = E(S, Sᶜ)`.\
This is the set of edges emanating from the set S to its complement. -/
def edgeBoundary (S : Set V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∃ u ∈ S, ∃ v ∈ Sᶜ, e = s(u, v)}


/-- The Edge Expansion is defined as: `min{frac{|∂S| / |S|, 0<|S|≤n/2}` -/
noncomputable def edgeExpansion (G : SimpleGraph V) : ℝ :=
  let n : ℝ := (Fintype.card V : ℝ)
  sInf (
    ((fun S : Set V ↦ (Set.ncard (edgeBoundary G S) : ℝ) / (Set.ncard S : ℝ)) ''
    {S : Set V | 0 < Set.ncard S ∧ (Set.ncard S : ℝ) ≤ n / 2} : Set ℝ)
  )


end ExpanderGraphs
