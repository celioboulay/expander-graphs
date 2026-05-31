import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Setoid.Partition
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace ExpanderGraphs

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


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


/-- A sequence of k-regular graphs `{Gi}` of size increasing with i
is a family of Expander Graphs if `∃ ε > 0` s.t. `h(Gi) ≥ ε`, for all i -/
def expanderFamily (g : ℕ → SimpleGraph V) (ε : ℝ) : Prop :=
  ε > 0 ∧ ∀ i : ℕ, ε ≤ edgeExpansion (g i)


/-- TODO, maybe use adjacency operator instead, cf Tao's notes -/
def graphLaplacianEigenvalues : Fin ((Fintype.card V)) → ℝ :=
  let L := SimpleGraph.lapMatrix ℝ G;
  fun (i : Fin ((Fintype.card V))) => (i : ℝ) -- tmp


end ExpanderGraphs
