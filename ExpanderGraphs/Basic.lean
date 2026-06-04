/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import Mathlib.Data.Set.Card
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Expander Graphs

TODO: write documentation :)
Probably move things in different files

## References
* [S. Hoory, N. Linial and A. Wigderson. Expander graphs and their applications.][Expander2006]
* [M. Cencelj, J. Dydak and A. Vavpetič. Large Scale Versus Small Scale.][Cencelj2014]
-/

namespace ExpanderGraphs

variable {α β : Type*} [Fintype α] [DecidableEq α]
variable (G : Graph α β)
variable [locally_finite : ∀ v : α, Fintype (G.incidenceSet v)]

open Matrix

/-- The Edge Boundary of a set S, denoted ∂S, is `∂S = E(S, Sᶜ)`.\
This is the set of edges emanating from the set S to its complement. -/
def edgeBoundary (S : Set α) : Set β :=
  {e | ∃ u ∈ S, ∃ v ∈ Sᶜ, G.IsLink e u v}


/-- The Edge Expansion is defined as: `min{frac{|∂S| / |S|, 0<|S|≤n/2}`. -/
noncomputable def edgeExpansion (G : Graph α β) : ℝ :=
  let n : ℝ := (Set.ncard G.vertexSet : ℝ)
  sInf (
    ((fun S : Set α ↦ (Set.ncard (edgeBoundary G S) : ℝ) / (Set.ncard S : ℝ)) ''
    {S : Set α | S ⊆ G.vertexSet ∧ 0 < Set.ncard S ∧ (Set.ncard S : ℝ) ≤ n / 2} : Set ℝ)
  )


omit [DecidableEq α] [Fintype α] in -- temp
/-- The Cheeger constant is strictly positive if and only if $G$ is a connected graph. -/
theorem cheeger_positive_iff_connected (G : Graph α β) :
  1 = 2 := by
  classical
  sorry


/-- A finite graph `G` is a \textbf{`(k, \varepsilon)`-expander}
  if each vertex of `G` has valency at most `k`, and `h(G) \ge \varepsilon > 0`. -/
def isExpander (G : Graph α β) : Prop := G = G -- TODO


/-- A sequence of k-regular graphs `{g i}` of size increasing with i
is a family of Expander Graphs if `∃ ε > 0` s.t. `h(Gi) ≥ ε`, for all i. -/
def expanderSequence (g : ℕ → Graph α β) (ε : ℝ) : Prop :=
  ε > 0 ∧ ∀ i : ℕ, ε ≤ edgeExpansion (g i)


/-- `A : Matrix α α ℕ` is qualified as the adjacency
matrix of a multigraph if `A` is symmetric. -/
def isMultiAdjMatrix (A : Matrix α α ℕ) : Prop :=
  A.IsSymm


/-- `adjMultiplicity u v` is the number of edges connecting `u` and `v`.
We use the convention that if `u` has a self-loop, this loop counts twice. -/
noncomputable def adjMultiplicity (G : Graph α β) (u v : α) : ℕ :=
  {e : G.edgeSet | G.IsLink e u v}.ncard


/-- `adjMatrixMulti G` is the adjacency matrix the multigraph `G` -/
noncomputable def adjMatrixMulti (G : Graph α β) : Matrix α α ℝ :=
  fun u v => adjMultiplicity G u v


/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree (G : Graph α β) (v : α) [Fintype (G.incidenceSet v)] : ℕ :=
  Fintype.card (G.incidenceSet v)


/-- A locally finite graph is regular of degree `d` if every vertex has degree `d`. -/
def isRegularOfDegree (d : ℕ) : Prop :=
  ∀ (v : α), v ∈ G.vertexSet → degree G v = d


end ExpanderGraphs
