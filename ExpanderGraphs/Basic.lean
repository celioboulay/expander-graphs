/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Expander Graphs

TODO: write documentation :)
Move things in different files (e.g. split multigraphs and expanders)

## References
* [Irit Dinur. The PCP theorem by gap amplification. ECCC, 2005.][Dinur2005]

-/

namespace ExpanderGraphs

variable {α β : Type*} [Fintype α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
variable (G : Graph α β)
variable [CommSemiring α] [Ring α] [Algebra ℝ α]
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


/-- A sequence of k-regular graphs `{g i}` of size increasing with i
is a family of Expander Graphs if `∃ ε > 0` s.t. `h(Gi) ≥ ε`, for all i. -/
def expanderFamily (g : ℕ → Graph α β) (ε : ℝ) : Prop :=
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
def isRegularOfDegree (d : ℕ) [∀ v : α, Fintype (G.incidenceSet v)] : Prop :=
  ∀ (v : α), v ∈ G.vertexSet → degree G v = d


/-- Given a `d`-regular graph `G`, `d` is an eigenvalue of its adjacency matrix -/
theorem degreeIsEigvalOfRegularGraph (d : ℕ)
  (hG : isRegularOfDegree G d)
  (hA : (adjMatrixMulti G).IsHermitian) :
    ∃ i, hA.eigenvalues i = d := by
      let v : α → ℝ := fun _ => 1
      have h_ev : (adjMatrixMulti G) *ᵥ v = d • v := by sorry
      -- proof that 1,1,1,1,1 is an eigenvector, also 1,...,1 ≠ 0

/- hasEigenvector_iff then,  x ∈ f.eigenspace μ ∧ x ≠ 0
also Module.End.mem_eigenspace_iff-/
      sorry



end ExpanderGraphs
