/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Graph Partitioning

This file defines isoperimetric ratio, and prove results about
its relation to the second-smallest eigenvalue of the Laplacian.

## References
* [Spectral and Algebraic Graph Theory, Daniel A. Spielman, 2025][Spielman2025]
* [S. Hoory, N. Linial and A. Wigderson. Expander graphs and their applications.][Expander2006]
-/


@[expose] public section

variable {α β : Type*}

namespace GraphPartitioning

/-- The ordered edge set from a subset `S` to a subset `T` in a graph `G`.
Given two subsets of vertices `S` and `T`, `\vec E(S, T)`
is the set of all directed pairs `(u, v)` such that `u ∈ S`, `v ∈ T`,
and there is an edge between `u` and `v` in `G`. -/
def orderedEdgeSet (G : Graph α β) (S T : Set α) : Set β :=
  {e ∈ G.edgeSet | ∃ a ∈ S, ∃ b ∈ T, G.IsLink e a b}


/-- The Edge Boundary of a set `S`, denoted `∂S`, is `∂S = E(S, Sᶜ)`.\
This is the set of edges emanating from the set S to its complement. -/
def boundary (G : Graph α β) (S : Set α) : Set β := orderedEdgeSet G S Sᶜ


/-- The isoperimetric ratio of a set S is defined as `θ(S) = |∂S| / |S|` -/
noncomputable def isoperimetricRatio (G : Graph α β) (S : Set α) : ℝ :=
  (boundary G S).ncard / S.ncard


/-- The Edge Expansion of a graph is defined as `min |∂S| / |S|`
over all subsets `S` such that `0 < |S| ≤ n / 2`. -/
noncomputable def cheegerConstant (G : Graph α β) : ℝ :=
  let n : ℝ := (Set.ncard G.vertexSet : ℝ)
  sInf (
    ((fun S : Set α ↦ isoperimetricRatio G S) ''
    {S : Set α | S ⊆ G.vertexSet ∧ 0 < Set.ncard S ∧ (Set.ncard S : ℝ) ≤ n / 2} : Set ℝ)
  )



/-- A finite graph is a graph in which the vertex set and the edge set are finite sets. -/
def IsFinite (G : Graph α β) : Prop := Finite G.vertexSet ∧ Finite G.edgeSet


/-- A finite graph `G` is a \textbf{`(k, \varepsilon)`-expander}
  if each vertex of `G` has valency at most `k`, and `h(G) \ge \varepsilon > 0`. -/
def IsEdgeExpander (G : Graph α β) (k : ℕ) (ε : ℝ) (_ : IsFinite G) : Prop :=
  (∀ v ∈ G.vertexSet, (G.incidenceSet v).ncard ≤ k) ∧ ε ≤ cheegerConstant G ∧ 0 < ε


/-- A sequence of finite graphs `{Gi}` is called an expander sequence if `|Gi| → ∞`
and there exists `k, ε` such that each `Gi` is a `(k, ε)-expander`. -/
def expanderSequence (g : ℕ → Graph α β) : Prop :=
  ∃ (hF : ∀ i, IsFinite (g i)),
    ∃ ε : ℝ, ∃ k : ℕ, ∀ i : ℕ, IsEdgeExpander (g i) k ε (hF i)


end GraphPartitioning



namespace Matrix

/-- `adjMultiplicity u v` is the number of edges connecting `u` and `v`.
We use the convention that if `u` has a self-loop, this loop counts twice. -/
noncomputable def adjMultiplicity (G : Graph α β) (u v : α) : ℕ :=
  {e : G.edgeSet | G.IsLink e u v}.ncard


/-- `adjMatrixMulti G` is the adjacency matrix the multigraph `G` -/
noncomputable def adjMatrixMulti (G : Graph α β) : Matrix α α ℝ :=
  fun u v => (adjMultiplicity G u v : ℝ)


/-- `adjMatrixMulti` is symm -/
lemma adj_symm (G : Graph α β) : IsSymm (adjMatrixMulti G) := by
  unfold IsSymm adjMatrixMulti adjMultiplicity;
  ext i j; simp only [transpose_apply, Nat.cast_inj];
  apply congr_arg Set.ncard
  ext e; constructor <;> (intro hl; simp [Graph.IsLink.symm hl])

/-- `adjMatrixMulti` is Hermitian -/
theorem isHermitian (G : Graph α β) : IsHermitian (adjMatrixMulti G) := by
  unfold IsHermitian; simp only [conjTranspose_eq_transpose_of_trivial]; rw [adj_symm];

end Matrix



section Degree

namespace Graph

variable {G : Graph α β}
variable [∀ s, Fintype (G.incidenceSet s)]

/-- `G.degree v` is the number of edges incident to `v`. -/
def degree (v : α) : ℕ :=
  Fintype.card (G.incidenceSet v)

/-- A graph is regular of degree `d` if every vertex has degree `d`. -/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v, G.degree v = d


end Graph

end Degree


end -- close @[expose] public section
