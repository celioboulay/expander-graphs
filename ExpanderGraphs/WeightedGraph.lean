/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.Graph.Basic

/-!
# WeightedGraph

This file develops the basic theory of weighted graphs `WeightedGraph α β`.

## Main definitions
- `WeightedGraph` is a finite `Graph` associated with a weight function.
- `degreeMatrix` and `lapMatrix`: matrices associated with a graph.

## References
* [Spectral Graph Theory, Fan Chung][Chung]
-/

@[expose] public section

variable {α β : Type*} {x y z u v : α} {e f : β}
variable [Fintype α] [DecidableEq α]

open Set

/-- A weighted graph on types α β is a `Graph α β` associated with a function `w`.
`w` the *weight function* is *symmetrical* and *non-negative*. -/
structure WeightedGraph (α β : Type*) extends Graph α β where
  w : α → α → ℝ
  positivity : ∀ u v, 0 ≤ w u v
  symm : ∀ u v, w u v = w v u
  edgeCondition : ∀ u v, ¬ toGraph.Adj u v → w u v = 0

variable (G : WeightedGraph α β) [DecidableRel G.Adj]

namespace WeightedGraph

/-- The degree of `v` in `G` is the sum of `G.w u v` for every `u` in α. -/
def degree (v : α) : ℝ := ∑ u : α, G.w u v

omit [Fintype α] [DecidableEq α] [DecidableRel G.Adj] in
lemma no_adj_of_notMem_vertexSet (v : α) (h : v ∉ G.vertexSet) : ∀ u, ¬ G.Adj u v := by
  intro u
  rw [Graph.Adj]
  grind

omit [DecidableEq α] [DecidableRel G.Adj] in
lemma degree_zero_of_notMem_vertexSet (v : α) (h : v ∉ G.vertexSet) : G.degree v = 0 := by
  unfold degree;
  have h_adj : ∀ u, ¬ G.Adj u v := by exact no_adj_of_notMem_vertexSet G v h
  have h_w0 : ∀ u, G.w u v = 0 := by exact fun u ↦ G.edgeCondition u v (h_adj u)
  exact Fintype.sum_eq_zero (fun a ↦ G.w a v) h_w0

/-- The volume of a graph `G` is the sum of the degree in `G` of each u ∈ α. -/
def vol : ℝ := ∑ u : α, G.degree u

open Matrix

noncomputable section

/-- The diagonal matrix consisting of the degrees of the vertices in the graph. -/
def degreeMatrix : Matrix G.vertexSet G.vertexSet ℝ :=
  Matrix.diagonal (fun u => G.degree u)

/-- The *Laplacian matrix* `lapMatrix` of a weigthed graph `G`. -/
def lapMatrix : Matrix G.vertexSet G.vertexSet ℝ :=
  fun (u v : G.vertexSet) =>
    if u = v then if G.degree v = 0 then 0 else 1 - (G.w u v / G.degree v)
    else if G.Adj u v then - G.w u v / √ (G.degree v * G.degree u)
    else 0

theorem isHermitian_lapMatrix : G.lapMatrix.IsHermitian := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [lapMatrix]
  · simp [lapMatrix, h, Ne.symm h, G.symm, mul_comm (G.degree v), Graph.adj_comm]

/-- Eigenvalues of `lapMatrix` in non-increasing order. -/
def lapEigvals [Fintype G.vertexSet] : Fin (Fintype.card G.vertexSet) → ℝ :=
  fun i => G.isHermitian_lapMatrix.eigenvalues₀ i.rev

end

end WeightedGraph
