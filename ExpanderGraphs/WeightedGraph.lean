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

This file develops the basic theory of weighted multigraphs `WeightedGraph α β`.

## Main definitions

- `WeightedGraph` is a finite `Graph` associated with a weight function.
- `degreeMatrix` and `lapMatrix`: matrices associated with a graph.

## References

* [Spectral Graph Theory, Fan Chung][Chung]
-/

set_option linter.unusedDecidableInType false

@[expose] public section

variable {α β K : Type*} {x y z u v : α} {e f : β}

open Finset Set

/-- A weighted multigraph on types α β K is a `Graph α β` associated with a function `w`: β → K. -/
structure WeightedGraph (α β K : Type*) extends Graph α β where
  w : β → K

namespace WeightedGraph

variable (G : WeightedGraph α β K) [AddCommMonoid K]

section FiniteAt

/-!
## Finiteness at a vertex

This section deals with vertices that have finitely many adjacent vertices.
We denote this condition by `Fintype (G.incidenceSet v)`.
We define `G.neighborFinset v` to be the `Finset` version of `G.neighborSet v`.
-/

variable (u v : α) [Fintype (G.incidenceSet v)] [Fintype (G.incidenceSet u)]
variable [∀ e u v, Decidable (G.IsLink e u v)]

/-- `G.incidenceFinset v` is the `Finset` version of `G.incidenceSet v` in case `G` is
locally finite at `v`. -/
def incidenceFinset : Finset β :=
  (G.incidenceSet v).toFinset

/-- The degree of `v` in `G` is the sum of `G.w e` for every edge `e` linked to `v`. -/
def degree : K :=
  ∑ e ∈ G.incidenceFinset v, G.w e

/-- The total weight of edges linking `u` and `v`. -/
def linkWeight : K :=
  ∑ e ∈ G.incidenceFinset u, if G.IsLink e u v then G.w e else 0

/-- Symmetry of edge weight between two vertices. -/
lemma weight_comm : G.linkWeight u v = G.linkWeight v u := by
  simp only [linkWeight, ← sum_filter, incidenceFinset]
  congr 1
  ext e
  simp only [Finset.mem_filter, Set.mem_toFinset]
  exact ⟨fun ⟨_, h⟩ => ⟨h.inc_right, h.symm⟩, fun ⟨_, h⟩ => ⟨h.inc_right, h.symm⟩⟩

end FiniteAt

section FiniteGraph

/-!
## Finite Graph

This section states results about graphs with a finite number of vertices and edges.
-/

variable [∀ u, Fintype (G.incidenceSet u)]
variable [Fintype G.vertexSet] [Fintype G.edgeSet]

/-- The volume of a graph `G` is the sum of the degrees of its vertices. -/
def vol : K := ∑ u : G.vertexSet, G.degree u

noncomputable section FiniteRealGraph

/-!
## Finite Graph

This section states results about graphs associated with a real weight function.
-/

variable (G : WeightedGraph α β ℝ)
variable [∀ u, Fintype (G.incidenceSet u)] [DecidableEq G.vertexSet]
variable [∀ e u v, Decidable (G.IsLink e u v)] [DecidableRel G.Adj]

open Matrix

/-- The diagonal matrix consisting of the degrees of the vertices in the graph. -/
def degreeMatrix : Matrix G.vertexSet G.vertexSet ℝ :=
  Matrix.diagonal (fun u => G.degree u)

/-- The *Laplacian matrix* `lapMatrix` of a weighted graph `G`. -/
def lapMatrix : Matrix G.vertexSet G.vertexSet ℝ :=
  fun (u v : G.vertexSet) =>
    if u = v then if G.degree v = 0 then 0 else 1 - (G.linkWeight u v / G.degree v)
    else if G.Adj u v then - G.linkWeight u v / √ (G.degree v * G.degree u)
    else 0

theorem isHermitian_lapMatrix : G.lapMatrix.IsHermitian := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [lapMatrix]
  · simp [lapMatrix, h, Ne.symm h, G.weight_comm v u, mul_comm (G.degree (v : α)), Graph.adj_comm]

/-- Eigenvalues of `lapMatrix` in non-increasing order. -/
def lapEigvals [Fintype G.vertexSet] : Fin (Fintype.card G.vertexSet) → ℝ :=
  fun i => G.isHermitian_lapMatrix.eigenvalues₀ i.rev

end FiniteRealGraph

end FiniteGraph

end WeightedGraph
