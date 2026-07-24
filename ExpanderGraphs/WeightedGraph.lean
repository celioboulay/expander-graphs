/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay
-/
module

public import Mathlib.Data.NNReal.Defs
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic


/-!
# WeightedGraph

This file develops the basic theory of weighted graphs.

## Main definitions
- A weigh function over a set α is defined as a symmetrical function w : α → α → ℝ≥0.
- A weighted undirected graph G (possibly with loops) has associated with it a weight function w.

## References
* [Spectral Graph Theory, Fan Chung][Chung]
-/

@[expose] public section

variable {α β : Type*} {x y z u v : α} {e f : β}
variable [Fintype α] [DecidableEq α]

open Set

open NNReal

structure WeightedGraph (α β : Type*) extends Graph α β where
  w : α → α → ℝ≥0
  symm : ∀ u v, w u v = w v u
  edgeCondition : ∀ u v, ¬ toGraph.Adj u v → w u v = 0

variable (G : WeightedGraph α β) [DecidableRel G.Adj]

namespace WeightedGraph

def degree (v : α) : ℝ≥0 := ∑ u : α, G.w u v

def vol : ℝ≥0 := ∑ u : α, G.degree u

open Matrix

def L : Matrix G.vertexSet G.vertexSet ℝ :=
  fun (u v : G.vertexSet) =>
    if u = v then G.degree v - G.w u v
    else if G.Adj u v then - G.w u v
    else 0


end WeightedGraph
