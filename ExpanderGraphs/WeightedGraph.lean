/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay
-/
module

public import Mathlib.Data.NNReal.Defs
public import Mathlib.Combinatorics.Graph.Basic


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

open Set

open NNReal

structure WeightFunction (α : Type*) where
  w : α → α → ℝ≥0
  symm : ∀ u v, w u v = w v u

structure WeightedGraph (α β : Type*) extends Graph α β where
  edgeWeight : WeightFunction α
