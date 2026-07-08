/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay.
-/

module

public import ExpanderGraphs.chapter1

/-!
# Connectivity for general graphs
-/

@[expose] public section


variable {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
variable {G : WeightedGraph α β} [DecidableRel G.Adj]
variable (hα : G.vertexSet = Set.univ) (hβ : G.edgeSet = Set.univ)

open Graph
open NNReal

namespace WeightedGraph

-- the following defs are 99% inspired by mathlib SimpleGraph.

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : α`,
the type `Walk G u v` consists of all walks starting at `u` and ending at `v`. -/
inductive Walk : α → α → Type _
  | nil {u : α} : Walk u u
  | cons {u v w : α} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

/-- Two vertices are *reachable* if there is a walk between them. -/
def Reachable (u v : α) : Prop := Nonempty (G.Walk u v)

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : α, G.Reachable u v

/-- A graph is connected if it's preconnected and contains at least one vertex. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty α]


end WeightedGraph
