/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import Mathlib.Data.Set.Card
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Preliminaries

This file defines essential properties about graphs (such as connectivity)
that were only available for SimpleGraph in mathlib (as of Jun 2026).
-/

namespace Graph

variable {α β : Type*}
variable (G : Graph α β)


/-- A finite graph is a graph in which the vertex set and the edge set are finite sets. -/
def IsFinite : Prop :=
  Finite G.vertexSet ∧ Finite G.edgeSet


/-- A walk is a sequence of adjacent vertices.  For vertices `u v : G.vertexSet ⊆ α`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`. -/
inductive Walk (G : Graph α β) : α → α → Type _
  | nil {v : α} (hv : v ∈ G.vertexSet) : G.Walk v v
  | cons {u v w : α} (e : β) (h_link : G.IsLink e u v) (p : G.Walk v w) : G.Walk u w
  deriving DecidableEq


/-- Two vertices are *reachable* if there is a walk between them. -/
def Reachable (u v : α) : Prop := Nonempty (G.Walk u v)

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : G.vertexSet, G.Reachable u v

/-- A graph is connected if it's preconnected and contains at least one vertex.
There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : Preconnected G
  protected [nonempty : Nonempty G.vertexSet]


end Graph
