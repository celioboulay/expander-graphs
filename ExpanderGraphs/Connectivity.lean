/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay
-/

module

public import ExpanderGraphs.chapter1

/-!
# Connectivity for general graphs
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section


variable {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
variable {G : UnweightedGraph α β} [DecidableRel G.Adj]
variable (hα : G.vertexSet = Set.univ) (hβ : G.edgeSet = Set.univ)

open Graph
open NNReal

namespace UnweightedGraph

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


/-- We define the edge boundary ∂S of S to consist of all edges with exactly one endpoint in S. -/
def edgeBoundary (S : Set α) : Set β :=
  {e ∈ G.edgeSet | ∃ a ∈ S, ∃ b ∈ Sᶜ, G.IsLink e a b}


/-- We can define the vertex boundary δS of S to be the set of
all vertices v not in S but adjacent to some vertex in S. -/
def vertexBoundary (S : Set α) : Set α :=
  {v ∉ S | ∃ u : S, ∃ e : G.edgeSet, G.IsLink e u v}


include hβ in
/-- If there is a walk going from S to Sᶜ then
there is a least on edge that goes from S to Sᶜ. -/
lemma walk_crossing (S : Set α) {u v : α} (hW : G.Walk u v) :
    u ∈ S → v ∉ S → ∃ e, e ∈ G.edgeBoundary S := by
  induction hW with
  | nil =>
    intro hu hv
    exact (hv hu).elim
  | cons h p ih =>
      rename_i x y z
      intro hx hz
      by_cases hy : y ∈ S
      · exact ih hy hz
      · rw [Adj] at h
        unfold edgeBoundary
        simp
        obtain ⟨e, he⟩ := h
        grind


include hβ in
/-- In a connected graph, every set of vertices, different from ∅ and univ,
has non empty edgeBoundary: ∂S ≠ ∅. -/
lemma connected_non_empty_edge_boundary (h : G.Connected) (S : Set α)
  (hS_nonempty : S.Nonempty) (hS_ne_univ : S ≠ Set.univ) :
  Nonempty (G.edgeBoundary S) := by
  rcases hS_nonempty with ⟨u, hu⟩
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by grind;
  have h_path := h.preconnected u v
  rw [Reachable] at h_path;
  rcases h_path with ⟨p⟩
  simp only [nonempty_subtype];
  exact walk_crossing hβ S p hu hv


end UnweightedGraph
