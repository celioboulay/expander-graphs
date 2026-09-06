/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

/-!
# Greedy colouring

This file proves the greedy colouring bound `χ(G) ≤ Δ(G) + 1`: a finite simple graph whose
vertices all have degree at most `d` can be properly coloured with `d + 1` colours.

## Main statements

* `exists_color_not_used`: a vertex of degree at most `d` always leaves one of `d + 1` colours
  unused among its coloured neighbours.
* `exists_coloring_on`: every finite set of vertices admits a proper colouring with `d + 1`
  colours.
* `chromaticNumber_le_maxDegree_add_one`: the bound `χ(G) ≤ d + 1` for any `d ≥ Δ(G)`, and
  `chromaticNumber_le_maxDegree_add_one'` for the usual form `χ(G) ≤ Δ(G) + 1`.
-/

open Fintype Function

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}

/-- A vertex `a` has at most `d` neighbours, so among `d + 1` colours there is always one that
no neighbour of `a` lying in `s` uses. -/
lemma exists_color_not_used (hd : G.maxDegree ≤ d) (a : V) (s : Finset V) (c : V → Fin (d + 1)) :
    ∃ x : Fin (d + 1), ∀ v ∈ s, G.Adj a v → c v ≠ x := by
  classical
  -- `T` collects the colours already taken by the neighbours of `a` inside `s`.
  set T : Finset (Fin (d + 1)) := ((G.neighborFinset a) ∩ s).image c with hT
  have hcard : T.card < Fintype.card (Fin (d + 1)) :=
    calc T.card ≤ ((G.neighborFinset a) ∩ s).card := Finset.card_image_le
      _ ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree a := G.card_neighborFinset_eq_degree a
      _ ≤ G.maxDegree := G.degree_le_maxDegree a
      _ ≤ d := hd
      _ < d + 1 := Nat.lt_succ_self d
      _ = Fintype.card (Fin (d + 1)) := (Fintype.card_fin _).symm
  -- `T` is therefore not all of `Fin (d + 1)`, so some colour escapes it.
  obtain ⟨x, hx⟩ : ∃ x : Fin (d + 1), x ∉ T := by
    by_contra h
    push Not at h
    rw [Finset.eq_univ_iff_forall.mpr h, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  refine ⟨x, fun v hv hadj hcv => hx ?_⟩
  rw [hT]
  exact Finset.mem_image.mpr
    ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a v).mpr hadj, hv⟩, hcv⟩

/-- **Greedy colouring.** Every finite set of vertices can be properly coloured with `d + 1`
colours, by induction on the set of vertices coloured so far. -/
lemma exists_coloring_on (hd : G.maxDegree ≤ d) (s : Finset V) :
    ∃ c : V → Fin (d + 1), ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      -- recolour `a` with a colour free among those of its already-coloured neighbours
      obtain ⟨x, hx⟩ := exists_color_not_used G hd a s c
      refine ⟨Function.update c a x, fun u hu v hv hadj => ?_⟩
      -- an already-coloured vertex differs from `a`, since `a ∉ s`
      have hne : ∀ w ∈ s, w ≠ a := by rintro w hw rfl; exact ha hw
      rcases Finset.mem_insert.mp hu with rfl | hu' <;>
        rcases Finset.mem_insert.mp hv with rfl | hv'
      · exact absurd hadj G.irrefl
      · rw [Function.update_self, Function.update_of_ne (hne v hv')]
        exact (hx v hv' hadj).symm
      · rw [Function.update_self, Function.update_of_ne (hne u hu')]
        exact hx u hu' hadj.symm
      · rw [Function.update_of_ne (hne u hu'), Function.update_of_ne (hne v hv')]
        exact hc u hu' v hv' hadj

/-- Any upper bound `d` on the maximum degree bounds the chromatic number by `d + 1`. -/
theorem chromaticNumber_le_maxDegree_add_one (hd : G.maxDegree ≤ d) :
    G.chromaticNumber ≤ d + 1 := by
  obtain ⟨c, hc⟩ := exists_coloring_on G hd Finset.univ
  exact Colorable.chromaticNumber_le
    ⟨Coloring.mk c fun {u v} hadj => hc u (Finset.mem_univ u) v (Finset.mem_univ v) hadj⟩

/-- The usual form of the greedy bound: `χ(G) ≤ Δ(G) + 1`. -/
theorem chromaticNumber_le_maxDegree_add_one' :
    G.chromaticNumber ≤ G.maxDegree + 1 :=
  chromaticNumber_le_maxDegree_add_one G le_rfl

end SimpleGraph
