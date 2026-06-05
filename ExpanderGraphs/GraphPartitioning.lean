/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Expander Graphs

An expander graph is a sparse graph that has strong connectivity properties.
This file states the main general definitions and early results.

## References
* [Spectral and Algebraic Graph Theory, Daniel A. Spielman, 2025][Spielman2025]
-/

namespace GraphPartitioning

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [Finite V]

/-- The Edge Boundary of a set `S`, denoted `∂S`, is `∂S = E(S, Sᶜ)`.\
This is the set of edges emanating from the set S to its complement. -/
def boundary (S : Set V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∃ a ∈ S, ∃ b ∈ Sᶜ, e = s(a, b)}


/-- The isoperimetric ratio of S is defined as `θ(S) = |∂S| / |S|` -/
noncomputable def isoperimetricRatio (S : Set V) : ℝ :=
  (boundary G S).ncard / S.ncard


/-- The Edge Expansion of a graph is defined as `θ = min |∂S| / |S|`
over all subsets `S` such that `0 < |S| ≤ n / 2`. -/
noncomputable def isoperimetricRatioGraph : ℝ :=
  let n : ℝ := (Nat.card V : ℝ)
  sInf ((fun S ↦ isoperimetricRatio G S) '' {S : Set V | 0 < S.ncard ∧ (S.ncard : ℝ) ≤ n / 2})


/-- The isoperimetricRatio of `G` is strictly positive if and only if `G` is connected. -/
theorem isoperimetric_positive_iff_connected :
  0 < isoperimetricRatioGraph G ↔ G.Connected := by
  sorry


end GraphPartitioning
