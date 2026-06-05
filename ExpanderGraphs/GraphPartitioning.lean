/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import ExpanderGraphs.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Graph Partitioning

This file defines isoperimetric ratio, and prove results about
its relation to the second-smallest eigenvalue of the Laplacian.

## References
* [Spectral and Algebraic Graph Theory, Daniel A. Spielman, 2025][Spielman2025]
-/

namespace GraphPartitioning

namespace Isoperimetry

variable {V : Type*}
variable [Fintype V] (G : SimpleGraph V)
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



variable [DecidableEq V] [Fact (1 < Fintype.card V)]
variable [DecidableRel G.Adj]

open SimpleGraph.Spectral

/-- For every `S ⊂ V`, `θ(S) ≥ λ₂(1 − s)`, where `s = |S|/|V|`. -/
theorem graphLapEigvals_mul_le_isoperimetricRatio (S : Set V) :
  let l₂ : ℝ := graphLapEigvals G 1
  let s  : ℝ := S.ncard / Nat.card V
  l₂ * (1 - s) ≤ isoperimetricRatio G S := by
  sorry


/-- `θ(G) ≥ λ₂ / 2`. -/
theorem graphLapEigvals_div_two_le_isoperimetricRatioGraph :
  let l₂ := (graphLapEigvals G 1)
  l₂ / 2 ≤ isoperimetricRatioGraph G := by
  sorry

namespace Connectivity

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
/-- The isoperimetricRatio of `G` is strictly positive if and only if `G` is connected. -/
theorem isoperimetricRatioGraph_pos_iff_connected :
  0 < isoperimetricRatioGraph G ↔ G.Connected := by
  sorry

end Connectivity

end Isoperimetry

end GraphPartitioning
