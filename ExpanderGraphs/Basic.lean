/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Expander Graphs

An expander graph is a sparse graph that has strong connectivity properties.
This file states general definitions and preliminary results.

## References
* [Spectral and Algebraic Graph Theory, Daniel A. Spielman, 2025][Spielman2025]
-/


variable {V : Type*}
variable [Fintype V] [DecidableEq V] [Fact (1 < Fintype.card V)]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph.Spectral

/-- Eigenvalues of the Laplacian in non-increasing order. -/
noncomputable def graphLapEigvals : Fin (Fintype.card V) → ℝ :=
  (SimpleGraph.isHermitian_lapMatrix ℝ G).eigenvalues₀

end SimpleGraph.Spectral


namespace ExpanderGraphs



end ExpanderGraphs
