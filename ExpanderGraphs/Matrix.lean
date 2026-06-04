/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

import ExpanderGraphs.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Graph Matrices

This file defines essential properties about matrices of graphs
that were only available for SimpleGraph in mathlib.
-/

namespace GraphMatrix

variable {α β : Type*}
variable (G : Graph α β)


/-- `A : Matrix α α ℕ` is qualified as the adjacency
matrix of a multigraph if `A` is symmetric. -/
def isMultiAdjMatrix (A : Matrix α α ℕ) : Prop :=
  A.IsSymm


/-- `adjMultiplicity u v` is the number of edges connecting `u` and `v`.
We use the convention that if `u` has a self-loop, this loop counts twice. -/
noncomputable def adjMultiplicity (G : Graph α β) (u v : α) : ℕ :=
  {e : G.edgeSet | G.IsLink e u v}.ncard


/-- `adjMatrixMulti G` is the adjacency matrix the multigraph `G` -/
noncomputable def adjMatrixMulti (G : Graph α β) : Matrix α α ℝ :=
  fun u v => adjMultiplicity G u v


/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree (G : Graph α β) (v : α) [Fintype (G.incidenceSet v)] : ℕ :=
  Fintype.card (G.incidenceSet v)


end GraphMatrix
