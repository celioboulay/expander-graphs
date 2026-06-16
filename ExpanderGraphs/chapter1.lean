module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Formalization of the book's content

## References
* [Spectral Graph Theory, Fan Chung][Chung]
-/


@[expose] public section


open NNReal


@[ext]
structure WeightedGraph (α β : Type*) extends Graph α β where
  edgeWeight : β → ℝ≥0
  /-- An edge weight is greater than 0 if and only if it belongs to the edge set of the graph. -/
  edgeDef (e : β) : e ∈ edgeSet ↔ 0 < edgeWeight e

variable {α β : Type*} [DecidableEq α] [Fintype α]
variable {G : WeightedGraph α β} [∀ s, Fintype (G.incidenceSet s)]
variable [DecidableRel G.Adj]


namespace WeightedGraph

/-- `G.degree v` is the number of edges incident to `v`. -/
def degree (v : α) : ℝ≥0 :=
  Fintype.card (G.incidenceSet v)

def L : Matrix α α ℝ :=
  fun (u v : α) =>
    if u = v then (G.degree v : ℝ)
    else if G.Adj u v then -1
    else 0

noncomputable def Laplacian : Matrix α α ℝ :=
  fun (u v : α) =>
    if u = v then if G.degree v = 0 then 0 else 1
    else if G.Adj u v then -1 / Real.sqrt (G.degree v * G.degree u)
    else 0

noncomputable def T_inv_sqrt : Matrix α α ℝ :=
  fun (u v : α) =>
    if u = v then if G.degree v = 0 then 0 else 1 / Real.sqrt (G.degree v)
    else 0


lemma Lap_symmetric_normalization : G.Laplacian = G.T_inv_sqrt * G.L * G.T_inv_sqrt := by
  ext u v; -- this look more annoying to prove than it should, I may be doing things wrong there
  sorry


/-- We say v is an isolated vertex if dᵥ = 0. -/
def IsIsolated (v : α) := G.degree v = 0

/-- A graph is said to be nontrivial if it contains at least one edge. -/
def Nontrivial (G : Graph α β) := G.edgeSet ≠ ∅


/-- The Laplacian can be viewed as an operator on the space of functions g :
V(G) → R which satisfies *big equation page 3* -/
noncomputable def LapOperator : (α → ℝ) → (α → ℝ) :=
  fun (g : α → ℝ) =>
    fun (u : α) =>
      ∑ e ∈ G.incidenceSet u,
        let v := sorry
        (g u / (Real.sqrt (G.degree u)) - g v / (Real.sqrt (G.degree v)))


end WeightedGraph
