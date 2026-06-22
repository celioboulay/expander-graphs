/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay, Dylan Sparrow, Rafael Castro
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Formalization of the book's content

## References
* [Spectral Graph Theory, Fan Chung][Chung]
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

@[expose] public section


open NNReal


structure WeightedGraph (α β : Type*) extends Graph α β where
  edgeWeight : β → ℝ≥0
  edgeDef (e : β) : e ∈ edgeSet ↔ 0 < edgeWeight e
  orientation : β → α

variable {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
variable {G : WeightedGraph α β}
variable [DecidableRel G.Adj]
variable (hα : G.vertexSet = Set.univ)
variable (hβ : G.edgeSet = Set.univ)


namespace WeightedGraph

noncomputable section

/-- `G.degree v` is the number of edges incident to `v`. -/
def degree (v : α) : ℝ≥0 :=
  (G.incidenceSet v).ncard


/-- The volume of a graph is defined as the sum of the degrees of its vertices -/
def Volume : ℝ≥0 := ∑ v : α, G.degree v


/-- We say v is an isolated vertex if dᵥ = 0. -/
def IsIsolated (v : G.vertexSet) := G.degree v = 0


/-- A graph is said to be nontrivial if it contains at least one edge. -/
def NonTrivial (G : Graph α β) := G.edgeSet ≠ ∅


open Matrix


def L : Matrix α α ℝ :=
  fun (u v : α) =>
    if u = v then (G.degree v : ℝ)
    else if G.Adj u v then -1
    else 0


def Laplacian : Matrix α α ℝ :=
  fun (u v : α) =>
    if u = v then if G.degree v = 0 then 0 else 1
    else if G.Adj u v then -1 / √ (G.degree v * G.degree u)
    else 0


def T_inv_sqrt : Matrix α α ℝ :=
  Matrix.diagonal (fun v => if G.degree v = 0 then 0 else 1 / √ (G.degree v))


/-- `Laplacian = T_inv_sqrt * L * T_inv_sqrt` -/
lemma Lap_symmetric_normalization : G.Laplacian = G.T_inv_sqrt * G.L * G.T_inv_sqrt := by
  ext u v;
  unfold Laplacian L T_inv_sqrt;
  split_ifs <;> simp_all +decide [mul_comm, mul_left_comm, div_eq_mul_inv];
  · field_simp;
    rw [ Real.sq_sqrt ( NNReal.coe_nonneg _ ) ];
  · by_cases hu : G.degree u = 0 <;> by_cases hv : G.degree v = 0 <;> simp_all +decide [degree]



/-- The Laplacian can be viewed as an operator on
the space of functions g : V(G) → R. -/
def LapOperator : (α → ℝ) →L[ℝ] (α → ℝ) :=
  (toLin' G.Laplacian).toContinuousLinearMap


/-- No multiple loops -/
def IsSimple : Prop := ∀ u, (G.degree u : ℝ) = ({v | G.Adj u v}).ncard


/-- The Laplacian Operator satisfies *big equation page 3*. -/
lemma LapOperatorFormula (hS : G.IsSimple) : ⇑G.LapOperator =
  fun g u => (1 / √ (G.degree u)) * ∑ v : α, if G.Adj u v then
      g u / √ (G.degree u) - g v / √ (G.degree v) else 0 := sorry



/-- A graph is regular of degree `d` if every vertex has degree `d`. -/
def IsRegularOfDegree (k : ℕ) := ∀ v, G.degree v = k


/-- Adjacency Matrix: `A(u, v) = 1` if `u` is adjacent to `v`, and `0` otherwise. -/
def Adjacency : Matrix α α ℝ :=
  fun u v => if G.Adj u v then 1 else 0


abbrev Identity := (1 : Matrix α α ℝ)


omit [Fintype α] in
/-- For a loopless, `k`-regular graph, `Laplacian = Identity − 1/k * Adjacency` -/
lemma LapOfRegGraph {k : ℕ+} (hLoopless : ∀ v, ¬ G.Adj v v) :
    G.IsRegularOfDegree k →
    G.Laplacian = Identity - (1 / (k : ℝ)) • G.Adjacency := by
  intro hReg; ext u v;
  unfold IsRegularOfDegree at hReg;
  have hDu : G.degree u = k := hReg u;
  have hDv : G.degree v = k := hReg v;
  unfold Laplacian Adjacency Identity;
  split_ifs <;> simp_all; ring;


/-- We say that a graph has no isolation when none of its vertices is isolated. -/
def NoIsolation := ∀ v : G.vertexSet, ¬ (G.IsIsolated v)



include hα in
/-- For a graph without isolated vertices, we have
`Laplacian = Identity - T_inv_sqrt * Adjacency * T_inv_sqrt`. -/
lemma LapOfNotIsolatedGraph (hLoopless : ∀ v, ¬ G.Adj v v) : G.NoIsolation →
  G.Laplacian = Identity - G.T_inv_sqrt * G.Adjacency * G.T_inv_sqrt := by
  intro hIso; ext u v;
  have hDu : G.degree u ≠ 0 := hIso ⟨u, by simp [hα]⟩
  have hDv : G.degree v ≠ 0 := hIso ⟨v, by simp [hα]⟩
  unfold Laplacian Adjacency Identity T_inv_sqrt;
  split_ifs <;> simp_all +decide [div_eq_mul_inv];



section BoundaryOperator

variable [DecidableRel G.Inc]

/-- `S` is the matrix whose rows are indexed by the vertices and whose columns
are indexed by the edges of G. Each column corresponding to an edgec`e = {u, v}`
has an entry `1/√dᵤ` in the row corresponding to `u`, an entry `−1/√dᵥ` in
the row corresponding to `v`, and has zero entries elsewhere. -/
def S : Matrix α β ℝ :=
  fun u e => if (G.Inc e u) then
    if G.orientation e = u then 1 / √ (G.degree u) else - 1 / √ (G.degree u)
    else 0


/-- `Laplacian = S * Sᵀ` -/
lemma LSS : G.Laplacian = G.S * (G.S)ᵀ := sorry

end BoundaryOperator



section Spectral


omit [Fintype α] in
/-- Proof that the Laplacian as defined above, is Hermitian. -/
lemma LapHermitian : G.Laplacian.IsHermitian := by
  unfold IsHermitian; simp only [conjTranspose_eq_transpose_of_trivial];
  ext u v; simp only [transpose_apply];
  unfold Laplacian;
  by_cases h : u = v
  · subst h; rfl
  · have hnot : v ≠ u := by tauto
    rw [if_neg hnot, if_neg h]
    rw [mul_comm (degree u : ℝ) (degree v : ℝ)]
    by_cases h : G.Adj v u <;> simp [Graph.adj_comm]


/-- Eigenvalues of the Laplacian Matrix in non-increasing order. -/
def lapEigvals : Fin (Fintype.card α) → ℝ :=
  Matrix.IsHermitian.eigenvalues₀ G.LapHermitian



section Rayleigh

open ContinuousLinearMap

variable {g : α → ℝ}

/-- The Dirichlet sum of a graph `G` is the sum of `(f(u) - f(v))²`
over all unordered pairs `{u, v}` for which `u` and `v` are adjacent. -/
def DirichletSum (f : α → ℝ) : ℝ :=
  ∑ u : α, ∑ v : α, if G.Adj u v then (f u - f v)^2 else 0



--lemma eigen_rayleigh : G.LapOperator.rayleighQuotient = todo := sorry

end Rayleigh


/-- The spectrum of a graph -/
def lapSpectrum (G : WeightedGraph α β) [DecidableRel G.Adj] : Set ℝ :=
  spectrum ℝ G.Laplacian


/-- `τ` denote the constant function which assigns the value `1` on each vertex -/
abbrev τ : α → ℝ := fun _ => 1 -- may change name from τ to smth else though


/-- `T_inv_sqrt * τ` is an eigenfunction of `Laplacian` with eigenvalue `0`. -/
theorem zero_eigenvalue_normalized :
  G.Laplacian.mulVec (G.T_inv_sqrt.mulVec τ) = 0 := by
  sorry


section CompleteGraph

/-- Complete Graph `Kₙ` on `n` vertices. -/
structure CompleteGraph (α β : Type*) extends WeightedGraph α β where
  completeness : ∀ (x y : vertexSet), x ≠ y ↔ ∃! e : edgeSet, IsLink e x y


/-- `0` is an eigenvalue of the Laplacian of a graph. -/
theorem zero_mem_spectrum_lapMatrix (K : CompleteGraph α β) [DecidableRel K.Adj] :
    0 ∈ lapSpectrum K.toWeightedGraph := sorry


/-- For the complete graph `Kₙ` on `n` vertices, the eigenvalues
are `0` and `n/(n − 1)` (with multiplicity `n − 1`). -/
lemma zero_mem_complete_graph_spectrum (K : CompleteGraph α β) [DecidableRel K.Adj] :
    0 ∈ lapSpectrum K.toWeightedGraph := sorry


end CompleteGraph

end Spectral

end

end WeightedGraph
