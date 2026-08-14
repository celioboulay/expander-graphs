import Mathlib.Data.Set.Card
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.Order.Archimedean.Real.Basic

universe u

open SimpleGraph

variable {V : Type u}
variable (G : SimpleGraph V) [LocallyFinite G] [DecidableRel G.Adj]
variable (n : ℕ) (h_card : n = Nat.card V) [Fact (1 ≤ n)]
variable (d : ℕ) (h_reg : G.IsRegularOfDegree d) [Fact (1 ≤ d)] -- bc 1/d

def norm_adj_matrix : Matrix V V ℝ :=
  fun (u v : V) => G.adjMatrix ℝ u v

def expander (γ : ℝ) : Prop := sorry
  -- all eigvals (but one) of the norm_adj_matrix are at most γ in absolute value

variable (A B : Set V) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

def indicator_A : V → ℝ :=
  fun (v : V) => if v ∈ A then 1 else 0

def indicator_B : V → ℝ :=
  fun (v : V) => if v ∈ B then 1 else 0
