import ExpanderGraphs.GraphPartitioning
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite

variable {V : Type*} [Fintype V]
variable (n : ℕ) [hV : Fact (Fintype.card V = n)] [Fact (1 < n)]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (S T : Finset V)
variable (nS : ℕ) (hnS : S.card = nS) (nT : ℕ) (hnT : T.card = nT)
variable (d : ℕ) (hG : G.IsRegularOfDegree d)

open GraphPartitioning.Isoperimetry

/-- The ordered edge set from a subset `S` to a subset `T` in a graph `G`.
Given two subsets of vertices `S` and `T`, `\vec E(S, T)`
is the set of all directed pairs `(u, v)` such that `u ∈ S`, `v ∈ T`,
and there is an edge between `u` and `v` in `G`. -/
def orderedEdgeFinset (S T : Finset V) : Finset (V × V) :=
  (S ×ˢ T).filter (fun p => G.Adj p.1 p.2)

/-- Number of edges in orderedEdgeFinset -/
def OES (S T : Finset V) : ℝ :=
  (orderedEdgeFinset G S T).card


variable (l : ℝ) -- the max eigenvalue

def vecOnes : V → ℝ := fun _ => 1


lemma OES_indicator_prod :
  OES G S T = ∑ u : V, ∑ v : V, setIndicator S u * G.adjMatrix ℝ u v * setIndicator T v := by
  sorry


theorem ExpanderMixingLemma :
  abs (OES G S T - d * (nS * nT) / n) ≤ l * d * Real.sqrt (nS * nT) := by
  sorry
