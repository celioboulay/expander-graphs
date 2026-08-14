/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay
-/

import Mathlib.Data.Set.Card
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The Expander Mixing Lemma

For a `d`-regular `λ`-expander `G` on `n` vertices and vertex sets `A`, `B`, the number of
edges between `A` and `B` is close to what one would expect in a random `d`-regular graph:
$$ \left| e(A, B) - \frac{d}{n} |A| |B| \right| \le \lambda d \sqrt{|A| |B|}. $$

## Main definitions

* `norm_adj_matrix`: the normalised adjacency matrix `M = A / d`.
* `expander`: `G` is a `γ`-expander when every eigenvalue of `M` other than `1` is at
  most `γ` in absolute value.
* `e_AB`: the number of ordered pairs in `A × B` joined by an edge.

## Main statements

* `eq_const_of_mulVec_eq`: on a connected graph every `1`-eigenvector of `M` is constant.
* `eigval_eq_one_unique`: consequently the eigenvalue `1` is simple.
* `expander_mixing_lemma`: the inequality above.

## References
* Swastik Kopparty, *Lecture 2: Expander Graphs, Mixing lemma and Applications to randomness*,
  Topics in Pseudo-randomness and Complexity Theory (Spring 2018), Rutgers University.
  Scribes: Danny Scheinerman, Harsha Tirumala.
-/

universe u

open SimpleGraph Matrix RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (n : ℕ) (h_card : n = Nat.card V) [Fact (1 ≤ n)]
variable (d : ℕ) (h_reg : G.IsRegularOfDegree d) [Fact (1 ≤ d)] -- bc 1/d

noncomputable section

/-- The normalized adjacency matrix `M = A / d`. Since `G` is `d`-regular, `M` is the
transition matrix of the simple random walk on `G`, so its eigenvalues all lie in `[-1, 1]`. -/
def norm_adj_matrix : Matrix V V ℝ := (d : ℝ)⁻¹ • G.adjMatrix ℝ

/-- `M` is symmetric (real symmetric matrices are Hermitian), so the spectral theorem applies. -/
lemma norm_adj_matrix_isHermitian : (norm_adj_matrix G d).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold norm_adj_matrix
  rw [Matrix.transpose_smul, SimpleGraph.transpose_adjMatrix]

include h_reg in
/-- Every constant function is a `1`-eigenvector of `M`: since `G` is `d`-regular, every vertex
has exactly `d` neighbours, so averaging a constant over them returns the same constant. -/
lemma norm_adj_matrix_mulVec_const (a : ℝ) :
    (norm_adj_matrix G d) *ᵥ (Function.const V a) = Function.const V a := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp Fact.out)
  funext v
  change (((d : ℝ)⁻¹ • G.adjMatrix ℝ) *ᵥ (Function.const V a)) v = a
  rw [Matrix.smul_mulVec, Pi.smul_apply,
    SimpleGraph.adjMatrix_mulVec_const_apply_of_regular h_reg, smul_eq_mul]
  field_simp

section EigenvalueOne

/-! ### The eigenvalue `1` and its eigenspace

The mixing lemma's proof needs to know that the eigenvalue `1` of `M` is *simple*, with the
constant function spanning its eigenspace. This is where connectivity of `G` enters: the
argument below propagates the maximum of an eigenvector along walks. -/

variable {G d} {f : V → ℝ} {m : ℝ}

include h_reg in
/-- A `1`-eigenvector `f` of `M` satisfies the mean-value property: its value at `v` is the
average of its values over the `d` neighbours of `v`. -/
lemma sum_neighbors_eq_of_mulVec_eq (hf : (norm_adj_matrix G d) *ᵥ f = f) (v : V) :
    ∑ u ∈ G.neighborFinset v, f u = d * f v := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp Fact.out)
  have hv : (((d : ℝ)⁻¹ • G.adjMatrix ℝ) *ᵥ f) v = f v := congrFun hf v
  rw [Matrix.smul_mulVec, Pi.smul_apply, SimpleGraph.adjMatrix_mulVec_apply, smul_eq_mul] at hv
  field_simp at hv
  linarith [hv]

include h_reg in
/-- **Maximum propagation.** If a `1`-eigenvector attains its global maximum `m` at `v`, then it
equals `m` at every neighbour of `v`.

The point is that `f v` is the *average* of the `d` neighbouring values, all of which are `≤ m`.
An average of values `≤ m` can only equal `m` if every one of them equals `m`. -/
lemma eq_of_adj_of_isMax (hf : (norm_adj_matrix G d) *ᵥ f = f) (hmax : ∀ w, f w ≤ m)
    {v : V} (hv : f v = m) {u : V} (hadj : G.Adj v u) : f u = m := by
  -- The neighbourly deficits `m - f u` are nonnegative and sum to zero, hence all vanish.
  have hsum : ∑ u ∈ G.neighborFinset v, (m - f u) = 0 := by
    rw [Finset.sum_sub_distrib, sum_neighbors_eq_of_mulVec_eq h_reg hf v, hv,
      Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, h_reg v, nsmul_eq_mul]
    ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u _ => sub_nonneg.mpr (hmax u))).mp hsum u ((G.mem_neighborFinset v u).mpr hadj)
  linarith [hzero]

include h_reg in
/-- The maximum spreads along any walk, so a `1`-eigenvector is constant on each connected
component. -/
lemma eq_of_walk_of_isMax (hf : (norm_adj_matrix G d) *ᵥ f = f) (hmax : ∀ w, f w ≤ m)
    {v w : V} (p : G.Walk v w) (hv : f v = m) : f w = m := by
  induction p with
  | nil => exact hv
  | cons hadj _ ih => exact ih (eq_of_adj_of_isMax h_reg hf hmax hv hadj)

include h_reg in
/-- **The eigenvalue `1` of `M` is simple on a connected graph**: every `1`-eigenvector is
constant. Together with `norm_adj_matrix_mulVec_const` this pins the eigenspace down exactly. -/
theorem eq_const_of_mulVec_eq (hconn : G.Connected)
    (hf : (norm_adj_matrix G d) *ᵥ f = f) : ∃ c : ℝ, f = Function.const V c := by
  have : Nonempty V := hconn.nonempty
  obtain ⟨v₀, hv₀⟩ := Finite.exists_max f
  refine ⟨f v₀, funext fun w => ?_⟩
  obtain ⟨p⟩ := hconn.preconnected v₀ w
  exact eq_of_walk_of_isMax h_reg hf hv₀ p rfl

end EigenvalueOne

section Spectrum

/-! ### The spectrum of `M` and the definition of an expander -/

/-- The eigenvalues of `M`, indexed by the vertex set. -/
def eigval (i : V) : ℝ := (norm_adj_matrix_isHermitian G d).eigenvalues i

/-- A fixed orthonormal basis of eigenvectors of `M`, indexed by the vertex set. -/
def eigvec : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
  (norm_adj_matrix_isHermitian G d).eigenvectorBasis

lemma mulVec_eigvec (i : V) :
    (norm_adj_matrix G d) *ᵥ ⇑(eigvec G d i) = (eigval G d i) • ⇑(eigvec G d i) :=
  (norm_adj_matrix_isHermitian G d).mulVec_eigenvectorBasis i

include h_reg in
/-- `1` is an eigenvalue of `M`, witnessed by the constant eigenvector. -/
lemma exists_eigval_eq_one [Nonempty V] : ∃ i : V, eigval G d i = 1 := by
  have h1 : (1 : ℝ) ∈ spectrum ℝ (norm_adj_matrix G d) := by
    rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := (Function.const V (1 : ℝ))) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply,
        norm_adj_matrix_mulVec_const G d h_reg]
      simp
    · exact fun h => one_ne_zero (congrFun h (Classical.arbitrary V))
  rw [(norm_adj_matrix_isHermitian G d).spectrum_real_eq_range_eigenvalues] at h1
  exact h1

variable (hconn : G.Connected)

/-- Normalisation: a constant eigenvector has unit length, so `n · c² = 1`. This is the
`v₁ = 𝟙/√n` of the informal proof, stated so that no square root — and no choice of sign —
is ever needed. -/
lemma card_mul_sq_eq_one {i : V} {c : ℝ} (hc : ⇑(eigvec G d i) = Function.const V c) :
    (Fintype.card V : ℝ) * c ^ 2 = 1 := by
  have h1 : ⟪eigvec G d i, eigvec G d i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, (eigvec G d).orthonormal.1 i]
    norm_num
  rw [PiLp.inner_apply] at h1
  simp only [RCLike.inner_apply, conj_trivial] at h1
  rw [show ((eigvec G d i : EuclideanSpace ℝ V) : V → ℝ) = Function.const V c from hc] at h1
  simpa [Finset.sum_const, mul_comm, sq] using h1

include h_reg hconn in
/-- At an index carrying the eigenvalue `1`, the eigenvector is a *nonzero* constant. -/
lemma eigvec_const_of_eigval_eq_one {i : V} (hi : eigval G d i = 1) :
    ∃ c : ℝ, c ≠ 0 ∧ ⇑(eigvec G d i) = Function.const V c := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ⇑(eigvec G d i) = Function.const V c :=
    eq_const_of_mulVec_eq h_reg hconn (by rw [mulVec_eigvec, hi, one_smul])
  refine ⟨c, fun hc0 => ?_, hc⟩
  -- `c = 0` would make the normalisation `n · c² = 1` read `0 = 1`
  have := card_mul_sq_eq_one G d hc
  rw [hc0] at this
  norm_num at this

include h_reg hconn in
/-- **The eigenvalue `1` is simple.** Two distinct eigenbasis indices cannot both carry the
eigenvalue `1`: their eigenvectors would both be nonzero constants, hence not orthogonal. -/
lemma eigval_eq_one_unique {i j : V} (hi : eigval G d i = 1) (hj : eigval G d j = 1) : i = j := by
  by_contra hij
  obtain ⟨a, ha0, ha⟩ := eigvec_const_of_eigval_eq_one G d h_reg hconn hi
  obtain ⟨b, hb0, hb⟩ := eigvec_const_of_eigval_eq_one G d h_reg hconn hj
  have h0 : ⟪eigvec G d i, eigvec G d j⟫ = 0 := (eigvec G d).orthonormal.2 hij
  rw [PiLp.inner_apply] at h0
  simp only [RCLike.inner_apply, conj_trivial] at h0
  rw [show ((eigvec G d i : EuclideanSpace ℝ V) : V → ℝ) = Function.const V a from ha,
    show ((eigvec G d j : EuclideanSpace ℝ V) : V → ℝ) = Function.const V b from hb] at h0
  simp only [Function.const_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h0
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    have : Nonempty V := hconn.nonempty
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact mul_ne_zero hcard (mul_ne_zero hb0 ha0) h0

/-- `G` is a `γ`-expander when every eigenvalue of `M` other than the top eigenvalue `1`
is at most `γ` in absolute value.

On a connected `d`-regular graph the eigenvalue `1` is simple (see `eigval_eq_one_unique`),
so this really does exclude exactly one eigenvalue, as in the informal statement. -/
def expander (γ : ℝ) : Prop := ∀ i : V, eigval G d i ≠ 1 → |eigval G d i| ≤ γ

/-! ### Expansion in the eigenbasis

The two identities below are the engine of the mixing lemma: the first is the informal
proof's `⟨𝟙_A, M𝟙_B⟩ = ∑ αᵢβᵢλᵢ`, the second is Parseval's `∑ αᵢ² = ‖𝟙_A‖²`. -/

/-- Applying `M` to a vector expanded in the eigenbasis scales each coordinate by `λᵢ`. -/
lemma mulVec_eq_sum_eigvec (y : EuclideanSpace ℝ V) :
    (norm_adj_matrix G d) *ᵥ (y : V → ℝ)
      = ∑ i, (eigval G d i * ⟪eigvec G d i, y⟫) • ⇑(eigvec G d i) := by
  conv_lhs => rw [← (eigvec G d).sum_repr' y]
  rw [WithLp.ofLp_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_smul, Matrix.mulVec_smul, mulVec_eigvec, smul_smul, mul_comm]

/-- `⟨x, M y⟩ = ∑ᵢ λᵢ αᵢ βᵢ`, where `αᵢ = ⟨vᵢ, x⟩` and `βᵢ = ⟨vᵢ, y⟩`. -/
lemma dotProduct_mulVec_eq_sum (x y : EuclideanSpace ℝ V) :
    (x : V → ℝ) ⬝ᵥ ((norm_adj_matrix G d) *ᵥ (y : V → ℝ))
      = ∑ i, eigval G d i * ⟪eigvec G d i, x⟫ * ⟪eigvec G d i, y⟫ := by
  rw [mulVec_eq_sum_eigvec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  -- `x ⬝ᵥ vᵢ` is the same number as `⟪vᵢ, x⟫`
  rw [show (x : V → ℝ) ⬝ᵥ ⇑(eigvec G d i) = ⟪eigvec G d i, x⟫ by
    rw [PiLp.inner_apply]; simp [dotProduct]]
  ring

/-- **Parseval.** The eigen-coefficients of `x` have the same total square as `x` itself. -/
lemma sum_sq_inner_eq (x : EuclideanSpace ℝ V) :
    ∑ i, ⟪eigvec G d i, x⟫ ^ 2 = (x : V → ℝ) ⬝ᵥ (x : V → ℝ) := by
  have h := (eigvec G d).sum_sq_norm_inner_right x
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [h, ← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [dotProduct, sq]

end Spectrum

variable (A B : Set V) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

def indicator (S : Set V) [DecidablePred (· ∈ S)] : V → ℝ :=
  fun (v : V) => if v ∈ S then 1 else 0

/-- `e(A, B)` counts ordered pairs `(a, b) ∈ A × B` joined by an edge of `G`. -/
def e_AB : ℕ := (Finset.univ.filter (fun p : V × V => p.1 ∈ A ∧ p.2 ∈ B ∧ G.Adj p.1 p.2)).card

lemma e_AB_eq_sum_indicators :
    (e_AB G A B : ℝ) = ∑ i : V, ∑ j : V, indicator A i * indicator B j * G.adjMatrix ℝ i j := by
  unfold e_AB indicator
  rw [Finset.card_filter]
  push_cast
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [SimpleGraph.adjMatrix_apply]
  -- Both sides are `1` exactly when `p.1 ∈ A`, `p.2 ∈ B` and `G.Adj p.1 p.2` all hold,
  -- and `0` otherwise: unfold every `if` and match on the three conditions.
  by_cases hA : p.1 ∈ A <;> by_cases hB : p.2 ∈ B <;> by_cases hAdj : G.Adj p.1 p.2 <;>
    simp [hA, hB, hAdj]

/-- `𝟙_S` viewed in `EuclideanSpace`, so that inner products against the eigenbasis
are available. -/
def ind (S : Set V) [DecidablePred (· ∈ S)] : EuclideanSpace ℝ V := WithLp.toLp 2 (indicator S)

@[simp] lemma ofLp_ind : ((ind A : EuclideanSpace ℝ V) : V → ℝ) = indicator A := rfl

lemma sum_indicator : ∑ v, indicator A v = A.toFinset.card := by
  simp [indicator]

/-- `‖𝟙_A‖² = |A|`, since the indicator is idempotent. -/
lemma dotProduct_ind_self : (ind A : V → ℝ) ⬝ᵥ (ind A : V → ℝ) = A.toFinset.card := by
  rw [ofLp_ind, dotProduct, ← sum_indicator A]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v ∈ A <;> simp [indicator, h]

include h_reg in
/-- `e(A, B) = d ⟨𝟙_A, M 𝟙_B⟩`, the first line of the informal computation. -/
lemma e_AB_eq_dotProduct :
    (e_AB G A B : ℝ) = d * ((ind A : V → ℝ) ⬝ᵥ ((norm_adj_matrix G d) *ᵥ (ind B : V → ℝ))) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp Fact.out)
  rw [e_AB_eq_sum_indicators]
  -- `M = d⁻¹ • A`, so the factor `d` cancels and we are left with `𝟙_A ⬝ (A *ᵥ 𝟙_B)`
  rw [show (norm_adj_matrix G d) = (d : ℝ)⁻¹ • G.adjMatrix ℝ from rfl,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  rw [ofLp_ind, ofLp_ind, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The coefficient of `𝟙_A` along a *constant* eigenvector of value `c` is `c · |A|`.
This is the informal proof's `α₁ = ⟨𝟙_A, v₁⟩ = |A|/√n`. -/
lemma inner_eigvec_ind {i : V} {c : ℝ} (hc : ⇑(eigvec G d i) = Function.const V c) :
    ⟪eigvec G d i, ind A⟫ = c * A.toFinset.card := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, hc, ofLp_ind, Function.const_apply]
  rw [← Finset.sum_mul, sum_indicator, mul_comm]

/-- Parseval, specialised to an indicator: `∑ᵢ αᵢ² = |A|`. -/
lemma sum_sq_inner_ind : ∑ i, ⟪eigvec G d i, ind A⟫ ^ 2 = A.toFinset.card :=
  (sum_sq_inner_eq G d (ind A)).trans (dotProduct_ind_self A)

variable (hconn : G.Connected) (γ : ℝ)

include h_reg hconn in
/-- **Expander mixing lemma.** For a connected `d`-regular `γ`-expander on `n = |V|` vertices
and any two sets of vertices `A`, `B`,
$$ \left| e(A,B) - \frac{d}{n}|A||B| \right| \le \gamma\, d \sqrt{|A||B|}. $$

The estimate `e(A,B) ≈ (d/n)|A||B|` is what one expects for a random `d`-regular graph. -/
theorem expander_mixing_lemma (hγ : 0 ≤ γ) (hexp : expander G d γ) :
    |(e_AB G A B : ℝ) - (d / Fintype.card V) * A.toFinset.card * B.toFinset.card|
      ≤ γ * d * Real.sqrt (A.toFinset.card * B.toFinset.card) := by
  have : Nonempty V := hconn.nonempty
  have hcard0 : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- the distinguished index: eigenvalue `1`, constant eigenvector of value `c` with `n c² = 1`
  obtain ⟨i₀, hi₀⟩ := exists_eigval_eq_one G d h_reg
  obtain ⟨c, _, hc⟩ := eigvec_const_of_eigval_eq_one G d h_reg hconn hi₀
  have hnc : (Fintype.card V : ℝ) * c ^ 2 = 1 := card_mul_sq_eq_one G d hc
  -- `e(A,B) = d ∑ᵢ λᵢ αᵢ βᵢ`
  have key : (e_AB G A B : ℝ)
      = d * ∑ i, eigval G d i * ⟪eigvec G d i, ind A⟫ * ⟪eigvec G d i, ind B⟫ := by
    rw [e_AB_eq_dotProduct G d h_reg, dotProduct_mulVec_eq_sum]
  -- the `i₀` term is exactly the main term `(d/n)|A||B|`
  have hmain : (d : ℝ) * (eigval G d i₀ * ⟪eigvec G d i₀, ind A⟫ * ⟪eigvec G d i₀, ind B⟫)
      = (d / Fintype.card V) * A.toFinset.card * B.toFinset.card := by
    rw [hi₀, inner_eigvec_ind G d A hc, inner_eigvec_ind G d B hc,
      div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hcard0]
    linear_combination ((d : ℝ) * A.toFinset.card * B.toFinset.card) * hnc
  -- every other eigenvalue is at most `γ` in absolute value, by simplicity of the eigenvalue `1`
  have hsmall : ∀ i ∈ Finset.univ.erase i₀, |eigval G d i| ≤ γ := fun i hi =>
    hexp i fun h1 => (Finset.mem_erase.mp hi).1 (eigval_eq_one_unique G d h_reg hconn h1 hi₀)
  -- Cauchy–Schwarz on the remaining coordinates, then Parseval
  have htail : |∑ i ∈ Finset.univ.erase i₀,
        eigval G d i * ⟪eigvec G d i, ind A⟫ * ⟪eigvec G d i, ind B⟫|
      ≤ γ * Real.sqrt (A.toFinset.card * B.toFinset.card) := by
    have hA' : ∑ i ∈ Finset.univ.erase i₀, |⟪eigvec G d i, ind A⟫| ^ 2
        ≤ A.toFinset.card := by
      rw [← sum_sq_inner_ind G d A]
      simp only [sq_abs]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun i _ _ => sq_nonneg _
    have hB' : ∑ i ∈ Finset.univ.erase i₀, |⟪eigvec G d i, ind B⟫| ^ 2
        ≤ B.toFinset.card := by
      rw [← sum_sq_inner_ind G d B]
      simp only [sq_abs]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun i _ _ => sq_nonneg _
    calc |∑ i ∈ Finset.univ.erase i₀,
            eigval G d i * ⟪eigvec G d i, ind A⟫ * ⟪eigvec G d i, ind B⟫|
        ≤ ∑ i ∈ Finset.univ.erase i₀,
            |eigval G d i * ⟪eigvec G d i, ind A⟫ * ⟪eigvec G d i, ind B⟫| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.univ.erase i₀,
            γ * (|⟪eigvec G d i, ind A⟫| * |⟪eigvec G d i, ind B⟫|) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (hsmall i hi) (by positivity)
      _ = γ * ∑ i ∈ Finset.univ.erase i₀,
            |⟪eigvec G d i, ind A⟫| * |⟪eigvec G d i, ind B⟫| := by rw [Finset.mul_sum]
      _ ≤ γ * (Real.sqrt (∑ i ∈ Finset.univ.erase i₀, |⟪eigvec G d i, ind A⟫| ^ 2) *
            Real.sqrt (∑ i ∈ Finset.univ.erase i₀, |⟪eigvec G d i, ind B⟫| ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hγ
      _ ≤ γ * Real.sqrt (A.toFinset.card * B.toFinset.card) := by
          refine mul_le_mul_of_nonneg_left ?_ hγ
          rw [← Real.sqrt_mul (by positivity)]
          exact Real.sqrt_le_sqrt (mul_le_mul hA' hB' (by positivity) (by positivity))
  -- split off the main term and bound what is left
  rw [key, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), mul_add, hmain, add_sub_cancel_left,
    abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ d by positivity)]
  calc (d : ℝ) * |∑ i ∈ Finset.univ.erase i₀,
        eigval G d i * ⟪eigvec G d i, ind A⟫ * ⟪eigvec G d i, ind B⟫|
      ≤ (d : ℝ) * (γ * Real.sqrt (A.toFinset.card * B.toFinset.card)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = γ * d * Real.sqrt (A.toFinset.card * B.toFinset.card) := by ring

end
