/-
Copyright (c) 2026 Celio Boulay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Celio Boulay
-/

module

public import ExpanderGraphs.chapter2

/-!
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

variable {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]

namespace UnweightedGraph

structure IsExpander (G : UnweightedGraph α β) [DecidableRel G.Adj]
    (d : ℕ) (γ : ℝ) [Fact (1 < Fintype.card α)] : Prop where
  regular : G.IsRegularOfDegree d
  spectral_gap : γ ≤ G.lapEigvals 1

structure IsCheegerExpander (G : UnweightedGraph α β) [DecidableRel G.Adj]
    (d : ℕ) (h : ℝ) : Prop where
  regular : G.IsRegularOfDegree d
  cheeger_bound : h ≤ Isoperimetry.cheeger G


variable (G : UnweightedGraph α β)

lemma IsExpander.mono {d : ℕ} {γ γ' : ℝ} [Fact (1 < Fintype.card α)]
    [DecidableRel G.Adj] (hG : G.IsExpander d γ) (hγ : γ' ≤ γ) :
    G.IsExpander d γ' :=
  ⟨hG.regular, hγ.trans hG.spectral_gap⟩


end UnweightedGraph
