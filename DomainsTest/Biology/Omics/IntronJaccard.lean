/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.IntronJaccard
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

/-! # Regressions for the intron Jaccard index -/

set_option autoImplicit false

namespace Domains.Biology.Omics.IntronJaccard.Tests

open Finset AlignedReads

/-- One sample around the intron `(10, 20)`. Three split reads map to it, one to the alternative
acceptor `(10, 15)`, one to the alternative donor `(5, 20)` and one to the unrelated `(30, 40)`.
One non-split read spans the boundary at `10`, one spans both boundaries `10` and `20` of the short
intron, and one spans `30`. -/
private def sample : AlignedReads ℕ (Fin 6) (Fin 3) where
  split := univ
  intron := ![(10, 20), (10, 20), (10, 20), (10, 15), (5, 20), (30, 40)]
  nonSplit := univ
  spans := ![{10}, {10, 20}, {30}]

private def introns : Finset (ℕ × ℕ) := {(10, 20), (10, 15), (5, 20), (30, 40)}

private theorem introns_cover : ∀ r ∈ sample.split, sample.intron r ∈ introns := by decide

-- Six donor-associated units at `10` and five acceptor-associated units at `20`.
example : #(sample.donorObservations 10) = 6 := by decide
example : #(sample.acceptorObservations 20) = 5 := by decide

-- The read spanning both boundaries of the short intron gives two distinct units, one in each set,
-- and neither is common to both.
example : Sum.inr (1, 10) ∈ sample.donorObservations 10 ∧
    Sum.inr (1, 20) ∈ sample.acceptorObservations 20 ∧
    Sum.inr (1, 10) ∉ sample.donorObservations 10 ∩ sample.acceptorObservations 20 ∧
    Sum.inr (1, 20) ∉ sample.donorObservations 10 ∩ sample.acceptorObservations 20 := by
  decide

-- The common units are the three junction observations of `(10, 20)`; the union has
-- `4 + 4 + (2 + 1) - 3 = 8` units.
example : #(sample.donorObservations 10 ∩ sample.acceptorObservations 20) = 3 := by decide
example : #(sample.donorObservations 10 ∪ sample.acceptorObservations 20) = 8 := by decide

-- The closed form gives the same value, `3 / 8`.
example : sample.intronJaccard (10, 20) = 3 / 8 := by
  rw [sample.intronJaccard_eq (by decide) introns introns_cover]
  have h₁ : #{r ∈ sample.split | sample.intron r = (10, 20)} = 3 := by decide
  have h₂ : ∑ j' ∈ introns with j'.1 = 10, #{r ∈ sample.split | sample.intron r = j'} = 4 := by
    decide
  have h₃ : ∑ j' ∈ introns with j'.2 = 20, #{r ∈ sample.split | sample.intron r = j'} = 4 := by
    decide
  have h₄ : ∑ t ∈ ({10, 20} : Finset ℕ), #{r ∈ sample.nonSplit | t ∈ sample.spans r} = 3 := by
    decide
  simp only [← Nat.cast_sum, h₁, h₂, h₃, h₄]
  norm_num

example : sample.intronJaccard (10, 20) = 3 / 8 := by
  rw [intronJaccard]
  have h₁ : #(sample.donorObservations 10 ∩ sample.acceptorObservations 20) = 3 := by decide
  have h₂ : #(sample.donorObservations 10 ∪ sample.acceptorObservations 20) = 8 := by decide
  rw [h₁, h₂]
  norm_num

-- The observed introns may serve as the finite set of introns.
example (j : ℕ × ℕ) (hj : j.1 ≠ j.2) :
    sample.intronJaccard j =
      (#{r ∈ sample.split | sample.intron r = j} : ℝ) /
        (∑ j' ∈ sample.split.image sample.intron with j'.1 = j.1,
            (#{r ∈ sample.split | sample.intron r = j'} : ℝ) +
          ∑ j' ∈ sample.split.image sample.intron with j'.2 = j.2,
            (#{r ∈ sample.split | sample.intron r = j'} : ℝ) +
          ∑ t ∈ {j.1, j.2}, (#{r ∈ sample.nonSplit | t ∈ sample.spans r} : ℝ) -
          #{r ∈ sample.split | sample.intron r = j}) :=
  sample.intronJaccard_eq hj _ fun _ hr => mem_image_of_mem _ hr

-- No read gives evidence at `50` or `60`: the denominator is `0`, and the index takes the value
-- `0`.
example : ¬ 0 < #(sample.donorObservations 50 ∪ sample.acceptorObservations 60) := by
  rw [sample.card_donorObservations_union_acceptorObservations_pos_iff (j := (50, 60))]
  decide

example : sample.intronJaccard (50, 60) = 0 :=
  sample.intronJaccard_eq_zero_of_no_evidence (by decide) (by decide)

-- A boundary read at `30` alone makes the denominator of `(30, 35)` positive.
example : 0 < #(sample.donorObservations 30 ∪ sample.acceptorObservations 35) :=
  (sample.card_donorObservations_union_acceptorObservations_pos_iff (j := (30, 35))).2
    (.inr ⟨2, by decide, .inl (by decide)⟩)

-- The pseudocount ratio is `1 / 2` when there is no evidence, inside `(0, 1)`.
example : ((#(sample.donorObservations 50 ∩ sample.acceptorObservations 60) : ℝ) + 1) /
    (#(sample.donorObservations 50 ∪ sample.acceptorObservations 60) + 2 * 1) = 1 / 2 := by
  have h₁ : #(sample.donorObservations 50 ∩ sample.acceptorObservations 60) = 0 := by decide
  have h₂ : #(sample.donorObservations 50 ∪ sample.acceptorObservations 60) = 0 := by decide
  rw [h₁, h₂]
  norm_num

example : ((#(sample.donorObservations 10 ∩ sample.acceptorObservations 20) : ℝ) + 1 / 2) /
    (#(sample.donorObservations 10 ∪ sample.acceptorObservations 20) + 2 * (1 / 2)) ∈
      Set.Ioo 0 1 :=
  sample.pseudocount_ratio_mem_Ioo (10, 20) (by norm_num)

/-- A degenerate intron whose donor and acceptor coincide, with one non-split read spanning that
site: its boundary observation lies in both sets, so `d ≠ a` cannot be dropped from
`donorObservations_inter_acceptorObservations`. -/
private def degenerate : AlignedReads ℕ (Fin 1) (Fin 1) where
  split := univ
  intron := ![(7, 7)]
  nonSplit := univ
  spans := ![{7}]

example : degenerate.donorObservations 7 ∩ degenerate.acceptorObservations 7 ≠
    {r ∈ degenerate.split | degenerate.intron r = (7, 7)}.map Function.Embedding.inl := by
  decide

end Domains.Biology.Omics.IntronJaccard.Tests
