/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sum
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The intron Jaccard index

The splice metric of FRASER 2.0: I. F. Scheller, K. Lutz, C. Mertes, V. A. Yépez and J. Gagneur,
*Improved detection of aberrant splicing with FRASER 2.0 and the intron Jaccard index*, American
Journal of Human Genetics 110 (2023), 2056–2067 (doi:10.1016/j.ajhg.2023.10.014), Material and
methods, “Splicing quantification with the intron Jaccard index” and “Denoising autoencoder”.

## Model

One RNA-seq sample is given by its aligned reads (`AlignedReads`). An intron is its ordered
donor–acceptor pair `(d, a) : Site × Site`. Each split read maps exactly to one intron; each
non-split read spans the exon–intron boundaries at a finite set of splice sites. The reads are
counted in *evidence units*, of type `ι ⊕ κ × Site`: a split read `r : ι` gives one junction
observation `Sum.inl r`, and a non-split read `r : κ` gives one boundary observation
`Sum.inr (r, t)` at each splice site `t` whose boundary it spans. So a non-split read that spans
both boundaries of a short intron gives two distinct units.

At a splice site `d`, the donor-associated observations (`donorObservations`) are the junction
observations of the introns with donor `d` and the boundary observations at `d`; the
acceptor-associated observations (`acceptorObservations`) at `a` are defined in the same way. The
intron Jaccard index of `j = (d, a)` (`intronJaccard`) is the Jaccard index `|D ∩ A| / |D ∪ A|`
of the donor-associated observations `D` at `d` and the acceptor-associated observations `A`
at `a`. With Lean's convention `x / 0 = 0` it is `0` when `D ∪ A` is empty, where the ratio is
undefined.

## Main results

Write `s j'` for the number of split reads mapping exactly to the intron `j'`, and `u t` for the
number of non-split reads spanning the boundary at the splice site `t`.

* `donorObservations_inter_acceptorObservations`: for `d ≠ a`, the units common to `D` and `A`
  are exactly the junction observations of `j = (d, a)` itself, so `|D ∩ A| = s j`
  (`card_donorObservations_inter_acceptorObservations`).
* `intronJaccard_eq`: the closed form
  `J = s j / (∑_{j' ∈ L} s j' + ∑_{j' ∈ R} s j' + ∑_{t ∈ {d, a}} u t - s j)`, where `L` and `R`
  are the introns with donor `d` and with acceptor `a` among any finite set of introns that
  contains the intron of every split read;
  `cast_card_donorObservations_union_acceptorObservations` is the closed form of the denominator.
* `card_donorObservations_union_acceptorObservations_pos_iff`: the denominator `|D ∪ A|` is
  positive exactly when some read gives evidence at `d` or `a`; otherwise `intronJaccard` is `0`
  (`intronJaccard_eq_zero_of_no_evidence`).
* `intronJaccard_nonneg`, `intronJaccard_le_one`: `0 ≤ J ≤ 1`.
* `pseudocount_ratio_mem_Ioo`: with the numerator `k = |D ∩ A|`, the denominator `n = |D ∪ A|`
  and a pseudocount `α > 0`, the pseudocount-smoothed ratio `(k + α) / (n + 2α)`, whose logit
  FRASER 2.0 feeds to its denoising autoencoder, lies in `(0, 1)`, also when `n = 0`.

This file does not model read alignment or the filtering of introns, nor the rest of FRASER 2.0:
the autoencoder that predicts `J`, the beta-binomial test of `k` given `n` (the beta-binomial
mean is `ProbabilityTheory.sum_mul_betaBinomialPMF`) and the multiple-testing corrections.
-/

@[expose] public section

set_option autoImplicit false

namespace Domains.Biology.Omics.IntronJaccard

open Finset

/-- **Aligned reads of one RNA-seq sample.** An intron is its donor–acceptor pair `(d, a)` of
splice sites of type `Site`, so introns with the same donor and the same acceptor are equal. Each
split read `r ∈ split` maps exactly to the intron `intron r`; each non-split read `r ∈ nonSplit`
spans the exon–intron boundaries at the splice sites `spans r`. -/
structure AlignedReads (Site ι κ : Type*) where
  /-- The split reads of the sample. -/
  split : Finset ι
  /-- The intron, as a donor–acceptor pair, to which a split read maps exactly. -/
  intron : ι → Site × Site
  /-- The non-split reads of the sample. -/
  nonSplit : Finset κ
  /-- The splice sites whose exon–intron boundary a non-split read spans. -/
  spans : κ → Finset Site

namespace AlignedReads

variable {Site ι κ : Type*} [DecidableEq Site] (x : AlignedReads Site ι κ)

/-- **Donor-associated observations** at the splice site `d`, as evidence units: the junction
observations `Sum.inl r` of the split reads `r` that map to an intron with donor `d`, and the
boundary observations `Sum.inr (r, d)` at `d` of the non-split reads `r` that span the boundary
at `d`. -/
def donorObservations (d : Site) : Finset (ι ⊕ κ × Site) :=
  {r ∈ x.split | (x.intron r).1 = d}.disjSum
    ({r ∈ x.nonSplit | d ∈ x.spans r}.map (Function.Embedding.sectL κ d))

/-- **Acceptor-associated observations** at the splice site `a`, as evidence units: the junction
observations `Sum.inl r` of the split reads `r` that map to an intron with acceptor `a`, and the
boundary observations `Sum.inr (r, a)` at `a` of the non-split reads `r` that span the boundary
at `a`. -/
def acceptorObservations (a : Site) : Finset (ι ⊕ κ × Site) :=
  {r ∈ x.split | (x.intron r).2 = a}.disjSum
    ({r ∈ x.nonSplit | a ∈ x.spans r}.map (Function.Embedding.sectL κ a))

@[simp]
theorem inl_mem_donorObservations {r : ι} {d : Site} :
    Sum.inl r ∈ x.donorObservations d ↔ r ∈ x.split ∧ (x.intron r).1 = d := by
  simp [donorObservations]

@[simp]
theorem inr_mem_donorObservations {r : κ} {t d : Site} :
    Sum.inr (r, t) ∈ x.donorObservations d ↔ r ∈ x.nonSplit ∧ d ∈ x.spans r ∧ t = d := by
  simp [donorObservations, and_assoc, eq_comm]

@[simp]
theorem inl_mem_acceptorObservations {r : ι} {a : Site} :
    Sum.inl r ∈ x.acceptorObservations a ↔ r ∈ x.split ∧ (x.intron r).2 = a := by
  simp [acceptorObservations]

@[simp]
theorem inr_mem_acceptorObservations {r : κ} {t a : Site} :
    Sum.inr (r, t) ∈ x.acceptorObservations a ↔ r ∈ x.nonSplit ∧ a ∈ x.spans r ∧ t = a := by
  simp [acceptorObservations, and_assoc, eq_comm]

/-- The donor-associated observations at `d` are the split reads that map to an intron with donor
`d` and the non-split reads that span the boundary at `d`, one unit each. -/
theorem card_donorObservations (d : Site) :
    #(x.donorObservations d) =
      #{r ∈ x.split | (x.intron r).1 = d} + #{r ∈ x.nonSplit | d ∈ x.spans r} := by
  simp [donorObservations, card_disjSum]

/-- The acceptor-associated observations at `a` are the split reads that map to an intron with
acceptor `a` and the non-split reads that span the boundary at `a`, one unit each. -/
theorem card_acceptorObservations (a : Site) :
    #(x.acceptorObservations a) =
      #{r ∈ x.split | (x.intron r).2 = a} + #{r ∈ x.nonSplit | a ∈ x.spans r} := by
  simp [acceptorObservations, card_disjSum]

/-- The split reads that map to an intron with a given donor (or acceptor) are counted by summing,
over the introns with that donor (or acceptor) in any finite set `I` that contains the intron of
every split read, the numbers of split reads that map exactly to each. -/
private theorem card_filter_eq_sum (I : Finset (Site × Site)) (hI : ∀ r ∈ x.split, x.intron r ∈ I)
    (f : Site × Site → Site) (t : Site) :
    #{r ∈ x.split | f (x.intron r) = t} =
      ∑ j' ∈ I with f j' = t, #{r ∈ x.split | x.intron r = j'} := by
  rw [card_eq_sum_card_fiberwise (f := x.intron) (t := {j' ∈ I | f j' = t})]
  · refine sum_congr rfl fun j' hj' => ?_
    rw [filter_filter]
    refine congrArg card (filter_congr fun r _ => ?_)
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨(mem_filter.1 hj').2, rfl⟩
  · intro r hr
    simp only [coe_filter, Set.mem_ofPred_eq] at hr ⊢
    exact ⟨hI r hr.1, hr.2⟩

variable [DecidableEq ι] [DecidableEq κ]

/-- **Intron Jaccard index** of the intron `j = (d, a)` in one sample (Scheller et al. 2023): the
Jaccard index `|D ∩ A| / |D ∪ A|` of the donor-associated observations `D` at `d` and the
acceptor-associated observations `A` at `a`, counted in evidence units. With the convention
`x / 0 = 0` it is `0` when no read gives evidence at `d` or `a`
(`intronJaccard_eq_zero_of_no_evidence`), where the ratio is undefined. For `d ≠ a` it has a
closed form in split and non-split read counts (`intronJaccard_eq`). -/
noncomputable def intronJaccard (j : Site × Site) : ℝ :=
  #(x.donorObservations j.1 ∩ x.acceptorObservations j.2) /
    #(x.donorObservations j.1 ∪ x.acceptorObservations j.2)

/-- **The common units are the junction observations of the intron itself.** For an intron
`j = (d, a)` with `d ≠ a`, a unit is both donor-associated at `d` and acceptor-associated at `a`
exactly when it is the junction observation of a split read that maps to `j`: a junction
observation of another intron misses `d` or `a`, and boundary observations at `d` and at `a` are
distinct units. So the intron Jaccard index is the fraction of the units at `d` or `a` that support
splicing of exactly `j`. -/
theorem donorObservations_inter_acceptorObservations {j : Site × Site} (hj : j.1 ≠ j.2) :
    x.donorObservations j.1 ∩ x.acceptorObservations j.2 =
      {r ∈ x.split | x.intron r = j}.map Function.Embedding.inl := by
  ext (r | ⟨r, t⟩)
  · simp only [mem_inter, inl_mem_donorObservations, inl_mem_acceptorObservations, mem_map,
      mem_filter, Function.Embedding.inl_apply, Sum.inl.injEq, exists_eq_right, Prod.ext_iff]
    tauto
  · simp only [mem_inter, inr_mem_donorObservations, inr_mem_acceptorObservations, mem_map,
      Function.Embedding.inl_apply, reduceCtorEq, and_false, exists_false, iff_false, not_and]
    rintro ⟨-, -, rfl⟩ - - h
    exact hj h

/-- `|D ∩ A| = s j`: the numerator of the intron Jaccard index of `j = (d, a)`, `d ≠ a`, is the
number of split reads that map exactly to `j`. -/
theorem card_donorObservations_inter_acceptorObservations {j : Site × Site} (hj : j.1 ≠ j.2) :
    #(x.donorObservations j.1 ∩ x.acceptorObservations j.2) = #{r ∈ x.split | x.intron r = j} := by
  rw [x.donorObservations_inter_acceptorObservations hj, card_map]

/-- **The denominator in closed form.** For an intron `j = (d, a)` with `d ≠ a` and any finite set
`I` of introns that contains the intron of every split read,
`|D ∪ A| = ∑_{j' ∈ L} s j' + ∑_{j' ∈ R} s j' + ∑_{t ∈ {d, a}} u t - s j`, where `L` and `R` are
the introns of `I` with donor `d` and with acceptor `a`, `s j'` is the number of split reads that
map exactly to `j'` and `u t` the number of non-split reads that span the boundary at `t`. -/
theorem cast_card_donorObservations_union_acceptorObservations {j : Site × Site} (hj : j.1 ≠ j.2)
    (I : Finset (Site × Site)) (hI : ∀ r ∈ x.split, x.intron r ∈ I) :
    (#(x.donorObservations j.1 ∪ x.acceptorObservations j.2) : ℝ) =
      ∑ j' ∈ I with j'.1 = j.1, (#{r ∈ x.split | x.intron r = j'} : ℝ) +
        ∑ j' ∈ I with j'.2 = j.2, (#{r ∈ x.split | x.intron r = j'} : ℝ) +
        ∑ t ∈ {j.1, j.2}, (#{r ∈ x.nonSplit | t ∈ x.spans r} : ℝ) -
        #{r ∈ x.split | x.intron r = j} := by
  have h := card_union_add_card_inter (x.donorObservations j.1) (x.acceptorObservations j.2)
  rw [x.card_donorObservations_inter_acceptorObservations hj, x.card_donorObservations,
    x.card_acceptorObservations, x.card_filter_eq_sum I hI Prod.fst,
    x.card_filter_eq_sum I hI Prod.snd] at h
  rw [sum_pair hj]
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  linarith

/-- **Closed form of the intron Jaccard index** (Scheller et al. 2023). For an intron `j = (d, a)`
with `d ≠ a` and any finite set `I` of introns that contains the intron of every split read,
`J = s j / (∑_{j' ∈ L} s j' + ∑_{j' ∈ R} s j' + ∑_{t ∈ {d, a}} u t - s j)`, where `L` and `R` are
the introns of `I` with donor `d` and with acceptor `a`, `s j'` is the number of split reads that
map exactly to `j'` and `u t` the number of non-split reads that span the boundary at `t`. Both
sides are `0` when the denominator is. -/
theorem intronJaccard_eq {j : Site × Site} (hj : j.1 ≠ j.2) (I : Finset (Site × Site))
    (hI : ∀ r ∈ x.split, x.intron r ∈ I) :
    x.intronJaccard j =
      (#{r ∈ x.split | x.intron r = j} : ℝ) /
        (∑ j' ∈ I with j'.1 = j.1, (#{r ∈ x.split | x.intron r = j'} : ℝ) +
          ∑ j' ∈ I with j'.2 = j.2, (#{r ∈ x.split | x.intron r = j'} : ℝ) +
          ∑ t ∈ {j.1, j.2}, (#{r ∈ x.nonSplit | t ∈ x.spans r} : ℝ) -
          #{r ∈ x.split | x.intron r = j}) := by
  rw [intronJaccard, ← x.cast_card_donorObservations_union_acceptorObservations hj I hI,
    x.card_donorObservations_inter_acceptorObservations hj]

/-- **The denominator is positive exactly when some read gives evidence at `d` or `a`**: a split
read that maps to an intron with donor `d` or with acceptor `a`, or a non-split read that spans the
boundary at `d` or at `a`. -/
theorem card_donorObservations_union_acceptorObservations_pos_iff {j : Site × Site} :
    0 < #(x.donorObservations j.1 ∪ x.acceptorObservations j.2) ↔
      (∃ r ∈ x.split, (x.intron r).1 = j.1 ∨ (x.intron r).2 = j.2) ∨
        ∃ r ∈ x.nonSplit, j.1 ∈ x.spans r ∨ j.2 ∈ x.spans r := by
  rw [card_pos, union_nonempty, donorObservations, acceptorObservations]
  simp only [Finset.Nonempty, mem_disjSum, mem_filter, mem_map, Function.Embedding.sectL_apply]
  constructor
  · rintro (⟨_, (⟨r, ⟨hr, h⟩, -⟩ | ⟨_, ⟨r, ⟨hr, h⟩, -⟩, -⟩)⟩ |
      ⟨_, (⟨r, ⟨hr, h⟩, -⟩ | ⟨_, ⟨r, ⟨hr, h⟩, -⟩, -⟩)⟩)
    · exact .inl ⟨r, hr, .inl h⟩
    · exact .inr ⟨r, hr, .inl h⟩
    · exact .inl ⟨r, hr, .inr h⟩
    · exact .inr ⟨r, hr, .inr h⟩
  · rintro (⟨r, hr, h | h⟩ | ⟨r, hr, h | h⟩)
    · exact .inl ⟨_, .inl ⟨r, ⟨hr, h⟩, rfl⟩⟩
    · exact .inr ⟨_, .inl ⟨r, ⟨hr, h⟩, rfl⟩⟩
    · exact .inl ⟨_, .inr ⟨_, ⟨r, ⟨hr, h⟩, rfl⟩, rfl⟩⟩
    · exact .inr ⟨_, .inr ⟨_, ⟨r, ⟨hr, h⟩, rfl⟩, rfl⟩⟩

/-- **No evidence.** When no split read maps to an intron with donor `d` or with acceptor `a`
and no non-split read spans the boundary at `d` or at `a`, the ratio `|D ∩ A| / |D ∪ A|` is
`0 / 0`, which is undefined, and `intronJaccard` takes Lean's value `0` for it. -/
theorem intronJaccard_eq_zero_of_no_evidence {j : Site × Site}
    (hsplit : ∀ r ∈ x.split, (x.intron r).1 ≠ j.1 ∧ (x.intron r).2 ≠ j.2)
    (hnonSplit : ∀ r ∈ x.nonSplit, j.1 ∉ x.spans r ∧ j.2 ∉ x.spans r) :
    x.intronJaccard j = 0 := by
  have h : ¬ 0 < #(x.donorObservations j.1 ∪ x.acceptorObservations j.2) := by
    rw [card_donorObservations_union_acceptorObservations_pos_iff]
    rintro (⟨r, hr, h | h⟩ | ⟨r, hr, h | h⟩)
    exacts [(hsplit r hr).1 h, (hsplit r hr).2 h, (hnonSplit r hr).1 h, (hnonSplit r hr).2 h]
  rw [intronJaccard, Nat.eq_zero_of_not_pos h, Nat.cast_zero, div_zero]

/-- The intron Jaccard index is nonnegative. -/
theorem intronJaccard_nonneg (j : Site × Site) : 0 ≤ x.intronJaccard j := by
  unfold intronJaccard
  positivity

/-- The intron Jaccard index is at most `1`. -/
theorem intronJaccard_le_one (j : Site × Site) : x.intronJaccard j ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast card_le_card inter_subset_union) (Nat.cast_nonneg _)

/-- **The pseudocount-smoothed ratio lies in `(0, 1)`.** With the numerator `k = |D ∩ A|` and the
denominator `n = |D ∪ A|` of the intron Jaccard index of `j` and a pseudocount `α > 0`, the ratio
`(k + α) / (n + 2α)`, whose logit FRASER 2.0 feeds to its denoising autoencoder, lies strictly
between `0` and `1`, also when `n = 0`, so its logit is defined. -/
theorem pseudocount_ratio_mem_Ioo (j : Site × Site) {α : ℝ} (hα : 0 < α) :
    ((#(x.donorObservations j.1 ∩ x.acceptorObservations j.2) : ℝ) + α) /
        (#(x.donorObservations j.1 ∪ x.acceptorObservations j.2) + 2 * α) ∈ Set.Ioo 0 1 := by
  have hkn : (#(x.donorObservations j.1 ∩ x.acceptorObservations j.2) : ℝ) ≤
      #(x.donorObservations j.1 ∪ x.acceptorObservations j.2) := by
    exact_mod_cast card_le_card inter_subset_union
  have hden : (0 : ℝ) < #(x.donorObservations j.1 ∪ x.acceptorObservations j.2) + 2 * α := by
    positivity
  exact ⟨by positivity, (div_lt_one hden).2 (by linarith)⟩

end AlignedReads

end Domains.Biology.Omics.IntronJaccard
