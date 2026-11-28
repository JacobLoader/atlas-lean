/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent

/-!
# Tests for the partition-valued Λ-coalescent and its branch lengths

Concrete rates for Kingman's coalescent (`Λ = δ₀`) and the Bolthausen–Sznitman coalescent
(`Λ` uniform): the exit rates `b.choose 2` and `b - 1`, and the rates of the binary and triple
mergers of two and three singletons. For the branch lengths: `I + E = L`, no branch at all for a
single gene, and no internal branch for two genes. For the mutations: the genealogy keeps its law,
and a zero mutation rate puts no mutation anywhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset unitInterval
open scoped ENNReal NNReal

namespace DomainsTest.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent

open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent

/-! ### Rates -/

/-- The rate matrix of the Bolthausen–Sznitman coalescent of five genes is a rate matrix. -/
example : IsRateMatrix (rateMatrix volume 5) := isRateMatrix_rateMatrix volume 5

/-- Bolthausen–Sznitman: a partition with `b ≥ 1` blocks is left at rate `λ_b = b - 1`. -/
example {n : ℕ} (π : SamplePartition n) (hπ : 1 ≤ #π.parts) :
    rateMatrix volume n π π = -((#π.parts : ℝ) - 1) := by
  rw [rateMatrix_self, totalMergerRate_volume hπ]

/-- Bolthausen–Sznitman: `n ≥ 1` singletons are left at rate `n - 1`. -/
example {n : ℕ} (hn : 1 ≤ n) : rateMatrix volume n ⊥ ⊥ = -((n : ℝ) - 1) := by
  rw [rateMatrix_self, Finpartition.card_bot, card_univ, Fintype.card_fin,
    totalMergerRate_volume hn]

/-- Kingman: a partition with `b` blocks is left at rate `b.choose 2`. -/
example {n : ℕ} (π : SamplePartition n) :
    rateMatrix (Measure.dirac 0) n π π = -((#π.parts).choose 2 : ℝ) := by
  rw [rateMatrix_self, totalMergerRate_dirac_zero]

/-- The partition of a nonempty sample into one block. -/
def oneBlock (n : ℕ) [NeZero n] : SamplePartition n :=
  Finpartition.indiscrete (univ_nonempty (α := Fin n)).ne_empty

/-- The two singletons of a sample of two genes merge into one block. -/
theorem isMultiMerge_two : IsMultiMerge (⊥ : SamplePartition 2) (oneBlock 2) :=
  ⟨bot_le, by decide⟩

/-- The three singletons of a sample of three genes merge into one block at once. -/
theorem isMultiMerge_three : IsMultiMerge (⊥ : SamplePartition 3) (oneBlock 3) :=
  ⟨bot_le, by decide⟩

/-- Bolthausen–Sznitman: two singletons merge at rate `λ_{2,2} = 1`. -/
example : rateMatrix volume 2 ⊥ (oneBlock 2) = 1 := by
  have hne : (⊥ : SamplePartition 2) ≠ oneBlock 2 := fun h => by
    simpa [oneBlock] using congrArg (fun π : SamplePartition 2 => #π.parts) h
  simp only [rateMatrix, Matrix.of_apply, hne, ite_false, isMultiMerge_two, ite_true]
  rw [mergerRate_volume (by decide) (by decide)]
  simp [oneBlock]

/-- Bolthausen–Sznitman: three singletons merge at once at rate `λ_{3,3} = 1 / 2`. -/
example : rateMatrix volume 3 ⊥ (oneBlock 3) = 1 / 2 := by
  have hne : (⊥ : SamplePartition 3) ≠ oneBlock 3 := fun h => by
    simpa [oneBlock] using congrArg (fun π : SamplePartition 3 => #π.parts) h
  simp only [rateMatrix, Matrix.of_apply, hne, ite_false, isMultiMerge_three, ite_true]
  rw [mergerRate_volume (by simp [oneBlock]) (by simp [oneBlock])]
  simp [oneBlock]

/-- Kingman: three singletons never merge at once. -/
example : rateMatrix (Measure.dirac 0) 3 ⊥ (oneBlock 3) = 0 := by
  have hne : (⊥ : SamplePartition 3) ≠ oneBlock 3 := fun h => by
    simpa [oneBlock] using congrArg (fun π : SamplePartition 3 => #π.parts) h
  simp only [rateMatrix, Matrix.of_apply, hne, ite_false, isMultiMerge_three, ite_true]
  rw [mergerRate_dirac_zero]
  simp [oneBlock]

/-! ### Branch lengths -/

/-- The internal and external lengths add up to the total length. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (n : ℕ) (ω) :
    internalLength Λ n ω + externalLength Λ n ω = totalLength Λ n ω :=
  internalLength_add_externalLength Λ n ω

/-- A single gene has no branch: its genealogy has total length `0`. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (ω) : totalLength Λ 1 ω = 0 := by
  refine tsum_eq_zero_iff.2 fun k => ?_
  have h := (ctmcJumpChain ⊥ ω k).card_parts_le_card
  rw [card_univ, Fintype.card_fin] at h
  rw [ite_eq_right (by omega)]

/-- Two genes have no internal branch: both branches are external until the root. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (ω) : internalLength Λ 2 ω = 0 := by
  refine tsum_eq_zero_iff.2 fun k => ?_
  split_ifs with h
  · set π := ctmcJumpChain ⊥ ω k
    suffices hB : #{B ∈ π.parts | 2 ≤ #B} = 0 by rw [hB, Nat.cast_zero, zero_mul]
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun B hB hB2 => ?_)
    obtain ⟨B', hB', hne⟩ := exists_mem_ne (by omega : 1 < #π.parts) B
    have h1 := card_pos.2 (π.nonempty_of_mem_parts hB')
    have hsum := π.sum_card_parts
    rw [card_univ, Fintype.card_fin] at hsum
    have hle : #B + #B' ≤ ∑ i ∈ π.parts, #i := by
      rw [← sum_pair hne.symm]
      exact sum_le_sum_of_subset (insert_subset hB (singleton_subset_iff.2 hB'))
    omega
  · rfl

/-! ### Mutations -/

/-- Adding the mutations leaves the law of the genealogy unchanged. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (n : ℕ) (μ : ℝ≥0) :
    (mutationMeasure Λ n μ).fst = inputMeasure Λ n :=
  fst_mutationMeasure Λ n μ

/-- With mutation rate `0` there are almost surely no mutations. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (n : ℕ) :
    (mutationMeasure Λ n 0).snd = Measure.dirac (0, 0) := by
  rw [mutationMeasure, Measure.snd_compProd]
  have hκ : mutationKernel Λ n 0 = Kernel.const _ (Measure.dirac (0, 0)) := by
    ext1 ω
    simp [mutationKernel, Kernel.prod_apply, poissonMeasure_zero, Measure.dirac_prod_dirac]
  rw [hκ, Measure.comp_eq_comp_const_apply, Kernel.const_comp', Kernel.const_apply]

end DomainsTest.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent
