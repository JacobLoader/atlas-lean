/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.CancerGenomics.PoissonExcessMutation
import MathlibExt.Probability.Distributions.PoissonGamma
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for the Poisson excess-mutation test.

* eq. (1) on two trinucleotides, one of them absent from the genome;
* standardization of a covariate, including a constant one, and the covariate vector;
* eq. (2) on three elements in two clusters, eq. (3) on them, the `p` value `1` of an element
  without mutations, and the conservativeness theorem at half the estimated rate;
* the null `p` values are not uniform: for one element with fitted mean `1`,
  `F_exp(9/10) = 1 - e^{-1} < 9/10`;
* the false discovery rate of that element at `p* = 9/10` is `1 - e^{-1}`, and at `p* = 1` it
  is `1`, whatever the covariates. -/

open Domains.Biology.CancerGenomics.PoissonExcessMutation
open MathlibExt.Probability.Statistics.ExactTests (upperTail upperTail_antitone)
open MathlibExt.Probability.FiniteProbability (sampleMean sampleVar sampleMean_eq_sum_div)
open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal

namespace DomainsTest.Biology.CancerGenomics.PoissonExcessMutation

/-! ### Eq. (1): the trinucleotide-content expectation -/

/-- An element with two occurrences of a trinucleotide that carries `3` of its `6` genomic
occurrences' mutations, and one of a trinucleotide with `4` mutations over `8` occurrences:
`μ = 2 · 3 / 6 + 1 · 4 / 8 = 3 / 2`. -/
example : trinucleotideExpectation (fun (_ : Fin 1) => ![2, 1]) ![3, 4] ![6, 8] 0 = 3 / 2 := by
  norm_num [trinucleotideExpectation, Fin.sum_univ_two]

/-- A trinucleotide absent from the genome contributes `0`. -/
example : trinucleotideExpectation (fun (_ : Fin 1) => ![0, 1]) ![5, 4] ![0, 8] 0 = 1 / 2 := by
  norm_num [trinucleotideExpectation, Fin.sum_univ_two]

/-! ### Standardization and the covariate vector -/

/-- The covariate `(1, 3)` has mean `2`. -/
theorem sampleMean_one_three : sampleMean ![(1 : ℝ), 3] = 2 := by
  norm_num [sampleMean_eq_sum_div, Fin.sum_univ_two]

/-- The covariate `(1, 3)` has variance `1` (divisor `2`). -/
theorem sampleVar_one_three : sampleVar ![(1 : ℝ), 3] = 1 := by
  norm_num [sampleVar, sampleMean_one_three, Fin.sum_univ_two]

/-- `(1, 3)` standardizes to `(-1, 1)`. -/
theorem standardize_one_three : standardize ![(1 : ℝ), 3] = ![-1, 1] := by
  ext i
  fin_cases i <;> norm_num [standardize, sampleMean_one_three, sampleVar_one_three]

/-- The theorems on this covariate: mean `0` and variance `1` after standardization. -/
example : sampleMean (standardize ![(1 : ℝ), 3]) = 0 ∧
    sampleVar (standardize ![(1 : ℝ), 3]) = 1 :=
  ⟨sampleMean_standardize _, sampleVar_standardize (by rw [sampleVar_one_three]; norm_num)⟩

/-- A constant covariate standardizes to `0`. -/
example : standardize (fun _ : Fin 3 => (7 : ℝ)) = 0 := by
  ext i
  simp [standardize, sampleMean_eq_sum_div]

/-- The first coordinate of the covariate vector is the standardized replication timing. -/
example : covariates ![(1 : ℝ), 3] 0 0 0 (fun _ (_ : Fin 1) => 0) 0 0 0 0 = -1 := by
  simp [covariates, standardize_one_three]

/-! ### Eqs. (2) and (3) on three elements in two clusters

Elements `0` and `1` form the cluster `true`, with lengths `100` and `300` and counts `1` and `3`;
element `2` forms the cluster `false`, with length `50` and no mutation. -/

/-- The clusters. -/
def cluster : Fin 3 → Bool := ![true, true, false]

/-- The repeat-masked lengths. -/
def len : Fin 3 → ℕ := ![100, 300, 50]

/-- The mutation counts. -/
def count : Fin 3 → ℕ := ![1, 3, 0]

/-- Eq. (2): the cluster `true` has rate `(1 + 3) / (100 + 300) = 1 / 100`. -/
theorem clusterRate_true : clusterRate cluster len count true = 1 / 100 := by
  have h : ({i | cluster i = true} : Finset (Fin 3)) = {0, 1} := by decide
  rw [clusterRate_eq, h]
  norm_num [len, count]

/-- The cluster `false` has rate `0`. -/
theorem clusterRate_false : clusterRate cluster len count false = 0 := by
  have h : ({i | cluster i = false} : Finset (Fin 3)) = {2} := by decide
  rw [clusterRate_eq, h]
  norm_num [count]

/-- Eq. (3): element `0`, with fitted mean `1 / 100 · 100 = 1` and one mutation, has
`p = 1 - e^{-1}`. -/
theorem pValue_zero : pValue cluster len count 0 = 1 - exp (-1) := by
  rw [pValue_eq, show cluster 0 = true from rfl, clusterRate_true]
  norm_num [len, count]

/-- Element `1`, with fitted mean `3` and three mutations, has
`p = 1 - e^{-3} (1 + 3 + 9 / 2)`. -/
example : pValue cluster len count 1 = 1 - exp (-3) * (1 + 3 + 9 / 2) := by
  rw [pValue_eq, show cluster 1 = true from rfl, clusterRate_true]
  norm_num [len, count, Finset.sum_range_succ, Nat.factorial]
  ring

/-- Element `2` has no mutation, so `p = 1`: the atom of the null distribution of `p`. -/
example : pValue cluster len count 2 = 1 := by
  simp [pValue_eq, count]

/-- At half the estimated rate, the `p` value of element `0` is at most the reported one. -/
example : upperTail (poissonMeasure ((1 / 200 : ℝ≥0) * len 0)) (count 0) ≤
    pValue cluster len count 0 :=
  upperTail_le_pValue (by rw [show cluster 0 = true from rfl, clusterRate_true]; norm_num)

/-! ### One element with fitted mean `1`: the null `p` values are not uniform -/

/-- `P(K ≥ 1) = 1 - e^{-1}` for `K ~ Po(1)`. -/
theorem upperTail_one_one : upperTail (poissonMeasure 1) 1 = 1 - exp (-1) := by
  change (poissonMeasure 1).real (Set.Ici 1) = _
  simp [poissonMeasure_real_Ici]

/-- The `p` value of a `Po(1)` count is at most `9 / 10` exactly when the count is positive. -/
theorem setOf_upperTail_le : {k : ℕ | upperTail (poissonMeasure 1) k ≤ 9 / 10} = Set.Ici 1 := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_Ici]
  constructor
  · intro h
    by_contra hk
    obtain rfl : k = 0 := by omega
    have h0 : upperTail (poissonMeasure 1) 0 = 1 := by
      change (poissonMeasure 1).real (Set.Ici 0) = 1
      simp
    linarith
  · intro hk
    have h1 := upperTail_antitone (poissonMeasure 1) hk
    rw [upperTail_one_one] at h1
    have := Real.exp_neg_one_gt_d9
    linarith

/-- The fitted mean of an element of length `1` with one mutation, alone in its cluster, is `1`. -/
theorem fittedMean_single :
    fittedMean (fun _ : Fin 1 => ()) (fun _ => 1) (fun _ => 1) 0 = 1 := by
  rw [← NNReal.coe_inj, coe_fittedMean, clusterRate_eq]
  simp

/-- `F_exp(9/10) = 1 - e^{-1}` for that element. -/
theorem expectedCDF_single :
    expectedCDF (fun _ : Fin 1 => ()) (fun _ => 1) (fun _ => 1) (9 / 10) = 1 - exp (-1) := by
  rw [expectedCDF, Fin.sum_univ_one, fittedMean_single, setOf_upperTail_le]
  simp [poissonMeasure_real_Ici]

/-- The null distribution function lies strictly below the uniform one at `9 / 10`. -/
example : expectedCDF (fun _ : Fin 1 => ()) (fun _ => 1) (fun _ => 1) (9 / 10) < 9 / 10 := by
  rw [expectedCDF_single]
  have := Real.exp_neg_one_gt_d9
  linarith

/-- `F_obs(9/10) = 1`: the element's `p = 1 - e^{-1}` is at most `9 / 10`. -/
theorem observedCDF_single :
    observedCDF (fun _ : Fin 1 => ()) (fun _ => 1) (fun _ => 1) (9 / 10) = 1 := by
  have hp : pValue (fun _ : Fin 1 => ()) (fun _ => 1) (fun _ => 1) 0 ≤ 9 / 10 := by
    have h : pValue (fun _ : Fin 1 => ()) (fun _ => 1) (fun _ => 1) 0 =
        upperTail (poissonMeasure 1) 1 := by
      rw [pValue, fittedMean_single]
    rw [h, upperTail_one_one]
    have := Real.exp_neg_one_gt_d9
    linarith
  rw [observedCDF, Finset.filter_true_of_mem fun i _ => by fin_cases i; exact hp]
  simp

/-- The false discovery rate at `p* = 9 / 10` of the single element, clustered by any rule. -/
example (clustering : (Fin 1 → Fin 5 → ℝ) → Fin 1 → Unit) :
    falseDiscoveryRate clustering 0 0 0 0 (fun _ (_ : Fin 1) => 0) 0 0 (fun _ => 1) (fun _ => 1)
      (9 / 10) = 1 - exp (-1) := by
  have hc : clustering (covariates 0 0 0 0 (fun _ (_ : Fin 1) => 0) 0 0) = fun _ => () :=
    Subsingleton.elim _ _
  simp only [falseDiscoveryRate, hc, expectedCDF_single, observedCDF_single, div_one]

/-- At `p* = 1` every `p` value is counted, so the false discovery rate of a nonempty set of
elements is `1`, whatever the covariates, the clustering, the lengths and the counts. -/
example {ι κ τ : Type*} [Fintype ι] [Nonempty ι] [DecidableEq κ] [Fintype τ]
    (clustering : (ι → Fin 5 → ℝ) → ι → κ) (rt ch gc gd : ι → ℝ) (occ : ι → τ → ℕ)
    (M N : τ → ℕ) (L n : ι → ℕ) :
    falseDiscoveryRate clustering rt ch gc gd occ M N L n 1 = 1 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hset : ∀ r : ℝ≥0, {k | upperTail (poissonMeasure r) k ≤ 1} = Set.univ := fun r =>
    Set.eq_univ_of_forall fun k => measureReal_le_one
  simp only [falseDiscoveryRate, expectedCDF, observedCDF, hset, probReal_univ,
    (pValue_mem_Icc _ _ _ _).2, Finset.filter_true]
  simp [hcard]

end DomainsTest.Biology.CancerGenomics.PoissonExcessMutation
