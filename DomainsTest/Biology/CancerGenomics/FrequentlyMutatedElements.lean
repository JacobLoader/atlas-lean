/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.CancerGenomics.FrequentlyMutatedElements
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the Poisson-binomial test for frequently mutated regulatory elements

For every cohort, `elementPValue` is `1` at zero mutated samples, and `0` at any positive count
for an element of length zero. For two samples with `1` and `2` variants over `10` covered base
pairs and an element of one base pair, the success probabilities are `1/10` and `1/5`, so the
p-values of one and of two mutated samples are `1 - (9/10) (4/5) = 7/25` and
`(1/10) (1/5) = 1/50`; the p-value of two mutated samples grows to `(19/100) (9/25) = 171/2500`
for an element of two base pairs, as `elementPValue_mono_length` says it must. Without its
hypothesis `n_k ≤ n_cov`, under which `elementPValue` is a probability, the formula can decrease
with the length.

The hypotheses of the null model are satisfiable for every cohort and element length whenever
`n_k ≤ n_cov`: the coordinate events of a product of Bernoulli measures on
`Fin S × Fin n → Bool` are mutually independent with the prescribed probabilities. On that model
the two-sample cohort above has two mutated samples with probability `1/50`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Domains.Biology.CancerGenomics.FrequentlyMutatedElements

namespace DomainsTest.Biology.CancerGenomics.FrequentlyMutatedElements

/-- For every cohort, `elementPValue` is `1` at zero mutated samples: the masses sum to one. -/
example {S : ℕ} (nSNV : Fin S → ℕ) (nCov n : ℕ) : elementPValue nSNV nCov n 0 = 1 := by
  rw [elementPValue, poissonBinomialTail, ← Nat.range_succ_eq_Icc_zero, sum_poissonBinomialPMF]

/-- For an element of length zero, `elementPValue` is `0` at every positive number of mutated
samples. -/
example {S : ℕ} (nSNV : Fin S → ℕ) (nCov s : ℕ) : elementPValue nSNV nCov 0 (s + 1) = 0 := by
  simp only [elementPValue, pow_zero, sub_self, poissonBinomialTail, poissonBinomialPMF_const]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [zero_pow (by have := (Finset.mem_Icc.mp hj).1; omega)]
  ring

/-- The success probabilities of two samples with `1` and `2` variants over `10` covered base
pairs, for an element of `n` base pairs: `1 - (9/10) ^ n` and `1 - (4/5) ^ n`. -/
lemma hitProbabilities (n : ℕ) :
    (fun k : Fin 2 => 1 - (1 - (((![1, 2] : Fin 2 → ℕ) k : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) ^ n) =
      (Fin.cons (1 - (9 / 10) ^ n) (Fin.cons (1 - (4 / 5) ^ n) Fin.elim0) : Fin 2 → ℝ) := by
  funext k
  fin_cases k <;> norm_num

/-- For the two-sample cohort, the p-value of one mutated sample in an element of `n` base pairs
is `1 - (9/10) ^ n (4/5) ^ n`. -/
lemma elementPValue_one (n : ℕ) :
    elementPValue ![1, 2] 10 n 1 = 1 - (9 / 10) ^ n * (4 / 5) ^ n := by
  rw [elementPValue, hitProbabilities]
  refine (poissonBinomialTail_cons_succ _ _ 0).trans ?_
  rw [poissonBinomialTail_cons_succ, poissonBinomialPMF_cons_zero]
  simp [poissonBinomialTail, poissonBinomialPMF]
  ring

/-- For the two-sample cohort, the p-value of two mutated samples in an element of `n` base
pairs is `(1 - (9/10) ^ n) (1 - (4/5) ^ n)`. -/
lemma elementPValue_two (n : ℕ) :
    elementPValue ![1, 2] 10 n 2 = (1 - (9 / 10) ^ n) * (1 - (4 / 5) ^ n) := by
  rw [elementPValue, hitProbabilities]
  refine (poissonBinomialTail_cons_succ _ _ 1).trans ?_
  rw [poissonBinomialTail_cons_succ, poissonBinomialPMF_cons_succ,
    poissonBinomialPMF_eq_zero_of_lt _ (by norm_num : 0 < 0 + 1)]
  simp [poissonBinomialTail, poissonBinomialPMF]

/-- An element of one base pair: the p-value of one mutated sample is
`1 - (9/10) (4/5) = 7/25`. -/
example : elementPValue ![1, 2] 10 1 1 = 7 / 25 := by
  rw [elementPValue_one]
  norm_num

/-- An element of one base pair: the p-value of two mutated samples is `(1/10) (1/5) = 1/50`. -/
example : elementPValue ![1, 2] 10 1 2 = 1 / 50 := by
  rw [elementPValue_two]
  norm_num

/-- An element of two base pairs: the p-value of two mutated samples is
`(19/100) (9/25) = 171/2500`. -/
example : elementPValue ![1, 2] 10 2 2 = 171 / 2500 := by
  rw [elementPValue_two]
  norm_num

/-- A longer element has a p-value at least as large (here `1/50 ≤ 171/2500`). -/
example : elementPValue ![1, 2] 10 1 2 ≤ elementPValue ![1, 2] 10 2 2 :=
  elementPValue_mono_length (fun k => by fin_cases k <;> decide) (by norm_num) 2

/-- The hypothesis `n_k ≤ n_cov` of `elementPValue_mono_length` is needed: with `3` variants
over one covered base pair the ratio `n_k / n_cov` is `3`, the entries `1 - (1 - 3) ^ n` of the
vector in `elementPValue` are `3` and `-3` for `n = 1, 2`, and `elementPValue` at one mutated
sample decreases from `3` to `-3` as the length grows. -/
example : elementPValue ![3] 1 2 1 < elementPValue ![3] 1 1 1 := by
  have h (n : ℕ) : elementPValue ![3] 1 n 1 = 1 - (-2) ^ n := by
    have hv : (fun k : Fin 1 => 1 - (1 - (((![3] : Fin 1 → ℕ) k : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ n) =
        (Fin.cons (1 - (-2) ^ n) Fin.elim0 : Fin 1 → ℝ) := by
      funext k
      fin_cases k
      norm_num
    rw [elementPValue, hv]
    refine (poissonBinomialTail_cons_succ _ _ 0).trans ?_
    simp [poissonBinomialTail, poissonBinomialPMF]
  rw [h, h]
  norm_num

/-- The product of Bernoulli measures with parameters `p x` on `J → Bool`. -/
noncomputable abbrev bernoulliProduct {J : Type*} [Fintype J] (p : J → unitInterval) :
    Measure (J → Bool) :=
  Measure.pi fun x => bernoulliMeasure true false (p x)

/-- The coordinate events of a product of Bernoulli measures are mutually independent. -/
lemma iIndepSet_coord {J : Type*} [Fintype J] (p : J → unitInterval) :
    iIndepSet (fun x => {ω : J → Bool | ω x = true}) (bernoulliProduct p) := by
  have hf := iIndepFun_pi (μ := fun x => bernoulliMeasure true false (p x))
    (X := fun _ => (id : Bool → Bool)) fun _ => aemeasurable_id
  rw [iIndepSet_iff_meas_biInter fun x => measurableSet_eq_fun (measurable_pi_apply x)
    measurable_const]
  intro S
  exact hf.meas_biInter fun x _ => ⟨{true}, measurableSet_singleton _, rfl⟩

/-- The coordinate event `{ω | ω x = true}` has probability `p x`. -/
lemma measureReal_coord {J : Type*} [Fintype J] (p : J → unitInterval) (x : J) :
    (bernoulliProduct p).real {ω | ω x = true} = p x := by
  have h := (measurePreserving_eval (fun x => bernoulliMeasure true false (p x))
    x).measureReal_preimage (s := {true}) (measurableSet_singleton _).nullMeasurableSet
  rw [show {ω : J → Bool | ω x = true} = Function.eval x ⁻¹' ({true} : Set Bool) from rfl, h]
  simp

/-- The background rate `n_k / n_cov` as a point of the unit interval, when `n_k ≤ n_cov`. -/
noncomputable def rate {S : ℕ} (nSNV : Fin S → ℕ) (nCov : ℕ) (hle : ∀ k, nSNV k ≤ nCov)
    (k : Fin S) : unitInterval :=
  ⟨(nSNV k : ℝ) / nCov, by positivity,
    div_le_one_of_le₀ (by exact_mod_cast hle k) (Nat.cast_nonneg _)⟩

/-- **Non-vacuity of the null model.** For every cohort with `n_k ≤ n_cov` and every element
length `n`, the coordinate events of the product of Bernoulli measures with parameters
`n_k / n_cov` satisfy the hypotheses of `measureReal_le_ncard_eq_elementPValue`, which then gives
the p-value as the probability of at least `s` mutated samples. -/
example {S : ℕ} (nSNV : Fin S → ℕ) (nCov n : ℕ) (hle : ∀ k, nSNV k ≤ nCov) (s : ℕ) :
    let μ := bernoulliProduct fun x : Fin S × Fin n => rate nSNV nCov hle x.1
    let M : Fin S → Fin n → Set (Fin S × Fin n → Bool) := fun k b => {ω | ω (k, b) = true}
    (∀ k b, MeasurableSet (M k b)) ∧ iIndepSet (Function.uncurry M) μ ∧
      (∀ k b, μ.real (M k b) = (nSNV k : ℝ) / nCov) ∧
      μ.real {ω | s ≤ {k | ∃ b, ω ∈ M k b}.ncard} = elementPValue nSNV nCov n s := by
  intro μ M
  have hM : ∀ k b, MeasurableSet (M k b) := fun k b =>
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hind : iIndepSet (Function.uncurry M) μ := by
    convert iIndepSet_coord (fun x : Fin S × Fin n => rate nSNV nCov hle x.1) using 1
    ext ⟨k, b⟩
    rfl
  have hp : ∀ k b, μ.real (M k b) = (nSNV k : ℝ) / nCov := fun k b =>
    measureReal_coord _ (k, b)
  exact ⟨hM, hind, hp, measureReal_le_ncard_eq_elementPValue hM hind hp s⟩

/-- On the product model, two samples with `1` and `2` variants over `10` base pairs and an
element of one base pair have two mutated samples with probability `1/50`. -/
example :
    let μ := bernoulliProduct fun x : Fin 2 × Fin 1 =>
      rate ![1, 2] 10 (fun k => by fin_cases k <;> decide) x.1
    μ.real {ω | 2 ≤ {k : Fin 2 | ∃ b : Fin 1, ω (k, b) = true}.ncard} = 1 / 50 := by
  intro μ
  have hM : ∀ (k : Fin 2) (b : Fin 1), MeasurableSet {ω : Fin 2 × Fin 1 → Bool | ω (k, b) = true} :=
    fun k b => measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hind : iIndepSet (Function.uncurry fun (k : Fin 2) (b : Fin 1) =>
      {ω : Fin 2 × Fin 1 → Bool | ω (k, b) = true}) μ := by
    convert iIndepSet_coord (fun x : Fin 2 × Fin 1 =>
      rate ![1, 2] 10 (fun k => by fin_cases k <;> decide) x.1) using 1
    ext ⟨k, b⟩
    rfl
  refine (measureReal_le_ncard_eq_elementPValue (nSNV := ![1, 2]) (nCov := 10) hM hind
    (fun k b => measureReal_coord _ (k, b)) 2).trans ?_
  rw [elementPValue_two]
  norm_num

end DomainsTest.Biology.CancerGenomics.FrequentlyMutatedElements
