/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import Domains.Biology.Omics.HierarchicalCountMLEVarying

import MathlibExt.Probability.Distributions.PoissonGamma

/-!
# The Poisson excess-mutation test for driver regulatory elements

D'Antonio et al. (2017) test candidate regulatory elements, DNase I hypersensitive sites (DHSs),
for an excess of somatic point mutations over the local neutral expectation. The elements are
first clustered, per chromosome, by `k`-means on five standardized covariates of local mutation
rate: replication timing, open or closed chromatin status, GC content, local gene density, and
the trinucleotide-content expectation

  `μᵢ = ∑ₜ n_{i,t} M_t / N_t`                                                         (1)

of element `i`, where `n_{i,t}` counts the occurrences of the trinucleotide `t` in the element,
and `M_t` and `N_t` count the mutations at `t` and the occurrences of `t` in the genome. Within
a cluster the per-nucleotide neutral mutation probability `μ` is taken to be constant, so that an
element of repeat-masked length `L` carries `n ~ Po(μ L)` mutations under neutrality. The rate is
estimated from the `N` elements of the cluster,

  `μ̂ = (∑ᵢ nᵢ) / (∑ᵢ Lᵢ)`,                                                          (2)

and an element with `n` mutations gets the upper Poisson tail

  `p = 1 - ∑_{k < n} λ̂^k / k! e^{-λ̂}`, `λ̂ = μ̂ L`.                                (3)

As `n` is discrete, the null distribution of `p` is not uniform: it is that of the `p` value of
counts `nᵢ ~ Po(μ̂ᵢ Lᵢ)`, which the source samples by simulation. With `F_exp` and `F_obs` the
distribution functions of these null `p` values and of the observed ones, the false discovery
rate at the threshold `p*` is

  `FDR(p*) = F_exp(p*) / F_obs(p*)`.                                                 (4)

## Conventions

* The elements form a finite type `ι`, the trinucleotides a finite type `τ` (the 64 from `AAA`
  to `TTT` in the source), and the clusters a type `κ`. Lengths `L` (base pairs left after
  repeat masking) and mutation counts `n` are natural numbers.
* A covariate is standardized over all the elements, with its mean and its standard deviation
  with divisor `card ι` (`MathlibExt.Probability.FiniteProbability.sampleMean`, `sampleVar`).
* The clustering is a parameter `clustering : (ι → Fin 5 → ℝ) → ι → κ`, applied to the table of
  standardized covariates. The source's rule is `k`-means run on each chromosome's elements, an
  iterative procedure whose result depends on its start and on the number of clusters; (2)–(4)
  are stated for whatever clustering it returns.
* The rate of a cluster is `MathlibExt.Biology.Omics.HierarchicalCount.pooledMean` of its
  elements, which is `0` when their total length is `0`.
* `p` is `MathlibExt.Probability.Statistics.ExactTests.upperTail` of Mathlib's
  `poissonMeasure λ̂`, the probability that a `Po(λ̂)` count is at least `n`; `pValue_eq` is (3).
* `F_exp` is the exact distribution function that the simulation estimates: the average over the
  elements of the probability that the `p` value of a count drawn from `Po(λ̂ᵢ)`, scored with the
  same `λ̂ᵢ`, is at most `p*`. `F_obs(p*)` is the fraction of elements whose `p` is at most `p*`.
  The false discovery rate is `0` where `F_obs(p*) = 0`, by `x / 0 = 0`.

## Main definitions

* `trinucleotideExpectation`: the covariate (1).
* `standardize`, `covariates`: the standardized covariate vector of an element.
* `clusterRate`: the rate estimate (2) of a cluster; `fittedMean`: the fitted mean `λ̂ = μ̂ L`.
* `pValue`: the test statistic (3).
* `observedCDF`, `expectedCDF`: `F_obs` and `F_exp`.
* `falseDiscoveryRate`: the false discovery rate (4) of the test, from the covariates, the
  clustering rule, the lengths and the counts.

## Main results

* `sampleMean_standardize`, `sampleVar_standardize`: a standardized covariate has mean `0` and,
  unless the covariate is constant, variance `1`.
* `clusterRate_eq`: (2) as a sum over the elements of the cluster.
* `pValue_eq`: (3).
* `upperTail_le_pValue`: the test is conservative: the `p` value at any rate `μ ≤ μ̂`, such as
  the neutral rate of a cluster that also holds elements under selection, is at most `p`.
* `expectedCDF_le`: `F_exp(p*) ≤ p*` on `[0, 1]`: the null `p` values are super-uniform, so the
  uniform distribution function would overstate `F_exp`.
* `observedCDF_mono`, `expectedCDF_mono`, `falseDiscoveryRate_nonneg`.

## References

* M. D'Antonio, D. Weghorn, A. D'Antonio-Chronowska, F. Coulet, K. M. Olson, C. DeBoever et al.,
  "Identifying DNase I hypersensitive sites as driver distal regulatory elements in breast
  cancer", Nat. Commun. 8 (2017), 436, <https://doi.org/10.1038/s41467-017-00100-x>: Methods
  ("Clustering DHSs into groups of similar sequence characteristics", "Inference of mutation
  probability", "Test statistic p", "False discovery rate"), eqs. (1)–(4).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open MathlibExt.Biology.Omics.HierarchicalCount (pooledMean)
open MathlibExt.Probability.Statistics.ExactTests (upperTail isValidPValue_upperTailPValue)
open MathlibExt.Probability.FiniteProbability (sampleMean sampleVar sum_sub_sampleMean
  sampleMean_eq_sum_div)
open scoped NNReal Nat

namespace Domains.Biology.CancerGenomics.PoissonExcessMutation

variable {ι κ τ : Type*}

/-! ### Covariates and clustering -/

section Covariates

variable [Fintype τ]

/-- The trinucleotide-content expectation of element `i` (D'Antonio et al. 2017, eq. (1)):

  `μᵢ = ∑ₜ n_{i,t} M_t / N_t`,

where `occ i t = n_{i,t}` is the number of occurrences of the trinucleotide `t` in element `i`,
`M t` the number of mutations observed at `t` and `N t` the number of occurrences of `t` in the
genome. It is the context-dependent mutation expectation of the element up to a constant factor,
and the fifth covariate of local mutation rate on which the elements are clustered. A
trinucleotide absent from the genome (`N t = 0`) contributes `0`, by `x / 0 = 0`. -/
noncomputable def trinucleotideExpectation (occ : ι → τ → ℕ) (M N : τ → ℕ) (i : ι) : ℝ :=
  ∑ t, (occ i t : ℝ) * (M t : ℝ) / (N t : ℝ)

/-- The trinucleotide-content expectation is nonnegative. -/
theorem trinucleotideExpectation_nonneg (occ : ι → τ → ℕ) (M N : τ → ℕ) (i : ι) :
    0 ≤ trinucleotideExpectation occ M N i := by
  unfold trinucleotideExpectation
  positivity

variable [Fintype ι]

/-- The standardization `(xᵢ - x̄) / s` of a covariate `x` over the elements, with `x̄` its mean
and `s` its standard deviation with divisor `card ι` (the square root of `sampleVar x`). The
standardized covariate has mean `0` (`sampleMean_standardize`) and, unless `x` is constant,
variance `1` (`sampleVar_standardize`); a constant covariate standardizes to `0`, by
`x / 0 = 0`. -/
noncomputable def standardize (x : ι → ℝ) (i : ι) : ℝ :=
  (x i - sampleMean x) / √(sampleVar x)

/-- The five standardized covariates of local mutation rate of element `i`, on which the
elements are clustered (D'Antonio et al. 2017): in this order, replication timing, open or closed
chromatin status, GC content, local gene density and the trinucleotide-content expectation
`trinucleotideExpectation occ M N` (eq. (1)), each standardized over the elements
(`standardize`). The first four are given as real values per element. -/
noncomputable def covariates (replicationTiming chromatin gcContent geneDensity : ι → ℝ)
    (occ : ι → τ → ℕ) (M N : τ → ℕ) (i : ι) : Fin 5 → ℝ :=
  ![standardize replicationTiming i, standardize chromatin i, standardize gcContent i,
    standardize geneDensity i, standardize (trinucleotideExpectation occ M N) i]

end Covariates

variable [Fintype ι]

/-- A standardized covariate has mean `0`. -/
theorem sampleMean_standardize (x : ι → ℝ) : sampleMean (standardize x) = 0 := by
  rw [sampleMean_eq_sum_div]
  simp only [standardize, ← Finset.sum_div, sum_sub_sampleMean, zero_div]

/-- A standardized covariate has variance `1` (with divisor `card ι`), unless the covariate is
constant, that is, unless its variance is `0`. -/
theorem sampleVar_standardize {x : ι → ℝ} (hx : sampleVar x ≠ 0) :
    sampleVar (standardize x) = 1 := by
  have hv : 0 ≤ sampleVar x := by
    unfold sampleVar
    positivity
  have hs : √(sampleVar x) ^ 2 = sampleVar x := sq_sqrt hv
  unfold sampleVar
  simp only [sampleMean_standardize, sub_zero, standardize, div_pow, hs, ← Finset.sum_div]
  rw [div_right_comm]
  exact div_self hx

/-! ### The test -/

section Test

variable [DecidableEq κ]

/-- The estimated per-nucleotide neutral mutation probability of the cluster `c`
(D'Antonio et al. 2017, eq. (2)):

  `μ̂ = (∑ᵢ nᵢ) / (∑ᵢ Lᵢ)`,

the sums running over the elements `i` with `cluster i = c`, of repeat-masked lengths `L i` and
mutation counts `n i`: the pooled Poisson rate `pooledMean` of the cluster's elements, with the
lengths as size factors (`clusterRate_eq`). For positive lengths it is the maximum-likelihood
estimate of `μ` in the model `nᵢ ~ Po(μ Lᵢ)`; it is `0` when the cluster's total length is `0`.
It pools every element of the cluster, including any under selection. -/
noncomputable def clusterRate (cluster : ι → κ) (L n : ι → ℕ) (c : κ) : ℝ :=
  pooledMean (fun i : {i // cluster i = c} => (L i : ℝ)) fun i => n i

/-- The fitted neutral mean `λ̂ = μ̂ L` of the mutation count of element `i`, with `μ̂` the rate
`clusterRate` of its cluster and `L` its repeat-masked length, as an element of `ℝ≥0`
(`coe_fittedMean`). -/
noncomputable def fittedMean (cluster : ι → κ) (L n : ι → ℕ) (i : ι) : ℝ≥0 :=
  (clusterRate cluster L n (cluster i) * L i).toNNReal

/-- The test statistic of element `i` (D'Antonio et al. 2017, eq. (3)): the probability that a
`Po(λ̂)` count is at least the observed count `n i`, where `λ̂ = μ̂ L` is the fitted mean
`fittedMean` of the element,

  `p = 1 - ∑_{k < n} λ̂^k / k! e^{-λ̂}` (`pValue_eq`).

It is the exact upper-tail `p` value of the count under the fitted neutral Poisson law. -/
noncomputable def pValue (cluster : ι → κ) (L n : ι → ℕ) (i : ι) : ℝ :=
  upperTail (poissonMeasure (fittedMean cluster L n i)) (n i)

/-- The distribution function `F_obs(t)` of the observed `p` values: the fraction of the elements
`i` whose `p` value `pValue cluster L n i` is at most `t` (`0` when there are no elements). -/
noncomputable def observedCDF (cluster : ι → κ) (L n : ι → ℕ) (t : ℝ) : ℝ :=
  (#{i | pValue cluster L n i ≤ t} : ℝ) / Fintype.card ι

/-- The null distribution function `F_exp(t)` of the `p` values: the average over the elements
`i` of the probability that a count `K ~ Po(λ̂ᵢ)`, drawn from the element's fitted neutral law
(`fittedMean`), has `p` value `upperTail (Po(λ̂ᵢ)) K`, scored with the same `λ̂ᵢ` as in
`pValue`, at most `t`. It is the distribution function that D'Antonio et al. (2017) estimate by
simulating counts `nᵢ ~ Po(μ̂ᵢ Lᵢ)` for every element; it is `0` when there are no elements. -/
noncomputable def expectedCDF (cluster : ι → κ) (L n : ι → ℕ) (t : ℝ) : ℝ :=
  (∑ i, (poissonMeasure (fittedMean cluster L n i)).real
    {k | upperTail (poissonMeasure (fittedMean cluster L n i)) k ≤ t}) / Fintype.card ι

/-- **The Poisson excess-mutation test** of D'Antonio et al. (2017), through its false discovery
rate at the threshold `t = p*` (eq. (4)):

  `FDR(p*) = F_exp(p*) / F_obs(p*)`.

The elements are clustered by the rule `clustering`, applied to their five standardized
covariates of local mutation rate (`covariates`: replication timing, chromatin status, GC
content, gene density and the trinucleotide-content expectation `μᵢ = ∑ₜ n_{i,t} M_t / N_t` of
eq. (1), from `occ`, `M` and `N`). The source's rule is `k`-means on the elements of each
chromosome. Within each cluster the neutral mutation probability is estimated by
`μ̂ = (∑ᵢ nᵢ) / (∑ᵢ Lᵢ)` (`clusterRate`, eq. (2)), and element `i`, of length `L i` with `n i`
mutations, gets the upper Poisson tail `p = 1 - ∑_{k < n} λ̂^k / k! e^{-λ̂}` at `λ̂ = μ̂ L`
(`pValue`, eq. (3)). `F_obs` is the distribution function of these `p` values (`observedCDF`),
and `F_exp` that of the `p` values of counts `nᵢ ~ Po(μ̂ᵢ Lᵢ)` (`expectedCDF`), which the source
estimates by simulation. The rate of a cluster of total length `0` is `0`, and the false
discovery rate is `0` where `F_obs(p*) = 0`, by `x / 0 = 0`. -/
noncomputable def falseDiscoveryRate [Fintype τ] (clustering : (ι → Fin 5 → ℝ) → ι → κ)
    (replicationTiming chromatin gcContent geneDensity : ι → ℝ) (occ : ι → τ → ℕ)
    (M N : τ → ℕ) (L n : ι → ℕ) (t : ℝ) : ℝ :=
  let cluster := clustering (covariates replicationTiming chromatin gcContent geneDensity occ M N)
  expectedCDF cluster L n t / observedCDF cluster L n t

variable {cluster : ι → κ} {L n : ι → ℕ}

/-- The rate of a cluster is the total mutation count of its elements divided by their total
length (eq. (2)). -/
theorem clusterRate_eq (cluster : ι → κ) (L n : ι → ℕ) (c : κ) :
    clusterRate cluster L n c =
      (∑ i with cluster i = c, (n i : ℝ)) / ∑ i with cluster i = c, (L i : ℝ) := by
  rw [clusterRate, pooledMean,
    Finset.sum_subtype (p := fun i => cluster i = c) (univ.filter fun i => cluster i = c)
      (by simp) fun i => (n i : ℝ),
    Finset.sum_subtype (p := fun i => cluster i = c) (univ.filter fun i => cluster i = c)
      (by simp) fun i => (L i : ℝ)]

/-- The rate estimate is nonnegative. -/
theorem clusterRate_nonneg (cluster : ι → κ) (L n : ι → ℕ) (c : κ) :
    0 ≤ clusterRate cluster L n c := by
  rw [clusterRate_eq]
  positivity

/-- The fitted mean is `μ̂ L`. -/
theorem coe_fittedMean (cluster : ι → κ) (L n : ι → ℕ) (i : ι) :
    (fittedMean cluster L n i : ℝ) = clusterRate cluster L n (cluster i) * L i :=
  Real.coe_toNNReal _ (mul_nonneg (clusterRate_nonneg _ _ _ _) (Nat.cast_nonneg _))

/-- The test statistic is eq. (3) of D'Antonio et al. (2017):
`p = 1 - ∑_{k < n} λ̂^k / k! e^{-λ̂}` with `λ̂ = μ̂ L`. -/
theorem pValue_eq (cluster : ι → κ) (L n : ι → ℕ) (i : ι) :
    pValue cluster L n i =
      1 - ∑ k ∈ range (n i), (clusterRate cluster L n (cluster i) * L i) ^ k / (k ! : ℝ) *
        exp (-(clusterRate cluster L n (cluster i) * L i)) := by
  change (poissonMeasure _).real (Set.Ici (n i)) = _
  rw [poissonMeasure_real_Ici, coe_fittedMean]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The `p` value lies in `[0, 1]`. -/
theorem pValue_mem_Icc (cluster : ι → κ) (L n : ι → ℕ) (i : ι) :
    pValue cluster L n i ∈ Set.Icc 0 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- **The test is conservative.** For a per-nucleotide rate `μ` at most the estimate `μ̂` of the
cluster of element `i`, such as its neutral rate when the cluster also holds elements under
selection, which raise `μ̂`, the `p` value of the element's count at the mean `μ L` is at most
the reported `p` value at `λ̂ = μ̂ L`. -/
theorem upperTail_le_pValue {i : ι} {μ : ℝ≥0}
    (hμ : (μ : ℝ) ≤ clusterRate cluster L n (cluster i)) :
    upperTail (poissonMeasure (μ * L i)) (n i) ≤ pValue cluster L n i := by
  have h : μ * (L i : ℝ≥0) ≤ fittedMean cluster L n i := by
    rw [← NNReal.coe_le_coe, coe_fittedMean, NNReal.coe_mul, NNReal.coe_natCast]
    exact mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg _)
  exact poissonMeasure_real_Ici_mono (n i) h

/-- `F_obs` is nonnegative. -/
theorem observedCDF_nonneg (cluster : ι → κ) (L n : ι → ℕ) (t : ℝ) :
    0 ≤ observedCDF cluster L n t := by
  unfold observedCDF
  positivity

/-- `F_obs` is monotone. -/
theorem observedCDF_mono (cluster : ι → κ) (L n : ι → ℕ) :
    Monotone (observedCDF cluster L n) := by
  intro s t hst
  unfold observedCDF
  gcongr with i

/-- `F_exp` is nonnegative. -/
theorem expectedCDF_nonneg (cluster : ι → κ) (L n : ι → ℕ) (t : ℝ) :
    0 ≤ expectedCDF cluster L n t := by
  unfold expectedCDF
  exact div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (Nat.cast_nonneg _)

/-- `F_exp` is monotone. -/
theorem expectedCDF_mono (cluster : ι → κ) (L n : ι → ℕ) :
    Monotone (expectedCDF cluster L n) := by
  intro s t hst
  unfold expectedCDF
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => measureReal_mono ?_)
    (Nat.cast_nonneg _)
  exact fun k (hk : _ ≤ s) => show _ ≤ t from hk.trans hst

/-- **The null `p` values are super-uniform:** `F_exp(t) ≤ t` for `t ∈ [0, 1]`. A count with a
Poisson law has an upper-tail `p` value with `P(p ≤ t) ≤ t`
(`MathlibExt.Probability.Statistics.ExactTests.isValidPValue_upperTailPValue`), with equality
only at the attainable values of `p`, since the law has atoms. -/
theorem expectedCDF_le (cluster : ι → κ) (L n : ι → ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    expectedCDF cluster L n t ≤ t := by
  have hterm : ∀ r : ℝ≥0,
      (poissonMeasure r).real {k | upperTail (poissonMeasure r) k ≤ t} ≤ t := fun r =>
    ENNReal.toReal_le_of_le_ofReal ht0
      (isValidPValue_upperTailPValue (X := id) HasLaw.id t ⟨ht0, ht1⟩)
  unfold expectedCDF
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp [h0, ht0]
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    calc ∑ i, (poissonMeasure (fittedMean cluster L n i)).real
          {k | upperTail (poissonMeasure (fittedMean cluster L n i)) k ≤ t}
        ≤ ∑ _i : ι, t := Finset.sum_le_sum fun i _ => hterm _
      _ = t * Fintype.card ι := by simp [mul_comm]

/-- The false discovery rate is nonnegative. -/
theorem falseDiscoveryRate_nonneg [Fintype τ] (clustering : (ι → Fin 5 → ℝ) → ι → κ)
    (replicationTiming chromatin gcContent geneDensity : ι → ℝ) (occ : ι → τ → ℕ)
    (M N : τ → ℕ) (L n : ι → ℕ) (t : ℝ) :
    0 ≤ falseDiscoveryRate clustering replicationTiming chromatin gcContent geneDensity occ M N
      L n t :=
  div_nonneg (expectedCDF_nonneg _ _ _ _) (observedCDF_nonneg _ _ _ _)

end Test

end Domains.Biology.CancerGenomics.PoissonExcessMutation
