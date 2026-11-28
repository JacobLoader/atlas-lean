/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.Distributions.PoissonBinomial

import Mathlib.MeasureTheory.Measure.Real
import MathlibExt.Probability.Distributions.PoissonBinomialEventCount
import MathlibExt.Probability.Independence.Blocks

/-!
# Poisson-binomial test for frequently mutated regulatory elements

Corona et al. (2020, Methods, "Identifying FMREs") look for the noncoding regulatory elements of a
cohort of `S` tumour samples that are mutated in more samples than chance allows. Sample `k` has a
global background mutation rate per base pair `p_k = n_k / n_cov`: the number `n_k` of noncoding
single-nucleotide variants called in it, divided by the total length `n_cov`, in base pairs, of
the regions of interest. The null hypothesis is that each base pair of an element of length `n`
is mutated in sample `k` with probability `p_k`, independently over all samples and base pairs.
Sample `k` then carries at least one mutation in the element with probability
`1 - (1 - p_k) ^ n`, independently of the other samples, so the number `X` of samples with at
least one mutation in the element has the Poisson-binomial law with success probabilities
`(1 - (1 - p_k) ^ n)_k`. The p-value of an element mutated in `s` samples is the upper tail
`P(X ≥ s)` of that law; Corona et al. adjust these p-values for multiple testing with the
Benjamini–Hochberg method and call the elements that remain significant frequently mutated.

In the null model, `M k b` is the event that base pair `b` of the element is mutated in sample
`k`. These events are mutually independent (`iIndepSet (Function.uncurry M) μ`), so the events
`⋃ b, M k b` of the different samples are too
(`ProbabilityTheory.iIndepSet.iIndepSet_of_measurableSet_generateFrom`), and the number of samples
in which one of them occurs has the Poisson-binomial law
(`ProbabilityTheory.iIndepSet.measureReal_ncard_eq_poissonBinomialPMF`,
`ProbabilityTheory.iIndepSet.measureReal_le_ncard_eq_poissonBinomialTail`).

## Main results

* `elementPValue`: the p-value `P(X ≥ s)` of an element of length `n` mutated in `s` samples,
  with the background rates `n_k / n_cov`.
* `measureReal_iUnion_eq_one_sub_pow`: under the null model, sample `k` carries a mutation in
  the element with probability `1 - (1 - p_k) ^ n`.
* `measureReal_ncard_eq_poissonBinomialPMF`, `measureReal_le_ncard_eq_poissonBinomialTail`: the
  number of samples with a mutation in the element has the Poisson-binomial law with success
  probabilities `1 - (1 - p_k) ^ n`.
* `measureReal_le_ncard_eq_elementPValue`: with the background rates `p_k = n_k / n_cov`, the
  probability `P(X ≥ s)` is `elementPValue`.
* `elementPValue_mono_length`: when every rate is at most one, the p-value of a fixed number of
  mutated samples does not decrease with the length of the element.

## References

* R. I. Corona et al., *Non-coding somatic mutations converge on the PAX8 pathway in ovarian
  cancer*, Nature Communications 11 (2020), 2020, Methods, "Identifying FMREs".
  <https://doi.org/10.1038/s41467-020-15951-0>
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace Domains.Biology.CancerGenomics.FrequentlyMutatedElements

/-- **Poisson-binomial test for frequently mutated regulatory elements** (Corona et al. 2020).
Let a cohort of $S$ tumour samples have $n_k$ noncoding single-nucleotide variants called in
sample $k$, and let the regions of interest cover $n_{\mathrm{cov}}$ base pairs, so that sample
$k$ has the global background mutation rate per base pair $p_k = n_k / n_{\mathrm{cov}}$ (with
$n_k / 0 = 0$). For a regulatory element of length $n$ base pairs in which $s$ samples carry at
least one mutation, the p-value of the test is the upper tail

$$\sum_{j = s}^{S} \pi(j)$$

of the Poisson-binomial law $\pi$ with success probabilities $1 - (1 - p_k)^n$,
$k = 0, \dots, S - 1$: the probability, under the null hypothesis that every base pair is mutated
independently at its sample's rate, that at least $s$ samples carry a mutation in the element
(`measureReal_le_ncard_eq_elementPValue`). An element is called frequently mutated when its
p-value is significant after correction for multiple testing. -/
noncomputable def elementPValue {S : ℕ} (nSNV : Fin S → ℕ) (nCov n s : ℕ) : ℝ :=
  poissonBinomialTail (fun k => 1 - (1 - (nSNV k : ℝ) / nCov) ^ n) s

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {S n : ℕ}
  {M : Fin S → Fin n → Set Ω} {p : Fin S → ℝ}

/-- The events "sample `k` carries a mutation in the element" of different samples are mutually
independent. -/
private lemma iIndepSet_iUnion (hM : ∀ k b, MeasurableSet (M k b))
    (h : iIndepSet (Function.uncurry M) μ) : iIndepSet (fun k => ⋃ b, M k b) μ :=
  h.iIndepSet_of_measurableSet_generateFrom (fun x => hM x.1 x.2) Prod.fst fun k =>
    MeasurableSet.iUnion fun b => measurableSet_generateFrom ⟨(k, b), rfl, rfl⟩

/-- **Probability that a sample carries a mutation in a regulatory element.** Let $\mu$ be a
probability measure and let $M_{k,b}$, for samples $k < S$ and base pairs $b < n$ of a
regulatory element, be mutually independent measurable events, the event $M_{k,b}$ that base
pair $b$ is mutated in sample $k$ having probability $p_k$. Then sample $k$ carries at least
one mutation in the element with probability

$$\mu\Bigl(\bigcup_{b < n} M_{k,b}\Bigr) = 1 - (1 - p_k)^n.$$ -/
theorem measureReal_iUnion_eq_one_sub_pow (hM : ∀ k b, MeasurableSet (M k b))
    (h : iIndepSet (Function.uncurry M) μ) (hp : ∀ k b, μ.real (M k b) = p k) (k : Fin S) :
    μ.real (⋃ b, M k b) = 1 - (1 - p k) ^ n := by
  have := h.isProbabilityMeasure
  have hk : iIndepSet (M k) μ :=
    (h.precomp (Prod.mk_right_injective k) : iIndepSet (Function.uncurry M ∘ Prod.mk k) μ)
  have hc : iIndepSet (fun b => (M k b)ᶜ) μ :=
    hk.iIndepSet_of_measurableSet_generateFrom (hM k) (id : Fin n → Fin n)
      (D := fun b => (M k b)ᶜ) fun b =>
        MeasurableSet.compl (measurableSet_generateFrom ⟨b, rfl, rfl⟩)
  have hinter : μ.real (⋂ b, (M k b)ᶜ) = ∏ b, μ.real (M k b)ᶜ := by
    simpa [measureReal_def, ENNReal.toReal_prod] using
      congrArg ENNReal.toReal (hc.meas_biInter Finset.univ)
  rw [← compl_compl (⋃ b, M k b), Set.compl_iUnion,
    probReal_compl_eq_one_sub (MeasurableSet.iInter fun b => (hM k b).compl), hinter]
  simp [probReal_compl_eq_one_sub (hM k _), hp]

/-- **Null law of the number of samples mutated in a regulatory element** (Corona et al. 2020).
Let $\mu$ be a probability measure and let $M_{k,b}$, for samples $k < S$ and base pairs
$b < n$ of a regulatory element, be mutually independent measurable events, the event $M_{k,b}$
that base pair $b$ is mutated in sample $k$ having probability $p_k$. Then the number
$X = \#\{k : \text{some } M_{k,b} \text{ occurs}\}$ of samples carrying at least one mutation in
the element has the Poisson-binomial law with success probabilities $1 - (1 - p_k)^n$: for every
$j \in \mathbb{N}$, $\mu\{X = j\} = \pi(j)$, where $\pi$ is the Poisson-binomial mass function of
the vector $\bigl(1 - (1 - p_k)^n\bigr)_{k < S}$. -/
theorem measureReal_ncard_eq_poissonBinomialPMF (hM : ∀ k b, MeasurableSet (M k b))
    (h : iIndepSet (Function.uncurry M) μ) (hp : ∀ k b, μ.real (M k b) = p k) (j : ℕ) :
    μ.real {ω | {k | ∃ b, ω ∈ M k b}.ncard = j} =
      poissonBinomialPMF (fun k => 1 - (1 - p k) ^ n) j := by
  simpa using (iIndepSet_iUnion hM h).measureReal_ncard_eq_poissonBinomialPMF
    (fun k => MeasurableSet.iUnion (hM k)) (measureReal_iUnion_eq_one_sub_pow hM h hp) j

/-- **Upper tail of the number of samples mutated in a regulatory element.** Let $\mu$ be a
probability measure and let $M_{k,b}$, for samples $k < S$ and base pairs $b < n$ of a
regulatory element, be mutually independent measurable events, the event $M_{k,b}$ that base
pair $b$ is mutated in sample $k$ having probability $p_k$. Then for every $s \in \mathbb{N}$
the probability that at least $s$ samples carry a mutation in the element is the
Poisson-binomial upper tail

$$\mu\{X \ge s\} = \sum_{j = s}^{S} \pi(j),$$

where $X = \#\{k : \text{some } M_{k,b} \text{ occurs}\}$ and $\pi$ is the Poisson-binomial mass
function of the vector $\bigl(1 - (1 - p_k)^n\bigr)_{k < S}$. -/
theorem measureReal_le_ncard_eq_poissonBinomialTail (hM : ∀ k b, MeasurableSet (M k b))
    (h : iIndepSet (Function.uncurry M) μ) (hp : ∀ k b, μ.real (M k b) = p k) (s : ℕ) :
    μ.real {ω | s ≤ {k | ∃ b, ω ∈ M k b}.ncard} =
      poissonBinomialTail (fun k => 1 - (1 - p k) ^ n) s := by
  simpa using (iIndepSet_iUnion hM h).measureReal_le_ncard_eq_poissonBinomialTail
    (fun k => MeasurableSet.iUnion (hM k)) (measureReal_iUnion_eq_one_sub_pow hM h hp) s

/-- **The test's p-value is the null probability of at least as many mutated samples.** Let a
cohort of $S$ samples have $n_k$ noncoding single-nucleotide variants called in sample $k$ over
regions of interest covering $n_{\mathrm{cov}}$ base pairs. Let $\mu$ be a probability measure
and let $M_{k,b}$, for $k < S$ and base pairs $b < n$ of a regulatory element, be mutually
independent measurable events, the event $M_{k,b}$ that base pair $b$ is mutated in sample $k$
having probability $n_k / n_{\mathrm{cov}}$. Then for every $s \in \mathbb{N}$ the probability
that at least $s$ samples carry a mutation in the element is `elementPValue`, the upper tail at
$s$ of the Poisson-binomial law with success probabilities
$1 - (1 - n_k / n_{\mathrm{cov}})^n$. -/
theorem measureReal_le_ncard_eq_elementPValue {nSNV : Fin S → ℕ} {nCov : ℕ}
    (hM : ∀ k b, MeasurableSet (M k b)) (h : iIndepSet (Function.uncurry M) μ)
    (hp : ∀ k b, μ.real (M k b) = (nSNV k : ℝ) / nCov) (s : ℕ) :
    μ.real {ω | s ≤ {k | ∃ b, ω ∈ M k b}.ncard} = elementPValue nSNV nCov n s :=
  measureReal_le_ncard_eq_poissonBinomialTail (p := fun k => (nSNV k : ℝ) / nCov) hM h hp s

/-- **Longer elements have larger p-values.** Let a cohort of $S$ samples have $n_k$ noncoding
single-nucleotide variants called in sample $k$ over regions of interest covering
$n_{\mathrm{cov}}$ base pairs, with $n_k \le n_{\mathrm{cov}}$ for every $k$, so that every
background rate $p_k = n_k / n_{\mathrm{cov}}$ lies in $[0, 1]$. If $n \le n'$, then for every
number $s$ of mutated samples the p-value `elementPValue` of an element of length $n$ is at most
that of an element of length $n'$: each success probability $1 - (1 - p_k)^n$ does not decrease
with the length, and the Poisson-binomial upper tail does not decrease when a success probability
grows. -/
theorem elementPValue_mono_length {nSNV : Fin S → ℕ} {nCov : ℕ} (hle : ∀ k, nSNV k ≤ nCov)
    {n n' : ℕ} (hn : n ≤ n') (s : ℕ) :
    elementPValue nSNV nCov n s ≤ elementPValue nSNV nCov n' s := by
  have hq (k : Fin S) : (nSNV k : ℝ) / nCov ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast hle k) (Nat.cast_nonneg _)⟩
  have h0 (k : Fin S) : 0 ≤ 1 - (nSNV k : ℝ) / nCov := sub_nonneg.mpr (hq k).2
  have h1 (k : Fin S) : 1 - (nSNV k : ℝ) / nCov ≤ 1 := sub_le_self _ (hq k).1
  have hmem (m : ℕ) (k : Fin S) :
      1 - (1 - (nSNV k : ℝ) / nCov) ^ m ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (pow_le_one₀ (h0 k) (h1 k)), sub_le_self _ (pow_nonneg (h0 k) m)⟩
  exact poissonBinomialTail_mono (hmem n) (hmem n')
    (fun k => sub_le_sub_left (pow_le_pow_of_le_one (h0 k) (h1 k) hn) 1) s

end Domains.Biology.CancerGenomics.FrequentlyMutatedElements
