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

import Mathlib.Probability.Distributions.Bernoulli
import MathlibExt.Probability.BernoulliSumPmf

/-!
# The number of independent events that occur has the Poisson-binomial law

If `E 0, …, E (m - 1)` are mutually independent events with probabilities `p 0, …, p (m - 1)`,
then the number `#{i | ω ∈ E i}` of events that occur has the Poisson-binomial law with success
probabilities `p`: it equals `j` with probability `poissonBinomialPMF p j` and is at least `k`
with probability `poissonBinomialTail p k`. This is the event form of the law of a sum of
independent Bernoulli variables (`ProbabilityTheory.bernoulli_sum_pmf`,
`ProbabilityTheory.measure_le_sum_eq_poissonBinomialTail`), applied to the indicators of the
events. `MathlibExt.Probability.Distributions.BinomialEventCount` treats events of equal
probability, where the law is binomial.

## Main results

* `ProbabilityTheory.iIndepSet.measureReal_ncard_eq_poissonBinomialPMF`: the probability that
  exactly `j` of the events occur.
* `ProbabilityTheory.iIndepSet.measureReal_le_ncard_eq_poissonBinomialTail`: the probability that
  at least `k` of the events occur.
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m : ℕ} {E : Fin m → Set Ω}
  {p : Fin m → ℝ}

/-- The number of events that occur at `ω` is the sum of their indicators at `ω`. -/
private lemma ncard_eq_sum_indicator (ω : Ω) :
    {i | ω ∈ E i}.ncard = ∑ i, (E i).indicator (1 : Ω → ℕ) ω := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, card_filter]
  simp [Set.indicator_apply]

/-- The indicators of independent events with probabilities `p i` are independent Bernoulli
variables with parameters `p i`. -/
private lemma isBernoulliRV_indicator (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p i) (i : Fin m) :
    IsBernoulliRV ((E i).indicator (1 : Ω → ℕ)) μ (p i) := by
  have := h.isProbabilityMeasure
  rw [← hp i]
  exact ⟨by simp, hasLaw_indicator_one_bernoulliMeasure (hE i).nullMeasurableSet⟩

/-- **Mass function of the number of independent events that occur.** Let $\mu$ be a probability
measure and let $E_0, \dots, E_{m-1}$ be mutually independent measurable events, $E_i$ having
probability $p_i$. Then for every $j \in \mathbb{N}$ the probability that exactly $j$ of them
occur is the Poisson-binomial mass

$$\mu\{\omega : \#\{i : \omega \in E_i\} = j\} =
  \sum_{\substack{A \subseteq \{0, \dots, m-1\} \\ |A| = j}} \prod_{i \in A} p_i
    \prod_{i \notin A} (1 - p_i),$$

which is $0$ for $j > m$. -/
theorem iIndepSet.measureReal_ncard_eq_poissonBinomialPMF (hE : ∀ i, MeasurableSet (E i))
    (h : iIndepSet E μ) (hp : ∀ i, μ.real (E i) = p i) (j : ℕ) :
    μ.real {ω | {i | ω ∈ E i}.ncard = j} = poissonBinomialPMF p j := by
  have := h.isProbabilityMeasure
  have hpmf := bernoulli_sum_pmf (isBernoulliRV_indicator hE h hp) h.iIndepFun_indicator
    (fun i => measurable_const.indicator (hE i)) j
  rw [measureReal_def, poissonBinomialPMF, ← hpmf]
  congr 2
  ext ω
  simp [ncard_eq_sum_indicator]

/-- **Upper tail of the number of independent events that occur.** Let $\mu$ be a probability
measure and let $E_0, \dots, E_{m-1}$ be mutually independent measurable events, $E_i$ having
probability $p_i$. Then for every $k \in \mathbb{N}$ the probability that at least $k$ of them
occur is the Poisson-binomial upper tail

$$\mu\{\omega : \#\{i : \omega \in E_i\} \ge k\} = \sum_{j = k}^{m} \pi_p(j),$$

where $\pi_p$ is the Poisson-binomial mass function with success probabilities $p$; it is an
empty sum, equal to $0$, when $k > m$. -/
theorem iIndepSet.measureReal_le_ncard_eq_poissonBinomialTail (hE : ∀ i, MeasurableSet (E i))
    (h : iIndepSet E μ) (hp : ∀ i, μ.real (E i) = p i) (k : ℕ) :
    μ.real {ω | k ≤ {i | ω ∈ E i}.ncard} = poissonBinomialTail p k := by
  have := h.isProbabilityMeasure
  rw [measureReal_def, ← measure_le_sum_eq_poissonBinomialTail (isBernoulliRV_indicator hE h hp)
    h.iIndepFun_indicator (fun i => measurable_const.indicator (hE i)) k]
  simp [ncard_eq_sum_indicator]

end ProbabilityTheory
