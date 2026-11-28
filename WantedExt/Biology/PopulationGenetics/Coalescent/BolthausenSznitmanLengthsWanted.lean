/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Domains.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Total, internal and external lengths of the Bolthausen–Sznitman coalescent

The Bolthausen–Sznitman coalescent is the Λ-coalescent with `Λ` uniform on `[0, 1]` (`volume`
on `unitInterval`): while there are `b` blocks, each particular set of `k ≥ 2` of them merges at
rate `λ_{b,k} = (k - 2)! (b - k)! / (b - 1)!`, and some merger happens at total rate
`λ_b = b - 1` (`LambdaCoalescent.mergerRate_volume`, `LambdaCoalescent.totalMergerRate_volume`).
For a sample of `n` genes, the genealogy is the partition-valued chain of
`Domains.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent`, driven by steps of law
`inputMeasure volume n`, and `L⁽ⁿ⁾`, `E⁽ⁿ⁾` and `I⁽ⁿ⁾ = L⁽ⁿ⁾ - E⁽ⁿ⁾` are its total, external and
internal branch lengths (`totalLength`, `externalLength`, `internalLength`). Let `Z` be the
strictly `1`-stable random variable with characteristic exponent
`-log E[e^{iθZ}] = (π / 2) |θ| - iθ log |θ|`. Kersting, Pardo and Siri-Jégousse (2014) proved:

* (Theorem 1.1) `(log n)² / n · I⁽ⁿ⁾ → 1` in probability;
* (Corollary 1.2) `(log n)² / n · E⁽ⁿ⁾ - log n - log log n → Z - 1` in distribution;
* (Proposition 3.1) if mutations fall on the tree as a Poisson process of rate `μ` per unit
  branch length, the numbers `M_I⁽ⁿ⁾` and `M_E⁽ⁿ⁾` of mutations on the internal and on the
  external branches (`mutationMeasure`) satisfy `(log n)² / n · M_I⁽ⁿ⁾ → μ` in probability and
  `(log n)² / n · M_E⁽ⁿ⁾ - μ log n - μ log log n → μ (Z - 1)` in distribution.

Corollary 1.2 combines Theorem 1.1 with the limit
`(log n)² / n · L⁽ⁿ⁾ - log n - log log n → Z` of Drmota, Iksanov, Möhle and Rösler (2007).

Source: G. Kersting, J. C. Pardo and A. Siri-Jégousse, "Total internal and external lengths of
the Bolthausen-Sznitman coalescent", J. Appl. Probab. 51A (2014), 73–86,
doi:10.1239/jap/1417528468; preprint arXiv:1302.1463, Theorem 1.1, Corollary 1.2 and
Proposition 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped NNReal

namespace WantedExt.Biology.PopulationGenetics.Coalescent.BolthausenSznitmanLengthsWanted

open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent

/-- **Total, internal and external lengths of the Bolthausen–Sznitman coalescent** (Kersting,
Pardo and Siri-Jégousse 2014, Theorem 1.1, Corollary 1.2 and Proposition 3.1). For the
Bolthausen–Sznitman coalescent (`Λ = volume` on `[0, 1]`) of a sample of `n` genes, let `I⁽ⁿ⁾`
and `E⁽ⁿ⁾` be the internal and external branch lengths (`internalLength`, `externalLength`,
read in `ℝ` through `ENNReal.toReal`), functions of the steps of law `inputMeasure volume n`,
and let `μ ≥ 0` be a mutation rate per unit branch length. Under `mutationMeasure volume n μ`,
whose points are `(ω, (M_I⁽ⁿ⁾, M_E⁽ⁿ⁾))`, given the genealogy `ω` the numbers of mutations on the
internal and on the external branches are independent Poisson counts with means `μ I⁽ⁿ⁾(ω)` and
`μ E⁽ⁿ⁾(ω)`. Then there is a probability measure `ν` on `ℝ`, the law of the strictly `1`-stable
random variable `Z` with characteristic function `E[e^{iθZ}] = exp (-(π / 2) |θ| + iθ log |θ|)`
(so `ν` is unique), such that, as `n → ∞`:

1. `(log n)² / n · I⁽ⁿ⁾ → 1` in probability: for every `ε > 0`,
   `P(|(log n)² / n · I⁽ⁿ⁾ - 1| ≥ ε) → 0`;
2. `(log n)² / n · E⁽ⁿ⁾ - log n - log log n` converges in distribution to `Z - 1`;
3. `(log n)² / n · M_I⁽ⁿ⁾ → μ` in probability, and
   `(log n)² / n · M_E⁽ⁿ⁾ - μ log n - μ log log n` converges in distribution to `μ (Z - 1)`.

At `n ≤ 1` the conventions `Real.log 0 = 0` and `x / 0 = 0` apply; they concern finitely many
`n` and do not affect the limits.

Source: G. Kersting, J. C. Pardo and A. Siri-Jégousse, "Total internal and external lengths of
the Bolthausen-Sznitman coalescent", J. Appl. Probab. 51A (2014), 73–86,
doi:10.1239/jap/1417528468, Theorem 1.1, Corollary 1.2 and Proposition 3.1. -/
theorem_wanted tendsto_internalLength_externalLength (μ : ℝ≥0) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ θ : ℝ, charFun (ν : Measure ℝ) θ =
        Complex.exp (-↑(Real.pi / 2 * |θ|) + ↑(θ * Real.log |θ|) * Complex.I)) ∧
      (∀ ε > 0, Tendsto (fun n : ℕ => inputMeasure volume n
        {ω | ε ≤ |Real.log n ^ 2 / n * (internalLength volume n ω).toReal - 1|})
        atTop (𝓝 0)) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.log n ^ 2 / n * (externalLength volume n ω).toReal -
          Real.log n - Real.log (Real.log n))
        atTop (fun z => z - 1) (inputMeasure volume) (ν : Measure ℝ) ∧
      (∀ ε > 0, Tendsto (fun n : ℕ => mutationMeasure volume n μ
        {p | ε ≤ |Real.log n ^ 2 / n * (p.2.1 : ℝ) - μ|})
        atTop (𝓝 0)) ∧
      TendstoInDistribution
        (fun (n : ℕ) p => Real.log n ^ 2 / n * (p.2.2 : ℝ) - μ * Real.log n -
          μ * Real.log (Real.log n))
        atTop (fun z => μ * (z - 1)) (fun n => mutationMeasure volume n μ) (ν : Measure ℝ)

end WantedExt.Biology.PopulationGenetics.Coalescent.BolthausenSznitmanLengthsWanted
