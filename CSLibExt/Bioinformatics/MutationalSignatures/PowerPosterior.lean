/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.MutationalSignatures.ARDNMF
public import CSLibExt.MachineLearning.Bayesian.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Topology.UnitInterval

/-!
# The power posterior for Poisson NMF

Xue, Miller, Carter and Huggins (2026) discover mutational signatures with the Poisson NMF model:
for `J` samples, `I` mutation types and `K` latent processes, the counts are independent with
`X_ji ~ Poisson(∑_k L_jk R_ki)` (Eq. 1), for nonnegative loadings `L` and nonnegative signatures
`R` whose rows sum to `1`. To make the inference robust to misspecification they replace the
standard posterior `p(X | θ) π₀(θ) / Z(X)` (Eq. 6) by the power posterior
`π_ξ(θ | X) = p(X | θ) ^ ξ π₀(θ) / Z_ξ(X)` with `ξ ∈ [0, 1]` (Eq. 7), whose log density is
`const + log π₀(θ) + ξ ∑_{j,i} log Poisson(X_ji | (L R)_ji)` (Eq. 8).

The parameter `θ` ranges over a measurable space `Θ` with a reference measure `ν` (the `dθ` of
the integrals) and a map `par : Θ → Params J K I` that reads off its loadings and signatures, so
`θ` may carry further parameters, such as the paper's mean loadings `μ`, on which the likelihood
does not depend. Densities, the likelihood and the normalizing constant take values in `[0, ∞]`.

## Main definitions

* `Params J K I`: loadings `L ≥ 0` and signatures `R ≥ 0` whose rows sum to `1`, a standard Borel
  space for countable `J` and `K`, so that Bayes' rule applies with `Θ = Params J K I`, or with
  `Θ = Params J K I × H` for a standard Borel space `H` of further parameters.
* `Params.rate`: the Poisson means `(L R)_ji`, the reconstruction `ARDNMF.recon L R`.
* `model θ`: the law of the counts (Eq. 1), with independent Poisson entries; `modelKernel` is
  the corresponding Markov kernel.
* `likelihood X θ`: the Poisson likelihood `∏_j ∏_i Poisson(X_ji | (L R)_ji)` (Eq. 2).
* `normConst ν π₀ par X ξ`: the normalizing constant `Z_ξ(X) = ∫ p(X | θ) ^ ξ π₀(θ) dν(θ)`.
* `powerPosterior ν π₀ par X ξ`: the power posterior density `π_ξ(θ | X)` (Eq. 7).

## Main results

* `model_singleton`: the likelihood is the probability that the model gives the counts `X`.
* `lintegral_powerPosterior`, `isProbabilityMeasure_withDensity_powerPosterior`: when
  `0 < Z_ξ(X) < ∞`, the power posterior is a probability density. `normConst_le` bounds
  `Z_ξ(X)` by the total mass of the prior, so a proper prior gives `Z_ξ(X) < ∞`.
* `powerPosterior_zero`: for `ξ = 0` and a prior with `∫ π₀ dν = 1`, the power posterior is the
  prior density.
* `powerPosterior_one`: for `ξ = 1` it is the standard posterior `p(X | θ) π₀(θ) / Z(X)`
  (Eq. 6); `withDensity_powerPosterior_one` identifies it with the Bayes posterior of the model
  (`Cslib.MachineLearning.Bayesian.bayesPosterior`), and
  `posterior_eq_withDensity_powerPosterior_one` with Mathlib's posterior kernel.
* `log_powerPosterior`: the log density (Eq. 8), in `[-∞, ∞]`, with constant `-log Z_ξ(X)`.

Out of scope: the paper's prior (Eqs. 3–5), its MCMC sampler and its simulation-based choice of
`ξ`.

## References

* C. Xue, J. W. Miller, S. L. Carter, J. H. Huggins, *Robust discovery of mutational signatures
  using power posteriors*, PLoS Comput. Biol. 22 (2026), e1014372 (Methods, Eqs. 1, 2, 6–8).
* J. W. Miller, D. B. Dunson, *Robust Bayesian inference via coarsening*, J. Amer. Statist.
  Assoc. 114 (2019), 1113–1125 (power posteriors).
-/

@[expose] public section

namespace Cslib.Bioinformatics.MutationalSignatures.PoissonNMF

open MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

/-- **Parameters of the Poisson NMF model.** For finite index types $J$ (samples), $K$ (latent
processes) and $I$ (mutation types), a parameter of the Poisson NMF model is a pair of real
matrices: loadings $L = (L_{jk}) \in \mathbb{R}_{\ge 0}^{J \times K}$, with nonnegative entries,
and signatures $R = (R_{ki}) \in \mathbb{R}_{\ge 0}^{K \times I}$, with nonnegative entries and
rows summing to $1$, $\sum_{i \in I} R_{ki} = 1$ for every $k \in K$, so that each row $R_k$ is a
probability vector over the mutation types. -/
structure Params (J K I : Type*) [Fintype I] where
  /-- The loadings: `L j k` is the activity of process `k` in sample `j`. -/
  L : J → K → ℝ
  /-- The signatures: `R k i` is the frequency of mutation type `i` under process `k`. -/
  R : K → I → ℝ
  /-- The loadings are nonnegative. -/
  L_nonneg : ∀ j k, 0 ≤ L j k
  /-- The signatures are nonnegative. -/
  R_nonneg : ∀ k i, 0 ≤ R k i
  /-- Each signature sums to `1` over the mutation types. -/
  sum_R : ∀ k, ∑ i, R k i = 1

namespace Params

variable {J K I : Type*} [Fintype I]

/-- Parameters carry the σ-algebra induced by their two matrices, each with the product of the
Borel σ-algebras of its entries. -/
instance : MeasurableSpace (Params J K I) :=
  MeasurableSpace.comap (fun θ ↦ (θ.L, θ.R)) inferInstance

@[fun_prop]
theorem measurable_L : Measurable (Params.L : Params J K I → J → K → ℝ) :=
  measurable_fst.comp (comap_measurable _)

@[fun_prop]
theorem measurable_R : Measurable (Params.R : Params J K I → K → I → ℝ) :=
  measurable_snd.comp (comap_measurable _)

theorem injective_prod : Function.Injective fun θ : Params J K I ↦ (θ.L, θ.R) := by
  intro a b h
  cases a
  cases b
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  rfl

theorem range_prod : Set.range (fun θ : Params J K I ↦ (θ.L, θ.R)) =
    {p | (∀ j k, 0 ≤ p.1 j k) ∧ (∀ k i, 0 ≤ p.2 k i) ∧ ∀ k, ∑ i, p.2 k i = 1} := by
  ext ⟨L, R⟩
  constructor
  · rintro ⟨θ, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨θ.L_nonneg, θ.R_nonneg, θ.sum_R⟩
  · rintro ⟨hL, hR, hR1⟩
    exact ⟨⟨L, R, hL, hR, hR1⟩, rfl⟩

/-- With countably many samples and processes, parameters form a standard Borel space: the map
`θ ↦ (θ.L, θ.R)` is a closed embedding into a Polish space for the topology it induces, whose
Borel σ-algebra is the σ-algebra of the parameters. -/
instance [Countable J] [Countable K] : StandardBorelSpace (Params J K I) := by
  let : TopologicalSpace (Params J K I) :=
    TopologicalSpace.induced (fun θ ↦ (θ.L, θ.R)) inferInstance
  have he : IsClosedEmbedding fun θ : Params J K I ↦ (θ.L, θ.R) := by
    refine ⟨⟨⟨rfl⟩, injective_prod⟩, ?_⟩
    rw [range_prod]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun j ↦ isClosed_iInter fun k ↦
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun k ↦ isClosed_iInter fun i ↦
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun k ↦ isClosed_eq (by fun_prop) continuous_const
  have : PolishSpace (Params J K I) := he.polishSpace
  have : BorelSpace (Params J K I) :=
    ⟨by rw [borel_comap, ← BorelSpace.measurable_eq]; rfl⟩
  exact ⟨⟨_, this, inferInstance⟩⟩

/-- With at least one mutation type there are parameters: zero loadings and uniform
signatures. -/
instance [Nonempty I] : Nonempty (Params J K I) :=
  ⟨{ L := fun _ _ ↦ 0
     R := fun _ _ ↦ 1 / Fintype.card I
     L_nonneg := fun _ _ ↦ le_rfl
     R_nonneg := fun _ _ ↦ by positivity
     sum_R := fun _ ↦ by
       rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
         mul_one_div_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero)] }⟩

variable [Fintype K]

/-- **Poisson means of the Poisson NMF model.** For a parameter of the Poisson NMF model with
loadings $L \in \mathbb{R}_{\ge 0}^{J \times K}$ and signatures
$R \in \mathbb{R}_{\ge 0}^{K \times I}$, the mean of the count of mutation type $i$ in sample $j$
is the entry $(LR)_{ji} = \sum_{k \in K} L_{jk} R_{ki}$ of the product $LR$, a nonnegative real
number since $L$ and $R$ have nonnegative entries. -/
def rate (θ : Params J K I) (j : J) (i : I) : ℝ≥0 :=
  ⟨ARDNMF.recon θ.L θ.R j i,
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (θ.L_nonneg j k) (θ.R_nonneg k i)⟩

@[simp]
theorem coe_rate (θ : Params J K I) (j : J) (i : I) :
    (θ.rate j i : ℝ) = ARDNMF.recon θ.L θ.R j i :=
  rfl

theorem measurable_rate (j : J) (i : I) : Measurable fun θ : Params J K I ↦ θ.rate j i := by
  refine Measurable.subtype_mk ?_
  simp only [ARDNMF.recon]
  exact Finset.measurable_sum _ fun k _ ↦
    ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_L)).mul
      ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_R))

end Params

variable {J K I : Type*} [Fintype J] [Fintype K] [Fintype I]

/-- **The Poisson NMF model.** For finite index types $J$ (samples), $K$ (latent processes) and
$I$ (mutation types), and a parameter with loadings $L \in \mathbb{R}_{\ge 0}^{J \times K}$ and
signatures $R \in \mathbb{R}_{\ge 0}^{K \times I}$ whose rows sum to $1$, the law of the count
matrix $X = (X_{ji}) \in \mathbb{N}^{J \times I}$ under which the entries are independent and
$X_{ji}$ is Poisson with mean $(LR)_{ji} = \sum_{k \in K} L_{jk} R_{ki}$: the product over
$j \in J$ and $i \in I$ of the Poisson distributions on $\mathbb{N}$ with these means. -/
noncomputable def model (θ : Params J K I) : Measure (J → I → ℕ) :=
  Measure.pi fun j ↦ Measure.pi fun i ↦ poissonMeasure (θ.rate j i)

instance (θ : Params J K I) : IsProbabilityMeasure (model θ) := by
  unfold model
  infer_instance

/-- **Poisson NMF likelihood.** For finite index types $J$ (samples), $K$ (latent processes) and
$I$ (mutation types), a count matrix $X = (X_{ji}) \in \mathbb{N}^{J \times I}$ and a parameter
with loadings $L \in \mathbb{R}_{\ge 0}^{J \times K}$ and signatures
$R \in \mathbb{R}_{\ge 0}^{K \times I}$ whose rows sum to $1$, the likelihood is
$$p(X \mid L, R) = \prod_{j \in J} \prod_{i \in I}
  \mathrm{Poisson}\Big(X_{ji} \,\Big|\, \sum_{k \in K} L_{jk} R_{ki}\Big), \qquad
  \mathrm{Poisson}(n \mid r) = \frac{e^{-r} r^n}{n!},$$
the product of the Poisson probabilities of the counts, valued in $[0, \infty]$ (in fact in
$[0, 1]$). -/
noncomputable def likelihood (X : J → I → ℕ) (θ : Params J K I) : ℝ≥0∞ :=
  ∏ j, ∏ i, poissonMeasure (θ.rate j i) {X j i}

theorem likelihood_eq (X : J → I → ℕ) (θ : Params J K I) :
    likelihood X θ = ∏ j, ∏ i, ENNReal.ofReal (Real.exp (-ARDNMF.recon θ.L θ.R j i) *
      ARDNMF.recon θ.L θ.R j i ^ X j i / (X j i).factorial) := by
  simp only [likelihood, poissonMeasure_singleton, Params.coe_rate]

/-- **The likelihood is the model's probability of the counts.** For finite index types $J$, $K$
and $I$, a parameter of the Poisson NMF model with loadings $L$ and signatures $R$ and a count
matrix $X \in \mathbb{N}^{J \times I}$, the probability of $\{X\}$ under the Poisson NMF model
of $(L, R)$, which makes the counts independent and Poisson with means $(LR)_{ji}$, is the
likelihood
$p(X \mid L, R) = \prod_{j \in J} \prod_{i \in I} \mathrm{Poisson}(X_{ji} \mid (LR)_{ji})$. -/
theorem model_singleton (θ : Params J K I) (X : J → I → ℕ) : model θ {X} = likelihood X θ := by
  simp only [model, likelihood, Measure.pi_singleton]

theorem likelihood_le_one (X : J → I → ℕ) (θ : Params J K I) : likelihood X θ ≤ 1 := by
  rw [← model_singleton]
  exact prob_le_one

theorem measurable_likelihood (X : J → I → ℕ) :
    Measurable fun θ : Params J K I ↦ likelihood X θ := by
  simp only [likelihood, poissonMeasure_singleton]
  refine Finset.measurable_prod _ fun j _ ↦ Finset.measurable_prod _ fun i _ ↦ ?_
  have h := (Params.measurable_rate (J := J) (K := K) j i).coe_nnreal_real
  exact (((h.neg.exp).mul (h.pow_const _)).div_const _).ennreal_ofReal

theorem measurable_model : Measurable (model : Params J K I → Measure (J → I → ℕ)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have h : (fun θ : Params J K I ↦ model θ s) =
      fun θ ↦ ∑' X, s.indicator (fun X ↦ likelihood X θ) X := by
    funext θ
    rw [← Measure.tsum_indicator_apply_singleton _ s hs]
    simp only [model_singleton]
  rw [h]
  refine Measurable.tsum fun X ↦ ?_
  by_cases hX : X ∈ s
  · simpa only [Set.indicator_of_mem hX] using measurable_likelihood X
  · simp only [Set.indicator_of_notMem hX]
    exact measurable_const

/-- **The Poisson NMF model as a Markov kernel.** For finite index types $J$ (samples), $K$
(latent processes) and $I$ (mutation types), the Markov kernel from the parameters of the
Poisson NMF model (loadings $L \in \mathbb{R}_{\ge 0}^{J \times K}$ and signatures
$R \in \mathbb{R}_{\ge 0}^{K \times I}$ whose rows sum to $1$) to the count matrices
$\mathbb{N}^{J \times I}$ that sends $(L, R)$ to the law under which the counts $X_{ji}$ are
independent and Poisson with means $(LR)_{ji} = \sum_{k \in K} L_{jk} R_{ki}$. -/
noncomputable def modelKernel : Kernel (Params J K I) (J → I → ℕ) where
  toFun := model
  measurable' := measurable_model

@[simp]
theorem modelKernel_apply (θ : Params J K I) : modelKernel θ = model θ :=
  rfl

instance : IsMarkovKernel (modelKernel : Kernel (Params J K I) (J → I → ℕ)) :=
  ⟨fun θ ↦ by rw [modelKernel_apply]; infer_instance⟩

section PowerPosterior

variable {Θ : Type*} [MeasurableSpace Θ]

/-- **Normalizing constant of the power posterior for Poisson NMF.** Let $\Theta$ be a
measurable space with a measure $\nu$, let $\pi_0 : \Theta \to [0, \infty]$ be a prior density
with respect to $\nu$, and let each $\theta \in \Theta$ determine Poisson NMF parameters
$\mathrm{par}(\theta)$, loadings and signatures for finite index types $J$, $K$ and $I$. For a
count matrix $X \in \mathbb{N}^{J \times I}$ and a power $\xi \in [0, 1]$,
$$Z_\xi(X) = \int_\Theta p(X \mid \theta)^\xi \, \pi_0(\theta) \, d\nu(\theta) \in [0, \infty],$$
the Lebesgue integral, where $p(X \mid \theta)$ is the Poisson NMF likelihood of
$\mathrm{par}(\theta)$ and $0^0 = 1$. -/
noncomputable def normConst (ν : Measure Θ) (π₀ : Θ → ℝ≥0∞) (par : Θ → Params J K I)
    (X : J → I → ℕ) (ξ : unitInterval) : ℝ≥0∞ :=
  ∫⁻ θ, likelihood X (par θ) ^ (ξ : ℝ) * π₀ θ ∂ν

/-- **Power posterior for Poisson NMF.** Let $\Theta$ be a measurable space of parameters with a
measure $\nu$, let $\pi_0 : \Theta \to [0, \infty]$ be a prior density with respect to $\nu$, and
let each $\theta \in \Theta$ determine Poisson NMF parameters $\mathrm{par}(\theta)$: loadings
$L \in \mathbb{R}_{\ge 0}^{J \times K}$ and signatures $R \in \mathbb{R}_{\ge 0}^{K \times I}$ whose
rows sum to $1$, for finite index types $J$ (samples), $K$ (latent processes) and $I$ (mutation
types); $\theta$ may carry further parameters. For a count matrix $X \in \mathbb{N}^{J \times I}$
and a power $\xi \in [0, 1]$, the power posterior density with respect to $\nu$ is
$$\pi_\xi(\theta \mid X) = \frac{p(X \mid \theta)^\xi \, \pi_0(\theta)}{Z_\xi(X)}, \qquad
  Z_\xi(X) = \int_\Theta p(X \mid \theta')^\xi \, \pi_0(\theta') \, d\nu(\theta'),$$
where $p(X \mid \theta) = \prod_{j \in J} \prod_{i \in I}
\mathrm{Poisson}(X_{ji} \mid \sum_{k \in K} L_{jk} R_{ki})$ is the Poisson NMF likelihood of
$\mathrm{par}(\theta)$ and $0^0 = 1$. It is a probability density when
$0 < Z_\xi(X) < \infty$. The quotient is taken in $[0, \infty]$, so otherwise its values are
conventions: $a / 0 = \infty$ for $a \ne 0$, $0 / 0 = 0$ and $a / \infty = 0$. -/
noncomputable def powerPosterior (ν : Measure Θ) (π₀ : Θ → ℝ≥0∞) (par : Θ → Params J K I)
    (X : J → I → ℕ) (ξ : unitInterval) (θ : Θ) : ℝ≥0∞ :=
  likelihood X (par θ) ^ (ξ : ℝ) * π₀ θ / normConst ν π₀ par X ξ

/-- **The normalizing constant is at most the prior mass.** Let $\Theta$ be a measurable space
with a measure $\nu$, $\pi_0 : \Theta \to [0, \infty]$ a prior density with respect to $\nu$,
and let each $\theta \in \Theta$ determine Poisson NMF parameters. For every count matrix $X$ and
every power $\xi \in [0, 1]$, the normalizing constant of the power posterior satisfies
$Z_\xi(X) = \int_\Theta p(X \mid \theta)^\xi \, \pi_0(\theta) \, d\nu(\theta) \le
\int_\Theta \pi_0 \, d\nu$, since the likelihood $p(X \mid \theta)$ is at most $1$. So
$Z_\xi(X) < \infty$ when the prior has finite mass. -/
theorem normConst_le (ν : Measure Θ) (π₀ : Θ → ℝ≥0∞) (par : Θ → Params J K I)
    (X : J → I → ℕ) (ξ : unitInterval) : normConst ν π₀ par X ξ ≤ ∫⁻ θ, π₀ θ ∂ν :=
  lintegral_mono fun θ ↦
    mul_le_of_le_one_left zero_le (ENNReal.rpow_le_one (likelihood_le_one X (par θ)) ξ.2.1)

variable {ν : Measure Θ} {π₀ : Θ → ℝ≥0∞} {par : Θ → Params J K I} {X : J → I → ℕ}
  {ξ : unitInterval}

/-- **The power posterior is a probability density.** Let $\Theta$ be a measurable space with a
measure $\nu$, $\pi_0 : \Theta \to [0, \infty]$ a prior density with respect to $\nu$, and let
each $\theta \in \Theta$ determine Poisson NMF parameters. For a count matrix $X$ and a power
$\xi \in [0, 1]$ whose normalizing constant satisfies $0 < Z_\xi(X) < \infty$, the power
posterior density integrates to one:
$\int_\Theta \pi_\xi(\theta \mid X) \, d\nu(\theta) = 1$. -/
theorem lintegral_powerPosterior (h0 : normConst ν π₀ par X ξ ≠ 0)
    (htop : normConst ν π₀ par X ξ ≠ ∞) :
    ∫⁻ θ, powerPosterior ν π₀ par X ξ θ ∂ν = 1 := by
  simp only [powerPosterior, div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 h0)]
  exact ENNReal.mul_inv_cancel h0 htop

theorem isProbabilityMeasure_withDensity_powerPosterior (h0 : normConst ν π₀ par X ξ ≠ 0)
    (htop : normConst ν π₀ par X ξ ≠ ∞) :
    IsProbabilityMeasure (ν.withDensity (powerPosterior ν π₀ par X ξ)) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_powerPosterior h0 htop]⟩

/-- **At power zero the power posterior is the prior.** Let $\Theta$ be a measurable space with a
measure $\nu$, $\pi_0 : \Theta \to [0, \infty]$ a probability density with respect to $\nu$
($\int_\Theta \pi_0 \, d\nu = 1$), and let each $\theta \in \Theta$ determine Poisson NMF
parameters. For every count matrix $X$, the power posterior with power $\xi = 0$ is the prior:
$\pi_{\xi = 0}(\theta \mid X) = \pi_0(\theta)$ for every $\theta \in \Theta$. -/
theorem powerPosterior_zero (h : ∫⁻ θ, π₀ θ ∂ν = 1) : powerPosterior ν π₀ par X 0 = π₀ := by
  funext θ
  simp [powerPosterior, normConst, h]

/-- **At power one the power posterior is the standard posterior.** Let $\Theta$ be a measurable
space with a measure $\nu$, $\pi_0 : \Theta \to [0, \infty]$ a prior density with respect to
$\nu$, and let each $\theta \in \Theta$ determine Poisson NMF parameters. For every count matrix
$X$, the power posterior with power $\xi = 1$ is the standard posterior density
$$\pi(\theta \mid X) = \frac{p(X \mid \theta) \, \pi_0(\theta)}{Z(X)}, \qquad
  Z(X) = \int_\Theta p(X \mid \theta') \, \pi_0(\theta') \, d\nu(\theta'),$$
with $p(X \mid \theta)$ the Poisson NMF likelihood, the quotient taken in $[0, \infty]$. -/
theorem powerPosterior_one (ν : Measure Θ) (π₀ : Θ → ℝ≥0∞) (par : Θ → Params J K I)
    (X : J → I → ℕ) :
    powerPosterior ν π₀ par X 1 =
      fun θ ↦ likelihood X (par θ) * π₀ θ / ∫⁻ θ', likelihood X (par θ') * π₀ θ' ∂ν := by
  funext θ
  simp [powerPosterior, normConst]

/-- **The evidence of the Poisson NMF model.** Let $\Theta$ be a measurable space with a measure
$\nu$, $\pi_0 : \Theta \to [0, \infty]$ a measurable prior density with respect to $\nu$, and
$\mathrm{par}$ a measurable map giving each $\theta \in \Theta$ its Poisson NMF parameters. Let
$\kappa$ be the likelihood kernel $\theta \mapsto P_{\mathrm{par}(\theta)}$, the Poisson NMF
model, and $\kappa \circ (\pi_0 \nu)$ the marginal law of the data under the prior
$\pi_0 \nu$. For every count matrix $X$, its evidence (marginal likelihood) is the normalizing
constant of the power posterior with power $\xi = 1$:
$$(\kappa \circ (\pi_0 \nu))(\{X\}) = Z_{\xi = 1}(X)
  = \int_\Theta p(X \mid \theta) \, \pi_0(\theta) \, d\nu(\theta).$$ -/
theorem comp_apply_singleton_eq_normConst (hpar : Measurable par) (hπ₀ : Measurable π₀) :
    (modelKernel.comap par hpar ∘ₘ ν.withDensity π₀) {X} = normConst ν π₀ par X 1 := by
  rw [MachineLearning.Bayesian.comp_apply_singleton,
    lintegral_withDensity_eq_lintegral_mul _ hπ₀
      (Kernel.measurable_coe _ (measurableSet_singleton X))]
  simp only [normConst, Pi.mul_apply, Kernel.comap_apply, modelKernel_apply, model_singleton,
    Set.Icc.coe_one, ENNReal.rpow_one, mul_comm]

/-- **The power posterior at power one is the Bayes posterior.** Let $\Theta$ be a measurable
space with a measure $\nu$, $\pi_0 : \Theta \to [0, \infty]$ a measurable prior density with
respect to $\nu$, and $\mathrm{par}$ a measurable map giving each $\theta \in \Theta$ its Poisson
NMF parameters. For every count matrix $X$, the measure with density
$\pi_{\xi = 1}(\cdot \mid X)$ with respect to $\nu$, the power posterior with power $1$, is the
Bayes posterior after observing $X$ for the prior $\pi_0 \nu$ and the
likelihood kernel $\theta \mapsto P_{\mathrm{par}(\theta)}$, the Poisson NMF model: the prior
reweighted by $\theta \mapsto P_{\mathrm{par}(\theta)}(\{X\})$ and divided by the evidence of
$X$. -/
theorem withDensity_powerPosterior_one (hpar : Measurable par) (hπ₀ : Measurable π₀) :
    ν.withDensity (powerPosterior ν π₀ par X 1) =
      MachineLearning.Bayesian.bayesPosterior (modelKernel.comap par hpar)
        (ν.withDensity π₀) X := by
  have hlik : Measurable fun θ ↦ likelihood X (par θ) := (measurable_likelihood X).comp hpar
  rw [MachineLearning.Bayesian.bayesPosterior, comp_apply_singleton_eq_normConst hpar hπ₀]
  simp only [Kernel.comap_apply, modelKernel_apply, model_singleton]
  rw [← withDensity_mul _ hπ₀ hlik, ← withDensity_smul _ (hπ₀.mul hlik)]
  congr 1
  funext θ
  simp only [powerPosterior, Set.Icc.coe_one, ENNReal.rpow_one, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, div_eq_mul_inv]
  ring

/-- **Bayes' rule for the Poisson NMF model.** Let $\Theta$ be a nonempty standard Borel space
with a measure $\nu$, $\pi_0 : \Theta \to [0, \infty]$ a measurable density with respect to
$\nu$ of finite total mass, and $\mathrm{par}$ a measurable map giving each $\theta \in \Theta$
its Poisson NMF parameters. Let $\kappa$ be the likelihood kernel
$\theta \mapsto P_{\mathrm{par}(\theta)}$, the Poisson NMF model, and $\kappa^\dagger$ Mathlib's
posterior kernel of $\kappa$ for the prior $\pi_0 \nu$. For every count matrix $X$ whose
evidence $Z_{\xi = 1}(X) = \int_\Theta p(X \mid \theta) \, \pi_0(\theta) \, d\nu(\theta)$ is
nonzero, $\kappa^\dagger(X)$ is the measure with density $\pi_{\xi = 1}(\cdot \mid X)$ with
respect to $\nu$, the power posterior with power $1$. -/
theorem posterior_eq_withDensity_powerPosterior_one [StandardBorelSpace Θ] [Nonempty Θ]
    (hpar : Measurable par) (hπ₀ : Measurable π₀) [IsFiniteMeasure (ν.withDensity π₀)]
    (h0 : normConst ν π₀ par X 1 ≠ 0) :
    ((modelKernel.comap par hpar)†(ν.withDensity π₀)) X =
      ν.withDensity (powerPosterior ν π₀ par X 1) := by
  rw [withDensity_powerPosterior_one hpar hπ₀]
  exact MachineLearning.Bayesian.posterior_eq_bayesPosterior _ _
    (by rwa [comp_apply_singleton_eq_normConst hpar hπ₀])

private theorem log_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ENNReal.log (∏ i ∈ s, f i) = ∑ i ∈ s, ENNReal.log (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ENNReal.log_mul_add, ih]

/-- **Log density of the power posterior for Poisson NMF.** Let $\Theta$ be a measurable space
with a measure $\nu$, $\pi_0 : \Theta \to [0, \infty]$ a prior density with respect to $\nu$, and
let each $\theta \in \Theta$ determine Poisson NMF parameters: loadings $L(\theta)$ and
signatures $R(\theta)$. For every count matrix $X$, power $\xi \in [0, 1]$ and
$\theta \in \Theta$, in the extended reals $[-\infty, \infty]$, with $\log 0 = -\infty$,
$\log \infty = \infty$, $-\infty + \infty = -\infty$ and $0 \cdot (-\infty) = 0$,
$$\log \pi_\xi(\theta \mid X) = -\log Z_\xi(X) + \log \pi_0(\theta)
  + \xi \sum_{j \in J} \sum_{i \in I}
    \log \mathrm{Poisson}\Big(X_{ji} \,\Big|\, \sum_{k \in K} L_{jk}(\theta) R_{ki}(\theta)\Big),$$
where $Z_\xi(X)$ is the normalizing constant, which does not depend on $\theta$. -/
theorem log_powerPosterior (ν : Measure Θ) (π₀ : Θ → ℝ≥0∞) (par : Θ → Params J K I)
    (X : J → I → ℕ) (ξ : unitInterval) (θ : Θ) :
    ENNReal.log (powerPosterior ν π₀ par X ξ θ) =
      -ENNReal.log (normConst ν π₀ par X ξ) + ENNReal.log (π₀ θ) +
        (ξ : ℝ) * ∑ j, ∑ i, ENNReal.log (poissonMeasure ((par θ).rate j i) {X j i}) := by
  rw [powerPosterior, div_eq_mul_inv, ENNReal.log_mul_add, ENNReal.log_mul_add,
    ENNReal.log_inv, ENNReal.log_rpow, likelihood, log_prod]
  simp only [log_prod]
  rw [add_comm, add_assoc, add_comm (ENNReal.log (π₀ θ))]

end PowerPosterior

end Cslib.Bioinformatics.MutationalSignatures.PoissonNMF
