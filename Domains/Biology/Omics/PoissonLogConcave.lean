/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonKernel
public import MathlibExt.Probability.Distributions.PoissonMixture
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# The Poisson log-concave compound model for read counts

Per-base read counts `x₁, …, x_G` along a genome are modelled as follows (Hashimoto, Edwards and
Gifford 2014, Methods, "Poisson log-concave distributions"). Each base has a latent log-rate
`η ∈ ℝ`, drawn independently from the density `e^{φ(η)} / ∫ e^{φ}` for a concave function `φ` (a
log-concave density), and given `η` its count is Poisson with rate `e^η`. The marginal probability
of a count `x` is

`P_φ(x) = (∫ e^{x η - e^η} / x! · e^{φ(η)} dη) / ∫ e^{φ(η)} dη`.

For estimation, the integrals are replaced by sums over quadrature points `η₁, …, η_Q` with values
`φ_q = φ(η_q)`. With `n_x` bases of count `x` and `w_{xq} = e^{x η_q - e^{η_q}} / x!`, the
maximum-likelihood problem maximizes

`ℓ(φ) = ∑ₓ n_x log ∑_q w_{xq} e^{φ_q} - (∑ₓ n_x) log ∑_q e^{φ_q}`

over the sequences `(φ_q)` whose increments `φ_{q+1} - φ_q` are nonincreasing.

## Main definitions

* `marginal φ x`: the marginal probability `P_φ(x)` of a count `x`.
* `gridMarginal η φ x`: its quadrature version `P^Q_φ(x) = ∑_q w_{xq} e^{φ_q} / ∑_q e^{φ_q}`.
* `gridLogLikelihood η n φ`: the quadrature log-likelihood `ℓ(φ)` on the grid `η` for the count
  histogram `n`.

## Main results

* `marginal_eq_poissonMixtureReal`: `P_φ` is the mixed Poisson mass function whose mixing law is
  the law of the rate `e^η`, `η ~ e^{φ} / ∫ e^{φ}` (the tilted measure `volume.tilted φ`).
* `bind_poissonMeasure_singleton`: `P_φ(x)` is the probability of the count `x` under the
  compound law: `η ~ volume.tilted φ`, then a Poisson count with rate `e^η`.
* `hasSum_marginal`: if `e^{φ}` is integrable, the masses `P_φ(x)` sum to one.
* `gridMarginal_eq_poissonMixtureReal`, `hasSum_gridMarginal`: `P^Q_φ` is the same mixed Poisson
  law with the latent law replaced by the law on the grid points with weights proportional to
  `e^{φ_q}`, and on a nonempty grid its masses sum to one.
* `gridLogLikelihood_eq_sum_log`: `ℓ(φ) = ∑ₓ n_x log P^Q_φ(x)` is the log-likelihood of the
  counts under the quadrature model.
* `antitone_grid_sub_of_concaveOn`: a concave `φ` sampled on an equally spaced grid has
  nonincreasing increments, so it satisfies the constraint of the estimation problem.
* `hasFDerivAt_gridLogLikelihood`, `hasDerivAt_gridLogLikelihood_update`: **the gradient.** The
  partial derivative of `ℓ` in `φ_q` is
  `∑ₓ n_x w_{xq} e^{φ_q} / ∑_{q'} w_{xq'} e^{φ_{q'}} - (∑ₓ n_x) e^{φ_q} / ∑_{q'} e^{φ_{q'}}`.

## Implementation notes

`P_φ` is defined by the ratio of integrals as in the source. When `e^{φ}` is not integrable the
normalising integral `∫ e^{φ}` is the junk value `0`, so `P_φ = 0`; the results that read `P_φ` as
a probability assume integrability. The latent law with density `e^{φ} / ∫ e^{φ}` is Mathlib's
tilted measure `volume.tilted φ`. Only `antitone_grid_sub_of_concaveOn` uses the concavity of `φ`:
the log-concave class keeps the nonparametric fit non-degenerate, as the source puts it, and makes
the feasible set of the grid problem convex. The source writes the normalization
`∫ e^{φ}` of `P_φ` as `∑ₖ ∫ Pois(k; e^η) e^{φ(η)} dη`, which equals it since the Poisson masses
sum to one, and likewise for the quadrature version.

Reuse: the mixed Poisson mass function and its normalization are
`ProbabilityTheory.poissonMixtureReal` and `ProbabilityTheory.hasSum_poissonMixtureReal`, the
Poisson law is Mathlib's `ProbabilityTheory.poissonMeasure`, and its measurability in the rate is
`ProbabilityTheory.measurable_poissonMeasure`.

## References

* T. B. Hashimoto, M. D. Edwards and D. K. Gifford, *Universal count correction for
  high-throughput sequencing*, PLoS Comput. Biol. 10 (2014), e1003494, Methods, "Poisson
  log-concave distributions".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace Domains.Biology.Omics.PoissonLogConcave

/-- **The Poisson log-concave compound model** (Hashimoto, Edwards and Gifford 2014). A count `x`
arises from a latent log-rate `η` with density proportional to `e^{φ(η)}` (log-concave when `φ` is
concave) and, given `η`, a Poisson law with rate `e^η`. Its marginal probability is
`P_φ(x) = (∫ e^{x η - e^η} / x! · e^{φ(η)} dη) / ∫ e^{φ(η)} dη`, the integrals over `ℝ` with
Lebesgue measure. This is a probability mass function when `e^{φ}` is integrable
(`hasSum_marginal`); otherwise the normalising integral `∫ e^{φ}` is the junk value `0`, so
`P_φ(x) = 0`. -/
noncomputable def marginal (φ : ℝ → ℝ) (x : ℕ) : ℝ :=
  (∫ η, exp (x * η - exp η) / x.factorial * exp (φ η)) / ∫ η, exp (φ η)

/-- **The quadrature marginal probability** of the Poisson log-concave compound model: the
integrals of `marginal` replaced by sums over the grid `η₁, …, η_Q` (`η : Fin Q → ℝ`), with `φ q`
the value of the latent log-density at `η q`,
`P^Q_φ(x) = ∑_q w_{xq} e^{φ_q} / ∑_q e^{φ_q}` with `w_{xq} = e^{x η_q - e^{η_q}} / x!`.
On a nonempty grid this is a probability mass function (`hasSum_gridMarginal`); on the empty grid
it is `0`. -/
noncomputable def gridMarginal {Q : ℕ} (η φ : Fin Q → ℝ) (x : ℕ) : ℝ :=
  (∑ q, exp (x * η q - exp (η q)) / x.factorial * exp (φ q)) / ∑ q, exp (φ q)

/-- **The quadrature log-likelihood** of the Poisson log-concave compound model. On the grid
`η₁, …, η_Q` (`η : Fin Q → ℝ`), with `n x` bases of count `x` and `φ q` the value of the latent
log-density at `η q`, it is
`ℓ(φ) = ∑ₓ n_x log ∑_q w_{xq} e^{φ_q} - (∑ₓ n_x) log ∑_q e^{φ_q}`, where
`w_{xq} = e^{x η_q - e^{η_q}} / x!`. The maximum-likelihood estimate maximizes it over the sequences
whose increments `φ (q + 1) - φ q` are nonincreasing (`antitone_grid_sub_of_concaveOn`). On a
nonempty grid it is the log-likelihood `∑ₓ n_x log P^Q_φ(x)` of the counts under the quadrature
model (`gridLogLikelihood_eq_sum_log`); on the empty grid both logarithms are `log 0 = 0`. -/
noncomputable def gridLogLikelihood {Q : ℕ} (η : Fin Q → ℝ) (n : ℕ →₀ ℕ) (φ : Fin Q → ℝ) : ℝ :=
  (∑ x ∈ n.support, (n x : ℝ) * log (∑ q, exp (x * η q - exp (η q)) / x.factorial * exp (φ q))) -
    (∑ x ∈ n.support, (n x : ℝ)) * log (∑ q, exp (φ q))

/-- The Poisson weight `e^{x η - e^η} / x!` is the Poisson mass of `x` at rate `e^η`. -/
private lemma exp_mul_sub_exp_div_factorial (x : ℕ) (η : ℝ) :
    exp (x * η - exp η) / x.factorial = exp (-exp η) * exp η ^ x / x.factorial := by
  rw [← exp_nat_mul, ← exp_add]
  ring_nf

/-- The Poisson weight `e^{x η - e^η} / x!` is at most one. -/
private lemma exp_mul_sub_exp_div_factorial_le_one (x : ℕ) (η : ℝ) :
    exp (x * η - exp η) / x.factorial ≤ 1 := by
  rw [exp_mul_sub_exp_div_factorial]
  have h := le_hasSum (hasSum_one_poissonMeasure (exp η).toNNReal) x fun _ _ => by positivity
  rwa [Real.coe_toNNReal _ (exp_pos η).le] at h

/-- The integrand of the numerator of `P_φ(x)` is integrable when `e^{φ}` is. -/
private lemma integrable_weight_mul {φ : ℝ → ℝ} (hφ : Integrable fun η => exp (φ η)) (x : ℕ) :
    Integrable fun η => exp (x * η - exp η) / x.factorial * exp (φ η) := by
  refine hφ.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact exp_mul_sub_exp_div_factorial_le_one x η

/-- The marginal probability is nonnegative. -/
theorem marginal_nonneg (φ : ℝ → ℝ) (x : ℕ) : 0 ≤ marginal φ x :=
  div_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)

/-- **`P_φ` is a mixed Poisson law.** The marginal probability is the mixed Poisson mass function
whose mixing law is the law of the rate `e^η` for a latent log-rate `η` with density
`e^{φ} / ∫ e^{φ}`, the tilted measure `volume.tilted φ`. -/
theorem marginal_eq_poissonMixtureReal (φ : ℝ → ℝ) (x : ℕ) :
    marginal φ x = poissonMixtureReal ((volume.tilted φ).map exp) x := by
  rw [poissonMixtureReal, integral_map measurable_exp.aemeasurable (by fun_prop), integral_tilted,
    marginal, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [smul_eq_mul, exp_mul_sub_exp_div_factorial]
  ring

/-- **The marginal probability of the compound model.** Draw a latent log-rate `η` with density
`e^{φ} / ∫ e^{φ}` (the tilted measure `volume.tilted φ`), then a count from the Poisson law with
rate `e^η`: the count is `x` with probability `P_φ(x)`. -/
theorem bind_poissonMeasure_singleton (φ : ℝ → ℝ) (x : ℕ) :
    (volume.tilted φ).bind (fun η => poissonMeasure (exp η).toNNReal) {x} =
      ENNReal.ofReal (marginal φ x) := by
  have hκ : Measurable fun η : ℝ => poissonMeasure (exp η).toNNReal :=
    measurable_poissonMeasure.comp measurable_exp.real_toNNReal
  rw [Measure.bind_apply (measurableSet_singleton x) hκ.aemeasurable, lintegral_tilted]
  simp_rw [poissonMeasure_singleton, Real.coe_toNNReal _ (exp_pos _).le,
    ← exp_mul_sub_exp_div_factorial, ← ENNReal.ofReal_mul (div_nonneg (exp_pos _).le
      (integral_nonneg fun _ => (exp_pos _).le))]
  by_cases hφ : Integrable fun η => exp (φ η)
  · rw [← ofReal_integral_eq_lintegral_ofReal
      (((integrable_weight_mul hφ x).div_const (∫ s, exp (φ s))).congr
        (Filter.Eventually.of_forall fun η => by simp only; ring))
      (Filter.Eventually.of_forall fun _ => by positivity), marginal, ← integral_div]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only
    ring
  · simp [integral_undef hφ, marginal]

/-- **Normalization.** If `e^{φ}` is integrable, the marginal probabilities `P_φ(x)` sum to one
over the counts `x`. -/
theorem hasSum_marginal {φ : ℝ → ℝ} (hφ : Integrable fun η => exp (φ η)) :
    HasSum (marginal φ) 1 := by
  have := isProbabilityMeasure_tilted hφ
  have h := hasSum_poissonMixtureReal (ν := (volume.tilted φ).map exp)
    ((ae_map_iff measurable_exp.aemeasurable measurableSet_Ici).2
      (Filter.Eventually.of_forall fun η => (exp_pos η).le))
  convert h using 1
  funext x
  exact marginal_eq_poissonMixtureReal φ x

/-- **The quadrature model is a mixed Poisson law.** `P^Q_φ` is the mixed Poisson mass function
whose mixing law puts mass `e^{φ_q} / ∑_{q'} e^{φ_{q'}}` on the rate `e^{η_q}`: the latent law of
`marginal_eq_poissonMixtureReal` with the integrals over `ℝ` replaced by sums over the grid. -/
theorem gridMarginal_eq_poissonMixtureReal {Q : ℕ} (η φ : Fin Q → ℝ) (x : ℕ) :
    gridMarginal η φ x = poissonMixtureReal
      (∑ q, ENNReal.ofReal (exp (φ q) / ∑ q', exp (φ q')) • Measure.dirac (exp (η q))) x := by
  rw [poissonMixtureReal, integral_finsetSum_measure fun q _ =>
    (integrable_dirac ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [gridMarginal, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ENNReal.toReal_ofReal (div_nonneg (exp_pos _).le
    (Finset.sum_nonneg fun _ _ => (exp_pos _).le)), exp_mul_sub_exp_div_factorial]
  ring

/-- **The quadrature masses sum to one.** On a nonempty grid, `P^Q_φ` is a probability mass
function on the counts. -/
theorem hasSum_gridMarginal {Q : ℕ} [NeZero Q] (η φ : Fin Q → ℝ) :
    HasSum (gridMarginal η φ) 1 := by
  have hZ : 0 < ∑ q, exp (φ q) := Finset.sum_pos (fun q _ => exp_pos _) Finset.univ_nonempty
  have h : HasSum (fun x : ℕ => ∑ q, exp (x * η q - exp (η q)) / x.factorial * exp (φ q))
      (∑ q, exp (φ q)) := by
    refine hasSum_sum fun q _ => ?_
    have := (hasSum_one_poissonMeasure (exp (η q)).toNNReal).mul_right (exp (φ q))
    rw [one_mul] at this
    convert this using 2 with x
    simp only [Real.coe_toNNReal _ (exp_pos _).le, exp_mul_sub_exp_div_factorial]
  convert h.div_const (∑ q, exp (φ q)) using 1
  · rfl
  · exact (div_self hZ.ne').symm

/-- **`ℓ` is a log-likelihood.** On a nonempty grid, the quadrature log-likelihood is
`∑ₓ n_x log P^Q_φ(x)`, the log-likelihood of `n x` independent bases of each count `x` under the
quadrature model. -/
theorem gridLogLikelihood_eq_sum_log {Q : ℕ} [NeZero Q] (η : Fin Q → ℝ) (n : ℕ →₀ ℕ)
    (φ : Fin Q → ℝ) :
    gridLogLikelihood η n φ = ∑ x ∈ n.support, (n x : ℝ) * log (gridMarginal η φ x) := by
  have hZ : 0 < ∑ q, exp (φ q) := Finset.sum_pos (fun q _ => exp_pos _) Finset.univ_nonempty
  have hS : ∀ x : ℕ, 0 < ∑ q, exp (x * η q - exp (η q)) / x.factorial * exp (φ q) := fun x =>
    Finset.sum_pos (fun q _ => by positivity) Finset.univ_nonempty
  simp only [gridLogLikelihood, gridMarginal, log_div (hS _).ne' hZ.ne', mul_sub,
    Finset.sum_sub_distrib, Finset.sum_mul]

/-- **The discrete concavity constraint.** A concave `φ` sampled on an equally spaced grid
`η q = a + q h` has nonincreasing increments `φ (η (q + 1)) - φ (η q)`. -/
theorem antitone_grid_sub_of_concaveOn {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {Q : ℕ}
    {η : Fin (Q + 1) → ℝ} {a h : ℝ} (hη : ∀ q, η q = a + q * h) :
    Antitone fun q : Fin Q => φ (η q.succ) - φ (η q.castSucc) := by
  have hnat : Antitone fun k : ℕ => φ (a + (k + 1 : ℕ) * h) - φ (a + k * h) := by
    refine antitone_nat_of_succ_le fun k => ?_
    have hmid := hφ.2 (Set.mem_univ (a + k * h)) (Set.mem_univ (a + (k + 2 : ℕ) * h))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hmid
    have : 1 / 2 * (a + k * h) + 1 / 2 * (a + (k + 2 : ℕ) * h) = a + (k + 1 : ℕ) * h := by
      push_cast
      ring
    rw [this] at hmid
    have e : a + ((k + 1 : ℕ) + 1 : ℕ) * h = a + (k + 2 : ℕ) * h := by push_cast; ring
    simp only [e]
    linarith
  intro q q' hqq'
  have := hnat (show (q : ℕ) ≤ q' from hqq')
  simpa [hη, Fin.val_succ] using this

/-- **The gradient of the quadrature log-likelihood.** Its partial derivative in `φ q` is the
expected number of bases whose latent log-rate is at grid point `q` given their counts, minus the
number the prior alone predicts:
`∑ₓ n_x w_{xq} e^{φ_q} / ∑_{q'} w_{xq'} e^{φ_{q'}} - (∑ₓ n_x) e^{φ_q} / ∑_{q'} e^{φ_{q'}}`. -/
theorem hasFDerivAt_gridLogLikelihood {Q : ℕ} (η : Fin Q → ℝ) (n : ℕ →₀ ℕ) (φ : Fin Q → ℝ) :
    HasFDerivAt (gridLogLikelihood η n)
      (∑ q, ((∑ x ∈ n.support, (n x : ℝ) * (exp (x * η q - exp (η q)) / x.factorial * exp (φ q) /
          ∑ q', exp (x * η q' - exp (η q')) / x.factorial * exp (φ q'))) -
        (∑ x ∈ n.support, (n x : ℝ)) * (exp (φ q) / ∑ q', exp (φ q'))) •
          (ContinuousLinearMap.proj q : (Fin Q → ℝ) →L[ℝ] ℝ)) φ := by
  rcases isEmpty_or_nonempty (Fin Q) with hQ | hQ
  · convert hasFDerivAt_of_subsingleton (𝕜 := ℝ) (gridLogLikelihood η n) φ
    simp
  have he : ∀ q, HasFDerivAt (fun ψ : Fin Q → ℝ => exp (ψ q))
      (exp (φ q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin Q => ℝ) q) φ :=
    fun q => (hasFDerivAt_apply q φ).exp
  have hS : ∀ x : ℕ, HasFDerivAt
      (fun ψ : Fin Q → ℝ => ∑ q, exp (x * η q - exp (η q)) / x.factorial * exp (ψ q))
      (∑ q, (exp (x * η q - exp (η q)) / x.factorial) •
        exp (φ q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin Q => ℝ) q) φ :=
    fun x => HasFDerivAt.fun_sum fun q _ => (he q).const_mul _
  have hT : HasFDerivAt (fun ψ : Fin Q → ℝ => ∑ q, exp (ψ q))
      (∑ q, exp (φ q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin Q => ℝ) q) φ :=
    HasFDerivAt.fun_sum fun q _ => he q
  have hSpos : ∀ x : ℕ, 0 < ∑ q, exp (x * η q - exp (η q)) / x.factorial * exp (φ q) :=
    fun x => Finset.sum_pos (fun q _ => by positivity) Finset.univ_nonempty
  have hTpos : 0 < ∑ q, exp (φ q) := Finset.sum_pos (fun q _ => exp_pos _) Finset.univ_nonempty
  have hL := (HasFDerivAt.fun_sum (u := n.support) fun x _ =>
    ((hS x).log (hSpos x).ne').const_mul (n x : ℝ)).sub
      ((hT.log hTpos.ne').const_mul (∑ x ∈ n.support, (n x : ℝ)))
  convert hL using 1
  · funext ψ
    rfl
  ext v
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, FunLike.coe_sub,
    Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun q _ => ?_
    field_simp
  · refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x _ => ?_
    field_simp

/-- **The partial derivative** of the quadrature log-likelihood in `φ q`, as in the source:
`∂ℓ / ∂φ_q` is
`∑ₓ n_x w_{xq} e^{φ_q} / ∑_{q'} w_{xq'} e^{φ_{q'}} - (∑ₓ n_x) e^{φ_q} / ∑_{q'} e^{φ_{q'}}`
(`hasFDerivAt_gridLogLikelihood` gives the full derivative). -/
theorem hasDerivAt_gridLogLikelihood_update {Q : ℕ} (η : Fin Q → ℝ) (n : ℕ →₀ ℕ)
    (φ : Fin Q → ℝ) (q : Fin Q) :
    HasDerivAt (fun t => gridLogLikelihood η n (Function.update φ q t))
      ((∑ x ∈ n.support, (n x : ℝ) * (exp (x * η q - exp (η q)) / x.factorial * exp (φ q) /
          ∑ q', exp (x * η q' - exp (η q')) / x.factorial * exp (φ q'))) -
        (∑ x ∈ n.support, (n x : ℝ)) * (exp (φ q) / ∑ q', exp (φ q'))) (φ q) := by
  have h := (hasFDerivAt_gridLogLikelihood η n φ).comp_hasDerivAt_of_eq (φ q)
    (hasDerivAt_update φ q (φ q)) (Function.update_eq_self q φ).symm
  convert h using 1
  · rfl
  simp [Pi.single_apply]

end Domains.Biology.Omics.PoissonLogConcave
