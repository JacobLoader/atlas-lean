/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.PoissonLogConcave
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Tests for the Poisson log-concave compound model.

* a Gaussian latent log-rate, `φ η = -η²`, is log-concave with integrable `e^{φ}`, so the
  hypotheses of the normalization results hold and `P_φ` is a probability mass function;
* the compound law over that latent law gives each count the probability `P_φ(x)`;
* on a one-point grid, the quadrature model is the Poisson law at that rate and the quadrature
  log-likelihood is the Poisson log-likelihood, whatever `φ`, and its derivative vanishes;
* on a three-point grid the quadrature masses sum to one;
* on any nonempty grid the partial derivatives sum to zero: `ℓ` only sees `φ` up to a constant;
* `-η²` sampled at `0, 1, 2, …` has increments `-1, -3, -5, …`, nonincreasing as the concavity
  constraint says. -/

open MeasureTheory ProbabilityTheory Real
open Domains.Biology.Omics.PoissonLogConcave

/-- The Gaussian log-density `-η²` is concave. -/
example : ConcaveOn ℝ Set.univ fun η : ℝ => -η ^ 2 :=
  (Even.convexOn_pow (𝕜 := ℝ) even_two).neg

/-- `e^{-η²}` is integrable, so the Gaussian latent law satisfies the integrability hypothesis. -/
lemma integrable_exp_neg_sq : Integrable fun η : ℝ => exp (-η ^ 2) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

/-- The Gaussian latent law is a probability measure. -/
example : IsProbabilityMeasure (volume.tilted fun η : ℝ => -η ^ 2) :=
  isProbabilityMeasure_tilted integrable_exp_neg_sq

/-- With a Gaussian latent log-rate, the marginal probabilities sum to one. -/
example : HasSum (marginal fun η => -η ^ 2) 1 :=
  hasSum_marginal integrable_exp_neg_sq

/-- With a Gaussian latent log-rate, the count `3` has probability `P_φ(3)` under the compound
law, and so does every count. -/
example : (volume.tilted fun η : ℝ => -η ^ 2).bind (fun η => poissonMeasure (exp η).toNNReal) {3} =
    ENNReal.ofReal (marginal (fun η => -η ^ 2) 3) :=
  bind_poissonMeasure_singleton (fun η => -η ^ 2) 3

/-- On a one-point grid the quadrature model is the Poisson law with rate `e^{η₀}`. -/
example (η φ : Fin 1 → ℝ) (x : ℕ) :
    gridMarginal η φ x = exp (x * η 0 - exp (η 0)) / x.factorial := by
  rw [gridMarginal, Fin.sum_univ_one, Fin.sum_univ_one, mul_div_assoc, div_self (exp_pos _).ne',
    mul_one]

/-- On a three-point grid the quadrature masses sum to one, whatever the grid and `φ`. -/
example (η φ : Fin 3 → ℝ) : HasSum (gridMarginal η φ) 1 :=
  hasSum_gridMarginal η φ

/-- On a one-point grid the quadrature log-likelihood is the Poisson log-likelihood of the counts at
rate `e^{η₀}`: the latent log-density cancels. -/
example (η φ : Fin 1 → ℝ) (n : ℕ →₀ ℕ) :
    gridLogLikelihood η n φ =
      ∑ x ∈ n.support, (n x : ℝ) * log (exp (x * η 0 - exp (η 0)) / x.factorial) := by
  simp only [gridLogLikelihood, Fin.sum_univ_one, log_exp]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [log_mul (by positivity) (exp_pos _).ne', log_exp]
  ring

/-- On a one-point grid the derivative of the quadrature log-likelihood vanishes. -/
example (η φ : Fin 1 → ℝ) (n : ℕ →₀ ℕ) :
    HasDerivAt (fun t => gridLogLikelihood η n (Function.update φ 0 t)) 0 (φ 0) := by
  convert hasDerivAt_gridLogLikelihood_update η n φ 0 using 1
  simp only [Fin.sum_univ_one]
  rw [Finset.sum_congr rfl fun x _ => by rw [div_self (by positivity), mul_one],
    div_self (exp_pos _).ne', mul_one, sub_self]

/-- On a nonempty grid the partial derivatives of the quadrature log-likelihood sum to zero. -/
example {Q : ℕ} [NeZero Q] (η φ : Fin Q → ℝ) (n : ℕ →₀ ℕ) :
    ∑ q, ((∑ x ∈ n.support, (n x : ℝ) * (exp (x * η q - exp (η q)) / x.factorial * exp (φ q) /
          ∑ q', exp (x * η q' - exp (η q')) / x.factorial * exp (φ q'))) -
        (∑ x ∈ n.support, (n x : ℝ)) * (exp (φ q) / ∑ q', exp (φ q'))) = 0 := by
  have hT : 0 < ∑ q, exp (φ q) := Finset.sum_pos (fun q _ => exp_pos _) Finset.univ_nonempty
  have hS : ∀ x : ℕ, 0 < ∑ q, exp (x * η q - exp (η q)) / x.factorial * exp (φ q) := fun x =>
    Finset.sum_pos (fun q _ => by positivity) Finset.univ_nonempty
  rw [Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.mul_sum, ← Finset.sum_div,
    div_self hT.ne', mul_one, sub_eq_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_div, div_self (hS x).ne', mul_one]

/-- The Gaussian log-density sampled on the grid `0, 1, …, 4` satisfies the concavity constraint. -/
example : Antitone fun q : Fin 4 =>
    (fun η : ℝ => -η ^ 2) ((q.succ : ℕ) : ℝ) - (fun η : ℝ => -η ^ 2) ((q.castSucc : ℕ) : ℝ) :=
  antitone_grid_sub_of_concaveOn (Even.convexOn_pow (𝕜 := ℝ) even_two).neg
    (η := fun q : Fin 5 => ((q : ℕ) : ℝ)) (a := 0) (h := 1) fun q => by simp

/-- Its increments are `-1, -3, -5, -7`. -/
example : (fun q : Fin 4 =>
    (fun η : ℝ => -η ^ 2) ((q.succ : ℕ) : ℝ) - (fun η : ℝ => -η ^ 2) ((q.castSucc : ℕ) : ℝ)) =
      ![-1, -3, -5, -7] := by
  funext q
  fin_cases q <;> norm_num
