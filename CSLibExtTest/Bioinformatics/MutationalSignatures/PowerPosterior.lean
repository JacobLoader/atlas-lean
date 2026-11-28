/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.MutationalSignatures.PowerPosterior
import Mathlib.Tactic.NormNum

/-! Tests for the power posterior for Poisson NMF: a `1 × 1 × 1` parameter and its likelihood,
a two-type signature, a one-point parameter space on which the hypotheses of the normalization
and Bayes-rule results hold (non-vacuity), and a two-point parameter space on which the power
posterior moves from the prior at `ξ = 0` to a point mass for `ξ > 0`. -/

namespace CSLibExtTest.Bioinformatics.MutationalSignatures.PowerPosterior

open Cslib.Bioinformatics.MutationalSignatures Cslib.Bioinformatics.MutationalSignatures.PoissonNMF
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The `1 × 1 × 1` parameter with loading `L = 1` and signature `R = 1` (a probability vector on
one mutation type). -/
noncomputable def θ₁ : Params Unit Unit Unit where
  L _ _ := 1
  R _ _ := 1
  L_nonneg _ _ := zero_le_one
  R_nonneg _ _ := zero_le_one
  sum_R _ := by simp

/-- The `1 × 1 × 1` parameter with loading `L = 0`: no mutations are expected. -/
noncomputable def θ₀ : Params Unit Unit Unit where
  L _ _ := 0
  R _ _ := 1
  L_nonneg _ _ := le_rfl
  R_nonneg _ _ := zero_le_one
  sum_R _ := by simp

example : θ₁.rate () () = 1 := by
  ext
  simp [θ₁, ARDNMF.recon]

/-- The likelihood of a zero count at mean `1` is `e⁻¹`. -/
example : likelihood (fun _ _ ↦ 0) θ₁ = ENNReal.ofReal (Real.exp (-1)) := by
  simp [likelihood_eq, θ₁, ARDNMF.recon]

/-- The likelihood of a count `2` at mean `1` is `e⁻¹ / 2!`. -/
example : likelihood (fun _ _ ↦ 2) θ₁ = ENNReal.ofReal (Real.exp (-1) / 2) := by
  simp [likelihood_eq, θ₁, ARDNMF.recon]

/-- A positive count has likelihood `0` at mean `0`. -/
example : likelihood (fun _ _ ↦ 1) θ₀ = 0 := by
  simp [likelihood_eq, θ₀, ARDNMF.recon]

example : model θ₁ {fun _ _ ↦ 0} = ENNReal.ofReal (Real.exp (-1)) := by
  simp [model_singleton, likelihood_eq, θ₁, ARDNMF.recon]

/-- One process with loading `2` and the signature `(1/2, 1/2)` over two mutation types: each
count has mean `1`. -/
noncomputable def θ₂ : Params Unit Unit Bool where
  L _ _ := 2
  R _ _ := 1 / 2
  L_nonneg _ _ := zero_le_two
  R_nonneg _ _ := by norm_num
  sum_R _ := by norm_num

example (i : Bool) : θ₂.rate () i = 1 := by
  ext
  simp [θ₂, ARDNMF.recon]

example : likelihood (fun _ _ ↦ 0) θ₂ = ENNReal.ofReal (Real.exp (-1)) ^ 2 := by
  simp [likelihood_eq, θ₂, ARDNMF.recon, sq]

/-! ### A one-point parameter space -/

/-- The zero count matrix. -/
def X₀ : Unit → Unit → ℕ := fun _ _ ↦ 0

theorem normConst_onePoint (ξ : unitInterval) :
    normConst (Measure.dirac ()) 1 (fun _ ↦ θ₁) X₀ ξ =
      ENNReal.ofReal (Real.exp (-1)) ^ (ξ : ℝ) := by
  simp [normConst, likelihood_eq, θ₁, X₀, ARDNMF.recon]

theorem normConst_onePoint_ne_zero (ξ : unitInterval) :
    normConst (Measure.dirac ()) 1 (fun _ ↦ θ₁) X₀ ξ ≠ 0 := by
  rw [normConst_onePoint]
  exact (ENNReal.rpow_pos (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).ne'

theorem normConst_onePoint_ne_top (ξ : unitInterval) :
    normConst (Measure.dirac ()) 1 (fun _ ↦ θ₁) X₀ ξ ≠ ∞ := by
  rw [normConst_onePoint]
  exact ENNReal.rpow_ne_top_of_nonneg ξ.2.1 ENNReal.ofReal_ne_top

/-- The hypotheses `0 < Z_ξ(X) < ∞` of the normalization hold here. -/
example (ξ : unitInterval) :
    ∫⁻ θ, powerPosterior (Measure.dirac ()) 1 (fun _ ↦ θ₁) X₀ ξ θ ∂Measure.dirac () = 1 :=
  lintegral_powerPosterior (normConst_onePoint_ne_zero ξ) (normConst_onePoint_ne_top ξ)

example (ξ : unitInterval) :
    IsProbabilityMeasure
      ((Measure.dirac ()).withDensity (powerPosterior (Measure.dirac ()) 1 (fun _ ↦ θ₁) X₀ ξ)) :=
  isProbabilityMeasure_withDensity_powerPosterior (normConst_onePoint_ne_zero ξ)
    (normConst_onePoint_ne_top ξ)

/-- The prior `1` is a probability density with respect to the point mass. -/
example : powerPosterior (Measure.dirac ()) 1 (fun _ ↦ θ₁) X₀ 0 = 1 :=
  powerPosterior_zero (by simp)

instance : IsFiniteMeasure ((Measure.dirac ()).withDensity (1 : Unit → ℝ≥0∞)) := by
  rw [withDensity_one]
  infer_instance

/-- Bayes' rule applies: its hypotheses hold on the one-point space. -/
example :
    ((modelKernel.comap (fun _ : Unit ↦ θ₁) measurable_const)†
        ((Measure.dirac ()).withDensity 1)) X₀ =
      (Measure.dirac ()).withDensity (powerPosterior (Measure.dirac ()) 1 (fun _ ↦ θ₁) X₀ 1) :=
  posterior_eq_withDensity_powerPosterior_one measurable_const measurable_one
    (normConst_onePoint_ne_zero 1)

/-! ### A two-point parameter space

The parameters `true ↦ θ₁` (mean `1`) and `false ↦ θ₀` (mean `0`), with prior mass `1/2` each,
and the count `1`, which has likelihood `e⁻¹` under `θ₁` and `0` under `θ₀`. The prior survives
at `ξ = 0`, and for every `ξ > 0` the power posterior puts all its mass on `θ₁`. -/

/-- The two parameters. -/
noncomputable def par₂ (b : Bool) : Params Unit Unit Unit := if b then θ₁ else θ₀

/-- The count `1`. -/
def X₁ : Unit → Unit → ℕ := fun _ _ ↦ 1

theorem likelihood_par₂_true : likelihood X₁ (par₂ true) = ENNReal.ofReal (Real.exp (-1)) := by
  simp [par₂, likelihood_eq, θ₁, X₁, ARDNMF.recon]

theorem likelihood_par₂_false : likelihood X₁ (par₂ false) = 0 := by
  simp [par₂, likelihood_eq, θ₀, X₁, ARDNMF.recon]

/-- At `ξ = 0` the power posterior is the uniform prior, even at `θ₀`, which cannot have produced
the count. -/
example : powerPosterior Measure.count (fun _ ↦ 2⁻¹) par₂ X₁ 0 false = 2⁻¹ := by
  rw [powerPosterior_zero]
  rw [lintegral_count, tsum_fintype, Fintype.sum_bool, ENNReal.inv_two_add_inv_two]

theorem normConst_two (ξ : unitInterval) (hξ : 0 < (ξ : ℝ)) :
    normConst Measure.count (fun _ ↦ 2⁻¹) par₂ X₁ ξ =
      ENNReal.ofReal (Real.exp (-1)) ^ (ξ : ℝ) * 2⁻¹ := by
  simp [normConst, lintegral_count, likelihood_par₂_true, likelihood_par₂_false,
    ENNReal.zero_rpow_of_pos hξ]

/-- For `ξ > 0` the power posterior gives `θ₁` density `1`. -/
example (ξ : unitInterval) (hξ : 0 < (ξ : ℝ)) :
    powerPosterior Measure.count (fun _ ↦ 2⁻¹) par₂ X₁ ξ true = 1 := by
  rw [powerPosterior, normConst_two ξ hξ, likelihood_par₂_true]
  refine ENNReal.div_self ?_ ?_
  · exact mul_ne_zero (ENNReal.rpow_pos (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).ne'
      (by simp)
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ξ.2.1 ENNReal.ofReal_ne_top)
      (by simp)

/-- For `ξ > 0` the power posterior gives `θ₀` density `0`. -/
example (ξ : unitInterval) (hξ : 0 < (ξ : ℝ)) :
    powerPosterior Measure.count (fun _ ↦ 2⁻¹) par₂ X₁ ξ false = 0 := by
  simp [powerPosterior, likelihood_par₂_false, ENNReal.zero_rpow_of_pos hξ]

/-- The log density at `θ₀` is `-∞` for `ξ > 0`, as `ξ · log 0 = -∞`. -/
example (ξ : unitInterval) (hξ : 0 < (ξ : ℝ)) :
    ENNReal.log (powerPosterior Measure.count (fun _ ↦ 2⁻¹) par₂ X₁ ξ false) = ⊥ := by
  simp [powerPosterior, likelihood_par₂_false, ENNReal.zero_rpow_of_pos hξ]

end CSLibExtTest.Bioinformatics.MutationalSignatures.PowerPosterior
