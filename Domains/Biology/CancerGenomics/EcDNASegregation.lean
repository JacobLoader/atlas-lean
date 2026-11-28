/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import MathlibExt.Probability.Distributions.BinomialMoments
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Binomial segregation of extrachromosomal DNA and its neutral moments

Extrachromosomal DNA (ecDNA) elements lack centromeres and are split at random between the
daughter cells. In the model of Lange et al. (2022), every cell divides at rate `1` (time is
measured in generations). A dividing cell with `i` ecDNA copies replicates them to `2i`; one
daughter receives `k` of them, with `k` distributed as `Bin(2i, 1/2)`, and the other receives
`2i - k`. Cells without ecDNA have only ecDNA-free daughters.

The expected number `N_k(t)` of cells with `k` copies then evolves by the mean equations

`dN_k/dt = -N_k + 2 ∑ᵢ N_i C(2i, k) 2^{-2i}`:

a division of a cell with `i` copies removes it and adds two daughters, each of which has `k`
copies with probability `segregationProb i k = C(2i, k) 2^{-2i}`. The terms with `2i < k`
vanish, so the sum runs over `i ≥ ⌈k/2⌉`. `IsSolution N` says that `N` is a nonnegative
solution of these equations on `t ≥ 0` with a finite population `N(t) = ∑ₖ N_k(t)`.

## Main definitions

* `segregationProb i k`: the probability `C(2i, k) 2^{-2i}` that a daughter of a cell with `i`
  copies receives `k` copies, the mass of `Bin(2i, 1/2)` at `k`.
* `IsSolution N`: the binomial segregation model under neutral growth.
* `totalCount`, `density`, `moment`, `copyNumberVariance`: the population
  `N(t) = ∑ₖ N_k(t)`, the densities `ρ_k = N_k / N`, the moments `M_l = ∑ₖ k^l ρ_k` and the
  variance `M₂ - M₁²` of the copy number.

## Main results

* `IsSolution.totalCount_eq`: `N(t) = N(0) e^t`.
* `IsSolution.tsum_mul_eq`, `IsSolution.tsum_sq_mul_eq`: `∑ₖ k N_k(t) = e^t ∑ₖ k N_k(0)` and
  `∑ₖ k² N_k(t) = (∑ₖ k² N_k(0) + t ∑ₖ k N_k(0)) e^t`.
* `IsSolution.hasDerivWithinAt_density`: the densities solve
  `dρ_k/dt = -2 ρ_k + 2 ∑ᵢ ρ_i C(2i, k) 2^{-2i}`.
* `IsSolution.moment_one_eq`: the mean copy number is conserved, `M₁(t) = M₁(0)`.
* `IsSolution.hasDerivWithinAt_moment_two`, `IsSolution.moment_two_eq`: `dM₂/dt = M₁`, so
  `M₂(t) = M₂(0) + M₁(0) t`.
* `IsSolution.copyNumberVariance_eq`: the variance grows linearly,
  `Var(t) = Var(0) + M₁(0) t`.
* `IsSolution.moment_of_single`: from one cell with one copy, `M₁ ≡ 1` and `M₂(t) = 1 + t`.
* `IsSolution.monotoneOn_density_zero`: the fraction `ρ₀` of ecDNA-free cells never decreases.

The moment results assume that the moments they use are finite at every time `t ≥ 0`, as the
definition of `M_l(t)` presupposes. The mean equations are the model: their derivation from the
individual-based stochastic process is not formalized here.

## References

* J. T. Lange, J. C. Rose, C. Y. Chen et al., *The evolutionary dynamics of extrachromosomal DNA
  in human cancers*, Nature Genetics 54 (2022), 1527–1533, Methods, "Stochastic dynamics of
  neutral ecDNA" and "Moment dynamics for neutral ecDNA copies".
-/

@[expose] public section

namespace Domains.Biology.CancerGenomics.EcDNASegregation

open Set Real MeasureTheory ProbabilityTheory
open scoped unitInterval

/-! ### The segregation law -/

/-- The probability `C(2i, k) 2^{-2i}` that a daughter of a dividing cell with `i` ecDNA copies
receives `k` of the `2i` replicated copies: the mass at `k` of the binomial law `Bin(2i, 1/2)`
(`segregationProb_eq_binomial`). It vanishes for `k > 2i`. -/
noncomputable def segregationProb (i k : ℕ) : ℝ := ((2 * i).choose k : ℝ) / 2 ^ (2 * i)

theorem segregationProb_nonneg (i k : ℕ) : 0 ≤ segregationProb i k := by
  unfold segregationProb
  positivity

/-- A daughter receives at most the `2i` replicated copies. -/
theorem segregationProb_eq_zero_of_lt {i k : ℕ} (h : 2 * i < k) : segregationProb i k = 0 := by
  simp [segregationProb, Nat.choose_eq_zero_of_lt h]

/-- Cells without ecDNA have only ecDNA-free daughters. -/
theorem segregationProb_zero_left (k : ℕ) : segregationProb 0 k = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [segregationProb]
  · simp [segregationProb, Nat.choose_eq_zero_of_lt hk, hk.ne']

/-- The two daughters, with `k` and `2i - k` copies, have the same law. -/
theorem segregationProb_symm {i k : ℕ} (h : k ≤ 2 * i) :
    segregationProb i (2 * i - k) = segregationProb i k := by
  simp [segregationProb, Nat.choose_symm h]

private lemma choose_mul_half_pow {i k : ℕ} (hk : k ≤ 2 * i) :
    ((2 * i).choose k : ℝ) * (1 / 2) ^ k * (1 - 1 / 2) ^ (2 * i - k) = segregationProb i k := by
  rw [segregationProb, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hk, one_div_pow, mul_one_div]

/-- `segregationProb i k` is the mass at `k` of the binomial law `Bin(2i, 1/2)`. -/
theorem segregationProb_eq_binomial {p : I} (hp : (p : ℝ) = 1 / 2) (i k : ℕ) :
    segregationProb i k = Bin(2 * i, p).real {k} := by
  rw [binomial_real_singleton, hp]
  rcases le_or_gt k (2 * i) with hk | hk
  · exact (choose_mul_half_pow hk).symm
  · simp [segregationProb, Nat.choose_eq_zero_of_lt hk]

private lemma hasSum_mul_segregationProb (f : ℕ → ℝ) (i : ℕ) :
    HasSum (fun k => f k * segregationProb i k)
      (∑ k ∈ Finset.range (2 * i + 1), f k * segregationProb i k) :=
  hasSum_sum_of_ne_finset_zero fun k hk => by
    rw [segregationProb_eq_zero_of_lt (by simp at hk; omega), mul_zero]

private lemma summable_mul_segregationProb (f : ℕ → ℝ) (i : ℕ) :
    Summable fun k => f k * segregationProb i k :=
  (hasSum_mul_segregationProb f i).summable

private lemma integral_binomial_half (f : ℝ → ℝ) (i : ℕ) {p : I} (hp : (p : ℝ) = 1 / 2) :
    ∫ x, f x ∂Bin(ℝ, 2 * i, p) = ∑' k : ℕ, f k * segregationProb i k := by
  rw [integral_map_cast_binomial, (hasSum_mul_segregationProb _ i).tsum_eq,
    ← Nat.range_succ_eq_Iic]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [smul_eq_mul, hp, choose_mul_half_pow (by simp at hk; omega), mul_comm]

private lemma exists_half : ∃ p : I, (p : ℝ) = 1 / 2 :=
  ⟨⟨1 / 2, by norm_num, by norm_num⟩, rfl⟩

/-- The segregation law is a probability distribution. -/
theorem tsum_segregationProb (i : ℕ) : ∑' k, segregationProb i k = 1 := by
  obtain ⟨p, hp⟩ := exists_half
  have h := integral_binomial_half (fun _ => 1) i hp
  simp only [one_mul] at h
  rw [← h, integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.map_apply_of_aemeasurable (by fun_prop) MeasurableSet.univ, preimage_univ,
    measure_univ, ENNReal.toReal_one]

theorem segregationProb_le_one (i k : ℕ) : segregationProb i k ≤ 1 := by
  rw [← tsum_segregationProb i]
  exact (by simpa using summable_mul_segregationProb (fun _ => 1) i : Summable _).le_tsum k
    fun j _ => segregationProb_nonneg i j

/-- **Mean of the segregation law**: a daughter of a cell with `i` copies receives `i` copies on
average. -/
theorem tsum_mul_segregationProb (i : ℕ) : ∑' k : ℕ, (k : ℝ) * segregationProb i k = i := by
  obtain ⟨p, hp⟩ := exists_half
  rw [← integral_binomial_half (fun x => x) i hp,
    (integral_of_hasLaw_binomial HasLaw.id : ∫ x, x ∂Bin(ℝ, 2 * i, p) = (p : ℝ) * (2 * i : ℕ)),
    hp]
  push_cast
  ring

/-- **Second moment of the segregation law**: the second moment of `Bin(2i, 1/2)` is
`i² + i / 2`. -/
theorem tsum_sq_mul_segregationProb (i : ℕ) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * segregationProb i k = (i : ℝ) ^ 2 + i / 2 := by
  obtain ⟨p, hp⟩ := exists_half
  rw [← integral_binomial_half (fun x => x ^ 2) i hp, integral_sq_map_cast_binomial, hp]
  push_cast
  ring

/-- Exchanging the order of summation in `∑ₖ w_k ∑ᵢ x_i P(i, k)` for nonnegative `x` and `w`,
where `∑ₖ w_k P(i, k) = m_i`. -/
private lemma tsum_mul_tsum_segregationProb {x w m : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hw : ∀ k, 0 ≤ w k) (hm : ∀ i, ∑' k, w k * segregationProb i k = m i)
    (hs : Summable fun i => x i * m i) :
    Summable (fun k => w k * ∑' i, x i * segregationProb i k) ∧
      ∑' k, w k * ∑' i, x i * segregationProb i k = ∑' i, x i * m i := by
  set F : ℕ → ℕ → ℝ := fun i k => x i * (w k * segregationProb i k) with hF
  have hF0 : 0 ≤ Function.uncurry F := fun p =>
    mul_nonneg (hx _) (mul_nonneg (hw _) (segregationProb_nonneg _ _))
  have hrow : ∀ i, Summable (F i) := fun i => (summable_mul_segregationProb w i).mul_left (x i)
  have hrow_tsum : ∀ i, ∑' k, F i k = x i * m i := fun i => by
    rw [hF, tsum_mul_left, hm]
  have hsum : Summable (Function.uncurry F) :=
    (summable_prod_of_nonneg hF0).2 ⟨hrow, by simpa [hrow_tsum] using hs⟩
  have hcol := (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => Function.uncurry F p.swap)
    fun p => hF0 p.swap).1 hsum.prod_symm
  simp only [Prod.swap_prod_mk, Function.uncurry_apply_pair] at hcol
  have hcol_tsum : ∀ k, ∑' i, F i k = w k * ∑' i, x i * segregationProb i k := fun k => by
    rw [← tsum_mul_left]
    exact tsum_congr fun i => by rw [hF]; ring
  refine ⟨?_, ?_⟩
  · simpa [hcol_tsum] using hcol.2
  · simp_rw [← hcol_tsum]
    rw [hsum.tsum_comm' hrow hcol.1]
    exact tsum_congr hrow_tsum

/-! ### The model and its observables -/

/-- **The binomial segregation model of ecDNA under neutral growth** (Lange et al., 2022).
`N k t` is the expected number of cells with `k` ecDNA copies at time `t ≥ 0` (in generations).
Every cell divides at rate `1`; a division of a cell with `i` copies removes it and adds two
daughters, each with `k` copies with probability `segregationProb i k = C(2i, k) 2^{-2i}`. So

`dN_k/dt = -N_k + 2 ∑ᵢ N_i C(2i, k) 2^{-2i}`,

where the terms with `2i < k` vanish, so that the sum runs over `i ≥ ⌈k/2⌉`. The counts are
nonnegative, the population `∑ₖ N_k(t)` is finite, and the derivative at `t = 0` is one-sided. -/
structure IsSolution (N : ℕ → ℝ → ℝ) : Prop where
  /-- Expected counts are nonnegative. -/
  nonneg : ∀ k t, 0 ≤ t → 0 ≤ N k t
  /-- The expected population `∑ₖ N_k(t)` is finite. -/
  summable : ∀ t, 0 ≤ t → Summable fun k => N k t
  /-- The mean equations `dN_k/dt = -N_k + 2 ∑ᵢ N_i C(2i, k) 2^{-2i}` on `t ≥ 0`. -/
  hasDerivWithinAt : ∀ k t, 0 ≤ t →
    HasDerivWithinAt (N k) (-N k t + 2 * ∑' i, N i t * segregationProb i k) (Ici 0) t

/-- The expected population `N(t) = ∑ₖ N_k(t)`. -/
noncomputable def totalCount (N : ℕ → ℝ → ℝ) (t : ℝ) : ℝ := ∑' k, N k t

/-- The density `ρ_k(t) = N_k(t) / N(t)` of cells with `k` ecDNA copies (`0` when `N(t) = 0`). -/
noncomputable def density (N : ℕ → ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ := N k t / totalCount N t

/-- The `l`-th moment `M_l(t) = ∑ₖ k^l ρ_k(t)` of the ecDNA copy number. -/
noncomputable def moment (N : ℕ → ℝ → ℝ) (l : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) ^ l * density N k t

/-- The variance `M₂(t) - M₁(t)²` of the ecDNA copy number: the variance of the copy-number
distribution `ρ(t)`, which is a probability distribution for a solution with `N(0) ≠ 0`
(`IsSolution.tsum_density`). -/
noncomputable def copyNumberVariance (N : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  moment N 2 t - moment N 1 t ^ 2

private lemma moment_eq_div (N : ℕ → ℝ → ℝ) (l : ℕ) (t : ℝ) :
    moment N l t = (∑' k : ℕ, (k : ℝ) ^ l * N k t) / totalCount N t := by
  rw [moment, ← tsum_div_const]
  exact tsum_congr fun k => by rw [density, mul_div_assoc]

/-- A function with zero derivative on `(0, ∞)` that is continuous on `[0, ∞)` is constant
there. -/
private lemma eq_of_hasDerivAt_eq_zero {F : ℝ → ℝ} (hc : ∀ T, 0 ≤ T → ContinuousOn F (Icc 0 T))
    (hd : ∀ t, 0 < t → HasDerivAt F 0 t) {t : ℝ} (ht : 0 ≤ t) : F t = F 0 := by
  rcases ht.eq_or_lt with h | ht
  · rw [← h]
  obtain ⟨c, -, h⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) ht (hc t ht.le)
    fun x hx => hd x hx.1
  rw [eq_div_iff (by linarith : t - 0 ≠ 0)] at h
  linarith

/-- Solutions of `F' = F + c e^t` on `t ≥ 0`. -/
private lemma eq_mul_exp_of_hasDerivAt {F : ℝ → ℝ} {c : ℝ}
    (hc : ∀ T, 0 ≤ T → ContinuousOn F (Icc 0 T))
    (hd : ∀ t, 0 < t → HasDerivAt F (F t + c * exp t) t) {t : ℝ} (ht : 0 ≤ t) :
    F t = (F 0 + c * t) * exp t := by
  have h := eq_of_hasDerivAt_eq_zero (F := fun s => F s * exp (-s) - c * s)
    (fun T hT => ((hc T hT).mul (continuous_exp.comp continuous_neg).continuousOn).sub
      (continuousOn_const.mul continuousOn_id))
    (fun s hs => by
      have := ((hd s hs).mul (hasDerivAt_neg s).exp).sub ((hasDerivAt_id s).const_mul c)
      convert this using 1
      · ext x
        simp
      · rw [exp_neg]
        field_simp
        ring) ht
  simp only [neg_zero, exp_zero, mul_one, mul_zero, sub_zero] at h
  have h' : F t * exp (-t) = F 0 + c * t := by linarith
  calc F t = F t * exp (-t) * exp t := by rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero,
        mul_one]
    _ = (F 0 + c * t) * exp t := by rw [h']

namespace IsSolution

variable {N : ℕ → ℝ → ℝ} (hN : IsSolution N)
include hN

theorem continuousOn (k : ℕ) : ContinuousOn (N k) (Ici 0) :=
  fun t ht => (hN.hasDerivWithinAt k t ht).continuousWithinAt

theorem hasDerivAt (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (N k) (-N k t + 2 * ∑' i, N i t * segregationProb i k) t :=
  (hN.hasDerivWithinAt k t ht.le).hasDerivAt (Ici_mem_nhds ht)

theorem totalCount_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ totalCount N t :=
  tsum_nonneg fun k => hN.nonneg k t ht

/-- `e^t N_k(t)` is nondecreasing, so `N_k(s) ≤ e^T N_k(T)` for `0 ≤ s ≤ T`. -/
private lemma le_exp_mul (k : ℕ) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    N k s ≤ exp T * N k T := by
  have hmono : MonotoneOn (fun t => exp t * N k t) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun t => exp t * (2 * ∑' i, N i t * segregationProb i k))
      (continuous_exp.continuousOn.mul (hN.continuousOn k)) (fun t ht => ?_) (fun t ht => ?_)
    · have := (Real.hasDerivAt_exp t).hasDerivWithinAt.mul
        (hN.hasDerivWithinAt k t (interior_subset ht))
      convert this.mono interior_subset using 1
      ring
    · exact mul_nonneg (exp_pos t).le (mul_nonneg zero_le_two (tsum_nonneg fun i =>
        mul_nonneg (hN.nonneg i t (interior_subset ht)) (segregationProb_nonneg i k)))
  calc N k s ≤ exp s * N k s := le_mul_of_one_le_left (hN.nonneg k s hs) (one_le_exp hs)
    _ ≤ exp T * N k T := hmono hs (hs.trans hsT) hsT

private lemma summable_mul_segregationProb {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    Summable fun i => N i t * segregationProb i k :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (hN.nonneg i t ht) (segregationProb_nonneg i k))
    (fun i => mul_le_of_le_one_right (hN.nonneg i t ht) (segregationProb_le_one i k))
    (hN.summable t ht)

private lemma continuousOn_tsum_weighted {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hW : ∀ t, 0 ≤ t → Summable fun k => w k * N k t) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun s => ∑' k, w k * N k s) (Icc 0 T) := by
  refine continuousOn_tsum (u := fun k => exp T * (w k * N k T))
    (fun k => continuousOn_const.mul ((hN.continuousOn k).mono Icc_subset_Ici_self))
    ((hW T hT).mul_left _) fun k s hs => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (hw k) (hN.nonneg k s hs.1))]
  calc w k * N k s ≤ w k * (exp T * N k T) :=
        mul_le_mul_of_nonneg_left (hN.le_exp_mul k hs.1 hs.2) (hw k)
    _ = exp T * (w k * N k T) := by ring

/-- Termwise differentiation of a weighted sum `∑ₖ w_k N_k(t)` with
`∑ₖ w_k C(2i, k) 2^{-2i} = m_i`. -/
private lemma hasDerivAt_tsum_weighted {w m : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hm : ∀ i, ∑' k, w k * segregationProb i k = m i)
    (hW : ∀ t, 0 ≤ t → Summable fun k => w k * N k t)
    (hM : ∀ t, 0 ≤ t → Summable fun i => N i t * m i) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∑' k, w k * N k s)
      (-(∑' k, w k * N k t) + 2 * ∑' i, N i t * m i) t := by
  set T := t + 1
  have hT : 0 ≤ T := by linarith
  have hinner : ∀ k s, 0 ≤ s → s ≤ T →
      ∑' i, N i s * segregationProb i k ≤ exp T * ∑' i, N i T * segregationProb i k := by
    intro k s hs hsT
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) (hN.summable_mul_segregationProb hs k)
      ((hN.summable_mul_segregationProb hT k).mul_left _)
    calc N i s * segregationProb i k ≤ (exp T * N i T) * segregationProb i k :=
          mul_le_mul_of_nonneg_right (hN.le_exp_mul i hs hsT) (segregationProb_nonneg i k)
      _ = exp T * (N i T * segregationProb i k) := by ring
  obtain ⟨hsumT, -⟩ := tsum_mul_tsum_segregationProb (x := fun i => N i T)
    (fun i => hN.nonneg i T hT) hw hm (hM T hT)
  obtain ⟨hsumt, htsumt⟩ := tsum_mul_tsum_segregationProb (x := fun i => N i t)
    (fun i => hN.nonneg i t ht.le) hw hm (hM t ht.le)
  have hderiv := hasDerivAt_tsum_of_isPreconnected (g := fun k s => w k * N k s)
    (g' := fun k s => w k * (-N k s + 2 * ∑' i, N i s * segregationProb i k))
    (u := fun k => exp T * (w k * N k T) +
      2 * exp T * (w k * ∑' i, N i T * segregationProb i k))
    (((hW T hT).mul_left _).add (hsumT.mul_left _)) isOpen_Ioo isPreconnected_Ioo
    (fun k s hs => (hN.hasDerivAt k hs.1).const_mul (w k)) (fun k s hs => ?_)
    (show t ∈ Ioo 0 T by constructor <;> linarith) (hW t ht.le)
    (show t ∈ Ioo 0 T by constructor <;> linarith)
  · convert hderiv using 1
    calc -(∑' k, w k * N k t) + 2 * ∑' i, N i t * m i
        = ∑' k, (-(w k * N k t) + 2 * (w k * ∑' i, N i t * segregationProb i k)) := by
          rw [(hW t ht.le).neg.tsum_add (hsumt.mul_left 2), tsum_neg, tsum_mul_left, htsumt]
      _ = ∑' k, w k * (-N k t + 2 * ∑' i, N i t * segregationProb i k) :=
          tsum_congr fun k => by ring
  · have hs0 : 0 ≤ s := hs.1.le
    have hsT : s ≤ T := hs.2.le
    have ha := hN.nonneg k s hs0
    have hc : 0 ≤ ∑' i, N i s * segregationProb i k := tsum_nonneg fun i =>
      mul_nonneg (hN.nonneg i s hs0) (segregationProb_nonneg i k)
    have ha' := hN.le_exp_mul k hs0 hsT
    have hc' := hinner k s hs0 hsT
    calc ‖w k * (-N k s + 2 * ∑' i, N i s * segregationProb i k)‖
        = w k * |-N k s + 2 * ∑' i, N i s * segregationProb i k| := by
          rw [norm_mul, Real.norm_of_nonneg (hw k), Real.norm_eq_abs]
      _ ≤ w k * (N k s + 2 * ∑' i, N i s * segregationProb i k) :=
          mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (hw k)
      _ ≤ w k * (exp T * N k T + 2 * (exp T * ∑' i, N i T * segregationProb i k)) :=
          mul_le_mul_of_nonneg_left (by linarith) (hw k)
      _ = exp T * (w k * N k T) + 2 * exp T * (w k * ∑' i, N i T * segregationProb i k) := by
          ring

/-- **The population grows exponentially**: `N(t) = N(0) e^t`, since every cell divides at
rate `1`. -/
theorem totalCount_eq {t : ℝ} (ht : 0 ≤ t) : totalCount N t = totalCount N 0 * exp t := by
  have hW : ∀ t, 0 ≤ t → Summable fun k => (1 : ℝ) * N k t := fun t ht => by
    simpa using hN.summable t ht
  have hS : (fun s => ∑' k, (1 : ℝ) * N k s) = totalCount N := by
    funext s
    simp [totalCount]
  have h := eq_mul_exp_of_hasDerivAt (F := totalCount N) (c := 0)
    (fun T hT => hS ▸ hN.continuousOn_tsum_weighted (fun _ => zero_le_one) hW hT)
    (fun s hs => by
      have := hN.hasDerivAt_tsum_weighted (m := fun _ => 1) (fun _ => zero_le_one)
        (fun i => by simpa using tsum_segregationProb i) hW
        (fun t ht => by simpa using hN.summable t ht) hs
      rw [hS] at this
      convert this using 1
      simp only [totalCount, one_mul, mul_one, zero_mul, add_zero]
      ring) ht
  simpa using h

/-- **The expected number of ecDNA copies grows exponentially**: `∑ₖ k N_k(t) = e^t ∑ₖ k N_k(0)`,
since a division replaces a cell with `i` copies by two daughters that carry `2i` copies between
them, provided the first moment is finite at every time. -/
theorem tsum_mul_eq (h1 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) * N k t) {t : ℝ}
    (ht : 0 ≤ t) : ∑' k : ℕ, (k : ℝ) * N k t = (∑' k : ℕ, (k : ℝ) * N k 0) * exp t := by
  have h := eq_mul_exp_of_hasDerivAt (F := fun s => ∑' k : ℕ, (k : ℝ) * N k s) (c := 0)
    (fun T hT => hN.continuousOn_tsum_weighted (fun k => k.cast_nonneg) h1 hT)
    (fun s hs => by
      have := hN.hasDerivAt_tsum_weighted (m := fun i => i) (fun k => k.cast_nonneg)
        tsum_mul_segregationProb h1 (fun t ht => by simpa [mul_comm] using h1 t ht) hs
      convert this using 1
      simp_rw [mul_comm (N _ s)]
      ring) ht
  simpa using h

private lemma summable_mul_of_sq (h2 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) ^ 2 * N k t) :
    ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) * N k t := fun t ht =>
  Summable.of_nonneg_of_le (fun k => mul_nonneg k.cast_nonneg (hN.nonneg k t ht))
    (fun k => mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_self_pow two_ne_zero k) (hN.nonneg k t ht)) (h2 t ht)

/-- **Second moment of the counts**: `∑ₖ k² N_k(t) = (∑ₖ k² N_k(0) + t ∑ₖ k N_k(0)) e^t`,
provided the second moment is finite at every time. -/
theorem tsum_sq_mul_eq (h2 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) ^ 2 * N k t) {t : ℝ}
    (ht : 0 ≤ t) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * N k t =
      (∑' k : ℕ, (k : ℝ) ^ 2 * N k 0 + (∑' k : ℕ, (k : ℝ) * N k 0) * t) * exp t := by
  have h1 := hN.summable_mul_of_sq h2
  have hsplit : ∀ s, 0 ≤ s → ∑' i, N i s * ((i : ℝ) ^ 2 + i / 2) =
      ∑' i : ℕ, (i : ℝ) ^ 2 * N i s + (∑' i : ℕ, (i : ℝ) * N i s) / 2 := fun s hs => by
    rw [← tsum_div_const, ← (h2 s hs).tsum_add ((h1 s hs).div_const 2)]
    exact tsum_congr fun i => by ring
  exact eq_mul_exp_of_hasDerivAt (F := fun s => ∑' k : ℕ, (k : ℝ) ^ 2 * N k s)
    (fun T hT => hN.continuousOn_tsum_weighted (fun k => sq_nonneg _) h2 hT)
    (fun s hs => by
      have := hN.hasDerivAt_tsum_weighted (m := fun i : ℕ => (i : ℝ) ^ 2 + i / 2)
        (fun k => sq_nonneg _) tsum_sq_mul_segregationProb h2
        (fun t ht => ((h2 t ht).add ((h1 t ht).div_const 2)).congr fun i => by ring) hs
      convert this using 1
      rw [hsplit s hs.le, hN.tsum_mul_eq h1 hs.le]
      ring) ht

/-- **The densities** `ρ_k = N_k / N` solve
`dρ_k/dt = -2 ρ_k + 2 ∑ᵢ ρ_i C(2i, k) 2^{-2i}` on `t ≥ 0`. -/
theorem hasDerivWithinAt_density (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (density N k)
      (-2 * density N k t + 2 * ∑' i, density N i t * segregationProb i k) (Ici 0) t := by
  have hdens : ∀ i s, 0 ≤ s → density N i s = N i s / (totalCount N 0 * exp s) :=
    fun i s hs => by rw [density, hN.totalCount_eq hs]
  by_cases h0 : totalCount N 0 = 0
  · have hz : ∀ i s, 0 ≤ s → density N i s = 0 := fun i s hs => by
      rw [hdens i s hs, h0, zero_mul, div_zero]
    simp only [hz _ t ht, zero_mul, tsum_zero, mul_zero, add_zero]
    exact (hasDerivWithinAt_const t (Ici 0) 0).congr (fun s hs => hz k s hs) (hz k t ht)
  · have hD : HasDerivAt (fun s => totalCount N 0 * exp s) (totalCount N 0 * exp t) t :=
      (Real.hasDerivAt_exp t).const_mul _
    have hDne : totalCount N 0 * exp t ≠ 0 := mul_ne_zero h0 (exp_pos t).ne'
    refine ((hN.hasDerivWithinAt k t ht).div hD.hasDerivWithinAt hDne).congr
      (fun s hs => hdens k s hs) (hdens k t ht) |>.congr_deriv ?_
    have hsum : ∑' i, density N i t * segregationProb i k =
        (∑' i, N i t * segregationProb i k) / (totalCount N 0 * exp t) := by
      rw [← tsum_div_const]
      exact tsum_congr fun i => by rw [hdens i t ht, div_mul_eq_mul_div]
    rw [hsum, hdens k t ht]
    field_simp
    ring

/-- The densities form a probability distribution once the population is nonzero. -/
theorem tsum_density (h0 : totalCount N 0 ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∑' k, density N k t = 1 := by
  have hne : totalCount N t ≠ 0 := by
    rw [hN.totalCount_eq ht]
    exact mul_ne_zero h0 (exp_pos t).ne'
  simp only [density]
  rw [tsum_div_const]
  exact div_self hne

/-- **The fraction of ecDNA-free cells never decreases**: `ρ₀` is monotone on `t ≥ 0`. -/
theorem monotoneOn_density_zero : MonotoneOn (density N 0) (Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t ht => (hN.hasDerivWithinAt_density 0 ht).continuousWithinAt)
    (fun t ht => (hN.hasDerivWithinAt_density 0 (interior_subset ht)).mono interior_subset)
    fun t ht => ?_
  have ht' : 0 ≤ t := interior_subset ht
  have hρ : ∀ i, 0 ≤ density N i t := fun i =>
    div_nonneg (hN.nonneg i t ht') (hN.totalCount_nonneg ht')
  have hsum : Summable fun i => density N i t * segregationProb i 0 :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hρ i) (segregationProb_nonneg i 0))
      (fun i => mul_le_of_le_one_right (hρ i) (segregationProb_le_one i 0))
      ((hN.summable t ht').div_const _)
  have h := hsum.le_tsum 0 fun j _ => mul_nonneg (hρ j) (segregationProb_nonneg j 0)
  simp only [segregationProb_zero_left, ite_true, mul_one] at h
  linarith

/-- **The mean copy number is conserved**: `M₁(t) = M₁(0)`, provided the first moment is finite
at every time. -/
theorem moment_one_eq (h1 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) * N k t) {t : ℝ}
    (ht : 0 ≤ t) : moment N 1 t = moment N 1 0 := by
  simp only [moment_eq_div, pow_one]
  rw [hN.tsum_mul_eq h1 ht, hN.totalCount_eq ht, mul_div_mul_right _ _ (exp_pos t).ne']

/-- **The second moment grows linearly**: `M₂(t) = M₂(0) + M₁(0) t`, provided the second moment
is finite at every time. -/
theorem moment_two_eq (h2 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) ^ 2 * N k t) {t : ℝ}
    (ht : 0 ≤ t) : moment N 2 t = moment N 2 0 + moment N 1 0 * t := by
  simp only [moment_eq_div, pow_one]
  rw [hN.tsum_sq_mul_eq h2 ht, hN.totalCount_eq ht, mul_div_mul_right _ _ (exp_pos t).ne',
    add_div, mul_div_right_comm]

/-- **`dM₂/dt = M₁`** on `t ≥ 0`, provided the second moment is finite at every time. -/
theorem hasDerivWithinAt_moment_two
    (h2 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) ^ 2 * N k t) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (moment N 2) (moment N 1 t) (Ici 0) t := by
  have hlin : HasDerivWithinAt (fun s => moment N 2 0 + moment N 1 0 * s) (moment N 1 0)
      (Ici 0) t := by
    simpa using (((hasDerivAt_id t).const_mul (moment N 1 0)).const_add
      (moment N 2 0)).hasDerivWithinAt
  rw [hN.moment_one_eq (hN.summable_mul_of_sq h2) ht]
  exact hlin.congr (fun s hs => hN.moment_two_eq h2 hs) (hN.moment_two_eq h2 ht)

/-- **The copy-number variance grows linearly**: `Var(t) = Var(0) + M₁(0) t`, provided the second
moment is finite at every time. -/
theorem copyNumberVariance_eq (h2 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) ^ 2 * N k t) {t : ℝ}
    (ht : 0 ≤ t) : copyNumberVariance N t = copyNumberVariance N 0 + moment N 1 0 * t := by
  rw [copyNumberVariance, copyNumberVariance, hN.moment_two_eq h2 ht,
    hN.moment_one_eq (hN.summable_mul_of_sq h2) ht]
  ring

/-- **From one cell with one copy**, `M₁(t) = 1` and `M₂(t) = 1 + t`, provided the second moment
is finite at every time. -/
theorem moment_of_single (h2 : ∀ t, 0 ≤ t → Summable fun k : ℕ => (k : ℝ) ^ 2 * N k t)
    (h0 : ∀ k, N k 0 = if k = 1 then 1 else 0) {t : ℝ} (ht : 0 ≤ t) :
    moment N 1 t = 1 ∧ moment N 2 t = 1 + t := by
  have hS : totalCount N 0 = 1 := by simp [totalCount, h0]
  have hM : ∀ l, moment N l 0 = 1 := fun l => by
    simp [moment, density, hS, h0]
  exact ⟨by rw [hN.moment_one_eq (hN.summable_mul_of_sq h2) ht, hM],
    by rw [hN.moment_two_eq h2 ht, hM, hM, one_mul]⟩

end IsSolution

end Domains.Biology.CancerGenomics.EcDNASegregation
