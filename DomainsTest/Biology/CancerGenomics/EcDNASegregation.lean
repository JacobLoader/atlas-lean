/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.CancerGenomics.EcDNASegregation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Tests for the binomial segregation model of ecDNA: values of the segregation law and of its
moments, the ecDNA-free population as a trivial solution, and, as a non-vacuity witness for the
moment results, the solution started from one cell with one copy. That solution is the series
`N_k(t) = e^{-t} ∑ₙ (2t)ⁿ/n! · Pₙ(k)` over generations, where `Pₙ` is the copy-number law of one
lineage after `n` divisions: a cell of generation `n` is alive at time `t` with weight
`e^{-t} tⁿ/n!`, and there are `2ⁿ` of them. -/

namespace DomainsTest.Biology.CancerGenomics.EcDNASegregation

open Set Real Domains.Biology.CancerGenomics.EcDNASegregation
open scoped Nat

/-! ### The segregation law -/

example : segregationProb 1 1 = 1 / 2 := by norm_num [segregationProb]

example : segregationProb 1 0 = 1 / 4 := by norm_num [segregationProb]

example : segregationProb 2 2 = 3 / 8 := by
  norm_num [segregationProb, Nat.choose_symm_half, Nat.choose]

/-- A daughter never receives more than the `2i` replicated copies. -/
example : segregationProb 1 3 = 0 := segregationProb_eq_zero_of_lt (by norm_num)

example : segregationProb 0 0 = 1 := by simp [segregationProb_zero_left]

/-- The two daughters of a cell with three copies: `1` copy and `5` copies are equally likely. -/
example : segregationProb 3 (2 * 3 - 1) = segregationProb 3 1 := segregationProb_symm (by norm_num)

example : ∑' k : ℕ, (k : ℝ) * segregationProb 3 k = 3 := by
  rw [tsum_mul_segregationProb]
  norm_num

/-- `Bin(6, 1/2)` has second moment `9 + 3/2`. -/
example : ∑' k : ℕ, (k : ℝ) ^ 2 * segregationProb 3 k = 21 / 2 := by
  rw [tsum_sq_mul_segregationProb]
  norm_num

/-! ### An ecDNA-free population -/

/-- An ecDNA-free population of size `e^t`. -/
noncomputable def ecDNAFree (k : ℕ) (t : ℝ) : ℝ := if k = 0 then exp t else 0

/-- **Trivial solution.** An ecDNA-free population grows as `e^t` and stays ecDNA-free. -/
theorem isSolution_ecDNAFree : IsSolution ecDNAFree where
  nonneg k t _ := by
    unfold ecDNAFree
    split_ifs <;> positivity
  summable t _ := summable_of_ne_finset_zero (s := {0}) fun k hk => by
    simp only [Finset.mem_singleton] at hk
    simp [ecDNAFree, hk]
  hasDerivWithinAt k t _ := by
    have hsum : ∑' i, ecDNAFree i t * segregationProb i k = ecDNAFree k t := by
      rw [tsum_eq_single 0 fun i hi => by simp [ecDNAFree, hi]]
      by_cases hk : k = 0 <;> simp [ecDNAFree, segregationProb_zero_left, hk]
    rw [hsum]
    by_cases hk : k = 0
    · subst hk
      convert (Real.hasDerivAt_exp t).hasDerivWithinAt using 1
      · ext s
        simp [ecDNAFree]
      · simp only [ecDNAFree, ite_true]
        ring
    · convert hasDerivWithinAt_const t (Ici 0) (0 : ℝ) using 1
      · ext s
        simp [ecDNAFree, hk]
      · simp only [ecDNAFree, hk, ite_false]
        ring

example (t : ℝ) (ht : 0 ≤ t) : totalCount ecDNAFree t = totalCount ecDNAFree 0 * exp t :=
  isSolution_ecDNAFree.totalCount_eq ht

/-- Every cell is ecDNA-free: `ρ₀ = 1`. -/
example (t : ℝ) : density ecDNAFree 0 t = 1 := by
  have h : totalCount ecDNAFree t = exp t := by
    rw [totalCount, tsum_eq_single 0 fun k hk => by simp [ecDNAFree, hk]]
    simp [ecDNAFree]
  rw [density, h]
  simp [ecDNAFree, (exp_pos t).ne']

/-! ### The solution from one cell with one copy -/

/-- The copy-number law of one lineage after `n` divisions, from one copy:
`P₀ = δ₁` and `Pₙ₊₁(k) = ∑ᵢ Pₙ(i) C(2i, k) 2^{-2i}`. -/
noncomputable def lineage : ℕ → ℕ → ℝ
  | 0, k => if k = 1 then 1 else 0
  | n + 1, k => ∑' i, lineage n i * segregationProb i k

theorem lineage_nonneg : ∀ n k, 0 ≤ lineage n k
  | 0, k => by
    unfold lineage
    split_ifs <;> norm_num
  | n + 1, k => tsum_nonneg fun i => mul_nonneg (lineage_nonneg n i) (segregationProb_nonneg i k)

/-- After `n` divisions a lineage carries at most `2ⁿ` copies. -/
theorem lineage_eq_zero : ∀ n k, 2 ^ n < k → lineage n k = 0
  | 0, k, hk => by
    simp only [lineage, pow_zero, ite_eq_right_iff] at hk ⊢
    omega
  | n + 1, k, hk => by
    rw [lineage]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rcases le_or_gt i (2 ^ n) with hi | hi
    · rw [segregationProb_eq_zero_of_lt (by rw [pow_succ] at hk; omega), mul_zero]
    · rw [lineage_eq_zero n i hi, zero_mul]

theorem tsum_lineage_mul (n : ℕ) (f : ℕ → ℝ) :
    ∑' k, lineage n k * f k = ∑ k ∈ Finset.range (2 ^ n + 1), lineage n k * f k :=
  tsum_eq_sum fun k hk => by
    rw [lineage_eq_zero n k (by simp only [Finset.mem_range] at hk; omega), zero_mul]

theorem summable_lineage_mul (n : ℕ) (f : ℕ → ℝ) : Summable fun k => lineage n k * f k :=
  summable_of_ne_finset_zero (s := Finset.range (2 ^ n + 1)) fun k hk => by
    rw [lineage_eq_zero n k (by simp only [Finset.mem_range] at hk; omega), zero_mul]

/-- One more division: `∑ₖ Pₙ₊₁(k) w_k = ∑ᵢ Pₙ(i) m_i` when `∑ₖ w_k C(2i, k) 2^{-2i} = m_i`. -/
theorem tsum_lineage_succ_mul {w m : ℕ → ℝ} (hm : ∀ i, ∑' k, w k * segregationProb i k = m i)
    (n : ℕ) : ∑' k, lineage (n + 1) k * w k = ∑' i, lineage n i * m i := by
  have hl : ∀ k, lineage (n + 1) k =
      ∑ i ∈ Finset.range (2 ^ n + 1), lineage n i * segregationProb i k := fun k => by
    rw [lineage, tsum_lineage_mul]
  rw [tsum_lineage_mul (n + 1), tsum_lineage_mul n]
  simp_rw [hl, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ 2 ^ n := by simp only [Finset.mem_range] at hi; omega
  rw [← hm i, tsum_eq_sum (s := Finset.range (2 ^ (n + 1) + 1)), Finset.mul_sum]
  · exact Finset.sum_congr rfl fun k _ => by ring
  · intro k hk
    simp only [Finset.mem_range] at hk
    rw [segregationProb_eq_zero_of_lt (by rw [pow_succ] at hk; omega), mul_zero]

theorem tsum_lineage (n : ℕ) : ∑' k, lineage n k * 1 = 1 := by
  induction n with
  | zero => simp [lineage]
  | succ n ih =>
    rw [tsum_lineage_succ_mul (m := fun _ => 1) (fun i => by simpa using tsum_segregationProb i)]
    exact ih

theorem lineage_le_one (n k : ℕ) : lineage n k ≤ 1 := by
  have h := (summable_lineage_mul n fun _ => 1).le_tsum k fun j _ => by
    simpa using lineage_nonneg n j
  rw [tsum_lineage] at h
  simpa using h

/-- A lineage keeps one copy on average. -/
theorem tsum_lineage_mul_cast (n : ℕ) : ∑' k, lineage n k * k = 1 := by
  induction n with
  | zero => simp [lineage]
  | succ n ih =>
    rw [tsum_lineage_succ_mul (m := fun i => i) tsum_mul_segregationProb]
    exact ih

/-- The second moment of a lineage grows by `1/2` per division. -/
theorem tsum_lineage_mul_sq (n : ℕ) : ∑' k, lineage n k * (k : ℝ) ^ 2 = 1 + n / 2 := by
  induction n with
  | zero => simp [lineage]
  | succ n ih =>
    rw [tsum_lineage_succ_mul (m := fun i : ℕ => (i : ℝ) ^ 2 + i / 2)
      tsum_sq_mul_segregationProb]
    have h : ∑' i, lineage n i * ((i : ℝ) ^ 2 + i / 2) =
        ∑' i, lineage n i * (i : ℝ) ^ 2 + (∑' i, lineage n i * i) / 2 := by
      rw [← tsum_div_const, ← (summable_lineage_mul n _).tsum_add
        ((summable_lineage_mul n fun i : ℕ => (i : ℝ)).div_const 2)]
      exact tsum_congr fun i => by ring
    rw [h, ih, tsum_lineage_mul_cast]
    push_cast
    ring

/-- Exchanging the order of a double sum of nonnegative terms. -/
theorem summable_and_tsum_comm {F : ℕ → ℕ → ℝ} (hF : ∀ n k, 0 ≤ F n k)
    (hrow : ∀ n, Summable (F n)) (hs : Summable fun n => ∑' k, F n k) :
    Summable (fun k => ∑' n, F n k) ∧ ∑' k, ∑' n, F n k = ∑' n, ∑' k, F n k := by
  have hF0 : 0 ≤ Function.uncurry F := fun p => hF p.1 p.2
  have hsum : Summable (Function.uncurry F) := (summable_prod_of_nonneg hF0).2 ⟨hrow, hs⟩
  have hcol := (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => Function.uncurry F p.swap)
    fun p => hF0 p.swap).1 hsum.prod_symm
  simp only [Prod.swap_prod_mk, Function.uncurry_apply_pair] at hcol
  exact ⟨hcol.2, hsum.tsum_comm' hrow hcol.1⟩

/-- The solution from one cell with one copy, `N_k(t) = e^{-t} ∑ₙ (2t)ⁿ/n! · Pₙ(k)`. -/
noncomputable def singleCell (k : ℕ) (t : ℝ) : ℝ :=
  exp (-t) * ∑' n : ℕ, (2 * t) ^ n / n ! * lineage n k

theorem weight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ (2 * t) ^ n / n ! :=
  div_nonneg (pow_nonneg (by linarith) n) (Nat.cast_nonneg _)

theorem singleCell_zero (k : ℕ) : singleCell k 0 = if k = 1 then 1 else 0 := by
  rw [singleCell, tsum_eq_single 0 fun n hn => by simp [hn]]
  simp [lineage]

/-- Moments of the single-cell solution: `∑ₖ w_k N_k(t) = e^{-t} ∑ₙ (2t)ⁿ/n! · a_n` when
`∑ₖ Pₙ(k) w_k = a_n`. -/
theorem singleCell_moment {w a : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (ha : ∀ n, ∑' k, lineage n k * w k = a n) {t : ℝ} (ht : 0 ≤ t)
    (hs : Summable fun n : ℕ => (2 * t) ^ n / n ! * a n) :
    Summable (fun k => w k * singleCell k t) ∧
      ∑' k, w k * singleCell k t = exp (-t) * ∑' n : ℕ, (2 * t) ^ n / n ! * a n := by
  set F : ℕ → ℕ → ℝ := fun n k => (2 * t) ^ n / n ! * (lineage n k * w k) with hF
  have hrow : ∀ n, ∑' k, F n k = (2 * t) ^ n / n ! * a n := fun n => by
    rw [hF, tsum_mul_left, ha]
  obtain ⟨hsum, htsum⟩ := summable_and_tsum_comm (F := F)
    (fun n k => mul_nonneg (weight_nonneg ht n) (mul_nonneg (lineage_nonneg n k) (hw k)))
    (fun n => (summable_lineage_mul n w).mul_left _) (by simpa only [hrow] using hs)
  have hk : ∀ k, w k * singleCell k t = exp (-t) * ∑' n, F n k := fun k => by
    rw [singleCell, hF, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  simp_rw [hk]
  exact ⟨hsum.mul_left _, by rw [tsum_mul_left, htsum, tsum_congr hrow]⟩

theorem summable_weight_mul_sq {t : ℝ} (ht : 0 ≤ t) :
    Summable fun n : ℕ => (2 * t) ^ n / n ! * (1 + (n : ℝ) / 2) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (weight_nonneg ht n) (by positivity))
    (fun n => ?_) ((Real.summable_pow_div_factorial (2 * t)).add
      (Real.summable_pow_div_factorial (2 * (2 * t))))
  have h2n : (n : ℝ) / 2 ≤ 2 ^ n := by
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast n.lt_two_pow_self.le
    linarith
  have hw := weight_nonneg ht n
  calc (2 * t) ^ n / n ! * (1 + (n : ℝ) / 2)
      = (2 * t) ^ n / n ! + (2 * t) ^ n / n ! * ((n : ℝ) / 2) := by ring
    _ ≤ (2 * t) ^ n / n ! + (2 * t) ^ n / n ! * 2 ^ n := by gcongr
    _ = (2 * t) ^ n / n ! + (2 * (2 * t)) ^ n / n ! := by
      rw [show (2 * (2 * t)) ^ n = 2 ^ n * (2 * t) ^ n from mul_pow _ _ _]
      ring

theorem summable_singleCell {t : ℝ} (ht : 0 ≤ t) : Summable fun k => singleCell k t := by
  simpa using (singleCell_moment (w := fun _ => 1) (a := fun _ => 1) (fun _ => zero_le_one)
    tsum_lineage ht (by simpa using Real.summable_pow_div_factorial (2 * t))).1

/-- The single-cell solution has a finite second moment at every time. -/
theorem summable_sq_singleCell {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => (k : ℝ) ^ 2 * singleCell k t :=
  (singleCell_moment (fun _ => sq_nonneg _) tsum_lineage_mul_sq ht
    (summable_weight_mul_sq ht)).1

/-- Termwise derivative of the series over generations. -/
theorem hasDerivAt_series (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s => ∑' n : ℕ, (2 * s) ^ n / n ! * lineage n k)
      (∑' n : ℕ, (n : ℝ) * (2 * t) ^ (n - 1) * 2 / n ! * lineage n k) t := by
  set R := |t| + 1
  have hR : 0 < R := by positivity
  have hu : Summable fun n : ℕ => (n : ℝ) * (2 * R) ^ (n - 1) * 2 / n ! := by
    rw [← summable_nat_add_iff 1]
    refine ((Real.summable_pow_div_factorial (2 * R)).mul_left 2).congr fun n => ?_
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun n s => (2 * s) ^ n / n ! * lineage n k)
    (g' := fun n s => (n : ℝ) * (2 * s) ^ (n - 1) * 2 / n ! * lineage n k)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n s _ => ((((hasDerivAt_id s).const_mul 2).fun_pow n).div_const _).mul_const _
      |>.congr_deriv (by simp)) (fun n s hs => ?_)
    (show (0 : ℝ) ∈ Ioo (-R) R by constructor <;> linarith)
    (summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp only [Finset.mem_singleton] at hn
      simp [hn])
    (show t ∈ Ioo (-R) R by
      constructor <;> linarith [neg_abs_le t, le_abs_self t])
  have h1 : |2 * s| ≤ 2 * R := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have h2 : |(2 * s) ^ (n - 1)| ≤ (2 * R) ^ (n - 1) := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 _
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hc0 := lineage_nonneg n k
  have hA : 0 ≤ (n : ℝ) * 2 / n ! := by positivity
  calc ‖(n : ℝ) * (2 * s) ^ (n - 1) * 2 / n ! * lineage n k‖
      = (n : ℝ) * 2 / n ! * (|(2 * s) ^ (n - 1)| * lineage n k) := by
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_mul, abs_of_nonneg n.cast_nonneg,
          abs_two, abs_of_pos hfac, abs_of_nonneg hc0]
        ring
    _ ≤ (n : ℝ) * 2 / n ! * ((2 * R) ^ (n - 1) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul h2 (lineage_le_one n k) hc0 (pow_nonneg (by linarith) _)) hA
    _ = (n : ℝ) * (2 * R) ^ (n - 1) * 2 / n ! := by ring

/-- The single-cell series solves the mean equations. -/
theorem hasDerivAt_singleCell (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (singleCell k) (-singleCell k t + 2 * ∑' i, singleCell i t * segregationProb i k)
      t := by
  have hd := ((hasDerivAt_neg t).exp).mul (hasDerivAt_series k t)
  -- the derivative series, shifted by one generation
  have hsumd : Summable fun n : ℕ => (n : ℝ) * (2 * t) ^ (n - 1) * 2 / n ! * lineage n k := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((Real.summable_pow_div_factorial (2 * t)).mul_left 2)
    · have := weight_nonneg ht (n + 1)
      have := lineage_nonneg (n + 1) k
      positivity
    · rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      have hw := weight_nonneg ht n
      calc ((n : ℝ) + 1) * (2 * t) ^ n * 2 / (((n : ℝ) + 1) * n !) * lineage (n + 1) k
          = 2 * ((2 * t) ^ n / n !) * lineage (n + 1) k := by field_simp
        _ ≤ 2 * ((2 * t) ^ n / n !) * 1 := by gcongr; exact lineage_le_one _ _
        _ = 2 * ((2 * t) ^ n / n !) := by ring
  have hshift : ∑' n : ℕ, (n : ℝ) * (2 * t) ^ (n - 1) * 2 / n ! * lineage n k =
      2 * ∑' n : ℕ, (2 * t) ^ n / n ! * lineage (n + 1) k := by
    rw [hsumd.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [Nat.cast_zero, zero_mul, zero_div, zero_add]
    refine tsum_congr fun n => ?_
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  -- the kernel sum of the solution, by exchanging generations and copy numbers
  have hkernel : ∑' i, singleCell i t * segregationProb i k =
      exp (-t) * ∑' n : ℕ, (2 * t) ^ n / n ! * lineage (n + 1) k := by
    set F : ℕ → ℕ → ℝ := fun n i => (2 * t) ^ n / n ! * (lineage n i * segregationProb i k)
      with hF
    have hrow : ∀ n, ∑' i, F n i = (2 * t) ^ n / n ! * lineage (n + 1) k := fun n => by
      rw [hF, tsum_mul_left, lineage]
    obtain ⟨-, htsum⟩ := summable_and_tsum_comm (F := F)
      (fun n i => mul_nonneg (weight_nonneg ht n)
        (mul_nonneg (lineage_nonneg n i) (segregationProb_nonneg i k)))
      (fun n => (summable_lineage_mul n _).mul_left _)
      (by
        simp only [hrow]
        exact Summable.of_nonneg_of_le
          (fun n => mul_nonneg (weight_nonneg ht n) (lineage_nonneg _ _))
          (fun n => mul_le_of_le_one_right (weight_nonneg ht n) (lineage_le_one _ _))
          (Real.summable_pow_div_factorial (2 * t)))
    rw [← tsum_congr hrow, ← htsum, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [singleCell, mul_assoc, ← tsum_mul_right]
    congr 1
    exact tsum_congr fun n => by rw [hF]; ring
  convert hd using 1
  · ext s
    simp [singleCell]
  · rw [hkernel, hshift, singleCell]
    ring

/-- **Non-vacuity witness.** The single-cell series is a solution of the model. -/
theorem isSolution_singleCell : IsSolution singleCell where
  nonneg k _ ht := mul_nonneg (exp_pos _).le
    (tsum_nonneg fun n => mul_nonneg (weight_nonneg ht n) (lineage_nonneg n k))
  summable _ ht := summable_singleCell ht
  hasDerivWithinAt k _ ht := (hasDerivAt_singleCell k ht).hasDerivWithinAt

/-- From one cell with one copy, `M₁ ≡ 1` and `M₂(t) = 1 + t`. -/
example {t : ℝ} (ht : 0 ≤ t) : moment singleCell 1 t = 1 ∧ moment singleCell 2 t = 1 + t :=
  isSolution_singleCell.moment_of_single (fun _ hs => summable_sq_singleCell hs)
    singleCell_zero ht

example {t : ℝ} (ht : 0 ≤ t) : copyNumberVariance singleCell t = t := by
  have h0 := isSolution_singleCell.moment_of_single (fun _ hs => summable_sq_singleCell hs)
    singleCell_zero le_rfl
  rw [isSolution_singleCell.copyNumberVariance_eq (fun _ hs => summable_sq_singleCell hs) ht,
    copyNumberVariance, h0.1, h0.2]
  ring

/-- The population is `N(t) = e^t`. -/
example {t : ℝ} (ht : 0 ≤ t) : totalCount singleCell t = exp t := by
  have h0 : totalCount singleCell 0 = 1 := by simp [totalCount, singleCell_zero]
  rw [isSolution_singleCell.totalCount_eq ht, h0, one_mul]

end DomainsTest.Biology.CancerGenomics.EcDNASegregation
