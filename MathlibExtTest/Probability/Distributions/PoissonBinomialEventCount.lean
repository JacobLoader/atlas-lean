/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonBinomialEventCount
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the number of independent events that occur

For independent events with probabilities `p i`: none of them occur with probability
`∏ i, (1 - p i)`; of two events with probabilities `a` and `b`, exactly one occurs with
probability `a (1 - b) + (1 - a) b` and at least one with probability `1 - (1 - a) (1 - b)`; at
least zero of them occur with probability `1`, and more than their number never occur. With
equal probabilities the mass function is the binomial one, as in
`MathlibExt.Probability.Distributions.BinomialEventCount`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Probability.Distributions.PoissonBinomialEventCount

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- None of the independent events occur with probability `∏ i, (1 - p i)`. -/
example {m : ℕ} {E : Fin m → Set Ω} {p : Fin m → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (h : iIndepSet E μ) (hp : ∀ i, μ.real (E i) = p i) :
    μ.real {ω | {i | ω ∈ E i}.ncard = 0} = ∏ i, (1 - p i) := by
  rw [h.measureReal_ncard_eq_poissonBinomialPMF hE hp 0]
  simp [poissonBinomialPMF]

/-- Of two independent events with probabilities `a` and `b`, exactly one occurs with probability
`a (1 - b) + (1 - a) b`. -/
example {E : Fin 2 → Set Ω} {a b : ℝ} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = (Fin.cons a (Fin.cons b Fin.elim0) : Fin 2 → ℝ) i) :
    μ.real {ω | {i | ω ∈ E i}.ncard = 1} = a * (1 - b) + (1 - a) * b := by
  rw [h.measureReal_ncard_eq_poissonBinomialPMF hE hp 1]
  refine (poissonBinomialPMF_cons_succ _ _ 0).trans ?_
  rw [poissonBinomialPMF_cons_zero, poissonBinomialPMF_cons_succ,
    poissonBinomialPMF_eq_zero_of_lt _ (by norm_num : 0 < 0 + 1)]
  simp [poissonBinomialPMF]

/-- Of two independent events with probabilities `a` and `b`, at least one occurs with
probability `1 - (1 - a) (1 - b)`. -/
example {E : Fin 2 → Set Ω} {a b : ℝ} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = (Fin.cons a (Fin.cons b Fin.elim0) : Fin 2 → ℝ) i) :
    μ.real {ω | 1 ≤ {i | ω ∈ E i}.ncard} = 1 - (1 - a) * (1 - b) := by
  rw [h.measureReal_le_ncard_eq_poissonBinomialTail hE hp 1]
  refine (poissonBinomialTail_cons_succ _ _ 0).trans ?_
  rw [poissonBinomialTail_cons_succ, poissonBinomialPMF_cons_zero]
  simp [poissonBinomialTail, poissonBinomialPMF]
  ring

/-- At least zero of the events occur with probability `1`. -/
example {m : ℕ} {E : Fin m → Set Ω} {p : Fin m → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (h : iIndepSet E μ) (hp : ∀ i, μ.real (E i) = p i) :
    μ.real {ω | 0 ≤ {i | ω ∈ E i}.ncard} = 1 := by
  rw [h.measureReal_le_ncard_eq_poissonBinomialTail hE hp 0, poissonBinomialTail,
    ← Nat.range_succ_eq_Icc_zero, sum_poissonBinomialPMF]

/-- More than `m` of `m` events never occur. -/
example {m : ℕ} {E : Fin m → Set Ω} {p : Fin m → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (h : iIndepSet E μ) (hp : ∀ i, μ.real (E i) = p i) :
    μ.real {ω | m + 1 ≤ {i | ω ∈ E i}.ncard} = 0 := by
  rw [h.measureReal_le_ncard_eq_poissonBinomialTail hE hp (m + 1), poissonBinomialTail,
    Icc_eq_empty (by omega), sum_empty]

/-- With equal probabilities `q`, exactly `j` events occur with the binomial probability
`C(m, j) q ^ j (1 - q) ^ (m - j)`. -/
example {m : ℕ} {E : Fin m → Set Ω} {q : ℝ} (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hq : ∀ i, μ.real (E i) = q) (j : ℕ) :
    μ.real {ω | {i | ω ∈ E i}.ncard = j} = m.choose j * q ^ j * (1 - q) ^ (m - j) := by
  rw [h.measureReal_ncard_eq_poissonBinomialPMF hE (p := fun _ => q) hq j,
    poissonBinomialPMF_const]

end MathlibExtTest.Probability.Distributions.PoissonBinomialEventCount
