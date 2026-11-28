/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.ThresholdAlgorithm
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for the threshold algorithm

* Ties: for three objects of equal score (`flat`), `{0}` and `{1}` are both top-1 answers and
  `{0, 1}` is not one; for the scores `2, 1, 1` (`scores`), `{0, 1}` and `{0, 2}` are top-2
  answers and `{1, 2}` is not. `isTopKAmong_univ_iff` turns the top-1 answer `{0}` of `flat` into
  a top-1 choice among all three objects.
* The database `D`: three objects `0, 1, 2` under two attributes, with grades `(1, 0)`,
  `(1/2, 3/4)` and `(0, 1)`; list `0` reads `0, 1, 2` and list `1` reads `2, 1, 0`. The
  aggregation function `t` is the sum, so the aggregate grades are `1`, `5/4` and `1`.
  - For `D`, `t` and `k = 1`, every run fails the stopping rule after round 1 (threshold `2`) and
    first satisfies it after round 2 (threshold `5/4`), with buffer `{1}` then, whichever of the
    tied objects `0` and `2` it buffered after round 1; `{1}` is a top-1 answer for `D` and `t`.
    The source's form of the rule also holds after round 2.
  - For `D`, `t` and `k = N = 3`, every run fails the stopping rule after rounds 1 and 2 and first
    satisfies it after round 3, the last, with all three objects buffered then.
* The database `D₀`: one object and no list. For `D₀` and `k = 1` no run ever satisfies the
  stopping rule, whatever the aggregation function, so the termination clause of
  `thresholdAlgorithm_correct` fails without its hypothesis `1 ≤ m`.
* Graded lists have exactly `N` objects even with no list: `GradedLists (Fin 5) 1 0` is empty.
-/

@[expose] public section

namespace Cslib.Databases.ThresholdAlgorithmTests

open Cslib.Databases GradedLists

/-! ### Ties -/

/-- Three objects of equal score. -/
def flat : Fin 3 → ℕ := fun _ => 0

example : IsTopK flat 1 {0} := by unfold IsTopK; decide
example : IsTopK flat 1 {1} := by unfold IsTopK; decide
example : ¬ IsTopK flat 1 {0, 1} := by unfold IsTopK; decide

/-- Scores `2, 1, 1`, for which `{0, 1}` and `{0, 2}` are top-2 answers and `{1, 2}` is not. -/
def scores : Fin 3 → ℕ := ![2, 1, 1]

example : IsTopK scores 2 {0, 1} := by unfold IsTopK; decide
example : IsTopK scores 2 {0, 2} := by unfold IsTopK; decide
example : ¬ IsTopK scores 2 {1, 2} := by unfold IsTopK; decide

/-- For `flat`, `{0}` is a top-1 choice among all three objects, as it is a top-1 answer. -/
example : IsTopKAmong flat 1 Finset.univ {0} :=
  (isTopKAmong_univ_iff (by simp)).2 (by unfold IsTopK; decide)

/-! ### Three objects under two attributes -/

/-- The grades: row `i` lists the grades of the objects `0, 1, 2` under attribute `i`. -/
noncomputable def grades : Fin 2 → Fin 3 → ℝ := ![![1, 1 / 2, 0], ![0, 3 / 4, 1]]

/-- List `0` reads the objects in the order `0, 1, 2`, and list `1` in the order `2, 1, 0`. -/
def lists : Fin 2 → Fin 3 ≃ Fin 3 := ![Equiv.refl _, Fin.revPerm]

/-- The example database `D`. -/
noncomputable def D : GradedLists (Fin 3) 3 2 where
  grade := grades
  grade_mem_Icc := by
    intro i x
    fin_cases i <;> fin_cases x <;> norm_num [grades]
  list := lists
  antitone_grade := by
    intro i p q hpq
    fin_cases i <;> fin_cases p <;> fin_cases q <;>
      simp_all [grades, lists, Fin.le_def, Fin.rev] <;> norm_num
  nonempty_equiv_fin := ⟨Equiv.refl _⟩

/-- The sum of the two grades. -/
def t : (Fin 2 → ℝ) → ℝ := fun x => x 0 + x 1

theorem t_monotoneOn : MonotoneOn t (Set.Icc 0 1) :=
  fun _ _ _ _ hab => add_le_add (hab 0) (hab 1)

theorem aggregate_eq (x : Fin 3) : D.aggregate t x = ![1, 5 / 4, 1] x := by
  fin_cases x <;> norm_num [aggregate, D, grades, t]

theorem threshold_zero : D.threshold t 0 = 2 := by
  norm_num [threshold, D, grades, lists, t]

theorem threshold_one : D.threshold t 1 = 5 / 4 := by
  norm_num [threshold, D, grades, lists, t, Fin.rev]

theorem threshold_two : D.threshold t 2 = 0 := by
  norm_num [threshold, D, grades, lists, t, Fin.rev]

theorem seen_one : D.seen 1 = {0, 2} := by
  ext x
  fin_cases x <;> simp [mem_seen, D, lists, Fin.exists_fin_two, Fin.rev]

theorem seen_two : D.seen 2 = Finset.univ := by
  ext x
  fin_cases x <;> simp [mem_seen, D, lists]

theorem seen_three : D.seen 3 = Finset.univ := by
  ext x
  fin_cases x <;> simp [mem_seen, D, lists]

/-- For `D`, `t` and `k = 1`, every run fails the stopping rule after round 1. (Its buffer then
holds `0` or `2`, of aggregate grade `1`, below the threshold `2`.) -/
theorem not_stoppingRuleHolds_zero (r : D.ThresholdRun t 1) : ¬ r.StoppingRuleHolds 0 := by
  have hsub : r.buf 1 ⊆ {0, 2} := seen_one ▸ (r.isTopKAmong_seen 1).1
  have hempty : (r.buf 1).filter (fun x => D.threshold t 0 ≤ D.aggregate t x) = ∅ := by
    refine Finset.filter_false_of_mem fun x hx => ?_
    rcases Finset.mem_insert.1 (hsub hx) with rfl | hx
    · norm_num [threshold_zero, aggregate_eq]
    · rw [Finset.mem_singleton] at hx
      subst hx
      norm_num [threshold_zero, aggregate_eq]
  simp [ThresholdRun.StoppingRuleHolds, hempty]

/-- For the example database `D`, sum `t` and `k = 1`, every run has buffer `{1}` after round 2
and satisfies the stopping rule then. -/
theorem buf_two_and_stoppingRuleHolds_one (r : D.ThresholdRun t 1) :
    r.buf 2 = {1} ∧ r.StoppingRuleHolds 1 := by
  obtain ⟨-, hc, hd⟩ := r.isTopKAmong_seen 2
  rw [seen_two, Finset.card_univ, Fintype.card_fin] at hc
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 (by simpa using hc)
  have hy1 : y = 1 := by
    by_contra hne
    have := hd y (by simp [hy]) 1 (by simp [seen_two]) (by simp [hy, Ne.symm hne])
    fin_cases y
    · norm_num [aggregate_eq] at this
    · exact hne rfl
    · norm_num [aggregate_eq] at this
  subst hy1
  refine ⟨hy, ?_⟩
  simp only [ThresholdRun.StoppingRuleHolds, Fin.val_one, Nat.reduceAdd, hy]
  rw [Finset.filter_true_of_mem fun x hx => by
    rw [Finset.mem_singleton.1 hx, threshold_one, aggregate_eq]; norm_num]
  simp

/-- For `D`, `t` and `k = 1`, every run first satisfies the stopping rule after round 2, its
buffer then is `{1}`, and `{1}` is a top-1 answer for `D` and `t`. (The last part is
`thresholdAlgorithm_correct` applied at round 2.) -/
example (r : D.ThresholdRun t 1) :
    ¬ r.StoppingRuleHolds 0 ∧ r.StoppingRuleHolds 1 ∧ r.buf 2 = {1} ∧
      IsTopK (D.aggregate t) 1 {1} := by
  have h := (thresholdAlgorithm_correct D t_monotoneOn (by norm_num) (by norm_num) (by norm_num)
    r).2.2.2.2 1 (buf_two_and_stoppingRuleHolds_one r).2
  exact ⟨not_stoppingRuleHolds_zero r, (buf_two_and_stoppingRuleHolds_one r).2,
    (buf_two_and_stoppingRuleHolds_one r).1,
    by simpa [(buf_two_and_stoppingRuleHolds_one r).1] using h⟩

/-- For `D`, `t` and `k = 1`, every run satisfies the stopping rule after round 2, checked here in
the source's form, over all objects seen. (After round 2 the objects seen are all three, and only
object `1` reaches the threshold `5/4`.) -/
example (r : D.ThresholdRun t 1) : r.StoppingRuleHolds 1 := by
  rw [ThresholdRun.stoppingRuleHolds_iff_seen]
  simp only [Fin.val_one, Nat.reduceAdd, seen_two, threshold_one]
  rw [show (Finset.univ.filter fun x : Fin 3 => (5 / 4 : ℝ) ≤ D.aggregate t x) = {1} by
    ext x; fin_cases x <;> norm_num [aggregate_eq]]
  simp

/-- For `D`, `t` and `k = 3`, every run fails the stopping rule after round 1. (Its buffer then
holds at most the two objects seen.) -/
theorem not_stoppingRuleHolds_zero_three (r : D.ThresholdRun t 3) : ¬ r.StoppingRuleHolds 0 := by
  have hsub : r.buf 1 ⊆ {0, 2} := seen_one ▸ (r.isTopKAmong_seen 1).1
  have hcard := (Finset.card_filter_le (r.buf 1) fun x => D.threshold t 0 ≤ D.aggregate t x).trans
    ((Finset.card_le_card hsub).trans (Finset.card_le_two (a := (0 : Fin 3)) (b := 2)))
  unfold ThresholdRun.StoppingRuleHolds
  simp only [Fin.val_zero, Nat.reduceAdd]
  omega

/-- For `D`, `t` and `k = 3`, every run fails the stopping rule after round 2. (Its buffer then
holds all three objects, but object `0`, of aggregate grade `1`, is below the threshold `5/4`.) -/
theorem not_stoppingRuleHolds_one_three (r : D.ThresholdRun t 3) : ¬ r.StoppingRuleHolds 1 := by
  obtain ⟨hs, hc, -⟩ := r.isTopKAmong_seen 2
  rw [seen_two, Finset.card_univ, Fintype.card_fin] at hc
  have hall : r.buf 2 = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hc)
  simp only [ThresholdRun.StoppingRuleHolds, Fin.val_one, Nat.reduceAdd, hall, threshold_one]
  rw [show (Finset.univ.filter fun x : Fin 3 => (5 / 4 : ℝ) ≤ D.aggregate t x) = {1} by
    ext x; fin_cases x <;> norm_num [aggregate_eq]]
  simp

/-- For `D`, `t` and `k = 3`, every run first satisfies the stopping rule after round 3, the last,
and its buffer then holds all three objects. -/
example (r : D.ThresholdRun t 3) :
    ¬ r.StoppingRuleHolds 0 ∧ ¬ r.StoppingRuleHolds 1 ∧ r.StoppingRuleHolds 2 ∧
      r.buf 3 = Finset.univ := by
  obtain ⟨-, hc, -⟩ := r.isTopKAmong_seen 3
  rw [seen_three, Finset.card_univ, Fintype.card_fin] at hc
  have hall : r.buf 3 = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hc)
  refine ⟨not_stoppingRuleHolds_zero_three r, not_stoppingRuleHolds_one_three r, ?_, hall⟩
  simp only [ThresholdRun.StoppingRuleHolds, Fin.val_two, Nat.reduceAdd, hall, threshold_two]
  rw [Finset.filter_true_of_mem fun x _ => by fin_cases x <;> norm_num [aggregate_eq]]
  simp

/-- For `D`, `t` and `k = 1`, a run exists. -/
example : Nonempty (D.ThresholdRun t 1) := inferInstance

/-! ### No lists -/

/-- One object and no attributes. -/
def D₀ : GradedLists (Fin 1) 1 0 where
  grade := Fin.elim0
  grade_mem_Icc := fun i => Fin.elim0 i
  list := Fin.elim0
  antitone_grade := fun i => Fin.elim0 i
  nonempty_equiv_fin := ⟨Equiv.refl _⟩

/-- For `D₀` and `k = 1`, whatever the aggregation function, no run satisfies the stopping rule
after any round. (With no list nothing is read, so the buffer stays empty.) -/
example (t₀ : (Fin 0 → ℝ) → ℝ) (r : D₀.ThresholdRun t₀ 1) (p : Fin 1) :
    ¬ r.StoppingRuleHolds p := by
  have hseen : D₀.seen ((p : ℕ) + 1) = ∅ := by
    ext x
    simp [mem_seen]
  have hbuf : r.buf ((p : ℕ) + 1) = ∅ :=
    Finset.subset_empty.1 (hseen ▸ (r.isTopKAmong_seen _).1)
  unfold ThresholdRun.StoppingRuleHolds
  rw [hbuf]
  simp

/-- `GradedLists (Fin 5) 1 0` is empty: graded lists with no list still have exactly `N` objects,
so five objects cannot be declared as one. -/
example : IsEmpty (GradedLists (Fin 5) 1 0) :=
  ⟨fun D => D.nonempty_equiv_fin.elim fun e => by simpa using Fintype.card_congr e⟩

end Cslib.Databases.ThresholdAlgorithmTests
