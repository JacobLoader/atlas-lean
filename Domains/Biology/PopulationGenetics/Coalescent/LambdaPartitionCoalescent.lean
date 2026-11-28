/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
public import Domains.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
public import MathlibExt.Probability.Distributions.PoissonKernel
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The partition-valued Λ-coalescent, its branch lengths and its mutations

For a finite measure `Λ` on `[0, 1]`, the **Λ-coalescent** of a sample of `n` genes (Pitman
1999; Sagitov 1999) is the continuous-time Markov chain on the set partitions of the sample
`{0, …, n - 1}` (`PartitionCoalescent.SamplePartition n`) in which, while there are `b` blocks,
each particular set of `k ≥ 2` of them merges into one block at rate `λ_{b,k}`
(`LambdaCoalescent.mergerRate`), and no two mergers happen at once. We encode "`π'` arises from
`π` by merging one set of blocks" as `IsMultiMerge π π'`: `π` refines `π'` and exactly one block
of `π'` is not a block of `π`. That block is then the union of the
`k = #π.parts + 1 - #π'.parts ≥ 2` merged blocks of `π`, and the other blocks are unchanged.
`rateMatrix Λ n` is the rate matrix of the chain, and the chain started from the partition
into singletons is the path process of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`, driven by i.i.d. steps `ω` of
law `inputMeasure Λ n`.

While at least two blocks remain, each block of the current partition is a branch of the
genealogical tree of the sample; the tree ends at its root, when one block remains. The block
`{i}` is the external branch of gene `i`, which ends at the first merger involving `i`, and a
block of at least two genes is an internal branch. With `Y k` the `k`-th state of the jump chain
and `S k` its holding time, the total, external and internal branch lengths are

* `L = ∑_k #(Y k).parts * S k` (`totalLength`),
* `E = ∑_k #{singleton blocks of Y k} * S k` (`externalLength`),
* `I = ∑_k #{blocks of Y k with at least two genes} * S k` (`internalLength`),

the sums running over the `k` with at least two blocks, so that `L = I + E`. If mutations fall
on the tree as a Poisson process of rate `μ` per unit branch length, then given the genealogy the
numbers of mutations on the internal and on the external branches are independent Poisson counts
with means `μ I` and `μ E` (`mutationKernel`, `mutationMeasure`).

## Main definitions

* `IsMultiMerge π π'`: `π'` arises from `π` by merging one set of blocks.
* `rateMatrix Λ n`: the rate matrix of the Λ-coalescent on the partitions of the sample.
* `inputMeasure Λ n`: the law of the steps driving the chain.
* `totalLength`, `externalLength`, `internalLength`: the branch lengths of the genealogy.
* `mutationKernel Λ n μ`, `mutationMeasure Λ n μ`: the genealogy together with the numbers of
  internal and external mutations.

## Main results

* `isRateMatrix_rateMatrix`: `rateMatrix Λ n` is a rate matrix.
* `rateMatrix_self`: the chain leaves a partition with `b` blocks at the total merger rate
  `λ_b = ∑_{k=2}^b (b.choose k) λ_{b,k}`, since the mergers of `k` blocks of a partition
  correspond to its `b.choose k` sets of `k` blocks.
* `internalLength_add_externalLength`: `I + E = L`.
* `measurable_totalLength`, `measurable_externalLength`, `measurable_internalLength`: the
  branch lengths are random variables.
* `fst_mutationMeasure`: adding the mutations leaves the law of the genealogy unchanged.

## References

* J. Pitman, *Coalescents with multiple collisions*, Ann. Probab. 27 (1999), 1870–1902.
* S. Sagitov, *The general coalescent with asynchronous mergers of ancestral lines*,
  J. Appl. Probab. 36 (1999), 1116–1125.
* G. Kersting, J. C. Pardo and A. Siri-Jégousse, *Total internal and external lengths of the
  Bolthausen-Sznitman coalescent*, J. Appl. Probab. 51A (2014), 73–86, Section 1 and Section 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset unitInterval
open scoped ENNReal NNReal

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent

open LambdaCoalescent PartitionCoalescent

-- The steps that drive the path process of
-- `MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`.
local notation "Steps" n => ℕ → (SamplePartition n → SamplePartition n) × ℝ

variable {n : ℕ}

/-- `π'` arises from `π` by merging one set of blocks into one block: `π` refines `π'` and
exactly one block of `π'` is not a block of `π`. That block is the union of the
`#π.parts + 1 - #π'.parts ≥ 2` blocks of `π` it contains, and the other blocks of `π'` are blocks
of `π`. A partition is never a merger of itself. -/
def IsMultiMerge (π π' : SamplePartition n) : Prop :=
  π ≤ π' ∧ #(π'.parts \ π.parts) = 1

/-- The partitions of a finite sample carry the discrete σ-algebra. -/
instance : MeasurableSpace (SamplePartition n) := ⊤

instance : DiscreteMeasurableSpace (SamplePartition n) := ⟨fun _ => trivial⟩

variable (Λ : Measure I) [IsFiniteMeasure Λ]

open scoped Classical in
/-- The **rate matrix of the Λ-coalescent** on the partitions of a sample of `n` genes: from a
partition `π` with `b` blocks, the rate of moving to a partition `π'` obtained by merging one set
of `k ≥ 2` blocks (`IsMultiMerge π π'`, with `k = b + 1 - #π'.parts`) is Pitman's merger rate
`λ_{b,k}` (`LambdaCoalescent.mergerRate Λ b k`); every other off-diagonal entry is `0`, and the
diagonal entry is minus the sum of the off-diagonal entries of its row, which is `-λ_b`
(`rateMatrix_self`). -/
def rateMatrix (n : ℕ) : Matrix (SamplePartition n) (SamplePartition n) ℝ :=
  Matrix.of fun π π' =>
    if π = π' then
      -∑ ρ ∈ univ.erase π,
        if IsMultiMerge π ρ then mergerRate Λ #π.parts (#π.parts + 1 - #ρ.parts) else 0
    else if IsMultiMerge π π' then mergerRate Λ #π.parts (#π.parts + 1 - #π'.parts) else 0

/-- `rateMatrix Λ n` is a rate matrix. -/
theorem isRateMatrix_rateMatrix (n : ℕ) : IsRateMatrix (rateMatrix Λ n) := by
  classical
  refine ⟨fun π π' h => ?_, fun π => ?_⟩
  · simp only [rateMatrix, Matrix.of_apply, h, ite_false]
    split_ifs
    exacts [mergerRate_nonneg Λ _ _, le_rfl]
  · rw [← add_sum_erase _ _ (mem_univ π)]
    simp only [rateMatrix, Matrix.of_apply, ite_true]
    rw [neg_add_eq_zero]
    refine sum_congr rfl fun ρ hρ => ?_
    simp only [(ne_of_mem_erase hρ).symm, ↓reduceIte]

/-! ### The exit rate: mergers of sets of blocks -/

section MultiMerge

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- Merge the parts in a nonempty set `K` of parts of `P` into one part. -/
private def mergeParts (P : Finpartition s) (K : Finset (Finset α)) (hK : K ⊆ P.parts)
    (hne : K.Nonempty) : Finpartition s where
  parts := insert (K.sup id) (P.parts \ K)
  supIndep := by
    refine Set.PairwiseDisjoint.supIndep ?_
    rw [coe_insert]
    refine (P.disjoint.subset (coe_subset.2 sdiff_subset)).insert fun j hj _ => ?_
    obtain ⟨hjP, hjK⟩ := mem_sdiff.1 (mem_coe.1 hj)
    exact Finset.disjoint_sup_left.2 fun A hA =>
      P.disjoint (hK hA) hjP fun h => hjK (h ▸ hA)
  sup_parts := by
    rw [sup_insert, id_eq, ← sup_union, union_sdiff_of_subset hK, P.sup_parts]
  bot_notMem := by
    obtain ⟨A, hA⟩ := hne
    rw [mem_insert, not_or]
    refine ⟨fun h => P.ne_bot (hK hA) (le_bot_iff.1 (h ▸ le_sup (f := id) hA)), fun h => ?_⟩
    exact P.bot_notMem (mem_sdiff.1 h).1

/-- A part of `P` lies in the union of a set `K` of parts of `P` only if it belongs to `K`. -/
private lemma subset_sup_iff {P : Finpartition s} {K : Finset (Finset α)} (hK : K ⊆ P.parts)
    {A : Finset α} (hA : A ∈ P.parts) : A ⊆ K.sup id ↔ A ∈ K := by
  refine ⟨fun h => by_contra fun hAK => P.ne_bot hA ?_, fun h => le_sup (f := id) h⟩
  have hd : Disjoint A (K.sup id) := Finset.disjoint_sup_right.2 fun B hB =>
    P.disjoint hA (hK hB) fun hAB => hAK (hAB ▸ hB)
  exact hd.eq_bot_of_le h

/-- The union of at least two parts is not a part. -/
private lemma sup_notMem {P : Finpartition s} {K : Finset (Finset α)} (hK : K ⊆ P.parts)
    (h2 : 2 ≤ #K) : K.sup id ∉ P.parts := by
  intro hS
  have hall : ∀ A ∈ K, A = K.sup id := fun A hA =>
    by_contra fun hne => P.ne_bot (hK hA)
      ((P.disjoint (hK hA) hS hne).eq_bot_of_le (le_sup (f := id) hA))
  have : #K ≤ 1 := card_le_one.2 fun A hA B hB => (hall A hA).trans (hall B hB).symm
  omega

private lemma mergeParts_sdiff {P : Finpartition s} {K : Finset (Finset α)} (hK : K ⊆ P.parts)
    (hne : K.Nonempty) (h2 : 2 ≤ #K) : (mergeParts P K hK hne).parts \ P.parts = {K.sup id} := by
  change insert (K.sup id) (P.parts \ K) \ P.parts = _
  rw [insert_sdiff_of_notMem _ (sup_notMem hK h2), sdiff_eq_empty_iff_subset.2 sdiff_subset,
    insert_empty]

private lemma le_mergeParts {P : Finpartition s} {K : Finset (Finset α)} (hK : K ⊆ P.parts)
    (hne : K.Nonempty) : P ≤ mergeParts P K hK hne := by
  intro A hA
  by_cases hAK : A ∈ K
  · exact ⟨K.sup id, mem_insert_self _ _, le_sup (f := id) hAK⟩
  · exact ⟨A, mem_insert_of_mem (mem_sdiff.2 ⟨hA, hAK⟩), le_rfl⟩

private lemma card_mergeParts {P : Finpartition s} {K : Finset (Finset α)} (hK : K ⊆ P.parts)
    (hne : K.Nonempty) (h2 : 2 ≤ #K) :
    #(mergeParts P K hK hne).parts + #K = #P.parts + 1 := by
  change #(insert (K.sup id) (P.parts \ K)) + #K = _
  rw [card_insert_of_notMem fun h => sup_notMem hK h2 (mem_sdiff.1 h).1,
    card_sdiff_of_subset hK]
  have := card_le_card hK
  omega

/-- From a merger `Q` of `P`, with new part `C`, the parts of `P` inside `C`: there are at least
two of them, `C` is their union, and `Q` merges exactly them. -/
private lemma eq_mergeParts {P Q : Finpartition s} (hPQ : P ≤ Q) {C : Finset α}
    (hC : Q.parts \ P.parts = {C}) :
    ∃ (hK : P.parts.filter (· ⊆ C) ⊆ P.parts) (hne : (P.parts.filter (· ⊆ C)).Nonempty),
      2 ≤ #(P.parts.filter (· ⊆ C)) ∧ (P.parts.filter (· ⊆ C)).sup id = C ∧
        Q = mergeParts P (P.parts.filter (· ⊆ C)) hK hne := by
  have hCQ : C ∈ Q.parts := (mem_sdiff.1 (hC ▸ mem_singleton_self C)).1
  have hCP : C ∉ P.parts := (mem_sdiff.1 (hC ▸ mem_singleton_self C)).2
  -- a part of `Q` other than `C` is a part of `P`
  have hQP : ∀ D ∈ Q.parts, D ≠ C → D ∈ P.parts := fun D hD hDC => by
    by_contra hDP
    exact hDC (mem_singleton.1 (hC ▸ mem_sdiff.2 ⟨hD, hDP⟩))
  -- a part of `P` meeting `C` lies in `C`
  have hsub : ∀ A ∈ P.parts, ∀ x ∈ A, x ∈ C → A ⊆ C := fun A hA x hxA hxC => by
    obtain ⟨D, hD, hAD⟩ := hPQ hA
    by_cases hDC : D = C
    · exact hDC ▸ hAD
    · exact absurd hxC (Finset.disjoint_left.1 (Q.disjoint hD hCQ hDC) (hAD hxA))
  set K := P.parts.filter (· ⊆ C)
  have hK : K ⊆ P.parts := filter_subset _ _
  have hsup : K.sup id = C := by
    refine le_antisymm (Finset.sup_le fun A hA => (mem_filter.1 hA).2) fun x hxC => ?_
    obtain ⟨A, hA, hxA⟩ := P.exists_mem (Q.le hCQ hxC)
    exact mem_sup.2 ⟨A, mem_filter.2 ⟨hA, hsub A hA x hxA hxC⟩, hxA⟩
  have hne : K.Nonempty := by
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hCQ
    obtain ⟨A, hA, hxA⟩ := P.exists_mem (Q.le hCQ hx)
    exact ⟨A, mem_filter.2 ⟨hA, hsub A hA x hxA hx⟩⟩
  have h2 : 2 ≤ #K := by
    by_contra h
    obtain ⟨A, hKA⟩ := card_eq_one.1 (le_antisymm (by omega) (card_pos.2 hne))
    have hAK : A ∈ K := hKA ▸ mem_singleton_self A
    have hCA : C = A := by rw [← hsup, hKA, sup_singleton, id]
    exact hCP (hCA ▸ (mem_filter.1 hAK).1)
  refine ⟨hK, hne, h2, hsup, Finpartition.ext ?_⟩
  change Q.parts = insert (K.sup id) (P.parts \ K)
  rw [hsup]
  ext D
  rw [mem_insert, mem_sdiff, mem_filter]
  constructor
  · intro hD
    by_cases hDC : D = C
    · exact Or.inl hDC
    · exact Or.inr ⟨hQP D hD hDC, fun ⟨_, hDsub⟩ =>
        Q.ne_bot hD ((Q.disjoint hD hCQ hDC).eq_bot_of_le hDsub)⟩
  · rintro (rfl | ⟨hDP, hDC⟩)
    · exact hCQ
    · obtain ⟨E, hE, hDE⟩ := hPQ hDP
      have hEC : E ≠ C := fun h => hDC ⟨hDP, h ▸ hDE⟩
      have hEP := hQP E hE hEC
      by_cases hDE' : D = E
      · exact hDE' ▸ hE
      · exact absurd ((P.disjoint hDP hEP hDE').eq_bot_of_le hDE) (P.ne_bot hDP)

end MultiMerge

open scoped Classical in
/-- **Exit rate.** The Λ-coalescent leaves a partition with `b` blocks at the total merger rate
`λ_b = ∑_{k=2}^b (b.choose k) λ_{b,k}` (`LambdaCoalescent.totalMergerRate`): the mergers of
`π` that merge `k` blocks correspond to the `b.choose k` sets of `k` blocks of `π`. -/
theorem rateMatrix_self (π : SamplePartition n) :
    rateMatrix Λ n π π = -totalMergerRate Λ #π.parts := by
  set b := #π.parts with hb
  have hself : ¬ IsMultiMerge π π := fun h => by simp [IsMultiMerge] at h
  simp only [rateMatrix, Matrix.of_apply, ite_true, neg_inj]
  rw [sum_erase _ (by simp [hself]), ← sum_filter]
  -- the mergers of `π` correspond to the sets of at least two blocks
  have hbij : ∑ ρ ∈ univ.filter (IsMultiMerge π), mergerRate Λ b (b + 1 - #ρ.parts) =
      ∑ K ∈ π.parts.powerset.filter (2 ≤ #·), mergerRate Λ b #K := by
    refine sum_bij' (fun ρ _ => π.parts.filter (· ⊆ (ρ.parts \ π.parts).sup id))
      (fun K hK => mergeParts π K (mem_powerset.1 (mem_filter.1 hK).1)
        (card_pos.1 (by have := (mem_filter.1 hK).2; omega))) ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      obtain ⟨hle, hcard⟩ := (mem_filter.1 hρ).2
      obtain ⟨C, hC⟩ := card_eq_one.1 hcard
      obtain ⟨-, -, h2, -, -⟩ := eq_mergeParts hle hC
      rw [hC, sup_singleton, id]
      exact mem_filter.2 ⟨mem_powerset.2 (filter_subset _ _), h2⟩
    · intro K hK
      obtain ⟨hKp, h2⟩ := mem_filter.1 hK
      refine mem_filter.2 ⟨mem_univ _, le_mergeParts _ _, ?_⟩
      rw [mergeParts_sdiff _ _ h2, card_singleton]
    · intro ρ hρ
      obtain ⟨hle, hcard⟩ := (mem_filter.1 hρ).2
      obtain ⟨C, hC⟩ := card_eq_one.1 hcard
      obtain ⟨hK, hne, -, -, hQ⟩ := eq_mergeParts hle hC
      simp only [hC, sup_singleton, id]
      exact hQ.symm
    · intro K hK
      obtain ⟨hKp, h2⟩ := mem_filter.1 hK
      rw [mergeParts_sdiff _ _ h2, sup_singleton, id]
      ext A
      rw [mem_filter]
      exact ⟨fun ⟨hA, hAs⟩ => (subset_sup_iff (mem_powerset.1 hKp) hA).1 hAs,
        fun hA => ⟨mem_powerset.1 hKp hA, (subset_sup_iff (mem_powerset.1 hKp)
          (mem_powerset.1 hKp hA)).2 hA⟩⟩
    · intro ρ hρ
      obtain ⟨hle, hcard⟩ := (mem_filter.1 hρ).2
      obtain ⟨C, hC⟩ := card_eq_one.1 hcard
      obtain ⟨hK, hne, h2, -, hQ⟩ := eq_mergeParts hle hC
      have hc := card_mergeParts hK hne h2
      rw [← hQ] at hc
      simp only [hC, sup_singleton, id]
      congr 1
      omega
  rw [hbij, sum_filter]
  -- sets of fewer than two blocks have merger rate `0`
  have hlt : ∀ K ∈ π.parts.powerset, (if 2 ≤ #K then mergerRate Λ b #K else 0) =
      mergerRate Λ b #K := fun K _ => by
    split_ifs with h
    · rfl
    · rw [mergerRate, ite_eq_right (by omega)]
  rw [sum_congr rfl hlt, sum_powerset_apply_card (fun k => mergerRate Λ b k), ← hb,
    totalMergerRate]
  symm
  refine sum_subset (fun k hk => mem_range.2 (by have := mem_Icc.1 hk; omega)) (fun k hk hk' =>
    ?_) |>.trans (sum_congr rfl fun k _ => by rw [nsmul_eq_mul])
  have : ¬ (2 ≤ k ∧ k ≤ b) := fun h => hk' (mem_Icc.2 h)
  rw [mergerRate, ite_eq_right this, mul_zero]

/-- The law of the steps that drive the Λ-coalescent of a sample of `n` genes: the steps are
i.i.d., each a random map drawing the next partition from the jump matrix of
`rateMatrix Λ n` and an independent exponential clock of rate `1`
(`ProbabilityTheory.ctmcInputMeasure`). -/
def inputMeasure (n : ℕ) : Measure (Steps n) :=
  open scoped Classical in ctmcInputMeasure (isRateMatrix_rateMatrix Λ n)

instance (n : ℕ) : IsProbabilityMeasure (inputMeasure Λ n) := by
  unfold inputMeasure
  infer_instance

/-- The **total branch length** `L` of the genealogy of a sample of `n` genes under the
Λ-coalescent driven by the steps `ω`. The chain starts from the partition into singletons `⊥`;
while it sits at its `k`-th state `Y k` (`ProbabilityTheory.ctmcJumpChain`), for the holding time
`S k` (`ProbabilityTheory.ctmcHoldingTime`), each of the `#(Y k).parts` blocks is a branch of the
tree. The tree ends at its root, when one block remains, so `L = ∑_k #(Y k).parts * S k`, the sum
over the `k` for which `Y k` has at least two blocks. The value is in `ℝ≥0∞`; a holding time is
`∞` at a state the chain never leaves, such as every state with at least two blocks when
`Λ = 0`. -/
def totalLength (n : ℕ) (ω : Steps n) : ℝ≥0∞ :=
  ∑' k, if 2 ≤ #(ctmcJumpChain ⊥ ω k).parts then
    (#(ctmcJumpChain ⊥ ω k).parts : ℝ≥0∞) * ctmcHoldingTime (rateMatrix Λ n) ⊥ ω k else 0

/-- The **total external branch length** `E` of the genealogy of a sample of `n` genes under the
Λ-coalescent driven by the steps `ω`. The external branch of gene `i` runs from the leaf `i` to
the first merger involving `i`; while it lasts, `{i}` is a block of the partition. So, with `Y k`
and `S k` as in `totalLength`, `E = ∑_k #{B ∈ (Y k).parts | #B = 1} * S k`, the sum over the `k`
for which `Y k` has at least two blocks. -/
def externalLength (n : ℕ) (ω : Steps n) : ℝ≥0∞ :=
  ∑' k, if 2 ≤ #(ctmcJumpChain ⊥ ω k).parts then
    (#{B ∈ (ctmcJumpChain ⊥ ω k).parts | #B = 1} : ℝ≥0∞) *
      ctmcHoldingTime (rateMatrix Λ n) ⊥ ω k else 0

/-- The **total internal branch length** `I` of the genealogy of a sample of `n` genes under the
Λ-coalescent driven by the steps `ω`: the total length of the branches that subtend at least two
genes, the blocks that have already taken part in a merger. With `Y k` and `S k` as in
`totalLength`, `I = ∑_k #{B ∈ (Y k).parts | 2 ≤ #B} * S k`, the sum over the `k` for which `Y k`
has at least two blocks, so that `I + E = L` (`internalLength_add_externalLength`). -/
def internalLength (n : ℕ) (ω : Steps n) : ℝ≥0∞ :=
  ∑' k, if 2 ≤ #(ctmcJumpChain ⊥ ω k).parts then
    (#{B ∈ (ctmcJumpChain ⊥ ω k).parts | 2 ≤ #B} : ℝ≥0∞) *
      ctmcHoldingTime (rateMatrix Λ n) ⊥ ω k else 0

/-- A block of a partition has one gene or at least two. -/
private lemma card_filter_two_le_add_card_filter_one (π : SamplePartition n) :
    #{B ∈ π.parts | 2 ≤ #B} + #{B ∈ π.parts | #B = 1} = #π.parts := by
  rw [← card_union_of_disjoint (disjoint_filter.2 fun B _ h h' => by omega), ← filter_or]
  congr 1
  refine filter_true_of_mem fun B hB => ?_
  have := card_pos.2 (π.nonempty_of_mem_parts hB)
  omega

/-- The internal and external branch lengths add up to the total branch length: `I + E = L`. -/
theorem internalLength_add_externalLength (n : ℕ) (ω : Steps n) :
    internalLength Λ n ω + externalLength Λ n ω = totalLength Λ n ω := by
  rw [internalLength, externalLength, totalLength, ← tsum_add]
  refine tsum_congr fun k => ?_
  split_ifs
  · rw [← add_mul, ← Nat.cast_add, card_filter_two_le_add_card_filter_one]
  · rw [add_zero]

/-- A branch length of the form `∑_k [Y k has at least two blocks] f(Y k) S k` is a measurable
function of the steps. -/
private lemma measurable_tsum_ite (f : SamplePartition n → ℕ) :
    Measurable fun ω : Steps n => ∑' k, if 2 ≤ #(ctmcJumpChain ⊥ ω k).parts then
      (f (ctmcJumpChain ⊥ ω k) : ℝ≥0∞) * ctmcHoldingTime (rateMatrix Λ n) ⊥ ω k else 0 := by
  refine Measurable.tsum fun k => ?_
  have hY := measurable_ctmcJumpChain (ι := SamplePartition n) ⊥ k
  refine Measurable.ite ?_ ?_ measurable_const
  · exact hY (DiscreteMeasurableSpace.forall_measurableSet {π : SamplePartition n | 2 ≤ #π.parts})
  · exact ((Measurable.of_discrete (f := fun π : SamplePartition n => (f π : ℝ≥0∞))).comp
      hY).mul (measurable_ctmcHoldingTime ⊥ k)

/-- The total branch length is a measurable function of the steps. -/
theorem measurable_totalLength (n : ℕ) : Measurable (totalLength Λ n) :=
  measurable_tsum_ite Λ fun π => #π.parts

/-- The external branch length is a measurable function of the steps. -/
theorem measurable_externalLength (n : ℕ) : Measurable (externalLength Λ n) :=
  measurable_tsum_ite Λ fun π => #{B ∈ π.parts | #B = 1}

/-- The internal branch length is a measurable function of the steps. -/
theorem measurable_internalLength (n : ℕ) : Measurable (internalLength Λ n) :=
  measurable_tsum_ite Λ fun π => #{B ∈ π.parts | 2 ≤ #B}

/-- **Poisson mutation on the genealogy.** Given the steps `ω`, and so the genealogy, the numbers
of mutations on the internal and on the external branches, when mutations fall on the tree as a
Poisson process of rate `μ` per unit branch length: independent Poisson counts with means
`μ I(ω)` and `μ E(ω)` (`internalLength`, `externalLength`). The lengths enter through
`ENNReal.toNNReal`, which sends an infinite length to `0`. -/
def mutationKernel (n : ℕ) (μ : ℝ≥0) : Kernel (Steps n) (ℕ × ℕ) :=
  poissonMeasureKernel.comap (fun ω => μ * (internalLength Λ n ω).toNNReal)
      (measurable_const.mul (measurable_internalLength Λ n).ennreal_toNNReal) ×ₖ
    poissonMeasureKernel.comap (fun ω => μ * (externalLength Λ n ω).toNNReal)
      (measurable_const.mul (measurable_externalLength Λ n).ennreal_toNNReal)

instance (n : ℕ) (μ : ℝ≥0) : IsMarkovKernel (mutationKernel Λ n μ) := by
  unfold mutationKernel
  infer_instance

/-- The joint law of the genealogy and its mutations: the steps `ω` driving the Λ-coalescent of a
sample of `n` genes (`inputMeasure Λ n`) and, given them, the pair `(M_I, M_E)` of the numbers of
mutations on the internal and on the external branches, under Poisson mutation of rate `μ` per
unit branch length (`mutationKernel`). A point is `(ω, (M_I, M_E))`. -/
def mutationMeasure (n : ℕ) (μ : ℝ≥0) : Measure ((Steps n) × (ℕ × ℕ)) :=
  inputMeasure Λ n ⊗ₘ mutationKernel Λ n μ

instance (n : ℕ) (μ : ℝ≥0) : IsProbabilityMeasure (mutationMeasure Λ n μ) := by
  unfold mutationMeasure
  infer_instance

/-- Adding the mutations leaves the law of the genealogy unchanged: the first marginal of
`mutationMeasure Λ n μ` is `inputMeasure Λ n`. -/
theorem fst_mutationMeasure (n : ℕ) (μ : ℝ≥0) :
    (mutationMeasure Λ n μ).fst = inputMeasure Λ n :=
  Measure.fst_compProd _ _

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaPartitionCoalescent
