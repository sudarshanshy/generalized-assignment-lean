import GeneralizedAssignment.Knapsack

set_option linter.unusedSectionVars false

/-!
# A value-indexed exact knapsack solver

This solver reuses the capacity-indexed DP with values and weights swapped.
For a target value `q`, it removes a maximum-weight set of value at most
`totalValue - q`. Its complement is a minimum-weight set reaching `q`.
The single shared table has `O(m * totalValue)` cells. This form is useful
for the value-scaling FPTAS.
-/

namespace GeneralizedAssignment.Knapsack

variable {Good : Type*} [DecidableEq Good]

theorem total_sdiff (f : Good → ℕ) {S T : Finset Good} (h : T ⊆ S) :
    total f (S \ T) + total f T = total f S := Finset.sum_sdiff h

def ValueTableCorrect (w v : Good → ℕ) (S : Finset Good)
    (rows : Vector (Finset Good) (total v S + 1)) : Prop :=
  ∀ c, Correct v w S c.val (rows.get c)

def remainder (v : Good → ℕ) (S : Finset Good)
    (rows : Vector (Finset Good) (total v S + 1)) (q : Fin (total v S + 1)) : Finset Good :=
  S \ rows.get ⟨total v S - q.val, lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)⟩

theorem remainder_spec (w v : Good → ℕ) (S : Finset Good)
    (rows : Vector (Finset Good) (total v S + 1)) (hrows : ValueTableCorrect w v S rows)
    (q : Fin (total v S + 1)) :
    remainder v S rows q ⊆ S ∧ q.val ≤ total v (remainder v S rows q) ∧
      ∀ U ⊆ S, q.val ≤ total v U → total w (remainder v S rows q) ≤ total w U := by
  let c : Fin (total v S + 1) :=
    ⟨total v S - q.val, lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)⟩
  have hc := hrows c
  have hval := total_sdiff v hc.1
  have hweight := total_sdiff w hc.1
  change remainder v S rows q ⊆ S ∧ q.val ≤ total v (S \ rows.get c) ∧
    ∀ U ⊆ S, q.val ≤ total v U → total w (S \ rows.get c) ≤ total w U
  refine ⟨Finset.sdiff_subset, ?_, ?_⟩
  · have hcap := hc.2.1
    have hq := q.isLt
    change total v (rows.get c) ≤ total v S - q.val at hcap
    omega
  · intro U hUS hqU
    have hcomp := total_sdiff v hUS
    have hcompW := total_sdiff w hUS
    have hcap : total v (S \ U) ≤ c.val := by
      dsimp [c]
      omega
    have hopt := hc.2.2 (S \ U) Finset.sdiff_subset hcap
    omega

def feasibleTargets (w v : Good → ℕ) (S : Finset Good) (C : ℕ)
    (rows : Vector (Finset Good) (total v S + 1)) : Finset (Fin (total v S + 1)) :=
  Finset.univ.filter fun q => total w (remainder v S rows q) ≤ C

theorem feasibleTargets_nonempty (w v : Good → ℕ) (S : Finset Good) (C : ℕ)
    (rows : Vector (Finset Good) (total v S + 1)) (hrows : ValueTableCorrect w v S rows) :
    (feasibleTargets w v S C rows).Nonempty := by
  let q : Fin (total v S + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have h := (remainder_spec w v S rows hrows q).2.2 ∅ (Finset.empty_subset _) (by simp [q])
  refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simpa using h.trans (by simp : total w ∅ ≤ C)

def selectTarget (w v : Good → ℕ) (S : Finset Good) (C : ℕ)
    (rows : Vector (Finset Good) (total v S + 1)) (hrows : ValueTableCorrect w v S rows) :
    Fin (total v S + 1) :=
  (feasibleTargets w v S C rows).max' (feasibleTargets_nonempty w v S C rows hrows)

theorem selectTarget_correct (w v : Good → ℕ) (S : Finset Good) (C : ℕ)
    (rows : Vector (Finset Good) (total v S + 1)) (hrows : ValueTableCorrect w v S rows) :
    Correct w v S C (remainder v S rows (selectTarget w v S C rows hrows)) := by
  let q := selectTarget w v S C rows hrows
  have hspec := remainder_spec w v S rows hrows q
  have hqmem : q ∈ feasibleTargets w v S C rows :=
    (feasibleTargets w v S C rows).max'_mem _
  refine ⟨hspec.1, (Finset.mem_filter.mp hqmem).2, ?_⟩
  intro U hUS hUC
  let p : Fin (total v S + 1) := ⟨total v U, Nat.lt_succ_of_le (total_mono v hUS)⟩
  have hpfeas : total w (remainder v S rows p) ≤ C :=
    ((remainder_spec w v S rows hrows p).2.2 U hUS le_rfl).trans hUC
  have hpmem : p ∈ feasibleTargets w v S C rows :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpfeas⟩
  have hpq : p ≤ q := (feasibleTargets w v S C rows).le_max' p hpmem
  exact (show total v U ≤ q.val from hpq).trans hspec.2.1

section Ordered

variable [LinearOrder Good]

theorem valueTable_correct (w v : Good → ℕ) (S : Finset Good) :
    ValueTableCorrect w v S (table v w (S.sort (· ≤ ·)) (total v S)) := by
  intro c
  simpa using table_correct v w (S.sort (· ≤ ·)) (S.sort_nodup _) (total v S) c

/-- Exact knapsack in time polynomial in the total value, using a shared DP table. -/
def valueSolve (w v : Good → ℕ) (S : Finset Good) (C : ℕ) : Finset Good :=
  let rows := table v w (S.sort (· ≤ ·)) (total v S)
  let q := selectTarget w v S C rows (valueTable_correct w v S)
  remainder v S rows q

theorem valueSolve_correct (w v : Good → ℕ) (S : Finset Good) (C : ℕ) :
    Correct w v S C (valueSolve w v S C) :=
  selectTarget_correct w v S C _ (valueTable_correct w v S)

/-- The number of DP cells created by the value-indexed solver. -/
theorem valueSolve_cells (v : Good → ℕ) (S : Finset Good) :
    cells (S.sort (· ≤ ·)).length (total v S) = (S.card + 1) * (total v S + 1) := by
  simp [cells_eq]

end Ordered

end GeneralizedAssignment.Knapsack
