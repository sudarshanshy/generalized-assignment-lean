import GeneralizedAssignment.Basic
import Mathlib.Data.Finset.Sort
import Init.Data.Vector.OfFn

set_option linter.unusedSectionVars false

/-!
# An exact integer knapsack solver

A capacity-indexed dynamic program. Each row is a materialized array
(`Vector`), not a recursively reevaluated function. The output includes
the chosen goods, and the correctness theorem compares it to every
feasible subset. This is the knapsack subroutine of Section 4.1.
-/

namespace GeneralizedAssignment.Knapsack

variable {Good : Type*} [DecidableEq Good]

def total (f : Good → ℕ) (S : Finset Good) : ℕ := ∑ g ∈ S, f g

@[simp] theorem total_empty (f : Good → ℕ) : total f ∅ = 0 := by simp [total]

theorem total_mono (f : Good → ℕ) {S T : Finset Good} (h : S ⊆ T) :
    total f S ≤ total f T := Finset.sum_le_sum_of_subset h

@[simp] theorem total_insert (f : Good → ℕ) {g : Good} {S : Finset Good} (h : g ∉ S) :
    total f (insert g S) = f g + total f S := by simp [total, h]

theorem total_erase (f : Good → ℕ) {g : Good} {S : Finset Good} (h : g ∈ S) :
    total f S = f g + total f (S.erase g) := by
  conv_lhs => rw [← Finset.insert_erase h]
  exact total_insert f (Finset.notMem_erase _ _)

/-- A feasible maximum-value subset. -/
def Correct (w v : Good → ℕ) (S : Finset Good) (c : ℕ) (T : Finset Good) : Prop :=
  T ⊆ S ∧ total w T ≤ c ∧ ∀ U ⊆ S, total w U ≤ c → total v U ≤ total v T

def best (v : Good → ℕ) (S T : Finset Good) : Finset Good :=
  if total v S ≤ total v T then T else S

theorem best_value (v : Good → ℕ) (S T : Finset Good) :
    total v (best v S T) = max (total v S) (total v T) := by
  unfold best
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

def step (w v : Good → ℕ) (g : Good) (c : ℕ) (skip take : Finset Good) : Finset Good :=
  if w g ≤ c then best v skip (insert g take) else skip

theorem step_correct (w v : Good → ℕ) (g : Good) {S skip take : Finset Good} {c : ℕ}
    (hg : g ∉ S) (hskip : Correct w v S c skip)
    (htake : Correct w v S (c - w g) take) :
    Correct w v (insert g S) c (step w v g c skip take) := by
  have hgskip : g ∉ skip := fun h => hg (hskip.1 h)
  have hgtake : g ∉ take := fun h => hg (htake.1 h)
  have hskipSub : skip ⊆ insert g S := hskip.1.trans (Finset.subset_insert _ _)
  have htakeSub : insert g take ⊆ insert g S := by
    intro h hh
    rcases Finset.mem_insert.mp hh with rfl | hh
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (htake.1 hh)
  have erase_subset : ∀ U ⊆ insert g S, U.erase g ⊆ S := by
    intro U hU h hh
    have hmem := hU (Finset.mem_of_mem_erase hh)
    rcases Finset.mem_insert.mp hmem with hEq | hS
    · exact False.elim ((Finset.mem_erase.mp hh).1 hEq)
    · exact hS
  have subset_of_notmem : ∀ U ⊆ insert g S, g ∉ U → U ⊆ S := by
    intro U hU hgu h hh
    rcases Finset.mem_insert.mp (hU hh) with hEq | hS
    · subst h; exact False.elim (hgu hh)
    · exact hS
  unfold step
  split_ifs with hfit
  · have htakeFeas : total w (insert g take) ≤ c := by
      rw [total_insert w hgtake]
      have := htake.2.1
      omega
    refine ⟨?_, ?_, ?_⟩
    · unfold best; split_ifs
      · exact htakeSub
      · exact hskipSub
    · unfold best; split_ifs
      · exact htakeFeas
      · exact hskip.2.1
    · intro U hU hUF
      rw [best_value]
      by_cases hgu : g ∈ U
      · have hrem : total w (U.erase g) ≤ c - w g := by
          have := total_erase w hgu
          omega
        have hval := htake.2.2 (U.erase g) (erase_subset U hU) hrem
        have hv : total v U ≤ total v (insert g take) := by
          rw [total_erase v hgu, total_insert v hgtake]
          omega
        exact hv.trans (le_max_right _ _)
      · exact (hskip.2.2 U (subset_of_notmem U hU hgu) hUF).trans (le_max_left _ _)
  · refine ⟨hskipSub, hskip.2.1, ?_⟩
    intro U hU hUF
    have hgu : g ∉ U := by
      intro hgu
      have := total_erase w hgu
      omega
    exact hskip.2.2 U (subset_of_notmem U hU hgu) hUF

/-- One array row of the capacity-indexed recurrence. -/
def advance (w v : Good → ℕ) (g : Good) (C : ℕ)
    (old : Vector (Finset Good) (C + 1)) : Vector (Finset Good) (C + 1) :=
  Vector.ofFn fun c => step w v g c.val (old.get c)
    (old.get ⟨c.val - w g, lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩)

/-- Rows are evaluated once and stored; lookups use array indexing. -/
def table (w v : Good → ℕ) : List Good → (C : ℕ) → Vector (Finset Good) (C + 1)
  | [], _C => Vector.ofFn fun _ => ∅
  | g :: L, C => advance w v g C (table w v L C)

@[simp] theorem vector_get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  exact Vector.getElem_ofFn (f := f) (i := i.val) i.isLt

theorem table_correct (w v : Good → ℕ) (L : List Good) (hL : L.Nodup) (C : ℕ)
    (c : Fin (C + 1)) : Correct w v L.toFinset c.val ((table w v L C).get c) := by
  induction L generalizing c with
  | nil =>
    simp only [table, vector_get_ofFn, List.toFinset_nil]
    refine ⟨Finset.empty_subset _, by simp, ?_⟩
    intro U hU _
    have : U = ∅ := Finset.subset_empty.mp hU
    simp [this]
  | cons g L ih =>
    have hnd := List.nodup_cons.mp hL
    simp only [table, advance, vector_get_ofFn, List.toFinset_cons]
    exact step_correct w v g (by simpa using hnd.1) (ih hnd.2 c)
      (ih hnd.2 ⟨c.val - w g, lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩)

section Ordered

variable [LinearOrder Good]

/-- An executable exact solver for a finite item set and natural-number capacity. -/
def solve (w v : Good → ℕ) (S : Finset Good) (C : ℕ) : Finset Good :=
  (table w v (S.sort (· ≤ ·)) C).get ⟨C, Nat.lt_succ_self C⟩

theorem solve_correct (w v : Good → ℕ) (S : Finset Good) (C : ℕ) :
    Correct w v S C (solve w v S C) := by
  simpa [solve] using table_correct w v (S.sort (· ≤ ·))
    (S.sort_nodup _) C ⟨C, Nat.lt_succ_self C⟩

end Ordered

/-- Number of materialized table cells, including the initial empty row. -/
def cells : ℕ → ℕ → ℕ
  | 0, C => C + 1
  | n + 1, C => cells n C + (C + 1)

theorem cells_eq (n C : ℕ) : cells n C = (n + 1) * (C + 1) := by
  induction n with
  | zero => simp [cells]
  | succ n ih => simp [cells, ih, Nat.add_mul]

end GeneralizedAssignment.Knapsack
