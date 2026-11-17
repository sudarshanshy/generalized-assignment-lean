import GeneralizedAssignment.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A counted finite deletion routine

Repeatedly delete an item while a decidable predicate remains true.
The result is locally minimal, with at most `|C|` deletions and `|C|²`
predicate tests. Algorithms 3 and 5 instantiate this common routine
with their exact and approximate envy tests.
-/

namespace GeneralizedAssignment.FiniteDeletion

variable {Good : Type*} [LinearOrder Good]

structure Result (P : Finset Good → Prop) (C : Finset Good) where
  bundle : Finset Good
  subset : bundle ⊆ C
  holds : P bundle
  stop : ∀ g ∈ bundle, ¬ P (bundle.erase g)
  deletions : ℕ
  deletion_bound : deletions ≤ C.card
  queries : ℕ
  query_bound : queries ≤ C.card ^ 2

def removable (P : Finset Good → Prop) [DecidablePred P] (C : Finset Good) : Finset Good :=
  C.filter fun g => P (C.erase g)

structure Output (Good : Type*) where
  bundle : Finset Good
  deletions : ℕ
  queries : ℕ

def runAux (P : Finset Good → Prop) [DecidablePred P] : ℕ → Finset Good → Output Good
  | 0, C => ⟨C, 0, 0⟩
  | fuel + 1, C =>
    let M := removable P C
    if hm : M.Nonempty then
      let g := M.min' hm
      let R := runAux P fuel (C.erase g)
      ⟨R.bundle, R.deletions + 1, C.card + R.queries⟩
    else ⟨C, 0, C.card⟩

theorem runAux_spec (P : Finset Good → Prop) [DecidablePred P]
    (fuel : ℕ) (C : Finset Good) (hC : P C) (hcard : C.card ≤ fuel) :
    let R := runAux P fuel C
    R.bundle ⊆ C ∧ P R.bundle ∧ (∀ g ∈ R.bundle, ¬ P (R.bundle.erase g)) ∧
      R.deletions ≤ C.card ∧ R.queries ≤ C.card ^ 2 := by
  induction fuel generalizing C with
  | zero =>
    have he : C = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    simp [runAux, he] at hC ⊢
    exact hC
  | succ fuel ih =>
    let M := removable P C
    by_cases hm : M.Nonempty
    · let g := M.min' hm
      have hg := M.min'_mem hm
      have hgC : g ∈ C := (Finset.mem_filter.mp hg).1
      have hnext : P (C.erase g) := (Finset.mem_filter.mp hg).2
      have hc : (C.erase g).card + 1 = C.card := Finset.card_erase_add_one hgC
      have hR := ih (C.erase g) hnext (by omega)
      simp only [runAux, show (removable P C).Nonempty from hm, ↓reduceDIte]
      refine ⟨hR.1.trans (Finset.erase_subset _ _), hR.2.1, hR.2.2.1, ?_, ?_⟩
      · change (runAux P fuel (C.erase g)).deletions + 1 ≤ C.card
        have := hR.2.2.2.1
        omega
      · change C.card + (runAux P fuel (C.erase g)).queries ≤ C.card ^ 2
        have := hR.2.2.2.2
        nlinarith
    · simp only [runAux, show ¬ (removable P C).Nonempty from hm, ↓reduceDIte]
      refine ⟨Finset.Subset.refl _, hC, ?_, Nat.zero_le _, ?_⟩
      · intro g hg h
        exact hm ⟨g, Finset.mem_filter.mpr ⟨hg, h⟩⟩
      · by_cases hzero : C.card = 0
        · simp [hzero]
        · have : 1 ≤ C.card := by omega
          nlinarith

def run (P : Finset Good → Prop) [DecidablePred P] (C : Finset Good) (hC : P C) :
    Result P C :=
  let R := runAux P C.card C
  let h := runAux_spec P C.card C hC le_rfl
  ⟨R.bundle, h.1, h.2.1, h.2.2.1, R.deletions, h.2.2.2.1, R.queries, h.2.2.2.2⟩

end GeneralizedAssignment.FiniteDeletion
