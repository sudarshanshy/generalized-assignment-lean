import GeneralizedAssignment.Basic
import Mathlib.Data.Nat.Log

/-!
# A counted binary search

This is the elementary oracle-search component of the Cook reduction in
Appendix C. A threshold oracle for `k ≤ q` determines `k` with at most
`log₂ upperBound + 1` queries.
-/

namespace GeneralizedAssignment.BinarySearch

def search (p : ℕ → Prop) [DecidablePred p] : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, _hi => (lo, 0)
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if p mid then
        let r := search p fuel lo mid
        (r.1, r.2 + 1)
      else
        let r := search p fuel (mid + 1) hi
        (r.1, r.2 + 1)
    else (lo, 0)

theorem search_spec (p : ℕ → Prop) [DecidablePred p] (k : ℕ)
    (hp : ∀ q, p q ↔ k ≤ q) (fuel lo hi : ℕ)
    (hlo : lo ≤ k) (hhi : k ≤ hi) (hwidth : hi - lo < 2 ^ fuel) :
    (search p fuel lo hi).1 = k ∧ (search p fuel lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [pow_zero] at hwidth
    simp only [search, le_refl, and_true]
    omega
  | succ fuel ih =>
    by_cases hlt : lo < hi
    · simp only [search, if_pos hlt]
      let mid := (lo + hi) / 2
      have hmlo : lo ≤ mid := by dsimp [mid]; omega
      have hmhi : mid < hi := by dsimp [mid]; omega
      have hwleft : mid - lo < 2 ^ fuel := by
        rw [pow_succ] at hwidth
        dsimp [mid]
        omega
      have hwright : hi - (mid + 1) < 2 ^ fuel := by
        rw [pow_succ] at hwidth
        dsimp [mid]
        omega
      by_cases hm : p mid
      · simp only [show p ((lo + hi) / 2) from hm, ↓reduceIte]
        have hr := ih lo mid hlo ((hp mid).mp hm) hwleft
        exact ⟨hr.1, Nat.add_le_add_right hr.2 1⟩
      · simp only [show ¬ p ((lo + hi) / 2) from hm, ↓reduceIte]
        have hk : mid + 1 ≤ k := by
          have := mt (hp mid).mpr hm
          omega
        have hr := ih (mid + 1) hi hk hhi hwright
        exact ⟨hr.1, Nat.add_le_add_right hr.2 1⟩
    · have heq : lo = k := by omega
      simpa only [search, if_neg hlt] using And.intro heq (Nat.zero_le (fuel + 1))

def recover (p : ℕ → Prop) [DecidablePred p] (upperBound : ℕ) : ℕ × ℕ :=
  search p (Nat.log 2 upperBound + 1) 0 upperBound

theorem recover_spec (p : ℕ → Prop) [DecidablePred p] (k upperBound : ℕ)
    (hp : ∀ q, p q ↔ k ≤ q) (hk : k ≤ upperBound) :
    (recover p upperBound).1 = k ∧
      (recover p upperBound).2 ≤ Nat.log 2 upperBound + 1 := by
  apply search_spec p k hp _ _ _ (Nat.zero_le _) hk
  simpa using Nat.lt_pow_succ_log_self (by decide : 1 < 2) upperBound

end GeneralizedAssignment.BinarySearch
