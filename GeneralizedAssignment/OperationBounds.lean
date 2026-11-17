import GeneralizedAssignment.FPTAS
import Mathlib.Data.Nat.Log

set_option linter.unusedSectionVars false

/-!
# Input-derived operation bounds

The earlier bounds allow any suitable value bit bound. Here that bound
is computed from the input itself. Exact knapsack table sizes are bounded
by the largest budget; approximate table sizes instead depend on the
accuracy parameter, as required for an FPTAS.
-/

namespace GeneralizedAssignment.NaturalInstance

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (N : NaturalInstance Agent Good)

def valueBits : ℕ := Nat.log 2 (N.totalValue + 1) + 1

theorem valueBits_bound (a : Agent) : N.value a Finset.univ + 1 ≤ 2 ^ N.valueBits := by
  have ha : N.value a Finset.univ ≤ N.totalValue := by
    unfold totalValue
    exact Finset.single_le_sum (f := fun b : Agent => N.value b (Finset.univ : Finset Good))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hp : N.totalValue + 1 < 2 ^ N.valueBits :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) (N.totalValue + 1)
  exact (Nat.add_le_add_right ha 1).trans hp.le

def maxBudget : ℕ := Finset.univ.sup N.budget

theorem budget_le_max (a : Agent) : N.budget a ≤ N.maxBudget :=
  Finset.le_sup (Finset.mem_univ a)

/-- A uniform bound for every exact-knapsack table queried by Algorithm 2. -/
theorem exact_knapsack_cells (a : Agent) (T : Finset Good) :
    Knapsack.cells (T.sort (· ≤ ·)).length (N.budget a) ≤
      (Fintype.card Good + 1) * (N.maxBudget + 1) := by
  rw [Knapsack.cells_eq, Finset.length_sort]
  exact Nat.mul_le_mul (Nat.add_le_add_right (Finset.card_le_univ T) 1)
    (Nat.add_le_add_right (N.budget_le_max a) 1)

theorem runApprox_queries_input_bound (r : ℕ) (hr : 2 ≤ r) :
    (N.runApprox r hr).queries ≤ (5 * Fintype.card Agent * N.valueBits * r + 1) *
      ((Fintype.card Agent + 1) * (1 + (Fintype.card Good + 1) ^ 2)) :=
  N.runApprox_queries_le r hr N.valueBits N.valueBits_bound

theorem runFPTAS_queries_input_bound (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    (N.runFPTAS ε hε₀ hε₁).queries ≤
      (5 * Fintype.card Agent * N.valueBits * accuracyParameter ε + 1) *
        ((Fintype.card Agent + 1) * (1 + (Fintype.card Good + 1) ^ 2)) :=
  N.runFPTAS_queries_le ε hε₀ hε₁ N.valueBits N.valueBits_bound

end GeneralizedAssignment.NaturalInstance
