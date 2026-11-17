import GeneralizedAssignment.ApproximateAlgorithm
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.CharZero

set_option linter.unusedSectionVars false

/-!
# The FPTAS with a rational error input

For any rational `0 < ε ≤ 1`, choose `r = ⌈2/ε⌉` and run the executable
integer algorithm. The result is `(1-ε)`-FEFx. The parameter is at most
`3/ε`; the previously proved call count and DP-size bounds are therefore
polynomial in the input bit length and `1/ε`.
-/

namespace GeneralizedAssignment

namespace Allocation

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

theorem ApproxFEFx.mono {I : Instance Agent Good} {A : Allocation Agent Good}
    {p q : ℝ} (h : A.ApproxFEFx I q) (hpq : p ≤ q) : A.ApproxFEFx I p := by
  refine ⟨h.1, ?_, ?_⟩
  · intro a b S hS hF
    exact (mul_le_mul_of_nonneg_right hpq (I.value_nonneg a S)).trans (h.2.1 a b S hS hF)
  · intro a S hS hF
    exact (mul_le_mul_of_nonneg_right hpq (I.value_nonneg a S)).trans (h.2.2 a S hS hF)

end Allocation

namespace NaturalInstance

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (N : NaturalInstance Agent Good)

def accuracyParameter (ε : ℚ) : ℕ := Nat.ceil (2 / ε)

theorem accuracyParameter_ge_two (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    2 ≤ accuracyParameter ε := by
  have h : (2 : ℚ) ≤ 2 / ε := (le_div_iff₀ hε₀).mpr (by linarith)
  have hc := Nat.ceil_le_ceil h
  simpa [accuracyParameter] using hc

theorem accuracyParameter_accuracy (ε : ℚ) (hε : 0 < ε) :
    2 / (accuracyParameter ε : ℚ) ≤ ε := by
  have hceil := Nat.le_ceil (2 / ε)
  have hpos : 0 < accuracyParameter ε := by
    apply Nat.ceil_pos.mpr
    exact div_pos (by norm_num) hε
  have hr : (0 : ℚ) < accuracyParameter ε := by exact_mod_cast hpos
  apply (div_le_iff₀ hr).mpr
  have h := (div_le_iff₀ hε).mp hceil
  simpa [accuracyParameter, mul_comm] using h

theorem accuracyParameter_bound (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    (accuracyParameter ε : ℚ) ≤ 3 / ε := by
  have hc := Nat.ceil_lt_add_one (le_of_lt (div_pos (by norm_num : (0 : ℚ) < 2) hε₀))
  have hsum : 2 / ε + 1 ≤ 3 / ε := by
    apply (mul_le_mul_iff_right₀ hε₀).mp
    have hne := ne_of_gt hε₀
    field_simp [hne]
    linarith
  exact hc.le.trans hsum

def runFPTAS (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) : ExecutionOutput Agent Good :=
  N.runApprox (accuracyParameter ε) (accuracyParameter_ge_two ε hε₀ hε₁)

def solveFPTAS (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) : Allocation Agent Good :=
  (N.runFPTAS ε hε₀ hε₁).allocation

/-- Theorem 4, correctness for any rational accuracy request. -/
theorem solveFPTAS_fair (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    (N.solveFPTAS ε hε₀ hε₁).ApproxFEFx N.toReal (1 - (ε : ℝ)) := by
  have h := N.solveApproxFEFx_fair (accuracyParameter ε) (accuracyParameter_ge_two ε hε₀ hε₁)
  apply h.mono
  have hacc : 2 / (accuracyParameter ε : ℝ) ≤ (ε : ℝ) := by
    have hc : ((2 / (accuracyParameter ε : ℚ) : ℚ) : ℝ) ≤ (ε : ℝ) :=
      Rat.cast_le.mpr (accuracyParameter_accuracy ε hε₀)
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hc
  linarith

theorem runFPTAS_queries_le (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (L : ℕ)
    (hbits : ∀ a, N.value a Finset.univ + 1 ≤ 2 ^ L) :
    (N.runFPTAS ε hε₀ hε₁).queries ≤
      (5 * Fintype.card Agent * L * accuracyParameter ε + 1) *
        ((Fintype.card Agent + 1) * (1 + (Fintype.card Good + 1) ^ 2)) :=
  N.runApprox_queries_le _ (accuracyParameter_ge_two ε hε₀ hε₁) L hbits

/-- Each queried knapsack table has polynomial size in `m` and the accuracy parameter. -/
theorem fptas_knapsack_cells (ε : ℚ) (a : Agent) (T : Finset Good) :
    let E := Knapsack.eligible (N.size a) T (N.budget a)
    Knapsack.cells E.card
      (Knapsack.total (Knapsack.scaledProfit (N.val a) E (accuracyParameter ε)) E) ≤
      (Fintype.card Good + 1) * (Fintype.card Good ^ 2 * accuracyParameter ε + 1) := by
  apply (N.approxKnapsack_cells (accuracyParameter ε) a T).trans
  apply Nat.mul_le_mul (Nat.add_le_add_right (Finset.card_le_univ T) 1)
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Finset.card_le_univ T) 2)

end NaturalInstance

end GeneralizedAssignment
