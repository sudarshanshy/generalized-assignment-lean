import GeneralizedAssignment.FPTAS
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option linter.unusedSectionVars false

/-!
# Rational inputs and exact denominator clearing

The paper assumes integral values and sizes without loss of generality.
This module implements that normalization, with separate positive scales
for each agent's values and constraints. Feasibility and every approximate
FEFx inequality are invariant, so the executable algorithms also accept
nonnegative rational inputs.
-/

open scoped BigOperators

namespace GeneralizedAssignment

structure RationalInstance (Agent Good : Type*) where
  val : Agent → Good → ℚ
  size : Agent → Good → ℚ
  budget : Agent → ℚ
  val_nonneg : ∀ a g, 0 ≤ val a g
  size_nonneg : ∀ a g, 0 ≤ size a g
  budget_nonneg : ∀ a, 0 ≤ budget a

namespace RationalInstance

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (R : RationalInstance Agent Good)

def toReal : Instance Agent Good where
  val a g := R.val a g
  size a g := R.size a g
  budget a := R.budget a
  val_nonneg a g := Rat.cast_nonneg.mpr (R.val_nonneg a g)
  size_nonneg a g := Rat.cast_nonneg.mpr (R.size_nonneg a g)
  budget_nonneg a := Rat.cast_nonneg.mpr (R.budget_nonneg a)

def clear (q : ℚ) (D : ℕ) : ℕ := q.num.toNat * (D / q.den)

theorem clear_eq (q : ℚ) (hq : 0 ≤ q) (D : ℕ) (hD : q.den ∣ D) :
    (clear q D : ℚ) = (D : ℚ) * q := by
  have hn : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)]
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hnum : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hd).mp q.num_div_den
  have hcancel : (q.den : ℚ) * (D / q.den : ℕ) = (D : ℚ) := by
    exact_mod_cast Nat.mul_div_cancel' hD
  rw [clear, Nat.cast_mul, hn, hnum]
  calc
    q * (q.den : ℚ) * (D / q.den : ℕ) = q * ((q.den : ℚ) * (D / q.den : ℕ)) := by ring
    _ = (D : ℚ) * q := by rw [hcancel]; ring

theorem clear_eq_real (q : ℚ) (hq : 0 ≤ q) (D : ℕ) (hD : q.den ∣ D) :
    (clear q D : ℝ) = (D : ℝ) * (q : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (clear_eq q hq D hD)
  simpa only [Rat.cast_natCast, Rat.cast_mul] using h

def valueScale (a : Agent) : ℕ := ∏ g, (R.val a g).den
def sizeScale (a : Agent) : ℕ := (R.budget a).den * ∏ g, (R.size a g).den

theorem valueScale_pos (a : Agent) : 0 < R.valueScale a :=
  Finset.prod_pos fun g _ => (R.val a g).den_pos

theorem sizeScale_pos (a : Agent) : 0 < R.sizeScale a :=
  Nat.mul_pos (R.budget a).den_pos (Finset.prod_pos fun g _ => (R.size a g).den_pos)

theorem val_den_dvd (a : Agent) (g : Good) : (R.val a g).den ∣ R.valueScale a :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ g)

theorem size_den_dvd (a : Agent) (g : Good) : (R.size a g).den ∣ R.sizeScale a :=
  (Finset.dvd_prod_of_mem (fun g => (R.size a g).den) (Finset.mem_univ g)).trans (dvd_mul_left _ _)

theorem budget_den_dvd (a : Agent) : (R.budget a).den ∣ R.sizeScale a := dvd_mul_right _ _

def normalize : NaturalInstance Agent Good where
  val a g := clear (R.val a g) (R.valueScale a)
  size a g := clear (R.size a g) (R.sizeScale a)
  budget a := clear (R.budget a) (R.sizeScale a)

theorem normalize_val (a : Agent) (g : Good) :
    R.normalize.toReal.val a g = (R.valueScale a : ℝ) * R.toReal.val a g :=
  clear_eq_real _ (R.val_nonneg a g) _ (R.val_den_dvd a g)

theorem normalize_size (a : Agent) (g : Good) :
    R.normalize.toReal.size a g = (R.sizeScale a : ℝ) * R.toReal.size a g :=
  clear_eq_real _ (R.size_nonneg a g) _ (R.size_den_dvd a g)

theorem normalize_budget (a : Agent) :
    R.normalize.toReal.budget a = (R.sizeScale a : ℝ) * R.toReal.budget a :=
  clear_eq_real _ (R.budget_nonneg a) _ (R.budget_den_dvd a)

theorem normalize_value (a : Agent) (S : Finset Good) :
    R.normalize.toReal.value a S = (R.valueScale a : ℝ) * R.toReal.value a S := by
  simp only [Instance.value, R.normalize_val, Finset.mul_sum]

theorem normalize_weight (a : Agent) (S : Finset Good) :
    R.normalize.toReal.weight a S = (R.sizeScale a : ℝ) * R.toReal.weight a S := by
  simp only [Instance.weight, R.normalize_size, Finset.mul_sum]

theorem normalize_feasible (a : Agent) (S : Finset Good) :
    R.normalize.toReal.Feasible a S ↔ R.toReal.Feasible a S := by
  unfold Instance.Feasible
  rw [R.normalize_weight, R.normalize_budget]
  apply mul_le_mul_iff_right₀
  exact_mod_cast R.sizeScale_pos a

theorem normalize_valid (A : Allocation Agent Good) :
    A.Valid R.normalize.toReal ↔ A.Valid R.toReal := by
  simp only [Allocation.Valid, R.normalize_feasible]

theorem normalize_comparison (q : ℝ) (a : Agent) (S T : Finset Good) :
    q * R.normalize.toReal.value a S ≤ R.normalize.toReal.value a T ↔
      q * R.toReal.value a S ≤ R.toReal.value a T := by
  rw [R.normalize_value, R.normalize_value, mul_left_comm]
  apply mul_le_mul_iff_right₀
  exact_mod_cast R.valueScale_pos a

theorem normalize_approxFEFx (q : ℝ) (A : Allocation Agent Good) :
    A.ApproxFEFx R.normalize.toReal q ↔ A.ApproxFEFx R.toReal q := by
  simp only [Allocation.ApproxFEFx, Allocation.ApproxAgentsFEFx,
    R.normalize_valid, R.normalize_feasible, R.normalize_comparison]

theorem normalize_fefx (A : Allocation Agent Good) :
    A.FEFx R.normalize.toReal ↔ A.FEFx R.toReal := by
  simpa only [Allocation.approxFEFx_one] using R.normalize_approxFEFx 1 A

def solveFEFx : Allocation Agent Good := R.normalize.solveFEFx

theorem solveFEFx_fair : R.solveFEFx.FEFx R.toReal :=
  (R.normalize_fefx _).mp R.normalize.solveFEFx_fair

def solveFPTAS (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) : Allocation Agent Good :=
  R.normalize.solveFPTAS ε hε₀ hε₁

/-- Theorem 4's executable correctness guarantee on the paper's rational input model. -/
theorem solveFPTAS_fair (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    (R.solveFPTAS ε hε₀ hε₁).ApproxFEFx R.toReal (1 - (ε : ℝ)) :=
  (R.normalize_approxFEFx _ _).mp (R.normalize.solveFPTAS_fair ε hε₀ hε₁)

end RationalInstance

end GeneralizedAssignment
