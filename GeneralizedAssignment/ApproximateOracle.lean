import GeneralizedAssignment.NaturalInstance
import GeneralizedAssignment.ScaledKnapsack

set_option linter.unusedSectionVars false

/-!
# A concrete approximation oracle for generalized assignment

The parameter `r ≥ 2` gives overall FEFx factor `1 - 2/r`.
The internal knapsack calls have factor `1 - 1/r`. Envy detection uses
integer arithmetic and is proved equivalent to the real-valued test
in Algorithm 4.
-/

namespace GeneralizedAssignment.NaturalInstance

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (N : NaturalInstance Agent Good)

def approxKnapsack (r : ℕ) (a : Agent) (T : Finset Good) : Finset Good :=
  Knapsack.scaledSolve (N.size a) (N.val a) T (N.budget a) r

def halfOracle (r : ℕ) (hr : 0 < r) : KnapsackOracle N.toReal ((2 / (r : ℝ)) / 2) where
  choose := N.approxKnapsack r
  subset a T := Knapsack.scaledSolve_subset _ _ _ _ _
  feasible a T := (N.real_feasible a _).mpr (Knapsack.scaledSolve_feasible _ _ _ _ _)
  guarantee a T S hST hF := by
    have h := Knapsack.scaledSolve_guarantee (N.size a) (N.val a) T (N.budget a) r hr
      S hST ((N.real_feasible a S).mp hF)
    have heq : (2 / (r : ℝ)) / 2 = 1 / (r : ℝ) := by ring
    simpa only [heq, real_value, value, approxKnapsack] using h

def ApproxDetect (r : ℕ) (A : Allocation Agent Good) (a : Agent) (T : Finset Good) : Prop :=
  r * N.value a (A a) < (r - 1) * N.value a (N.approxKnapsack r a T)

instance (r : ℕ) (A : Allocation Agent Good) (a : Agent) (T : Finset Good) :
    Decidable (N.ApproxDetect r A a T) := inferInstanceAs (Decidable (_ < _))

theorem approxDetect_iff (r : ℕ) (hr : 0 < r) (A : Allocation Agent Good)
    (a : Agent) (T : Finset Good) :
    N.ApproxDetect r A a T ↔ N.toReal.value a (A a) <
      (1 - (2 / (r : ℝ)) / 2) * N.toReal.value a ((N.halfOracle r hr).choose a T) := by
  have hr1 : 1 ≤ r := hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (r : ℝ) * ((1 - (2 / (r : ℝ)) / 2) *
      (N.value a (N.approxKnapsack r a T) : ℝ)) =
      ((r : ℝ) - 1) * (N.value a (N.approxKnapsack r a T) : ℝ) := by
    field_simp [ne_of_gt hrR]
  change r * N.value a (A a) < (r - 1) * N.value a (N.approxKnapsack r a T) ↔ _
  simp only [real_value, halfOracle]
  rw [← mul_lt_mul_iff_right₀ hrR, heq]
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr1, Nat.cast_one]
  rw [← hcast]
  exact_mod_cast (Iff.rfl : r * N.value a (A a) < (r - 1) *
    N.value a (N.approxKnapsack r a T) ↔ r * N.value a (A a) < (r - 1) *
    N.value a (N.approxKnapsack r a T))

def approxEnvyingAgents (r : ℕ) (A : Allocation Agent Good) (T : Finset Good) : Finset Agent :=
  Finset.univ.filter fun a => N.ApproxDetect r A a T

theorem approxEnvyingAgents_nonempty_iff (r : ℕ) (hr : 0 < r)
    (A : Allocation Agent Good) (T : Finset Good) :
    (N.approxEnvyingAgents r A T).Nonempty ↔
      A.OracleEnvied N.toReal (2 / (r : ℝ)) (N.halfOracle r hr) T := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (N.approxDetect_iff r hr A a T).mp (Finset.mem_filter.mp ha).2⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (N.approxDetect_iff r hr A a T).mpr ha⟩⟩

def chooseApproxEnvier (r : ℕ) (A : Allocation Agent Good) (T : Finset Good)
    (h : (N.approxEnvyingAgents r A T).Nonempty) : Agent :=
  (N.approxEnvyingAgents r A T).min' h

theorem chooseApproxEnvier_detects (r : ℕ) (A : Allocation Agent Good) (T : Finset Good)
    (h : (N.approxEnvyingAgents r A T).Nonempty) :
    N.ApproxDetect r A (N.chooseApproxEnvier r A T h) T := by
  exact (Finset.mem_filter.mp ((N.approxEnvyingAgents r A T).min'_mem h)).2

theorem approxKnapsack_cells (r : ℕ) (a : Agent) (T : Finset Good) :
    let E := Knapsack.eligible (N.size a) T (N.budget a)
    Knapsack.cells E.card (Knapsack.total (Knapsack.scaledProfit (N.val a) E r) E) ≤
      (T.card + 1) * (T.card ^ 2 * r + 1) :=
  Knapsack.scaledSolve_cells _ _ _ _ _

end GeneralizedAssignment.NaturalInstance
