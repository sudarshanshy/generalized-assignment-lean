import GeneralizedAssignment.Knapsack
import GeneralizedAssignment.Algorithms

set_option linter.unusedSectionVars false

/-!
# Integer inputs and the exact knapsack oracle

An executable input model and a bridge to the real-valued theorems.
The oracle is implemented by the verified capacity-indexed dynamic program.
-/

open scoped BigOperators

namespace GeneralizedAssignment

structure NaturalInstance (Agent Good : Type*) where
  val : Agent → Good → ℕ
  size : Agent → Good → ℕ
  budget : Agent → ℕ

namespace NaturalInstance

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (N : NaturalInstance Agent Good)

def toReal : Instance Agent Good where
  val a g := N.val a g
  size a g := N.size a g
  budget a := N.budget a
  val_nonneg := by intros; positivity
  size_nonneg := by intros; positivity
  budget_nonneg := by intros; positivity

def value (a : Agent) (S : Finset Good) : ℕ := Knapsack.total (N.val a) S
def weight (a : Agent) (S : Finset Good) : ℕ := Knapsack.total (N.size a) S
def welfare (A : Allocation Agent Good) : ℕ := ∑ a, N.value a (A a)
def totalValue : ℕ := ∑ a, N.value a Finset.univ

@[simp] theorem real_value (a : Agent) (S : Finset Good) :
    N.toReal.value a S = (N.value a S : ℝ) := by
  simp [Instance.value, value, Knapsack.total, toReal]

@[simp] theorem real_weight (a : Agent) (S : Finset Good) :
    N.toReal.weight a S = (N.weight a S : ℝ) := by
  simp [Instance.weight, weight, Knapsack.total, toReal]

@[simp] theorem real_feasible (a : Agent) (S : Finset Good) :
    N.toReal.Feasible a S ↔ N.weight a S ≤ N.budget a := by
  unfold Instance.Feasible
  rw [N.real_weight]
  simp [toReal]

@[simp] theorem real_welfare (A : Allocation Agent Good) :
    A.welfare N.toReal = (N.welfare A : ℝ) := by
  simp [Allocation.welfare, welfare]

theorem integral : Allocation.IntegralValues N.toReal := fun a g => ⟨N.val a g, rfl⟩

theorem welfare_le_total (A : Allocation Agent Good) : N.welfare A ≤ N.totalValue := by
  apply Finset.sum_le_sum
  intro a _
  exact Knapsack.total_mono _ (Finset.subset_univ _)

def knapsack (a : Agent) (S : Finset Good) : Finset Good :=
  Knapsack.solve (N.size a) (N.val a) S (N.budget a)

theorem knapsack_correct (a : Agent) (S : Finset Good) :
    Knapsack.Correct (N.size a) (N.val a) S (N.budget a) (N.knapsack a S) :=
  Knapsack.solve_correct _ _ _ _

/-- A concrete zero-error oracle, backed by the verified dynamic program. -/
def exactOracle : KnapsackOracle N.toReal 0 where
  choose := N.knapsack
  subset a S := (N.knapsack_correct a S).1
  feasible a S := (N.real_feasible a _).mpr (N.knapsack_correct a S).2.1
  guarantee a T S hST hF := by
    have h := (N.knapsack_correct a T).2.2 S hST ((N.real_feasible a S).mp hF)
    simp only [sub_zero, one_mul, real_value]
    exact_mod_cast h

/-- The executable test for an agent's envy (Section 4.1). -/
def Envies (A : Allocation Agent Good) (a : Agent) (T : Finset Good) : Prop :=
  N.value a (A a) < N.value a (N.knapsack a T)

instance (A : Allocation Agent Good) (a : Agent) (T : Finset Good) :
    Decidable (N.Envies A a T) := inferInstanceAs (Decidable (_ < _))

theorem envies_iff (A : Allocation Agent Good) (a : Agent) (T : Finset Good) :
    N.Envies A a T ↔ A.Envies N.toReal a T := by
  constructor
  · intro h
    refine ⟨N.knapsack a T, (N.knapsack_correct a T).1,
      N.exactOracle.feasible a T, ?_⟩
    simpa [Envies] using h
  · rintro ⟨S, hST, hF, hV⟩
    have hmax := (N.knapsack_correct a T).2.2 S hST ((N.real_feasible a S).mp hF)
    have hlt : N.value a (A a) < N.value a S := by simpa using hV
    exact hlt.trans_le hmax

def envyingAgents (A : Allocation Agent Good) (T : Finset Good) : Finset Agent :=
  Finset.univ.filter fun a => N.Envies A a T

theorem envyingAgents_nonempty_iff (A : Allocation Agent Good) (T : Finset Good) :
    (N.envyingAgents A T).Nonempty ↔ A.Envied N.toReal T := by
  simp [envyingAgents, Finset.nonempty_iff_ne_empty, Finset.filter_eq_empty_iff,
    Allocation.Envied, ← N.envies_iff]

def chooseEnvier (A : Allocation Agent Good) (T : Finset Good)
    (h : (N.envyingAgents A T).Nonempty) : Agent := (N.envyingAgents A T).min' h

theorem chooseEnvier_envies (A : Allocation Agent Good) (T : Finset Good)
    (h : (N.envyingAgents A T).Nonempty) : N.Envies A (N.chooseEnvier A T h) T := by
  exact (Finset.mem_filter.mp ((N.envyingAgents A T).min'_mem h)).2

end NaturalInstance

end GeneralizedAssignment
