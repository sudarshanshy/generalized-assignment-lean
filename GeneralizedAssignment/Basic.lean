import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

set_option linter.unusedSectionVars false

/-!
# Generalized assignment instances

The model of Section 2 of Barman–Khan–Shyam–Sreenivas,
*Guaranteeing Envy-Freeness under Generalized Assignment Constraints*
(arXiv:2305.01339v1).

Agent and good types are finite. Values, sizes, and budgets are nonnegative
reals; this includes the rational/integer instances in the paper. Strict
positivity of sizes is imposed separately wherever densities require it.
-/

open scoped BigOperators

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

/-- Agent-specific additive values and generalized assignment constraints. -/
structure Instance (Agent Good : Type*) where
  val : Agent → Good → ℝ
  size : Agent → Good → ℝ
  budget : Agent → ℝ
  val_nonneg : ∀ a g, 0 ≤ val a g
  size_nonneg : ∀ a g, 0 ≤ size a g
  budget_nonneg : ∀ a, 0 ≤ budget a

namespace Instance

variable (I : Instance Agent Good)

def value (a : Agent) (S : Finset Good) : ℝ := ∑ g ∈ S, I.val a g
def weight (a : Agent) (S : Finset Good) : ℝ := ∑ g ∈ S, I.size a g
def Feasible (a : Agent) (S : Finset Good) : Prop := I.weight a S ≤ I.budget a

@[simp] theorem value_empty (a : Agent) : I.value a ∅ = 0 := by simp [value]
@[simp] theorem weight_empty (a : Agent) : I.weight a ∅ = 0 := by simp [weight]
@[simp] theorem feasible_empty (a : Agent) : I.Feasible a ∅ := by
  simpa [Feasible] using I.budget_nonneg a

theorem value_nonneg (a : Agent) (S : Finset Good) : 0 ≤ I.value a S :=
  Finset.sum_nonneg fun g _ => I.val_nonneg a g

theorem weight_nonneg (a : Agent) (S : Finset Good) : 0 ≤ I.weight a S :=
  Finset.sum_nonneg fun g _ => I.size_nonneg a g

theorem value_mono (a : Agent) {S T : Finset Good} (h : S ⊆ T) :
    I.value a S ≤ I.value a T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun g _ _ => I.val_nonneg a g

theorem weight_mono (a : Agent) {S T : Finset Good} (h : S ⊆ T) :
    I.weight a S ≤ I.weight a T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun g _ _ => I.size_nonneg a g

theorem Feasible.subset {a : Agent} {S T : Finset Good}
    (hT : I.Feasible a T) (hST : S ⊆ T) : I.Feasible a S :=
  (I.weight_mono a hST).trans hT

@[simp] theorem value_singleton (a : Agent) (g : Good) :
    I.value a {g} = I.val a g := by simp [value]

@[simp] theorem weight_singleton (a : Agent) (g : Good) :
    I.weight a {g} = I.size a g := by simp [weight]

end Instance

/-- An allocation is a tuple of bundles. Feasibility/disjointness are explicit predicates. -/
abbrev Allocation (Agent Good : Type*) := Agent → Finset Good

namespace Allocation

variable (A : Allocation Agent Good) (I : Instance Agent Good)

def Valid : Prop :=
  (∀ a, I.Feasible a (A a)) ∧ ∀ a b, a ≠ b → Disjoint (A a) (A b)

/-- Goods unassigned to every agent, not an independently chosen bundle. -/
def charity : Finset Good := Finset.univ.filter fun g => ∀ a, g ∉ A a

@[simp] theorem mem_charity {g : Good} : g ∈ A.charity ↔ ∀ a, g ∉ A a := by
  classical
  simp [charity]

theorem disjoint_charity (a : Agent) : Disjoint (A.charity) (A a) := by
  rw [Finset.disjoint_left]
  intro g hg hga
  exact (A.mem_charity.mp hg) a hga

/-- Definition 2, restricted to comparisons between agents. -/
def AgentsFEFx : Prop :=
  ∀ a b S, S ⊂ A b → I.Feasible a S → I.value a S ≤ I.value a (A a)

/-- Full feasible envy-freeness towards charity. -/
def CharityFEF : Prop :=
  ∀ a S, S ⊆ A.charity → I.Feasible a S → I.value a S ≤ I.value a (A a)

/-- Definition 2, including feasibility and the actual unallocated goods. -/
def FEFx : Prop :=
  A.Valid I ∧ A.AgentsFEFx I ∧
    ∀ a S, S ⊂ A.charity → I.Feasible a S → I.value a S ≤ I.value a (A a)

/-- The stronger guarantee returned by Algorithm 2. -/
def StrongFEFx : Prop := A.Valid I ∧ A.AgentsFEFx I ∧ A.CharityFEF I

theorem StrongFEFx.fefx (h : A.StrongFEFx I) : A.FEFx I :=
  ⟨h.1, h.2.1, fun a S hS hF => h.2.2 a S hS.subset hF⟩

/-- Definition 7: envy is tested against feasible subsets of the target. -/
def Envies (a : Agent) (T : Finset Good) : Prop :=
  ∃ S ⊆ T, I.Feasible a S ∧ I.value a (A a) < I.value a S

def Envied (T : Finset Good) : Prop := ∃ a, A.Envies I a T

/-- Definition 7: minimal with respect to all agents, not just the selected one. -/
def MinimalEnvied (T : Finset Good) : Prop :=
  A.Envied I T ∧ ∀ S, S ⊂ T → ¬ A.Envied I S

theorem Envies.mono {a : Agent} {S T : Finset Good}
    (h : A.Envies I a S) (hST : S ⊆ T) : A.Envies I a T := by
  obtain ⟨U, hUS, hF, hV⟩ := h
  exact ⟨U, hUS.trans hST, hF, hV⟩

theorem not_envies_iff {a : Agent} {T : Finset Good} :
    ¬ A.Envies I a T ↔
      ∀ S ⊆ T, I.Feasible a S → I.value a S ≤ I.value a (A a) := by
  simp only [Envies, not_exists, not_and, not_lt]

theorem charityFEF_iff : A.CharityFEF I ↔ ¬ A.Envied I A.charity := by
  simp only [CharityFEF, Envied, not_exists, not_envies_iff]

def welfare : ℝ := ∑ a, I.value a (A a)

theorem welfare_nonneg : 0 ≤ A.welfare I :=
  Finset.sum_nonneg fun a _ => I.value_nonneg a (A a)

theorem welfare_le : A.welfare I ≤ ∑ a, I.value a Finset.univ := by
  exact Finset.sum_le_sum fun a _ => I.value_mono a (Finset.subset_univ _)

def empty : Allocation Agent Good := fun _ => ∅

@[simp] theorem empty_apply (a : Agent) : (empty : Allocation Agent Good) a = ∅ := rfl

theorem empty_valid : (empty : Allocation Agent Good).Valid I := by
  exact ⟨fun a => I.feasible_empty a, fun _ _ _ => Finset.disjoint_empty_left _⟩

theorem empty_agentsFEFx : (empty : Allocation Agent Good).AgentsFEFx I := by
  intro a b S hS _
  exact False.elim (Finset.not_ssubset_empty S hS)

@[simp] theorem empty_welfare : (empty : Allocation Agent Good).welfare I = 0 := by
  simp [welfare, empty]

end Allocation

end GeneralizedAssignment
