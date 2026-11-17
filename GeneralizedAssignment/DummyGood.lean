import GeneralizedAssignment.Fractional
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.BigOperators

set_option linter.unusedSectionVars false

/-!
# Adding and removing a fictional good

Proposition 1 and the capacity obstruction used in Lemma 6.
`none` denotes the fictional good and `some g` an original good.
We use size `1 + ∑ a, B_a`, which is strictly larger than the total
budget, instead of `2 n max_a B_a`. This harmless change also handles
zero budgets and an empty agent type.
-/

open scoped BigOperators

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

namespace Instance

variable (I : Instance Agent Good)

def dummySize : ℝ := 1 + ∑ a, I.budget a

theorem dummySize_pos : 0 < I.dummySize := by
  have hs : 0 ≤ ∑ a, I.budget a := Finset.sum_nonneg fun a _ => I.budget_nonneg a
  dsimp [dummySize]
  linarith

def withDummy : Instance Agent (Option Good) where
  val a := fun g => g.elim 0 (I.val a)
  size a := fun g => g.elim I.dummySize (I.size a)
  budget := I.budget
  val_nonneg := by intro a g; cases g <;> simp [I.val_nonneg]
  size_nonneg := by
    intro a g
    cases g with
    | none => exact I.dummySize_pos.le
    | some g => exact I.size_nonneg a g
  budget_nonneg := I.budget_nonneg

theorem withDummy_size_pos (h : ∀ a g, 0 < I.size a g) :
    ∀ a g, 0 < I.withDummy.size a g := by
  intro a g
  cases g with
  | none => exact I.dummySize_pos
  | some g => exact h a g

@[simp] theorem withDummy_fvalue (a : Agent) (y : Option Good → ℝ) :
    I.withDummy.fvalue a y = I.fvalue a (fun g => y (some g)) := by
  simp [fvalue, withDummy, Fintype.sum_option]

@[simp] theorem withDummy_fweight (a : Agent) (y : Option Good → ℝ) :
    I.withDummy.fweight a y = y none * I.dummySize + I.fweight a (fun g => y (some g)) := by
  simp [fweight, withDummy, Fintype.sum_option]

end Instance

namespace FractionalAllocation

variable (x : FractionalAllocation Agent (Option Good)) (I : Instance Agent Good)

def restrict : FractionalAllocation Agent Good := fun a g => x a (some g)

theorem Valid.restrict (hx : x.Valid I.withDummy) : x.restrict.Valid I := by
  refine ⟨fun a g => hx.1 a (some g), fun g => hx.2.1 (some g), ?_⟩
  intro a
  have h := hx.2.2 a
  rw [I.withDummy_fweight] at h
  have hz := mul_nonneg (hx.1 a none) I.dummySize_pos.le
  change I.fweight a (fun g => x a (some g)) ≤ I.budget a
  change x a none * I.dummySize + I.fweight a (fun g => x a (some g)) ≤ I.budget a at h
  linarith

/-- Proposition 1: discarding the zero-valued fictional good preserves FEF. -/
theorem FEF.restrict (hx : x.FEF I.withDummy) : x.restrict.FEF I := by
  refine ⟨hx.1.restrict x I, ?_, ?_⟩
  · intro a b y hy hsub hfeas
    let y' : Option Good → ℝ := fun g => g.elim 0 y
    have hy' : ∀ g, 0 ≤ y' g := by intro g; cases g <;> simp [y', hy]
    have hsub' : ∀ g, y' g ≤ x b g := by
      intro g
      cases g with
      | none => exact hx.1.1 b none
      | some g => exact hsub g
    have hfeas' : I.withDummy.fweight a y' ≤ I.withDummy.budget a := by
      change I.withDummy.fweight a y' ≤ I.budget a
      rw [I.withDummy_fweight]
      simpa [y'] using hfeas
    have h := hx.2.1 a b y' hy' hsub' hfeas'
    simp only [I.withDummy_fvalue] at h
    exact h
  · intro a y hy hsub hfeas
    let y' : Option Good → ℝ := fun g => g.elim 0 y
    have hy' : ∀ g, 0 ≤ y' g := by intro g; cases g <;> simp [y', hy]
    have hsub' : ∀ g, y' g ≤ x.charity g := by
      intro g
      cases g with
      | none => exact hx.1.charity_nonneg x I.withDummy none
      | some g => exact hsub g
    have hfeas' : I.withDummy.fweight a y' ≤ I.withDummy.budget a := by
      change I.withDummy.fweight a y' ≤ I.budget a
      rw [I.withDummy_fweight]
      simpa [y'] using hfeas
    have h := hx.2.2 a y' hy' hsub' hfeas'
    simp only [I.withDummy_fvalue] at h
    exact h

/-- Lemma 6's obstruction: no valid allocation can fully allocate the fictional good. -/
theorem dummy_not_full (hx : x.Valid I.withDummy) : (∑ a, x a none) ≠ 1 := by
  intro hfull
  have hbound : ∀ a, x a none * I.dummySize ≤ I.budget a := by
    intro a
    have h := hx.2.2 a
    rw [I.withDummy_fweight] at h
    have hz := I.fweight_nonneg a (fun g => hx.1 a (some g))
    change x a none * I.dummySize + I.fweight a (fun g => x a (some g)) ≤ I.budget a at h
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun a _ => hbound a
  rw [← Finset.sum_mul, hfull, one_mul] at hs
  dsimp [Instance.dummySize] at hs
  linarith

end FractionalAllocation

end GeneralizedAssignment
