import GeneralizedAssignment.RationalInputs
import Mathlib.Data.Fin.VecNotation

/-! Small executable examples, including zero sizes, zero budgets, and empty types. -/

namespace GeneralizedAssignment.Examples

def heterogeneous : NaturalInstance (Fin 2) (Fin 3) where
  val := ![![5, 2, 4], ![1, 6, 2]]
  size := ![![2, 1, 2], ![1, 2, 3]]
  budget := ![3, 3]

def zeros : NaturalInstance (Fin 2) (Fin 3) where
  val := ![![0, 4, 2], ![3, 0, 6]]
  size := ![![0, 0, 4], ![1, 0, 0]]
  budget := ![0, 1]

def noGoods : NaturalInstance (Fin 2) (Fin 0) where
  val _ g := Fin.elim0 g
  size _ g := Fin.elim0 g
  budget := ![0, 7]

def noAgents : NaturalInstance (Fin 0) (Fin 2) where
  val a := Fin.elim0 a
  size a := Fin.elim0 a
  budget a := Fin.elim0 a

def rational : RationalInstance (Fin 2) (Fin 3) where
  val := ![![1 / 2, 2 / 3, 0], ![1 / 3, 0, 5 / 4]]
  size := ![![1 / 2, 1 / 3, 1], ![1 / 4, 1, 1 / 2]]
  budget := ![3 / 2, 1]
  val_nonneg := by intro a g; fin_cases a <;> fin_cases g <;> norm_num
  size_nonneg := by intro a g; fin_cases a <;> fin_cases g <;> norm_num
  budget_nonneg := by intro a; fin_cases a <;> norm_num

theorem heterogeneous_exact_fair : heterogeneous.solveFEFx.FEFx heterogeneous.toReal :=
  heterogeneous.solveFEFx_fair

theorem zero_sizes_exact_fair : zeros.solveFEFx.FEFx zeros.toReal := zeros.solveFEFx_fair

theorem rational_approximate_fair :
    (rational.solveFPTAS (1 / 4) (by norm_num) (by norm_num)).ApproxFEFx rational.toReal (3 / 4) := by
  have h := rational.solveFPTAS_fair (1 / 4) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

def bundles {n m : ℕ} (A : Allocation (Fin n) (Fin m)) : List (List ℕ) :=
  List.ofFn fun a : Fin n => ((A a).sort (· ≤ ·)).map Fin.val

end GeneralizedAssignment.Examples
