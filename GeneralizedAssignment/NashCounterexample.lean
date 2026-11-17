import GeneralizedAssignment.Fractional
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedSectionVars false

/-!
# Appendix D: maximum Nash welfare need not be FEF

The exact two-agent, two-good instance in the paper. Claim 16 is proved
algebraically by completing a square, so no differentiation is needed.
-/

noncomputable section

namespace GeneralizedAssignment.NashCounterexample

open scoped BigOperators

def data : Instance (Fin 2) (Fin 2) where
  val := fun _ g => if g = 0 then 1 else 1 / 2
  size := fun a g => if a = 0 then 1 else if g = 0 then 1 else 8
  budget := fun _ => 1
  val_nonneg := by intro a g; split_ifs <;> norm_num
  size_nonneg := by intro a g; split_ifs <;> norm_num
  budget_nonneg := by intro a; norm_num

def optimum : FractionalAllocation (Fin 2) (Fin 2) :=
  ![![1 / 30, 29 / 30], ![29 / 30, 1 / 240]]

def nashProduct (x : FractionalAllocation (Fin 2) (Fin 2)) : ℝ :=
  data.fvalue 0 (x 0) * data.fvalue 1 (x 1)

def nashWelfare (x : FractionalAllocation (Fin 2) (Fin 2)) : ℝ :=
  Real.sqrt (nashProduct x)

theorem optimum_valid : optimum.Valid data := by
  constructor
  · intro a g
    fin_cases a <;> fin_cases g <;> norm_num [optimum]
  constructor
  · intro g
    fin_cases g <;> norm_num [Fin.sum_univ_two, optimum]
  · intro a
    fin_cases a <;> norm_num [Instance.fweight, Fin.sum_univ_two, data, optimum]

theorem optimum_product : nashProduct optimum = 961 / 1920 := by
  norm_num [nashProduct, Instance.fvalue, Fin.sum_univ_two, data, optimum]

/-- Claim 16, in product form. -/
theorem product_maximal (x : FractionalAllocation (Fin 2) (Fin 2))
    (hx : x.Valid data) : nashProduct x ≤ nashProduct optimum := by
  have h₁ := hx.2.2 0
  have h₂ := hx.2.2 1
  have h₃ := hx.2.1 0
  norm_num [Instance.fweight, Fin.sum_univ_two, data] at h₁ h₂ h₃
  have ha := hx.1 0 0
  have hb := hx.1 0 1
  have hc := hx.1 1 0
  have hd := hx.1 1 1
  have hU : x 0 0 + x 0 1 / 2 ≤ (1 + x 0 0) / 2 := by linarith
  have hV : x 1 0 + x 1 1 / 2 ≤ 1 - 15 * x 0 0 / 16 := by linarith
  have hVp : 0 ≤ x 1 0 + x 1 1 / 2 := by positivity
  have hUp : 0 ≤ (1 + x 0 0) / 2 := by positivity
  have hprod := (mul_le_mul_of_nonneg_right hU hVp).trans
    (mul_le_mul_of_nonneg_left hV hUp)
  have hsq := sq_nonneg (x 0 0 - 1 / 30)
  rw [optimum_product]
  norm_num [nashProduct, Instance.fvalue, Fin.sum_univ_two, data]
  nlinarith

/-- Claim 16 for the geometric-mean definition of Nash welfare. -/
theorem welfare_maximal (x : FractionalAllocation (Fin 2) (Fin 2))
    (hx : x.Valid data) : nashWelfare x ≤ nashWelfare optimum :=
  Real.sqrt_le_sqrt (product_maximal x hx)

/-- Claim 17: the second agent's whole bundle is a feasible, better bundle for agent 0. -/
theorem optimum_not_fef : ¬ optimum.FEF data := by
  intro h
  have hnonneg : ∀ g, 0 ≤ optimum 1 g := optimum_valid.1 1
  have hfeas : data.fweight 0 (optimum 1) ≤ data.budget 0 := by
    norm_num [Instance.fweight, Fin.sum_univ_two, data, optimum]
  have henvy := h.2.1 0 1 (optimum 1) hnonneg (fun _ => le_rfl) hfeas
  norm_num [Instance.fvalue, Fin.sum_univ_two, data, optimum] at henvy

/-- The non-implication asserted in Appendix D. -/
theorem exists_nash_maximizer_not_fef :
    ∃ x : FractionalAllocation (Fin 2) (Fin 2), x.Valid data ∧
      (∀ y, y.Valid data → nashWelfare y ≤ nashWelfare x) ∧ ¬ x.FEF data :=
  ⟨optimum, optimum_valid, welfare_maximal, optimum_not_fef⟩

end GeneralizedAssignment.NashCounterexample
