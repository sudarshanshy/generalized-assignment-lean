import GeneralizedAssignment.FamilyComplexity
import Mathlib.Combinatorics.Matroid.Basic

set_option linter.unusedSectionVars false

/-!
# Remark 1: matroid constraints

Instantiate the feasibility-family results with each agent's matroid
independent sets. The exact and approximate iteration bounds and the
polynomial oracle-query bound are checked. As in the paper, the standard
polynomial-time weighted-matroid optimization algorithm is an external
ingredient, represented by the exact oracle interface.
-/

open scoped BigOperators

namespace GeneralizedAssignment.MatroidConstraints

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]

def family (M : Agent → Matroid Good) : FeasibleFamily Agent Good where
  feasible a S := (M a).Indep (S : Set Good)
  empty a := by simp
  downward a _ _ h hST := h.subset (Finset.coe_subset.mpr hST)

theorem exists_strongFEFx (M : Agent → Matroid Good) (I : Instance Agent Good) :
    ∃ A : Allocation Agent Good, (family M).StrongFEFx I 1 A :=
  (family M).exists_strongFEFx I

theorem exact_iterations_le (M : Agent → Matroid Good) (I : Instance Agent Good)
    (hint : Allocation.IntegralValues I) (K : (family M).Oracle I) :
    (((family M).algorithm I K 1 (by norm_num) le_rfl).iterations : ℝ) ≤
      ∑ a, I.value a Finset.univ :=
  (family M).algorithm_iterations_le I hint K 1 (by norm_num) le_rfl

theorem approximate_queries_le (M : Agent → Matroid Good) (I : Instance Agent Good)
    (hint : Allocation.IntegralValues I) (K : (family M).Oracle I)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (L : ℕ)
    (hbits : ∀ a, I.value a Finset.univ + 1 ≤ (2 : ℝ) ^ L) :
    (((family M).approximateAlgorithm I K ε hε₀.le hε₁).queries : ℝ) ≤
      (5 * Fintype.card Agent * L / ε + 1) * (family M).callsPerIteration :=
  (family M).approximateAlgorithm_queries_le I hint K hε₀ hε₁ L hbits

end GeneralizedAssignment.MatroidConstraints
