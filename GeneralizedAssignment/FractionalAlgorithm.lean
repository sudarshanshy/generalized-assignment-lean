import GeneralizedAssignment.Divisible
import GeneralizedAssignment.Algorithms

set_option linter.unusedSectionVars false

/-!
# Algorithm 1: threshold progress and LP-query bounds

The LPs are explicit predicates, not axioms. This module gives a checked
threshold trace ending at a feasible tight LP, together with the `n*m`
iteration bound. Testing LP1 and scanning at most `n` LP2 candidates per
iteration gives a polynomial number of feasibility queries. The actual
polynomial-time linear-program solver is an external algorithmic ingredient.
-/

open scoped BigOperators

namespace GeneralizedAssignment.Ranking

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good] {m : ℕ}
variable (π : Ranking Agent Good m) (I : Instance Agent Good)

def thresholdPotential (τ : Agent → ℕ) : ℕ := ∑ a, τ a

theorem thresholdPotential_update (τ : Agent → ℕ) (k : Agent) :
    thresholdPotential (Function.update τ k (τ k + 1)) = thresholdPotential τ + 1 := by
  have heq : Function.update τ k (τ k + 1) = fun a => τ a + if a = k then 1 else 0 := by
    funext a
    by_cases ha : a = k <;> simp [ha]
  rw [heq]
  simp [thresholdPotential, Finset.sum_add_distrib]

def ThresholdStep (τ σ : Agent → ℕ) : Prop :=
  (∃ k, σ = Function.update τ k (τ k + 1)) ∧ ∃ x, π.LP2 I σ x

theorem ThresholdStep.potential {τ σ : Agent → ℕ} (h : π.ThresholdStep I τ σ) :
    thresholdPotential σ = thresholdPotential τ + 1 := by
  obtain ⟨⟨k, rfl⟩, _⟩ := h
  exact thresholdPotential_update τ k

theorem thresholdRun_potential {τ σ : Agent → ℕ} {t : ℕ}
    (h : Run (π.ThresholdStep I) τ σ t) :
    thresholdPotential σ = thresholdPotential τ + t := by
  induction h with
  | refl => simp
  | cons hs _ ih =>
    have hp := hs.potential π I
    omega

theorem thresholdPotential_le {τ : Agent → ℕ} (hτ : ∀ a, τ a < m) :
    thresholdPotential τ ≤ Fintype.card Agent * (m - 1) := by
  have hsum : (∑ a, τ a) ≤ ∑ _a : Agent, (m - 1) := by
    apply Finset.sum_le_sum
    intro a _
    have := hτ a
    omega
  simpa [thresholdPotential] using hsum

structure ThresholdResult (τ : Agent → ℕ) where
  thresholds : Agent → ℕ
  allocation : FractionalAllocation Agent Good
  iterations : ℕ
  trace : Run (π.ThresholdStep I) τ thresholds iterations
  tight : π.LP1 I thresholds allocation

theorem ThresholdResult.iterations_le (d : Good)
    (hblocked : ∀ x : FractionalAllocation Agent Good, x.Valid I → (∑ a, x a d) ≠ 1)
    {τ : Agent → ℕ} (R : π.ThresholdResult I τ) :
    thresholdPotential τ + R.iterations ≤ Fintype.card Agent * (m - 1) := by
  rw [← thresholdRun_potential π I R.trace]
  exact thresholdPotential_le (π.lp2_threshold_lt I d hblocked R.tight.toLP2)

/-- A classical specification of Algorithm 1. The only uncomputed operations
are feasibility tests and witness choices for the explicitly defined LPs. -/
noncomputable def solveThresholds (d : Good)
    (hblocked : ∀ x : FractionalAllocation Agent Good, x.Valid I → (∑ a, x a d) ≠ 1)
    (τ : Agent → ℕ) (hfeas : ∃ x, π.LP2 I τ x) : π.ThresholdResult I τ := by
  classical
  by_cases hdone : ∃ x, π.LP1 I τ x
  · exact ⟨τ, Classical.choose hdone, 0, Run.refl τ, Classical.choose_spec hdone⟩
  · have hτ : ∀ a, τ a < m := π.lp2_threshold_lt I d hblocked (Classical.choose_spec hfeas)
    let hnext := lp_incongruity π I τ hτ hfeas hdone
    let k := Classical.choose hnext
    have hk : ∃ x, π.LP2 I (Function.update τ k (τ k + 1)) x := Classical.choose_spec hnext
    let σ := Function.update τ k (τ k + 1)
    let R := solveThresholds d hblocked σ hk
    exact ⟨R.thresholds, R.allocation, R.iterations + 1,
      Run.cons ⟨⟨k, rfl⟩, hk⟩ R.trace, R.tight⟩
termination_by Fintype.card Agent * (m - 1) - thresholdPotential τ
decreasing_by
  classical
  change Fintype.card Agent * (m - 1) - thresholdPotential σ <
    Fintype.card Agent * (m - 1) - thresholdPotential τ
  have hσ : ∀ a, σ a < m := π.lp2_threshold_lt I d hblocked (Classical.choose_spec hk)
  have hb := thresholdPotential_le hσ
  have hp : thresholdPotential σ = thresholdPotential τ + 1 := thresholdPotential_update τ k
  omega

noncomputable def fractionalAlgorithm (d : Good)
    (hblocked : ∀ x : FractionalAllocation Agent Good, x.Valid I → (∑ a, x a d) ≠ 1) :
    π.ThresholdResult I (fun _ => 0) :=
  π.solveThresholds I d hblocked (fun _ => 0) ⟨fun _ _ => 0, lp2_initial I π⟩

theorem fractionalAlgorithm_iterations_le (d : Good)
    (hblocked : ∀ x : FractionalAllocation Agent Good, x.Valid I → (∑ a, x a d) ≠ 1) :
    (π.fractionalAlgorithm I d hblocked).iterations ≤ Fintype.card Agent * (m - 1) := by
  have h := (π.fractionalAlgorithm I d hblocked).iterations_le π I d hblocked
  simpa [thresholdPotential] using h

/-- One LP1 test per state and at most `n` candidate LP2 tests per update. -/
def lpQueryBound (iterations : ℕ) : ℕ := 1 + (Fintype.card Agent + 1) * iterations

theorem fractionalAlgorithm_queries_le (d : Good)
    (hblocked : ∀ x : FractionalAllocation Agent Good, x.Valid I → (∑ a, x a d) ≠ 1) :
    lpQueryBound (Agent := Agent) (π.fractionalAlgorithm I d hblocked).iterations ≤
      1 + (Fintype.card Agent + 1) * (Fintype.card Agent * (m - 1)) := by
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (π.fractionalAlgorithm_iterations_le I d hblocked)) 1

/-- The returned LP certificate implies FEF, as in Theorem 1. -/
theorem fractionalAlgorithm_fef (d : Good)
    (hblocked : ∀ x : FractionalAllocation Agent Good, x.Valid I → (∑ a, x a d) ≠ 1)
    (hsize : ∀ a g, 0 < I.size a g) (hsorted : π.Sorted I) :
    (π.fractionalAlgorithm I d hblocked).allocation.FEF I :=
  (π.fractionalAlgorithm I d hblocked).tight.fef hsize hsorted

end GeneralizedAssignment.Ranking
