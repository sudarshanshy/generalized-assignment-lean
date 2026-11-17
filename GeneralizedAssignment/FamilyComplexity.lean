import GeneralizedAssignment.FeasibleFamilies
import GeneralizedAssignment.ApproximateComplexity

set_option linter.unusedSectionVars false

/-!
# Approximation bounds for feasibility families

With an exact feasible-subset oracle, test envy at factor `1-ε` directly.
The resulting allocation is `(1-ε)`-FEFx, and the same logarithmic
potential gives polynomially many oracle calls. This is the modification
of Algorithm 4 used in the matroid remark.
-/

open scoped BigOperators

namespace GeneralizedAssignment.FeasibleFamily

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (F : FeasibleFamily Agent Good) (I : Instance Agent Good)

theorem Step.log_increase (hint : Allocation.IntegralValues I) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {A B : Allocation Agent Good}
    (h : F.Step I (1 - ε) A B) :
    Allocation.logPotential I A + ε / 5 ≤ Allocation.logPotential I B := by
  obtain ⟨k, T, _, hT, rfl⟩ := h
  have hg : I.value k (A k) < (1 - ε / 2) * I.value k T := by
    have hp := mul_nonneg hε₀ (I.value_nonneg k T)
    nlinarith only [hT.2.1, hp]
  exact Allocation.log_increase_replace I hint hε₀ hε₁ hg

theorem run_log_bound (hint : Allocation.IntegralValues I) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {A B : Allocation Agent Good} {t : ℕ}
    (h : Run (F.Step I (1 - ε)) A B t) :
    Allocation.logPotential I A + t * (ε / 5) ≤ Allocation.logPotential I B := by
  induction h with
  | refl => simp
  | cons hs _ ih =>
    have hp := hs.log_increase F I hint hε₀ hε₁
    push_cast
    nlinarith

noncomputable def approximateAlgorithm (K : F.Oracle I) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) : F.Result I (1 - ε) Allocation.empty :=
  F.algorithm I K (1 - ε) (sub_nonneg.mpr hε₁) (by linarith)

theorem approximateAlgorithm_iterations_log (hint : Allocation.IntegralValues I)
    (K : F.Oracle I) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    ((F.approximateAlgorithm I K ε hε₀.le hε₁).iterations : ℝ) ≤
      5 * (∑ a, Real.log (I.value a Finset.univ + 1)) / ε := by
  have h := F.run_log_bound I hint hε₀.le hε₁
    (F.approximateAlgorithm I K ε hε₀.le hε₁).trace
  simp only [Allocation.logPotential_empty, zero_add] at h
  have hu := Allocation.logPotential_le I (F.approximateAlgorithm I K ε hε₀.le hε₁).allocation
  apply (le_div_iff₀ hε₀).mpr
  nlinarith

theorem approximateAlgorithm_iterations_bits (hint : Allocation.IntegralValues I)
    (K : F.Oracle I) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (L : ℕ)
    (hbits : ∀ a, I.value a Finset.univ + 1 ≤ (2 : ℝ) ^ L) :
    ((F.approximateAlgorithm I K ε hε₀.le hε₁).iterations : ℝ) ≤
      5 * Fintype.card Agent * L / ε := by
  have hlog : ∀ a, Real.log (I.value a Finset.univ + 1) ≤ L := by
    intro a
    have hp : 0 < I.value a Finset.univ + 1 := by
      have := I.value_nonneg a Finset.univ
      linarith
    have h := Real.log_le_log hp (hbits a)
    rw [Real.log_pow] at h
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    nlinarith
  have hsum : (∑ a, Real.log (I.value a Finset.univ + 1)) ≤ Fintype.card Agent * (L : ℝ) := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun a _ => hlog a)
  apply (F.approximateAlgorithm_iterations_log I hint K hε₀ hε₁).trans
  apply (div_le_div_iff_of_pos_right hε₀).mpr
  nlinarith

/-- The polynomial oracle-query bound used for the matroid FPTAS. -/
theorem approximateAlgorithm_queries_le (hint : Allocation.IntegralValues I)
    (K : F.Oracle I) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (L : ℕ)
    (hbits : ∀ a, I.value a Finset.univ + 1 ≤ (2 : ℝ) ^ L) :
    ((F.approximateAlgorithm I K ε hε₀.le hε₁).queries : ℝ) ≤
      (5 * Fintype.card Agent * L / ε + 1) * F.callsPerIteration := by
  let R := F.approximateAlgorithm I K ε hε₀.le hε₁
  have ht : (R.iterations : ℝ) ≤ 5 * Fintype.card Agent * L / ε :=
    F.approximateAlgorithm_iterations_bits I hint K hε₀ hε₁ L hbits
  have hq : (R.queries : ℝ) ≤ ((R.iterations : ℝ) + 1) * (F.callsPerIteration : ℝ) := by
    exact_mod_cast R.query_bound
  exact hq.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

end GeneralizedAssignment.FeasibleFamily
