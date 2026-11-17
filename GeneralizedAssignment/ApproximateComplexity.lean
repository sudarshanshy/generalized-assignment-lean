import GeneralizedAssignment.Algorithms
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.unusedSectionVars false

/-!
# Polynomial iteration bounds for approximate FEFx

Theorem 4's multiplicative-progress analysis. We use the potential
`∑ a, log (v_a(A_a) + 1)`. The shift by one handles zero utilities and
zero-valued goods explicitly, avoiding a minimum-positive-value assumption.

For integral values and `0 < ε ≤ 1`, every update increases this potential
by at least `ε / 5`. Consequently at most `5 n L / ε` updates occur when
each agent's total value plus one is at most `2^L`.
-/

open scoped BigOperators

namespace GeneralizedAssignment.Allocation

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]
variable (I : Instance Agent Good)

noncomputable def logPotential (A : Allocation Agent Good) : ℝ :=
  ∑ a, Real.log (I.value a (A a) + 1)

@[simp] theorem logPotential_empty : logPotential I (empty : Allocation Agent Good) = 0 := by
  simp [logPotential]

theorem shifted_value_growth (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {a : Agent} {S T : Finset Good}
    (hgain : I.value a S < (1 - ε / 2) * I.value a T) :
    (1 + ε / 4) * (I.value a S + 1) ≤ I.value a T + 1 := by
  have hS := I.value_nonneg a S
  have hT := I.value_nonneg a T
  have hlt : I.value a S < I.value a T := by
    have := mul_nonneg hε₀ hT
    nlinarith
  have hpos : 0 < I.value a T := hS.trans_lt hlt
  have hT1 : 1 ≤ I.value a T := by
    have h := integral_value_gap I hint (S := ∅) (T := T) (by simpa using hpos)
    simpa using h
  by_cases hzero : I.value a S = 0
  · rw [hzero]
    nlinarith
  · have hSpos : 0 < I.value a S := lt_of_le_of_ne hS (Ne.symm hzero)
    have hS1 : 1 ≤ I.value a S := by
      have h := integral_value_gap I hint (S := ∅) (T := S) (by simpa using hSpos)
      simpa using h
    have h₁ := mul_nonneg hε₀ (sub_nonneg.mpr hlt.le)
    have h₂ := mul_nonneg hε₀ (sub_nonneg.mpr hS1)
    nlinarith

theorem log_growth_lower {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ε / 5 ≤ Real.log (1 + ε / 4) := by
  have hp : 0 < 1 + ε / 4 := by linarith
  have hd : 0 < 4 + ε := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have heq : 1 - (1 + ε / 4)⁻¹ = ε / (4 + ε) := by
    field_simp
    ring
  rw [heq] at hlog
  apply le_trans _ hlog
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hd).mpr
  nlinarith

theorem log_increase_replace (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {A : Allocation Agent Good} {k : Agent} {T : Finset Good}
    (hgain : I.value k (A k) < (1 - ε / 2) * I.value k T) :
    logPotential I A + ε / 5 ≤ logPotential I (A.replace k T) := by
  classical
  have hg := shifted_value_growth I hint hε₀ hε₁ hgain
  have hp : 0 < 1 + ε / 4 := by linarith
  have hu : 0 < I.value k (A k) + 1 := by have := I.value_nonneg k (A k); linarith
  have hlog := Real.log_le_log (mul_pos hp hu) hg
  rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hu)] at hlog
  have hlower := log_growth_lower hε₀ hε₁
  have hlocal : Real.log (I.value k (A k) + 1) + ε / 5 ≤ Real.log (I.value k T + 1) := by
    linarith
  have hsum : (∑ a, (Real.log (I.value a (A a) + 1) + if a = k then ε / 5 else 0)) ≤
      ∑ a, Real.log (I.value a (A.replace k T a) + 1) := by
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : a = k
    · subst a; simpa using hlocal
    · simp [ha]
  simpa [logPotential, Finset.sum_add_distrib] using hsum

theorem ApproxStep.log_increase (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {A B : Allocation Agent Good}
    (h : ApproxStep I ε A B) : logPotential I A + ε / 5 ≤ logPotential I B := by
  obtain ⟨k, T, _, hmin, rfl⟩ := h
  exact log_increase_replace I hint hε₀ hε₁ hmin.2.1

theorem approxRun_log_bound (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) {A B : Allocation Agent Good} {t : ℕ}
    (h : Run (ApproxStep I ε) A B t) :
    logPotential I A + t * (ε / 5) ≤ logPotential I B := by
  induction h with
  | refl => simp
  | cons hs _ ih =>
    have hstep := hs.log_increase I hint hε₀ hε₁
    push_cast
    nlinarith

theorem logPotential_le (A : Allocation Agent Good) :
    logPotential I A ≤ ∑ a, Real.log (I.value a Finset.univ + 1) := by
  apply Finset.sum_le_sum
  intro a _
  have hp : 0 < I.value a (A a) + 1 := by have := I.value_nonneg a (A a); linarith
  exact Real.log_le_log hp (by
    have := I.value_mono a (Finset.subset_univ (A a))
    linarith)

/-- The logarithmic bound applies to every execution trace, including executable implementations. -/
theorem approxRun_iterations_log (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) {B : Allocation Agent Good} {t : ℕ}
    (hRun : Run (ApproxStep I ε) empty B t) :
    (t : ℝ) ≤ 5 * (∑ a, Real.log (I.value a Finset.univ + 1)) / ε := by
  have h := approxRun_log_bound I hint hε₀.le hε₁ hRun
  simp only [logPotential_empty, zero_add] at h
  have hu := logPotential_le I B
  apply (le_div_iff₀ hε₀).mpr
  nlinarith

theorem approxRun_iterations_bits (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) {B : Allocation Agent Good} {t : ℕ}
    (hRun : Run (ApproxStep I ε) empty B t) (L : ℕ)
    (hbits : ∀ a, I.value a Finset.univ + 1 ≤ (2 : ℝ) ^ L) :
    (t : ℝ) ≤ 5 * Fintype.card Agent * L / ε := by
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
    have hmul := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    nlinarith
  have hsum : (∑ a, Real.log (I.value a Finset.univ + 1)) ≤ Fintype.card Agent * (L : ℝ) := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun a _ => hlog a)
  apply (approxRun_iterations_log I hint hε₀ hε₁ hRun).trans
  apply (div_le_div_iff_of_pos_right hε₀).mpr
  nlinarith

/-- A logarithmic bound, without requiring all goods to have positive value. -/
theorem approximateAlgorithm_iterations_log (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (K : KnapsackOracle I (ε / 2)) :
    ((approximateAlgorithm I ε hε₀.le hε₁ K).iterations : ℝ) ≤
      5 * (∑ a, Real.log (I.value a Finset.univ + 1)) / ε := by
  exact approxRun_iterations_log I hint hε₀ hε₁ (approximateAlgorithm I ε hε₀.le hε₁ K).trace

/-- The polynomial-in-bit-length iteration guarantee underlying Theorem 4. -/
theorem approximateAlgorithm_iterations_bits (hint : IntegralValues I) {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (K : KnapsackOracle I (ε / 2)) (L : ℕ)
    (hbits : ∀ a, I.value a Finset.univ + 1 ≤ (2 : ℝ) ^ L) :
    ((approximateAlgorithm I ε hε₀.le hε₁ K).iterations : ℝ) ≤
      5 * Fintype.card Agent * L / ε := by
  exact approxRun_iterations_bits I hint hε₀ hε₁
    (approximateAlgorithm I ε hε₀.le hε₁ K).trace L hbits

end GeneralizedAssignment.Allocation
