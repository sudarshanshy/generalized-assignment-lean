import GeneralizedAssignment.Indivisible

set_option linter.unusedSectionVars false

/-!
# Approximate FEFx

Definitions 8–9 and the correctness arguments of Section 4.2.
The knapsack interface records the mathematical guarantee of an
approximation oracle; it does not assume any running-time bound.
-/

open scoped BigOperators

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

/-- A feasible knapsack approximation, expressed against every feasible competitor. -/
structure KnapsackOracle (I : Instance Agent Good) (η : ℝ) where
  choose : Agent → Finset Good → Finset Good
  subset : ∀ a T, choose a T ⊆ T
  feasible : ∀ a T, I.Feasible a (choose a T)
  guarantee : ∀ a T S, S ⊆ T → I.Feasible a S →
    (1 - η) * I.value a S ≤ I.value a (choose a T)

namespace Allocation

variable (A : Allocation Agent Good) (I : Instance Agent Good)

/-- Definition 8. The argument is the approximation factor itself. -/
def ApproxAgentsFEFx (q : ℝ) : Prop :=
  ∀ a b S, S ⊂ A b → I.Feasible a S → q * I.value a S ≤ I.value a (A a)

def ApproxCharityFEF (q : ℝ) : Prop :=
  ∀ a S, S ⊆ A.charity → I.Feasible a S → q * I.value a S ≤ I.value a (A a)

def ApproxFEFx (q : ℝ) : Prop :=
  A.Valid I ∧ A.ApproxAgentsFEFx I q ∧
    ∀ a S, S ⊂ A.charity → I.Feasible a S → q * I.value a S ≤ I.value a (A a)

/-- Approximate envy with factor `q` (Definition 9). -/
def ApproxEnvies (q : ℝ) (a : Agent) (T : Finset Good) : Prop :=
  ∃ S ⊆ T, I.Feasible a S ∧ I.value a (A a) < q * I.value a S

/-- Definition 9, with the feasible witnessing bundle made explicit. -/
def ApproxMinimalEnvied (ε : ℝ) (T : Finset Good) (k : Agent) : Prop :=
  I.Feasible k T ∧ I.value k (A k) < (1 - ε / 2) * I.value k T ∧
    ∀ S, S ⊂ T → ∀ a, ¬ A.ApproxEnvies I (1 - ε) a S

@[simp] theorem approxFEFx_one : A.ApproxFEFx I 1 ↔ A.FEFx I := by
  simp [ApproxFEFx, ApproxAgentsFEFx, FEFx, AgentsFEFx]

theorem FEFx.approx {q : ℝ} (h : A.FEFx I) (hq : q ≤ 1) : A.ApproxFEFx I q := by
  refine ⟨h.1, ?_, ?_⟩
  · intro a b S hS hF
    exact (mul_le_of_le_one_left (I.value_nonneg a S) hq).trans (h.2.1 a b S hS hF)
  · intro a S hS hF
    exact (mul_le_of_le_one_left (I.value_nonneg a S) hq).trans (h.2.2 a S hS hF)

theorem not_approxEnvies_iff {q : ℝ} {a : Agent} {T : Finset Good} :
    ¬ A.ApproxEnvies I q a T ↔
      ∀ S ⊆ T, I.Feasible a S → q * I.value a S ≤ I.value a (A a) := by
  simp only [ApproxEnvies, not_exists, not_and, not_lt]

/-- Proposition 10, first implication. -/
theorem oracle_detects_envy {η : ℝ} (K : KnapsackOracle I η)
    {a : Agent} {T : Finset Good}
    (h : I.value a (A a) < (1 - η) * I.value a (K.choose a T)) :
    A.ApproxEnvies I (1 - η) a T :=
  ⟨K.choose a T, K.subset a T, K.feasible a T, h⟩

/-- Proposition 10, second implication. -/
theorem oracle_no_envy {η : ℝ} (K : KnapsackOracle I η)
    (hη : η ≤ 1) {a : Agent} {T : Finset Good}
    (h : (1 - η) * I.value a (K.choose a T) ≤ I.value a (A a)) :
    ¬ A.ApproxEnvies I (1 - 2 * η) a T := by
  rw [not_approxEnvies_iff]
  intro S hST hF
  have happrox := K.guarantee a T S hST hF
  have hmul := mul_le_mul_of_nonneg_left happrox (sub_nonneg.mpr hη)
  have hnonneg := I.value_nonneg a S
  have hsq := mul_nonneg (sq_nonneg η) hnonneg
  nlinarith

/-- The exact precondition of the while-loop in Algorithm 4. -/
def OracleEnvied (ε : ℝ) (K : KnapsackOracle I (ε / 2)) (T : Finset Good) : Prop :=
  ∃ a, I.value a (A a) < (1 - ε / 2) * I.value a (K.choose a T)

/-- Lemma 11: deletion until the oracle detects no smaller set, followed by
the final knapsack call, returns an approximately minimal envied set. -/
theorem approxMinimal_of_oracle_stop {ε : ℝ} (hε : ε ≤ 1)
    (K : KnapsackOracle I (ε / 2)) {R : Finset Good} {k : Agent}
    (henvy : I.value k (A k) < (1 - ε / 2) * I.value k (K.choose k R))
    (hstop : ∀ g ∈ R, ¬ A.OracleEnvied I ε K (R.erase g)) :
    A.ApproxMinimalEnvied I ε (K.choose k R) k := by
  refine ⟨K.feasible k R, henvy, ?_⟩
  intro S hS a
  have hSR : S ⊂ R := lt_of_lt_of_le hS (K.subset k R)
  obtain ⟨g, hg, hSg⟩ := Finset.ssubset_iff_exists_subset_erase.mp hSR
  have hn : (1 - ε / 2) * I.value a (K.choose a (R.erase g)) ≤ I.value a (A a) := by
    by_contra h
    exact hstop g hg ⟨a, lt_of_not_ge h⟩
  have hnot := A.oracle_no_envy I K (by linarith : ε / 2 ≤ 1) hn
  have hnot' : ¬ A.ApproxEnvies I (1 - ε) a (R.erase g) := by
    have heps : 1 - 2 * (ε / 2) = 1 - ε := by ring
    simpa only [heps] using hnot
  intro h
  obtain ⟨U, hUS, hF, hV⟩ := h
  exact hnot' ⟨U, hUS.trans hSg, hF, hV⟩

/-- The deletion subroutine terminates because every deletion reduces cardinality. -/
theorem exists_oracle_minimal {ε : ℝ} (K : KnapsackOracle I (ε / 2))
    {C : Finset Good} (hC : A.OracleEnvied I ε K C) :
    ∃ R ⊆ C, A.OracleEnvied I ε K R ∧
      ∀ g ∈ R, ¬ A.OracleEnvied I ε K (R.erase g) := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hstop : ∀ g ∈ C, ¬ A.OracleEnvied I ε K (C.erase g)
    · exact ⟨C, Finset.Subset.refl _, hC, hstop⟩
    · push Not at hstop
      obtain ⟨g, hg, henvy⟩ := hstop
      obtain ⟨R, hRC, hR, hstopR⟩ := ih (C.erase g) (Finset.erase_ssubset hg) henvy
      exact ⟨R, hRC.trans (Finset.erase_subset _ _), hR, hstopR⟩

theorem exists_approxMinimalEnvied {ε : ℝ} (hε : ε ≤ 1)
    (K : KnapsackOracle I (ε / 2)) {C : Finset Good}
    (hC : A.OracleEnvied I ε K C) :
    ∃ T ⊆ C, ∃ k, A.ApproxMinimalEnvied I ε T k := by
  obtain ⟨R, hRC, ⟨k, hk⟩, hstop⟩ := A.exists_oracle_minimal I K hC
  exact ⟨K.choose k R, (K.subset k R).trans hRC, k,
    A.approxMinimal_of_oracle_stop I hε K hk hstop⟩

/-- Strict utility improvement, including the case of a zero initial utility. -/
theorem ApproxMinimalEnvied.improves {ε : ℝ} (hε : 0 ≤ ε)
    {T : Finset Good} {k : Agent} (h : A.ApproxMinimalEnvied I ε T k) :
    I.value k (A k) < I.value k T := by
  have hv := I.value_nonneg k T
  have : (1 - ε / 2) * I.value k T ≤ I.value k T := by nlinarith
  exact h.2.1.trans_le this

/-- Claim 12: a selected agent's utility improves multiplicatively. -/
theorem ApproxMinimalEnvied.multiplicative {ε : ℝ} (hε : ε ≤ 1)
    {T : Finset Good} {k : Agent} (h : A.ApproxMinimalEnvied I ε T k) :
    (1 / (1 - ε / 2)) * I.value k (A k) < I.value k T := by
  have hp : 0 < 1 - ε / 2 := by linarith
  rw [one_div, inv_mul_eq_div]
  exact (div_lt_iff₀ hp).mpr (by simpa [mul_comm] using h.2.1)

/-- Lemma 13: the approximate fairness invariant survives an update. -/
theorem replace_approxAgentsFEFx {ε : ℝ} (hε : 0 ≤ ε)
    {T : Finset Good} {k : Agent}
    (hA : A.ApproxAgentsFEFx I (1 - ε)) (hT : A.ApproxMinimalEnvied I ε T k) :
    (A.replace k T).ApproxAgentsFEFx I (1 - ε) := by
  intro a b S hS hF
  apply le_trans _ (A.value_le_replace I (hT.improves A I hε).le a)
  by_cases hb : b = k
  · subst b
    simp only [replace_same] at hS
    exact (A.not_approxEnvies_iff I).mp (hT.2.2 S hS a) S (Finset.Subset.refl _) hF
  · rw [replace_other A T hb] at hS
    exact hA a b S hS hF

/-- Lemma 14: failure of the outer oracle test gives approximate FEF towards
every feasible subset of charity, including charity itself. -/
theorem oracle_termination_charity {ε : ℝ} (hε : ε ≤ 1)
    (K : KnapsackOracle I (ε / 2))
    (hstop : ¬ A.OracleEnvied I ε K A.charity) :
    A.ApproxCharityFEF I (1 - ε) := by
  intro a S hS hF
  have hn : (1 - ε / 2) * I.value a (K.choose a A.charity) ≤ I.value a (A a) := by
    by_contra h
    exact hstop ⟨a, lt_of_not_ge h⟩
  have h := (A.not_approxEnvies_iff I).mp
    (A.oracle_no_envy I K (by linarith : ε / 2 ≤ 1) hn) S hS hF
  have heps : 1 - 2 * (ε / 2) = 1 - ε := by ring
  simpa only [heps] using h

end Allocation

end GeneralizedAssignment
