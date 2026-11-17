import GeneralizedAssignment.Approximate
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.unusedSectionVars false

/-!
# Certified executions of the swapping algorithms

Algorithms 2 and 4, their invariants, and the integer iteration bound
used in Theorem 3. These real-valued implementations use classical
finite choice. Their outputs carry complete execution traces.
-/

open scoped BigOperators

namespace GeneralizedAssignment

/-- A finite execution, with its number of transitions recorded in the type. -/
inductive Run {α : Type*} (step : α → α → Prop) : α → α → ℕ → Prop
  | refl (a) : Run step a a 0
  | cons {a b c n} : step a b → Run step b c n → Run step a c (n + 1)

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

namespace Allocation

variable (I : Instance Agent Good)

/-- The number of allocations with strictly larger welfare. -/
noncomputable def improvementRank (A : Allocation Agent Good) : ℕ := by
  classical
  exact (Finset.univ.filter fun B : Allocation Agent Good => A.welfare I < B.welfare I).card

theorem improvementRank_lt {A B : Allocation Agent Good}
    (h : A.welfare I < B.welfare I) : improvementRank I B < improvementRank I A := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro C hC
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hC).2⟩
  · intro heq
    have hB : B ∈ Finset.univ.filter (fun C : Allocation Agent Good => A.welfare I < C.welfare I) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← heq] at hB
    exact lt_irrefl _ (Finset.mem_filter.mp hB).2

/-- One iteration of Algorithm 2. -/
def ExactStep (A B : Allocation Agent Good) : Prop :=
  ∃ k T, T ⊆ A.charity ∧ A.MinimalEnvied I T ∧ I.Feasible k T ∧
    I.value k (A k) < I.value k T ∧ B = A.replace k T

theorem ExactStep.welfare_lt {A B : Allocation Agent Good} (h : ExactStep I A B) :
    A.welfare I < B.welfare I := by
  obtain ⟨k, T, _, _, _, hV, rfl⟩ := h
  exact A.welfare_lt_replace I hV

theorem ExactStep.invariant {A B : Allocation Agent Good} (h : ExactStep I A B)
    (hA : A.Valid I) (hEF : A.AgentsFEFx I) : B.Valid I ∧ B.AgentsFEFx I := by
  obtain ⟨k, T, hsub, hmin, hfeas, hV, rfl⟩ := h
  exact ⟨A.replace_valid I hA hsub hfeas, A.replace_agentsFEFx I hEF hmin hV.le⟩

/-- Lemma 7 for every finite execution, regardless of the choices of minimal bundles. -/
theorem exactRun_invariant {A B : Allocation Agent Good} {n : ℕ}
    (h : Run (ExactStep I) A B n) (hA : A.Valid I) (hEF : A.AgentsFEFx I) :
    B.Valid I ∧ B.AgentsFEFx I := by
  induction h with
  | refl => exact ⟨hA, hEF⟩
  | cons hs _ ih =>
    have hnext := hs.invariant I hA hEF
    exact ih hnext.1 hnext.2

structure ExactResult (A : Allocation Agent Good) where
  allocation : Allocation Agent Good
  iterations : ℕ
  trace : Run (ExactStep I) A allocation iterations
  fair : allocation.StrongFEFx I

/-- Algorithm 2 with a checked termination measure, even for real values. -/
noncomputable def computeFEFx (A : Allocation Agent Good)
    (hA : A.Valid I) (hEF : A.AgentsFEFx I) : ExactResult I A := by
  classical
  by_cases henvy : A.Envied I A.charity
  · let hExists := A.exists_minimal_envied I henvy
    let T := Classical.choose hExists
    have hT := Classical.choose_spec hExists
    let hw := hT.2.witness A I
    let k := Classical.choose hw
    have hk := Classical.choose_spec hw
    have hvalid := A.replace_valid I hA hT.1 hk.1
    have hfair := A.replace_agentsFEFx I hEF hT.2 hk.2.le
    let R := computeFEFx (A.replace k T) hvalid hfair
    refine ⟨R.allocation, R.iterations + 1, ?_, R.fair⟩
    exact Run.cons ⟨k, T, hT.1, hT.2, hk.1, hk.2, rfl⟩ R.trace
  · exact ⟨A, 0, Run.refl A, hA, hEF, (A.charityFEF_iff I).mpr henvy⟩
termination_by improvementRank I A
decreasing_by
  apply improvementRank_lt
  exact A.welfare_lt_replace I hk.2

/-- The complete exact algorithm, initialized with empty bundles. -/
noncomputable def exactAlgorithm : ExactResult I empty :=
  computeFEFx I empty (empty_valid I) (empty_agentsFEFx I)

/-- Integer data have a unit gap between distinct bundle values. -/
def IntegralValues : Prop := ∀ a g, ∃ n : ℕ, I.val a g = n

theorem integral_value_gap (hint : IntegralValues I) {a : Agent} {S T : Finset Good}
    (h : I.value a S < I.value a T) : I.value a S + 1 ≤ I.value a T := by
  classical
  choose v hv using hint
  have hS : I.value a S = ((∑ g ∈ S, v a g : ℕ) : ℝ) := by
    simp [Instance.value, hv]
  have hT : I.value a T = ((∑ g ∈ T, v a g : ℕ) : ℝ) := by
    simp [Instance.value, hv]
  rw [hS, hT] at h ⊢
  have hn : (∑ g ∈ S, v a g) < ∑ g ∈ T, v a g := by exact_mod_cast h
  exact_mod_cast (Nat.succ_le_of_lt hn)

theorem welfare_add_one_le_replace (hint : IntegralValues I)
    {A : Allocation Agent Good} {k : Agent} {T : Finset Good}
    (hV : I.value k (A k) < I.value k T) :
    A.welfare I + 1 ≤ (A.replace k T).welfare I := by
  classical
  have hgap := integral_value_gap I hint hV
  have hsum : (∑ a, (I.value a (A a) + if a = k then (1 : ℝ) else 0)) ≤
      ∑ a, I.value a (A.replace k T a) := by
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : a = k
    · subst a; simpa using hgap
    · simp [ha]
  simpa [welfare, Finset.sum_add_distrib] using hsum

theorem ExactStep.welfare_add_one_le (hint : IntegralValues I)
    {A B : Allocation Agent Good} (h : ExactStep I A B) :
    A.welfare I + 1 ≤ B.welfare I := by
  obtain ⟨k, T, _, _, _, hV, rfl⟩ := h
  exact welfare_add_one_le_replace I hint hV

/-- The unit welfare increase bounds the length of every exact execution. -/
theorem exactRun_welfare_bound (hint : IntegralValues I)
    {A B : Allocation Agent Good} {n : ℕ} (h : Run (ExactStep I) A B n) :
    A.welfare I + n ≤ B.welfare I := by
  induction h with
  | refl => simp
  | cons hs _ ih =>
    have hstep := hs.welfare_add_one_le I hint
    push_cast
    linarith

/-- The iteration bound used in Theorem 3. -/
theorem exactAlgorithm_iterations_le (hint : IntegralValues I) :
    ((exactAlgorithm I).iterations : ℝ) ≤ ∑ a, I.value a Finset.univ := by
  have h := exactRun_welfare_bound I hint (exactAlgorithm I).trace
  simp only [empty_welfare, zero_add] at h
  exact h.trans ((exactAlgorithm I).allocation.welfare_le I)

/-- The paper's `n * max_a v_a([m])` version of the same bound. -/
theorem exactAlgorithm_iterations_le_card_mul (hint : IntegralValues I) (M : ℕ)
    (hM : ∀ a, I.value a Finset.univ ≤ M) :
    (exactAlgorithm I).iterations ≤ Fintype.card Agent * M := by
  have hsum : (∑ a, I.value a Finset.univ) ≤ Fintype.card Agent * (M : ℝ) := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun a _ => hM a)
  have h := (exactAlgorithm_iterations_le I hint).trans hsum
  exact_mod_cast h

/-- One iteration of Algorithm 4. -/
def ApproxStep (ε : ℝ) (A B : Allocation Agent Good) : Prop :=
  ∃ k T, T ⊆ A.charity ∧ A.ApproxMinimalEnvied I ε T k ∧ B = A.replace k T

theorem ApproxStep.welfare_lt {ε : ℝ} (hε : 0 ≤ ε)
    {A B : Allocation Agent Good} (h : ApproxStep I ε A B) :
    A.welfare I < B.welfare I := by
  obtain ⟨k, T, _, hmin, rfl⟩ := h
  exact A.welfare_lt_replace I (hmin.improves A I hε)

structure ApproxResult (ε : ℝ) (A : Allocation Agent Good) where
  allocation : Allocation Agent Good
  iterations : ℕ
  trace : Run (ApproxStep I ε) A allocation iterations
  valid : allocation.Valid I
  agents : allocation.ApproxAgentsFEFx I (1 - ε)
  charity : allocation.ApproxCharityFEF I (1 - ε)

theorem ApproxResult.fair {ε : ℝ} {A : Allocation Agent Good} (R : ApproxResult I ε A) :
    R.allocation.ApproxFEFx I (1 - ε) :=
  ⟨R.valid, R.agents, fun a S hS hF => R.charity a S hS.subset hF⟩

/-- Algorithm 4, with its approximation-oracle guarantee explicit. -/
noncomputable def computeApproxFEFx (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (K : KnapsackOracle I (ε / 2)) (A : Allocation Agent Good)
    (hA : A.Valid I) (hEF : A.ApproxAgentsFEFx I (1 - ε)) : ApproxResult I ε A := by
  classical
  by_cases henvy : A.OracleEnvied I ε K A.charity
  · let hExists := A.exists_approxMinimalEnvied I hε₁ K henvy
    let T := Classical.choose hExists
    have hT := Classical.choose_spec hExists
    let k := Classical.choose hT.2
    have hk := Classical.choose_spec hT.2
    have hvalid := A.replace_valid I hA hT.1 hk.1
    have hfair := A.replace_approxAgentsFEFx I hε₀ hEF hk
    let R := computeApproxFEFx ε hε₀ hε₁ K (A.replace k T) hvalid hfair
    refine ⟨R.allocation, R.iterations + 1, ?_, R.valid, R.agents, R.charity⟩
    exact Run.cons ⟨k, T, hT.1, hk, rfl⟩ R.trace
  · exact ⟨A, 0, Run.refl A, hA, hEF, A.oracle_termination_charity I hε₁ K henvy⟩
termination_by improvementRank I A
decreasing_by
  apply improvementRank_lt
  exact A.welfare_lt_replace I (hk.improves A I hε₀)

noncomputable def approximateAlgorithm (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (K : KnapsackOracle I (ε / 2)) : ApproxResult I ε empty :=
  computeApproxFEFx I ε hε₀ hε₁ K empty (empty_valid I)
    (fun _ _ S hS _ => False.elim (Finset.not_ssubset_empty S hS))

end Allocation

end GeneralizedAssignment
