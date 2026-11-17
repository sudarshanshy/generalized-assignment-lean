import GeneralizedAssignment.ExactAlgorithm
import GeneralizedAssignment.ApproximateOracle
import GeneralizedAssignment.ApproximateComplexity

set_option linter.unusedSectionVars false

/-!
# Executable approximate FEFx

Algorithms 4–5 with the verified scaling oracle. The input `r ≥ 2`
gives factor `1 - 2/r`. All choices and comparisons use integer arithmetic.
Correctness, a polynomial iteration bound, and a counted knapsack-call
bound are proved for the executable implementation.
-/

namespace GeneralizedAssignment.NaturalInstance

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (N : NaturalInstance Agent Good)

theorem accuracy_pos (r : ℕ) (hr : 0 < r) : (0 : ℝ) < 2 / (r : ℝ) := by
  apply div_pos (by norm_num)
  exact_mod_cast hr

theorem accuracy_le_one (r : ℕ) (hr : 2 ≤ r) : 2 / (r : ℝ) ≤ 1 := by
  have hp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  apply (div_le_one hp).mpr
  exact_mod_cast hr

structure ApproxMinimalResult (r : ℕ) (A : Allocation Agent Good) (C : Finset Good) where
  bundle : Finset Good
  agent : Agent
  subset : bundle ⊆ C
  minimal : A.ApproxMinimalEnvied N.toReal (2 / (r : ℝ)) bundle agent
  gain : N.value agent (A agent) < N.value agent bundle
  deletions : ℕ
  deletion_bound : deletions ≤ C.card
  queries : ℕ
  query_bound : queries ≤ (Fintype.card Agent + 1) * (C.card + 1) ^ 2

/-- Algorithm 5, including the final feasible-knapsack selection. -/
def findApproxMinimal (r : ℕ) (hr : 2 ≤ r) (A : Allocation Agent Good) (C : Finset Good)
    (hC : (N.approxEnvyingAgents r A C).Nonempty) : ApproxMinimalResult N r A C := by
  have hr0 : 0 < r := by omega
  let D := FiniteDeletion.run (fun T => (N.approxEnvyingAgents r A T).Nonempty) C hC
  let k := N.chooseApproxEnvier r A D.bundle D.holds
  let K := N.halfOracle r hr0
  have hk : N.toReal.value k (A k) <
      (1 - (2 / (r : ℝ)) / 2) * N.toReal.value k (K.choose k D.bundle) :=
    (N.approxDetect_iff r hr0 A k D.bundle).mp (N.chooseApproxEnvier_detects r A _ D.holds)
  have hstop : ∀ g ∈ D.bundle,
      ¬ A.OracleEnvied N.toReal (2 / (r : ℝ)) K (D.bundle.erase g) := by
    intro g hg h
    exact D.stop g hg ((N.approxEnvyingAgents_nonempty_iff r hr0 A _).mpr h)
  have hmin := A.approxMinimal_of_oracle_stop N.toReal (accuracy_le_one r hr) K hk hstop
  refine ⟨K.choose k D.bundle, k, (K.subset k _).trans D.subset, hmin, ?_,
    D.deletions, D.deletion_bound, Fintype.card Agent * (D.queries + 1) + 1, ?_⟩
  · have h := hmin.improves A N.toReal (accuracy_pos r hr0).le
    simpa using h
  · have hs : D.queries + 1 ≤ (C.card + 1) ^ 2 := by
      nlinarith only [D.query_bound, Nat.zero_le C.card]
    have hm := Nat.mul_le_mul_left (Fintype.card Agent) hs
    nlinarith only [hm, Nat.zero_le C.card]

def approxCallsPerIteration (_N : NaturalInstance Agent Good) : ℕ :=
  (Fintype.card Agent + 1) * (1 + (Fintype.card Good + 1) ^ 2)

def executeApproxAux (r : ℕ) (hr : 2 ≤ r) : ℕ → Allocation Agent Good → ExecutionOutput Agent Good
  | 0, A => ⟨A, 0, Fintype.card Agent⟩
  | fuel + 1, A =>
    if henvy : (N.approxEnvyingAgents r A A.charity).Nonempty then
      let M := N.findApproxMinimal r hr A A.charity henvy
      let R := executeApproxAux r hr fuel (A.replace M.agent M.bundle)
      ⟨R.allocation, R.iterations + 1, Fintype.card Agent + M.queries + R.queries⟩
    else ⟨A, 0, Fintype.card Agent⟩

structure ApproxExecutionSpec (r : ℕ) (A : Allocation Agent Good)
    (R : ExecutionOutput Agent Good) : Prop where
  trace : Run (Allocation.ApproxStep N.toReal (2 / (r : ℝ))) A R.allocation R.iterations
  valid : R.allocation.Valid N.toReal
  agents : R.allocation.ApproxAgentsFEFx N.toReal (1 - 2 / (r : ℝ))
  charity : R.allocation.ApproxCharityFEF N.toReal (1 - 2 / (r : ℝ))
  welfare_bound : N.welfare A + R.iterations ≤ N.welfare R.allocation
  query_bound : R.queries ≤ (R.iterations + 1) * N.approxCallsPerIteration

theorem ApproxExecutionSpec.fair {r : ℕ} {A : Allocation Agent Good}
    {R : ExecutionOutput Agent Good} (h : ApproxExecutionSpec N r A R) :
    R.allocation.ApproxFEFx N.toReal (1 - 2 / (r : ℝ)) :=
  ⟨h.valid, h.agents, fun a S hS hF => h.charity a S hS.subset hF⟩

theorem approxTerminal_spec (r : ℕ) (hr : 2 ≤ r) (A : Allocation Agent Good)
    (hA : A.Valid N.toReal) (hEF : A.ApproxAgentsFEFx N.toReal (1 - 2 / (r : ℝ)))
    (hno : ¬ A.OracleEnvied N.toReal (2 / (r : ℝ)) (N.halfOracle r (by omega)) A.charity) :
    ApproxExecutionSpec N r A ⟨A, 0, Fintype.card Agent⟩ := by
  refine ⟨Run.refl A, hA, hEF,
    A.oracle_termination_charity N.toReal (accuracy_le_one r hr) _ hno, by simp, ?_⟩
  simp only [zero_add, one_mul, approxCallsPerIteration]
  nlinarith only [Nat.zero_le ((Fintype.card Agent + 1) * (Fintype.card Good + 1) ^ 2)]

theorem executeApproxAux_spec (r : ℕ) (hr : 2 ≤ r) (fuel : ℕ) (A : Allocation Agent Good)
    (hA : A.Valid N.toReal) (hEF : A.ApproxAgentsFEFx N.toReal (1 - 2 / (r : ℝ)))
    (hspace : N.totalValue - N.welfare A ≤ fuel) :
    ApproxExecutionSpec N r A (N.executeApproxAux r hr fuel A) := by
  have hr0 : 0 < r := by omega
  induction fuel generalizing A with
  | zero =>
    apply N.approxTerminal_spec r hr A hA hEF
    intro henvy
    let M := N.findApproxMinimal r hr A A.charity
      ((N.approxEnvyingAgents_nonempty_iff r hr0 A _).mpr henvy)
    have hp := N.welfare_replace_lt M.gain
    have hb := N.welfare_le_total (A.replace M.agent M.bundle)
    omega
  | succ fuel ih =>
    by_cases henvy : (N.approxEnvyingAgents r A A.charity).Nonempty
    · let M := N.findApproxMinimal r hr A A.charity henvy
      let B := A.replace M.agent M.bundle
      have hvalid : B.Valid N.toReal := A.replace_valid N.toReal hA M.subset M.minimal.1
      have hfair : B.ApproxAgentsFEFx N.toReal (1 - 2 / (r : ℝ)) :=
        A.replace_approxAgentsFEFx N.toReal (accuracy_pos r hr0).le hEF M.minimal
      have hprogress : N.welfare A < N.welfare B := N.welfare_replace_lt M.gain
      have hspaceB : N.totalValue - N.welfare B ≤ fuel := by
        have hb := N.welfare_le_total B
        omega
      let R := N.executeApproxAux r hr fuel B
      have hR := ih B hvalid hfair hspaceB
      simp only [executeApproxAux, henvy, ↓reduceDIte]
      change ApproxExecutionSpec N r A ⟨R.allocation, R.iterations + 1,
        Fintype.card Agent + M.queries + R.queries⟩
      refine ⟨Run.cons ⟨M.agent, M.bundle, M.subset, M.minimal, rfl⟩ hR.trace,
        hR.valid, hR.agents, hR.charity, ?_, ?_⟩
      · have hb : N.welfare B + R.iterations ≤ N.welfare R.allocation := hR.welfare_bound
        change N.welfare A + (R.iterations + 1) ≤ N.welfare R.allocation
        omega
      · have hm : M.queries ≤ (Fintype.card Agent + 1) * (Fintype.card Good + 1) ^ 2 := by
          apply M.query_bound.trans
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left (Nat.add_le_add_right (Finset.card_le_univ A.charity) 1) 2
        have hlocal : Fintype.card Agent + M.queries ≤ N.approxCallsPerIteration := by
          dsimp [approxCallsPerIteration]
          nlinarith only [hm]
        have hq : R.queries ≤ (R.iterations + 1) * N.approxCallsPerIteration := hR.query_bound
        change Fintype.card Agent + M.queries + R.queries ≤
          (R.iterations + 1 + 1) * N.approxCallsPerIteration
        nlinarith only [hlocal, hq]
    · simp only [executeApproxAux, henvy, ↓reduceDIte]
      apply N.approxTerminal_spec r hr A hA hEF
      intro h
      exact henvy ((N.approxEnvyingAgents_nonempty_iff r hr0 A _).mpr h)

def runApprox (r : ℕ) (hr : 2 ≤ r) : ExecutionOutput Agent Good :=
  N.executeApproxAux r hr N.totalValue Allocation.empty

theorem runApprox_spec (r : ℕ) (hr : 2 ≤ r) :
    ApproxExecutionSpec N r Allocation.empty (N.runApprox r hr) := by
  apply N.executeApproxAux_spec r hr N.totalValue Allocation.empty (Allocation.empty_valid N.toReal)
  · intro a b S hS _
    exact False.elim (Finset.not_ssubset_empty S hS)
  · exact Nat.sub_le _ _

def solveApproxFEFx (r : ℕ) (hr : 2 ≤ r) : Allocation Agent Good :=
  (N.runApprox r hr).allocation

/-- Correctness of the fully instantiated, executable approximation algorithm. -/
theorem solveApproxFEFx_fair (r : ℕ) (hr : 2 ≤ r) :
    (N.solveApproxFEFx r hr).ApproxFEFx N.toReal (1 - 2 / (r : ℝ)) :=
  (N.runApprox_spec r hr).fair N

theorem runApprox_iterations_twice (r : ℕ) (hr : 2 ≤ r) (L : ℕ)
    (hbits : ∀ a, N.value a Finset.univ + 1 ≤ 2 ^ L) :
    2 * (N.runApprox r hr).iterations ≤ 5 * Fintype.card Agent * L * r := by
  have hr0 : 0 < r := by omega
  have hbitsR : ∀ a, N.toReal.value a Finset.univ + 1 ≤ (2 : ℝ) ^ L := by
    intro a
    rw [N.real_value]
    exact_mod_cast hbits a
  have h := Allocation.approxRun_iterations_bits N.toReal N.integral
    (accuracy_pos r hr0) (accuracy_le_one r hr) (N.runApprox_spec r hr).trace L hbitsR
  have heq : 5 * (Fintype.card Agent : ℝ) * L / (2 / (r : ℝ)) =
      (5 * (Fintype.card Agent : ℝ) * L * r) / 2 := by
    field_simp
  rw [heq] at h
  have hR : 2 * ((N.runApprox r hr).iterations : ℝ) ≤
      5 * (Fintype.card Agent : ℝ) * L * r := by linarith
  exact_mod_cast hR

theorem runApprox_iterations_le (r : ℕ) (hr : 2 ≤ r) (L : ℕ)
    (hbits : ∀ a, N.value a Finset.univ + 1 ≤ 2 ^ L) :
    (N.runApprox r hr).iterations ≤ 5 * Fintype.card Agent * L * r := by
  have := N.runApprox_iterations_twice r hr L hbits
  omega

/-- Polynomially many polynomial-time knapsack calls: Theorem 4. -/
theorem runApprox_queries_le (r : ℕ) (hr : 2 ≤ r) (L : ℕ)
    (hbits : ∀ a, N.value a Finset.univ + 1 ≤ 2 ^ L) :
    (N.runApprox r hr).queries ≤ (5 * Fintype.card Agent * L * r + 1) *
      ((Fintype.card Agent + 1) * (1 + (Fintype.card Good + 1) ^ 2)) := by
  apply (N.runApprox_spec r hr).query_bound.trans
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (N.runApprox_iterations_le r hr L hbits) 1)

end GeneralizedAssignment.NaturalInstance
