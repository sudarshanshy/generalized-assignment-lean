import GeneralizedAssignment.NaturalInstance
import GeneralizedAssignment.FiniteDeletion

set_option linter.unusedSectionVars false

/-!
# Executable exact FEFx algorithm

Algorithms 2–3 on natural-number inputs. Choices are implemented with
finite minima and envy tests use the verified knapsack dynamic program.
The implementation records iterations and a conservative count of
knapsack calls (full scans, even when a short-circuit could save work).
-/

open scoped BigOperators

namespace GeneralizedAssignment.NaturalInstance

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (N : NaturalInstance Agent Good)

def removable (A : Allocation Agent Good) (T : Finset Good) : Finset Good :=
  T.filter fun g => (N.envyingAgents A (T.erase g)).Nonempty

structure MinimalResult (A : Allocation Agent Good) (C : Finset Good) where
  bundle : Finset Good
  agent : Agent
  subset : bundle ⊆ C
  minimal : A.MinimalEnvied N.toReal bundle
  feasible : N.toReal.Feasible agent bundle
  gain : N.value agent (A agent) < N.value agent bundle
  deletions : ℕ
  deletion_bound : deletions ≤ C.card
  queries : ℕ
  query_bound : queries ≤ Fintype.card Agent * (C.card + 1) ^ 2

/-- Algorithm 3, using the shared checked deletion routine. -/
def findMinimal (A : Allocation Agent Good) (C : Finset Good)
    (hC : (N.envyingAgents A C).Nonempty) : MinimalResult N A C := by
  let D := FiniteDeletion.run (fun T => (N.envyingAgents A T).Nonempty) C hC
  let k := N.chooseEnvier A D.bundle D.holds
  have henvy : A.Envied N.toReal D.bundle := (N.envyingAgents_nonempty_iff A _).mp D.holds
  have hmin : A.MinimalEnvied N.toReal D.bundle := by
    apply A.minimalEnvied_of_no_erase N.toReal henvy
    intro g hg henv
    exact D.stop g hg ((N.envyingAgents_nonempty_iff A _).mpr henv)
  have hkenvy : A.Envies N.toReal k D.bundle :=
    (N.envies_iff A k _).mp (N.chooseEnvier_envies A _ D.holds)
  have hk := hmin.envier A N.toReal hkenvy
  refine ⟨D.bundle, k, D.subset, hmin, hk.1, ?_, D.deletions, D.deletion_bound,
    Fintype.card Agent * (D.queries + 1), ?_⟩
  · simpa using hk.2
  · apply Nat.mul_le_mul_left
    nlinarith only [D.query_bound, Nat.zero_le C.card]

/-- A worst-case number of exact-knapsack calls for one outer iteration. -/
def callsPerIteration (_N : NaturalInstance Agent Good) : ℕ :=
  Fintype.card Agent * (1 + (Fintype.card Good + 1) ^ 2)

structure ExactExecution (A : Allocation Agent Good) where
  allocation : Allocation Agent Good
  iterations : ℕ
  trace : Run (Allocation.ExactStep N.toReal) A allocation iterations
  fair : allocation.StrongFEFx N.toReal
  welfare_bound : N.welfare A + iterations ≤ N.welfare allocation
  queries : ℕ
  query_bound : queries ≤ (iterations + 1) * N.callsPerIteration

theorem welfare_replace_lt {A : Allocation Agent Good} {k : Agent} {T : Finset Good}
    (h : N.value k (A k) < N.value k T) : N.welfare A < N.welfare (A.replace k T) := by
  have hreal : N.toReal.value k (A k) < N.toReal.value k T := by simpa using h
  have hw := A.welfare_lt_replace N.toReal hreal
  simpa using hw

structure ExecutionOutput (Agent Good : Type*) where
  allocation : Allocation Agent Good
  iterations : ℕ
  queries : ℕ

def executeAux : ℕ → Allocation Agent Good → ExecutionOutput Agent Good
  | 0, A => ⟨A, 0, Fintype.card Agent⟩
  | fuel + 1, A =>
    if henvy : (N.envyingAgents A A.charity).Nonempty then
      let M := N.findMinimal A A.charity henvy
      let R := executeAux fuel (A.replace M.agent M.bundle)
      ⟨R.allocation, R.iterations + 1, Fintype.card Agent + M.queries + R.queries⟩
    else ⟨A, 0, Fintype.card Agent⟩

structure ExecutionSpec (A : Allocation Agent Good) (R : ExecutionOutput Agent Good) : Prop where
  trace : Run (Allocation.ExactStep N.toReal) A R.allocation R.iterations
  fair : R.allocation.StrongFEFx N.toReal
  welfare_bound : N.welfare A + R.iterations ≤ N.welfare R.allocation
  query_bound : R.queries ≤ (R.iterations + 1) * N.callsPerIteration

theorem terminal_spec (A : Allocation Agent Good) (hA : A.Valid N.toReal)
    (hEF : A.AgentsFEFx N.toReal) (hno : ¬ A.Envied N.toReal A.charity) :
    ExecutionSpec N A ⟨A, 0, Fintype.card Agent⟩ := by
  refine ⟨Run.refl A, ⟨hA, hEF, (A.charityFEF_iff N.toReal).mpr hno⟩, by simp, ?_⟩
  simp only [zero_add, one_mul, callsPerIteration]
  nlinarith [Nat.zero_le (Fintype.card Agent * (Fintype.card Good + 1) ^ 2)]

theorem executeAux_spec (fuel : ℕ) (A : Allocation Agent Good) (hA : A.Valid N.toReal)
    (hEF : A.AgentsFEFx N.toReal) (hspace : N.totalValue - N.welfare A ≤ fuel) :
    ExecutionSpec N A (N.executeAux fuel A) := by
  induction fuel generalizing A with
  | zero =>
    apply N.terminal_spec A hA hEF
    intro henvy
    let M := N.findMinimal A A.charity ((N.envyingAgents_nonempty_iff A _).mpr henvy)
    have hp := N.welfare_replace_lt M.gain
    have hb := N.welfare_le_total (A.replace M.agent M.bundle)
    omega
  | succ fuel ih =>
    by_cases henvy : (N.envyingAgents A A.charity).Nonempty
    · let M := N.findMinimal A A.charity henvy
      let B := A.replace M.agent M.bundle
      have hvalid : B.Valid N.toReal := A.replace_valid N.toReal hA M.subset M.feasible
      have hgain : N.toReal.value M.agent (A M.agent) < N.toReal.value M.agent M.bundle := by
        simpa using M.gain
      have hfair : B.AgentsFEFx N.toReal := A.replace_agentsFEFx N.toReal hEF M.minimal hgain.le
      have hprogress : N.welfare A < N.welfare B := N.welfare_replace_lt M.gain
      have hspaceB : N.totalValue - N.welfare B ≤ fuel := by
        have hb := N.welfare_le_total B
        omega
      let R := N.executeAux fuel B
      have hR := ih B hvalid hfair hspaceB
      simp only [executeAux, henvy, ↓reduceDIte]
      change ExecutionSpec N A ⟨R.allocation, R.iterations + 1,
        Fintype.card Agent + M.queries + R.queries⟩
      refine ⟨Run.cons ⟨M.agent, M.bundle, M.subset, M.minimal, M.feasible, hgain, rfl⟩ hR.trace,
        hR.fair, ?_, ?_⟩
      · have hb : N.welfare B + R.iterations ≤ N.welfare R.allocation := hR.welfare_bound
        change N.welfare A + (R.iterations + 1) ≤ N.welfare R.allocation
        omega
      · have hm : M.queries ≤ Fintype.card Agent * (Fintype.card Good + 1) ^ 2 := by
          apply M.query_bound.trans
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left (Nat.add_le_add_right (Finset.card_le_univ A.charity) 1) 2
        have hlocal : Fintype.card Agent + M.queries ≤ N.callsPerIteration := by
          dsimp [callsPerIteration]
          nlinarith
        have hr := hR.query_bound
        change Fintype.card Agent + M.queries + R.queries ≤
          (R.iterations + 1 + 1) * N.callsPerIteration
        nlinarith
    · simp only [executeAux, henvy, ↓reduceDIte]
      apply N.terminal_spec A hA hEF
      intro h
      exact henvy ((N.envyingAgents_nonempty_iff A _).mpr h)

/-- Algorithm 2 with a proved sufficient fuel bound and a checked execution trace. -/
def execute (A : Allocation Agent Good) (hA : A.Valid N.toReal)
    (hEF : A.AgentsFEFx N.toReal) : ExactExecution N A :=
  let R := N.executeAux (N.totalValue - N.welfare A) A
  let h := N.executeAux_spec (N.totalValue - N.welfare A) A hA hEF le_rfl
  ⟨R.allocation, R.iterations, h.trace, h.fair, h.welfare_bound, R.queries, h.query_bound⟩

def run : ExactExecution N Allocation.empty :=
  N.execute Allocation.empty (Allocation.empty_valid N.toReal) (Allocation.empty_agentsFEFx N.toReal)

def solveFEFx : Allocation Agent Good := N.run.allocation

theorem solveFEFx_strong : N.solveFEFx.StrongFEFx N.toReal := N.run.fair

/-- Correctness of the executable algorithm. -/
theorem solveFEFx_fair : N.solveFEFx.FEFx N.toReal :=
  N.solveFEFx_strong.fefx N.solveFEFx N.toReal

/-- Theorem 3's integer iteration bound for the executable implementation. -/
theorem run_iterations_le : N.run.iterations ≤ N.totalValue := by
  have h := N.run.welfare_bound
  have hzero : N.welfare Allocation.empty = 0 := by
    simp [welfare, value, Knapsack.total, Allocation.empty]
  rw [hzero, zero_add] at h
  exact h.trans (N.welfare_le_total _)

/-- A polynomial number of exact-knapsack calls per unit of the welfare bound. -/
theorem run_queries_le :
    N.run.queries ≤ (N.totalValue + 1) *
      (Fintype.card Agent * (1 + (Fintype.card Good + 1) ^ 2)) := by
  exact N.run.query_bound.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right N.run_iterations_le 1))

end GeneralizedAssignment.NaturalInstance
