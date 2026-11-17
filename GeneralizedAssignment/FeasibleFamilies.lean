import GeneralizedAssignment.Algorithms
import GeneralizedAssignment.FiniteDeletion

set_option linter.unusedSectionVars false

/-!
# Swapping under general feasibility families

The part of the proof used in Remark 1 does not depend on budgets.
This module makes that generality explicit. With an exact maximum-value
feasible-subset oracle, the same deletion and swapping method gives exact
or approximate FEFx. The oracle-call count is polynomial per update.
-/

open scoped BigOperators

namespace GeneralizedAssignment

structure FeasibleFamily (Agent Good : Type*) where
  feasible : Agent → Finset Good → Prop
  empty : ∀ a, feasible a ∅
  downward : ∀ a {S T}, feasible a T → S ⊆ T → feasible a S

namespace FeasibleFamily

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]
variable (F : FeasibleFamily Agent Good) (I : Instance Agent Good)

def ofInstance (I : Instance Agent Good) : FeasibleFamily Agent Good where
  feasible := I.Feasible
  empty := I.feasible_empty
  downward _a _ _ h hST := h.subset I hST

def Valid (A : Allocation Agent Good) : Prop :=
  (∀ a, F.feasible a (A a)) ∧ ∀ a b, a ≠ b → Disjoint (A a) (A b)

def AgentsFEFx (q : ℝ) (A : Allocation Agent Good) : Prop :=
  ∀ a b S, S ⊂ A b → F.feasible a S → q * I.value a S ≤ I.value a (A a)

def CharityFEF (q : ℝ) (A : Allocation Agent Good) : Prop :=
  ∀ a S, S ⊆ A.charity → F.feasible a S → q * I.value a S ≤ I.value a (A a)

def FEFx (q : ℝ) (A : Allocation Agent Good) : Prop :=
  F.Valid A ∧ F.AgentsFEFx I q A ∧
    ∀ a S, S ⊂ A.charity → F.feasible a S → q * I.value a S ≤ I.value a (A a)

def StrongFEFx (q : ℝ) (A : Allocation Agent Good) : Prop :=
  F.Valid A ∧ F.AgentsFEFx I q A ∧ F.CharityFEF I q A

theorem StrongFEFx.fefx {q : ℝ} {A : Allocation Agent Good} (h : F.StrongFEFx I q A) :
    F.FEFx I q A := ⟨h.1, h.2.1, fun a S hS hF => h.2.2 a S hS.subset hF⟩

theorem ofInstance_fefx (q : ℝ) (A : Allocation Agent Good) :
    (ofInstance I).FEFx I q A ↔ A.ApproxFEFx I q := Iff.rfl

theorem empty_valid : F.Valid (Allocation.empty : Allocation Agent Good) :=
  ⟨F.empty, fun _ _ _ => Finset.disjoint_empty_left _⟩

theorem empty_agents (q : ℝ) : F.AgentsFEFx I q (Allocation.empty : Allocation Agent Good) := by
  intro a b S hS _
  exact False.elim (Finset.not_ssubset_empty S hS)

theorem replace_valid {A : Allocation Agent Good} {k : Agent} {T : Finset Good}
    (hA : F.Valid A) (hT : T ⊆ A.charity) (hF : F.feasible k T) :
    F.Valid (A.replace k T) := by
  constructor
  · intro a
    by_cases h : a = k
    · subst a; simpa using hF
    · simpa [Allocation.replace_other A T h] using hA.1 a
  · intro a b hab
    by_cases ha : a = k
    · subst a
      have hb : b ≠ k := Ne.symm hab
      simp only [Allocation.replace_same, Allocation.replace_other A T hb]
      exact (A.disjoint_charity b).mono_left hT
    · by_cases hb : b = k
      · subst b
        simp only [Allocation.replace_other A T ha, Allocation.replace_same]
        exact ((A.disjoint_charity a).mono_left hT).symm
      · simpa only [Allocation.replace_other A T ha, Allocation.replace_other A T hb] using hA.2 a b hab

/-- The standard weighted-independent-set oracle when `F` comes from matroids. -/
structure Oracle where
  choose : Agent → Finset Good → Finset Good
  subset : ∀ a T, choose a T ⊆ T
  feasible : ∀ a T, F.feasible a (choose a T)
  optimal : ∀ a T S, S ⊆ T → F.feasible a S → I.value a S ≤ I.value a (choose a T)

theorem exists_optimal (a : Agent) (T : Finset Good) :
    ∃ S ⊆ T, F.feasible a S ∧ ∀ U ⊆ T, F.feasible a U → I.value a U ≤ I.value a S := by
  classical
  let C := T.powerset.filter (F.feasible a)
  have hC : C.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨by simp, F.empty a⟩⟩
  obtain ⟨S, hS, hmax⟩ := C.exists_max_image (I.value a) hC
  have hs := Finset.mem_filter.mp hS
  refine ⟨S, Finset.mem_powerset.mp hs.1, hs.2, ?_⟩
  intro U hUT hU
  exact hmax U (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUT, hU⟩)

/-- Existence of an exact oracle by finite maximization; no efficiency is claimed here. -/
noncomputable def exactOracle : F.Oracle I where
  choose a T := Classical.choose (F.exists_optimal I a T)
  subset a T := (Classical.choose_spec (F.exists_optimal I a T)).1
  feasible a T := (Classical.choose_spec (F.exists_optimal I a T)).2.1
  optimal a T := (Classical.choose_spec (F.exists_optimal I a T)).2.2

def Envied (K : F.Oracle I) (q : ℝ) (A : Allocation Agent Good) (T : Finset Good) : Prop :=
  ∃ a, I.value a (A a) < q * I.value a (K.choose a T)

def MinimalCertificate (q : ℝ) (A : Allocation Agent Good) (T : Finset Good) (k : Agent) : Prop :=
  F.feasible k T ∧ I.value k (A k) < q * I.value k T ∧
    ∀ a S, S ⊂ T → F.feasible a S → q * I.value a S ≤ I.value a (A a)

theorem minimal_of_stop (K : F.Oracle I) {q : ℝ} (hq : 0 ≤ q)
    (A : Allocation Agent Good) {R : Finset Good} {k : Agent}
    (hk : I.value k (A k) < q * I.value k (K.choose k R))
    (hstop : ∀ g ∈ R, ¬ F.Envied I K q A (R.erase g)) :
    F.MinimalCertificate I q A (K.choose k R) k := by
  refine ⟨K.feasible k R, hk, ?_⟩
  intro a S hS hF
  have hSR : S ⊂ R := lt_of_lt_of_le hS (K.subset k R)
  obtain ⟨g, hg, hSg⟩ := Finset.ssubset_iff_exists_subset_erase.mp hSR
  have hno : q * I.value a (K.choose a (R.erase g)) ≤ I.value a (A a) := by
    apply le_of_not_gt
    intro h
    exact hstop g hg ⟨a, h⟩
  exact (mul_le_mul_of_nonneg_left (K.optimal a _ S hSg hF) hq).trans hno

theorem MinimalCertificate.improves {q : ℝ} (hq : q ≤ 1)
    {A : Allocation Agent Good} {T : Finset Good} {k : Agent}
    (h : F.MinimalCertificate I q A T k) : I.value k (A k) < I.value k T :=
  h.2.1.trans_le (mul_le_of_le_one_left (I.value_nonneg k T) hq)

theorem replace_agents {q : ℝ} (hq : q ≤ 1) {A : Allocation Agent Good}
    {T : Finset Good} {k : Agent} (hA : F.AgentsFEFx I q A)
    (hT : F.MinimalCertificate I q A T k) : F.AgentsFEFx I q (A.replace k T) := by
  intro a b S hS hF
  apply le_trans _ (A.value_le_replace I (hT.improves F I hq).le a)
  by_cases hb : b = k
  · subst b
    simp only [Allocation.replace_same] at hS
    exact hT.2.2 a S hS hF
  · rw [Allocation.replace_other A T hb] at hS
    exact hA a b S hS hF

theorem terminal_charity (K : F.Oracle I) {q : ℝ} (hq : 0 ≤ q)
    (A : Allocation Agent Good) (hstop : ¬ F.Envied I K q A A.charity) :
    F.CharityFEF I q A := by
  intro a S hS hF
  have hno : q * I.value a (K.choose a A.charity) ≤ I.value a (A a) := by
    apply le_of_not_gt
    exact fun h => hstop ⟨a, h⟩
  exact (mul_le_mul_of_nonneg_left (K.optimal a _ S hS hF) hq).trans hno

structure MinimalResult (q : ℝ) (A : Allocation Agent Good) (C : Finset Good) where
  bundle : Finset Good
  agent : Agent
  subset : bundle ⊆ C
  certificate : F.MinimalCertificate I q A bundle agent
  queries : ℕ
  query_bound : queries ≤ (Fintype.card Agent + 1) * (C.card + 1) ^ 2

noncomputable def findMinimal (K : F.Oracle I) (q : ℝ) (hq : 0 ≤ q)
    (A : Allocation Agent Good) (C : Finset Good) (hC : F.Envied I K q A C) :
    F.MinimalResult I q A C := by
  classical
  let D := FiniteDeletion.run (F.Envied I K q A) C hC
  let k := Classical.choose D.holds
  have hk := Classical.choose_spec D.holds
  refine ⟨K.choose k D.bundle, k, (K.subset k _).trans D.subset,
    F.minimal_of_stop I K hq A hk D.stop,
    Fintype.card Agent * (D.queries + 1) + 1, ?_⟩
  have hs : D.queries + 1 ≤ (C.card + 1) ^ 2 := by
    nlinarith only [D.query_bound, Nat.zero_le C.card]
  have hm := Nat.mul_le_mul_left (Fintype.card Agent) hs
  nlinarith only [hm, Nat.zero_le C.card]

def Step (q : ℝ) (A B : Allocation Agent Good) : Prop :=
  ∃ k T, T ⊆ A.charity ∧ F.MinimalCertificate I q A T k ∧ B = A.replace k T

def callsPerIteration (_F : FeasibleFamily Agent Good) : ℕ :=
  (Fintype.card Agent + 1) * (1 + (Fintype.card Good + 1) ^ 2)

structure Result (q : ℝ) (A : Allocation Agent Good) where
  allocation : Allocation Agent Good
  iterations : ℕ
  trace : Run (F.Step I q) A allocation iterations
  fair : F.StrongFEFx I q allocation
  queries : ℕ
  query_bound : queries ≤ (iterations + 1) * F.callsPerIteration

/-- The swapping algorithm, relative to an exact feasible-subset oracle. -/
noncomputable def compute (K : F.Oracle I) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (A : Allocation Agent Good) (hA : F.Valid A) (hEF : F.AgentsFEFx I q A) : F.Result I q A := by
  classical
  by_cases henvy : F.Envied I K q A A.charity
  · let M := F.findMinimal I K q hq₀ A A.charity henvy
    have hvalid := F.replace_valid hA M.subset M.certificate.1
    have hfair := F.replace_agents I hq₁ hEF M.certificate
    let R := compute K q hq₀ hq₁ (A.replace M.agent M.bundle) hvalid hfair
    refine ⟨R.allocation, R.iterations + 1,
      Run.cons ⟨M.agent, M.bundle, M.subset, M.certificate, rfl⟩ R.trace, R.fair,
      Fintype.card Agent + M.queries + R.queries, ?_⟩
    have hm : M.queries ≤ (Fintype.card Agent + 1) * (Fintype.card Good + 1) ^ 2 := by
      apply M.query_bound.trans
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (Nat.add_le_add_right (Finset.card_le_univ A.charity) 1) 2
    have hlocal : Fintype.card Agent + M.queries ≤ F.callsPerIteration := by
      dsimp [callsPerIteration]
      nlinarith only [hm]
    have hq := R.query_bound
    nlinarith only [hlocal, hq]
  · refine ⟨A, 0, Run.refl A, ⟨hA, hEF, F.terminal_charity I K hq₀ A henvy⟩,
      Fintype.card Agent, ?_⟩
    simp only [zero_add, one_mul, callsPerIteration]
    nlinarith only [Nat.zero_le ((Fintype.card Agent + 1) * (Fintype.card Good + 1) ^ 2)]
termination_by Allocation.improvementRank I A
decreasing_by
  apply Allocation.improvementRank_lt
  exact A.welfare_lt_replace I (M.certificate.improves F I hq₁)

noncomputable def algorithm (K : F.Oracle I) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    F.Result I q Allocation.empty :=
  F.compute I K q hq₀ hq₁ Allocation.empty F.empty_valid (F.empty_agents I q)

/-- Existence is independent of the particular feasibility constraints. -/
theorem exists_strongFEFx : ∃ A : Allocation Agent Good, F.StrongFEFx I 1 A := by
  let R := F.algorithm I (F.exactOracle I) 1 (by norm_num) le_rfl
  exact ⟨R.allocation, R.fair⟩

theorem Step.welfare_add_one_le (hint : Allocation.IntegralValues I) {q : ℝ} (hq : q ≤ 1)
    {A B : Allocation Agent Good} (h : F.Step I q A B) : A.welfare I + 1 ≤ B.welfare I := by
  obtain ⟨k, T, _, hT, rfl⟩ := h
  exact Allocation.welfare_add_one_le_replace I hint (hT.improves F I hq)

theorem run_welfare_bound (hint : Allocation.IntegralValues I) {q : ℝ} (hq : q ≤ 1)
    {A B : Allocation Agent Good} {t : ℕ} (h : Run (F.Step I q) A B t) :
    A.welfare I + t ≤ B.welfare I := by
  induction h with
  | refl => simp
  | cons hs _ ih =>
    have hp := hs.welfare_add_one_le F I hint hq
    push_cast
    linarith

/-- The pseudo-polynomial iteration bound, including the exact case `q = 1`. -/
theorem algorithm_iterations_le (hint : Allocation.IntegralValues I)
    (K : F.Oracle I) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ((F.algorithm I K q hq₀ hq₁).iterations : ℝ) ≤ ∑ a, I.value a Finset.univ := by
  have h := F.run_welfare_bound I hint hq₁ (F.algorithm I K q hq₀ hq₁).trace
  simp only [Allocation.empty_welfare, zero_add] at h
  exact h.trans ((F.algorithm I K q hq₀ hq₁).allocation.welfare_le I)

end FeasibleFamily

end GeneralizedAssignment
