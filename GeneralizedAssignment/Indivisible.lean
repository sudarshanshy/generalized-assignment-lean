import GeneralizedAssignment.Basic

set_option linter.unusedSectionVars false

/-!
# Minimal envied bundles and exact FEFx

Definition 7, Lemmas 7–9, and the existence assertion of Theorem 2.
The proof works for real valuations: finiteness of the allocation space
replaces the integer welfare argument used in the paper.
-/

open scoped BigOperators

namespace GeneralizedAssignment.Allocation

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]
variable (A : Allocation Agent Good) (I : Instance Agent Good)

/-- Every envied set contains an inclusion-minimal envied set (Definition 7). -/
theorem exists_minimal_envied {C : Finset Good} (hC : A.Envied I C) :
    ∃ T ⊆ C, A.MinimalEnvied I T := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hmin : ∀ S, S ⊂ C → ¬ A.Envied I S
    · exact ⟨C, Finset.Subset.refl _, hC, hmin⟩
    · push Not at hmin
      obtain ⟨S, hSC, hS⟩ := hmin
      obtain ⟨T, hTS, hT⟩ := ih S hSC hS
      exact ⟨T, hTS.trans hSC.subset, hT⟩

/-- The envying agent can receive the *whole* minimal set feasibly. -/
theorem MinimalEnvied.witness {T : Finset Good} (h : A.MinimalEnvied I T) :
    ∃ k, I.Feasible k T ∧ I.value k (A k) < I.value k T := by
  obtain ⟨k, S, hST, hF, hV⟩ := h.1
  have hEq : S = T := by
    by_contra hne
    exact h.2 S (Finset.ssubset_iff_subset_ne.mpr ⟨hST, hne⟩)
      ⟨k, S, Finset.Subset.refl _, hF, hV⟩
  subst S
  exact ⟨k, hF, hV⟩

/-- The whole minimal bundle is feasible for every agent that envies it. -/
theorem MinimalEnvied.envier {T : Finset Good} {k : Agent}
    (h : A.MinimalEnvied I T) (hk : A.Envies I k T) :
    I.Feasible k T ∧ I.value k (A k) < I.value k T := by
  obtain ⟨S, hST, hF, hV⟩ := hk
  have hEq : S = T := by
    by_contra hne
    exact h.2 S (Finset.ssubset_iff_subset_ne.mpr ⟨hST, hne⟩)
      ⟨k, S, Finset.Subset.refl _, hF, hV⟩
  subst S
  exact ⟨hF, hV⟩

theorem MinimalEnvied.proper_value_le {T S : Finset Good}
    (h : A.MinimalEnvied I T) (hST : S ⊂ T) (a : Agent)
    (hF : I.Feasible a S) : I.value a S ≤ I.value a (A a) := by
  by_contra hV
  exact h.2 S hST ⟨a, S, Finset.Subset.refl _, hF, lt_of_not_ge hV⟩

/-- The stopping test in Algorithm 3 suffices to establish minimality. -/
theorem minimalEnvied_of_no_erase {T : Finset Good}
    (hT : A.Envied I T)
    (hstop : ∀ g ∈ T, ¬ A.Envied I (T.erase g)) : A.MinimalEnvied I T := by
  refine ⟨hT, ?_⟩
  intro S hST hS
  obtain ⟨g, hg, hSg⟩ := Finset.ssubset_iff_exists_subset_erase.mp hST
  obtain ⟨a, ha⟩ := hS
  exact hstop g hg ⟨a, ha.mono A I hSg⟩

/-- The update in Algorithms 2 and 4; the old bundle returns to charity. -/
def replace (k : Agent) (T : Finset Good) : Allocation Agent Good :=
  Function.update A k T

@[simp] theorem replace_same (k : Agent) (T : Finset Good) : A.replace k T k = T := by
  simp [replace]

@[simp] theorem replace_other {k a : Agent} (T : Finset Good) (h : a ≠ k) :
    A.replace k T a = A a := by simp [replace, h]

theorem replace_valid {k : Agent} {T : Finset Good}
    (hA : A.Valid I) (hT : T ⊆ A.charity) (hF : I.Feasible k T) :
    (A.replace k T).Valid I := by
  constructor
  · intro a
    by_cases h : a = k
    · subst a; simpa using hF
    · simpa [replace_other A T h] using hA.1 a
  · intro a b hab
    by_cases ha : a = k
    · subst a
      have hb : b ≠ k := Ne.symm hab
      simp only [replace_same, replace_other A T hb]
      exact (A.disjoint_charity b).mono_left hT
    · by_cases hb : b = k
      · subst b
        simp only [replace_other A T ha, replace_same]
        exact ((A.disjoint_charity a).mono_left hT).symm
      · simpa only [replace_other A T ha, replace_other A T hb] using hA.2 a b hab

theorem value_le_replace {k : Agent} {T : Finset Good}
    (hV : I.value k (A k) ≤ I.value k T) (a : Agent) :
    I.value a (A a) ≤ I.value a (A.replace k T a) := by
  by_cases h : a = k
  · subst a; simpa using hV
  · simp [replace_other A T h]

/-- Lemma 7: swapping in a minimal envied set preserves inter-agent FEFx. -/
theorem replace_agentsFEFx {k : Agent} {T : Finset Good}
    (hA : A.AgentsFEFx I) (hT : A.MinimalEnvied I T)
    (hV : I.value k (A k) ≤ I.value k T) : (A.replace k T).AgentsFEFx I := by
  intro a b S hS hF
  apply le_trans _ (A.value_le_replace I hV a)
  by_cases hb : b = k
  · subst b
    simp only [replace_same] at hS
    exact hT.proper_value_le A I hS a hF
  · rw [replace_other A T hb] at hS
    exact hA a b S hS hF

/-- Every Algorithm 2 update strictly increases total welfare. -/
theorem welfare_lt_replace {k : Agent} {T : Finset Good}
    (hV : I.value k (A k) < I.value k T) :
    A.welfare I < (A.replace k T).welfare I := by
  apply Finset.sum_lt_sum
  · intro a _
    exact A.value_le_replace I hV.le a
  · exact ⟨k, Finset.mem_univ _, by simpa using hV⟩

/-- The one-step improvement underlying Algorithm 2. -/
theorem improve {C : Finset Good} (hA : A.Valid I) (hEF : A.AgentsFEFx I)
    (hC : C ⊆ A.charity) (henvy : A.Envied I C) :
    ∃ A' : Allocation Agent Good,
      A'.Valid I ∧ A'.AgentsFEFx I ∧ A.welfare I < A'.welfare I := by
  obtain ⟨T, hTC, hmin⟩ := A.exists_minimal_envied I henvy
  obtain ⟨k, hF, hV⟩ := hmin.witness A I
  exact ⟨A.replace k T, A.replace_valid I hA (hTC.trans hC) hF,
    A.replace_agentsFEFx I hEF hmin hV.le, A.welfare_lt_replace I hV⟩

/-- Theorem 2, strengthened to full FEF towards charity.

Choose a welfare maximizer among the finite set of feasible allocations
that are FEFx between agents. If charity were envied, `improve` would
contradict maximality. This is also a termination argument for Algorithm 2.
-/
theorem exists_strongFEFx : ∃ A : Allocation Agent Good, A.StrongFEFx I := by
  classical
  let candidates : Finset (Allocation Agent Good) :=
    Finset.univ.filter fun A => A.Valid I ∧ A.AgentsFEFx I
  have hne : candidates.Nonempty := by
    refine ⟨empty, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨empty_valid I, empty_agentsFEFx I⟩
  obtain ⟨A, hA, hmax⟩ := candidates.exists_max_image (fun A => A.welfare I) hne
  have hA' := (Finset.mem_filter.mp hA).2
  refine ⟨A, hA'.1, hA'.2, (A.charityFEF_iff I).mpr ?_⟩
  intro henvy
  obtain ⟨A', hvalid, hEF, hlt⟩ :=
    A.improve I hA'.1 hA'.2 (Finset.Subset.refl _) henvy
  have hle := hmax A' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalid, hEF⟩)
  exact (not_lt_of_ge hle) hlt

/-- Theorem 2 (the paper's stated existential guarantee). -/
theorem exists_fefx : ∃ A : Allocation Agent Good, A.FEFx I := by
  obtain ⟨A, hA⟩ := exists_strongFEFx I
  exact ⟨A, hA.fefx A I⟩

end GeneralizedAssignment.Allocation
