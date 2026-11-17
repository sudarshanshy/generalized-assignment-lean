import GeneralizedAssignment.LPGeometry

set_option linter.unusedSectionVars false

/-!
# The LP incongruity lemma

Lemma 4 and Claim 5. Both “sufficiently small” perturbations are checked
using the finite affine perturbation theorem, including all active
dominance constraints.
-/

open scoped BigOperators

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good] {m : ℕ}

namespace FractionalAllocation

/-- Change a single agent-good coordinate. -/
def unit (b : Agent) (g : Good) : FractionalAllocation Agent Good :=
  fun a h => if a = b then if h = g then 1 else 0 else 0

@[simp] theorem sum_unit (b : Agent) (g h : Good) :
    ∑ a, unit b g a h = if h = g then 1 else 0 := by
  classical
  simp [unit]

@[simp] theorem fweight_unit (I : Instance Agent Good) (b a : Agent) (g : Good) :
    I.fweight a (unit b g a) = if a = b then I.size a g else 0 := by
  classical
  by_cases h : a = b <;> simp [Instance.fweight, unit, h]

@[simp] theorem edgeObjective_unit (e : Agent → Good) (b : Agent) (g : Good)
    (he : e b = g) : edgeObjective e (unit b g) = 1 := by
  classical
  simp [edgeObjective, unit, he]

end FractionalAllocation

namespace Ranking

open FractionalAllocation

variable {π : Ranking Agent Good m} {I : Instance Agent Good} {τ : Agent → ℕ}
  {x : FractionalAllocation Agent Good} {e : Agent → Good}

/-- At an edge-objective maximizer, the edge of an agent with slack budget is full. -/
theorem slack_edge_full (hx : π.LP2 I τ x)
    (he : ∀ a, (π a (e a)).val = τ a)
    (hmax : ∀ y, π.LP2 I τ y → edgeObjective e y ≤ edgeObjective e x)
    {b : Agent} (hslack : I.fweight b (x b) < I.budget b) :
    ∑ a, x a (e b) = 1 := by
  classical
  let g := e b
  have hedge : (π b g).val = τ b := he b
  by_contra hne
  have hlt : (∑ a, x a g) < 1 := lt_of_le_of_ne (hx.valid.2.1 g) hne
  have hnotinternal : ∀ a, ¬ (π a g).val < τ a := by
    intro a ha
    have := hx.complete a g ha
    linarith
  obtain ⟨t, ht, hpert⟩ := hx.perturb (unit b g)
    (by intro a h _; simp only [unit]; split_ifs <;> norm_num)
    (by
      intro a ha
      by_cases hab : a = b
      · subst a; linarith
      · simp [fweight_unit, hab])
    (by
      intro a c h hi _
      have hh : h ≠ g := by rintro rfl; exact hnotinternal a hi
      simp [unit, hh])
    (by
      intro h hh
      by_cases hhg : h = g
      · subst h; linarith
      · simp [hhg])
    (by
      intro a h hi
      have hh : h ≠ g := by rintro rfl; exact hnotinternal a hi
      simp [hh])
    (by
      intro a h hs
      by_cases hab : a = b
      · subst a
        have hh : h ≠ g := by intro hh; subst h; omega
        simp [unit, hh]
      · simp [unit, hab])
  have hopt := hmax (shift x (unit b g) t) hpert
  rw [edgeObjective_shift, edgeObjective_unit e b g rfl] at hopt
  linarith

/-- Claim 5: some edge-agent has a largest share of the slack agent's edge good. -/
theorem edge_maximum_exists (hx : π.LP2 I τ x)
    (he : ∀ a, (π a (e a)).val = τ a)
    (hmax : ∀ y, π.LP2 I τ y → edgeObjective e y ≤ edgeObjective e x)
    {b : Agent} (hslack : I.fweight b (x b) < I.budget b)
    (hfull : ∑ a, x a (e b) = 1) :
    ∃ k, (π k (e b)).val = τ k ∧ ∀ a, x a (e b) ≤ x k (e b) := by
  classical
  let g := e b
  have hedge : (π b g).val = τ b := he b
  by_contra hnone
  have noEdgeMax : ∀ k, (π k g).val = τ k → ¬ ∀ a, x a g ≤ x k g := by
    intro k hk hkm
    exact hnone ⟨k, hk, hkm⟩
  obtain ⟨l, _, hl⟩ := Finset.univ.exists_max_image (fun a => x a g)
    ⟨b, Finset.mem_univ _⟩
  have hmaxl : ∀ a, x a g ≤ x l g := fun a => hl a (Finset.mem_univ _)
  have hlpos : 0 < x l g := by
    by_contra h
    have hsum : ∑ a, x a g ≤ 0 := by
      apply Finset.sum_nonpos
      intro a _
      exact (hmaxl a).trans (le_of_not_gt h)
    linarith
  have max_internal : ∀ a, x a g = x l g → (π a g).val < τ a := by
    intro a ha
    have hapos : 0 < x a g := ha.symm ▸ hlpos
    have hle : (π a g).val ≤ τ a := by
      by_contra h
      have := hx.support a g (Nat.lt_of_not_ge h)
      linarith
    have hne : (π a g).val ≠ τ a := by
      intro hEq
      exact noEdgeMax a hEq (fun c => (hmaxl c).trans_eq ha.symm)
    omega
  let F : Finset Agent := Finset.univ.filter fun a => (π a g).val < τ a
  have hF : F.Nonempty := ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, max_internal l rfl⟩⟩
  have hcard : 0 < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
  have hbnot : b ∉ F := by simp [F, hedge]
  have internal_eq : ∀ a ∈ F, x a g = x l g := by
    intro a ha
    exact le_antisymm (hmaxl a) (hx.dominates a l g (Finset.mem_filter.mp ha).2)
  have equal_internal : ∀ a ∈ F, ∀ c, x a g = x c g → c ∈ F := by
    intro a ha c hac
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      max_internal c (hac.symm.trans (internal_eq a ha))⟩
  let coeff : Agent → ℝ := fun a =>
    (if a = b then (F.card : ℝ) else 0) - (if a ∈ F then 1 else 0)
  let d : FractionalAllocation Agent Good := fun a h => if h = g then coeff a else 0
  have coeff_b : coeff b = F.card := by simp [coeff, hbnot]
  have coeff_internal : ∀ a ∈ F, coeff a = -1 := by
    intro a ha
    have hab : a ≠ b := by intro h; subst a; exact hbnot ha
    simp [coeff, hab, ha]
  have coeff_sum : ∑ a, coeff a = 0 := by
    simp [coeff, Finset.sum_sub_distrib]
  have d_sum : ∀ h, ∑ a, d a h = 0 := by
    intro h
    by_cases hh : h = g <;> simp [d, hh, coeff_sum]
  have d_weight : ∀ a, I.fweight a (d a) = coeff a * I.size a g := by
    intro a
    simp [Instance.fweight, d]
  have d_objective : edgeObjective e d = F.card := by
    unfold edgeObjective
    rw [Finset.sum_eq_single b]
    · simp [d, g, coeff_b]
    · intro a _ hab
      by_cases hage : e a = g
      · have hanot : a ∉ F := by
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hage, he a]
          exact Nat.lt_irrefl _
        simp [d, hage, coeff, hab, hanot]
      · simp [d, hage]
    · simp
  obtain ⟨t, ht, hpert⟩ := hx.perturb d
    (by
      intro a h hz
      by_cases hh : h = g
      · subst h
        have hanot : a ∉ F := by
          intro ha
          have := internal_eq a ha
          linarith
        simp only [d, if_pos rfl, coeff, if_neg hanot, sub_zero]
        split_ifs <;> positivity
      · simp [d, hh])
    (by
      intro a htight
      have hab : a ≠ b := by intro h; subst a; linarith
      rw [d_weight]
      apply mul_nonpos_of_nonpos_of_nonneg _ (I.size_nonneg a g)
      simp only [coeff, if_neg hab, zero_sub]
      split_ifs <;> norm_num)
    (by
      intro a c h hi hac
      by_cases hh : h = g
      · subst h
        have ha : a ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        have hc := equal_internal a ha c hac
        simp [d, coeff_internal a ha, coeff_internal c hc]
      · simp [d, hh])
    (by intro h _; exact le_of_eq (d_sum h))
    (by intro a h _; exact d_sum h)
    (by
      intro a h hs
      by_cases hh : h = g
      · subst h
        have hanot : a ∉ F := by
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        have hab : a ≠ b := by intro h; subst a; omega
        simp [d, coeff, hab, hanot]
      · simp [d, hh])
  have hopt := hmax (shift x d t) hpert
  rw [edgeObjective_shift, d_objective] at hopt
  have hprod := mul_pos ht hcard
  linarith

/-- Lemma 4: feasibility of the relaxation can be advanced when tight budgets are impossible. -/
theorem lp_incongruity (π : Ranking Agent Good m) (I : Instance Agent Good)
    (τ : Agent → ℕ) (hτ : ∀ a, τ a < m)
    (hfeas : ∃ x, π.LP2 I τ x) (hnot : ¬ ∃ x, π.LP1 I τ x) :
    ∃ k x, π.LP2 I (Function.update τ k (τ k + 1)) x := by
  classical
  let e : Agent → Good := fun a => (π a).symm ⟨τ a, hτ a⟩
  have he : ∀ a, (π a (e a)).val = τ a := by intro a; simp [e]
  obtain ⟨x, hx, hmax⟩ := exists_edge_maximizer π I τ e hfeas
  have hslack : ∃ b, I.fweight b (x b) < I.budget b := by
    by_contra h
    push Not at h
    apply hnot
    exact ⟨x, hx, fun a => le_antisymm (hx.valid.2.2 a) (h a)⟩
  obtain ⟨b, hb⟩ := hslack
  have hfull := slack_edge_full hx he hmax hb
  obtain ⟨k, hk, hdom⟩ := edge_maximum_exists hx he hmax hb hfull
  exact ⟨k, x, hx.promote hk hdom hfull⟩

end Ranking

end GeneralizedAssignment
