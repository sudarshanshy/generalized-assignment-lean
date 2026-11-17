import GeneralizedAssignment.LinearPrograms

set_option linter.unusedSectionVars false

/-!
# Geometry of the relaxed program

Compactness supplies the edge-assignment maximizer used in Lemma 4.
`LP2.perturb` verifies all the constraints for small affine changes;
in particular, it accounts for tight dominance constraints.
-/

open scoped BigOperators

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good] {m : ℕ}

namespace FractionalAllocation

def shift (x d : FractionalAllocation Agent Good) (t : ℝ) :
    FractionalAllocation Agent Good := fun a g => x a g + t * d a g

@[simp] theorem sum_shift (x d : FractionalAllocation Agent Good) (t : ℝ) (g : Good) :
    ∑ a, shift x d t a g = (∑ a, x a g) + t * ∑ a, d a g := by
  simp [shift, Finset.sum_add_distrib, Finset.mul_sum]

@[simp] theorem fweight_shift (x d : FractionalAllocation Agent Good)
    (I : Instance Agent Good) (t : ℝ) (a : Agent) :
    I.fweight a (shift x d t a) = I.fweight a (x a) + t * I.fweight a (d a) := by
  simp [Instance.fweight, shift, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

def edgeObjective (e : Agent → Good) (x : FractionalAllocation Agent Good) : ℝ :=
  ∑ a, x a (e a)

@[simp] theorem edgeObjective_shift (e : Agent → Good)
    (x d : FractionalAllocation Agent Good) (t : ℝ) :
    edgeObjective e (shift x d t) = edgeObjective e x + t * edgeObjective e d := by
  simp [edgeObjective, shift, Finset.sum_add_distrib, Finset.mul_sum]

end FractionalAllocation

namespace Ranking

open FractionalAllocation

variable {π : Ranking Agent Good m} {I : Instance Agent Good} {τ : Agent → ℕ}
  {x : FractionalAllocation Agent Good}

theorem LP2.perturb (hx : π.LP2 I τ x) (d : FractionalAllocation Agent Good)
    (hnonneg : ∀ a g, x a g = 0 → 0 ≤ d a g)
    (hbudget : ∀ a, I.fweight a (x a) = I.budget a → I.fweight a (d a) ≤ 0)
    (hdom : ∀ a b g, (π a g).val < τ a → x a g = x b g → d b g ≤ d a g)
    (hsupply : ∀ g, (∑ a, x a g) = 1 → ∑ a, d a g ≤ 0)
    (hfull : ∀ a g, (π a g).val < τ a → ∑ b, d b g = 0)
    (hsupport : ∀ a g, τ a < (π a g).val → d a g = 0) :
    ∃ t : ℝ, 0 < t ∧ π.LP2 I τ (shift x d t) := by
  classical
  let Idx := (Agent × Good) ⊕ Agent ⊕ (Agent × Agent × Good) ⊕ Good
  let c : Idx → ℝ
    | .inl (a, g) => -x a g
    | .inr (.inl a) => I.fweight a (x a) - I.budget a
    | .inr (.inr (.inl (a, b, g))) =>
        if (π a g).val < τ a then x b g - x a g else 0
    | .inr (.inr (.inr g)) => (∑ a, x a g) - 1
  let slope : Idx → ℝ
    | .inl (a, g) => -d a g
    | .inr (.inl a) => I.fweight a (d a)
    | .inr (.inr (.inl (a, b, g))) =>
        if (π a g).val < τ a then d b g - d a g else 0
    | .inr (.inr (.inr g)) => ∑ a, d a g
  have hc : ∀ i, c i ≤ 0 := by
    intro i
    rcases i with ⟨a, g⟩ | a | ⟨a, b, g⟩ | g
    · dsimp [c]; exact neg_nonpos.mpr (hx.valid.1 a g)
    · dsimp [c]; exact sub_nonpos.mpr (hx.valid.2.2 a)
    · dsimp [c]; split_ifs with h
      · exact sub_nonpos.mpr (hx.dominates a b g h)
      · exact le_rfl
    · dsimp [c]; exact sub_nonpos.mpr (hx.valid.2.1 g)
  have hd : ∀ i, c i = 0 → slope i ≤ 0 := by
    intro i hi
    rcases i with ⟨a, g⟩ | a | ⟨a, b, g⟩ | g
    · dsimp [c] at hi
      exact neg_nonpos.mpr (hnonneg a g (neg_eq_zero.mp hi))
    · exact hbudget a (sub_eq_zero.mp hi)
    · dsimp [c, slope] at *
      split_ifs at * with h
      · exact sub_nonpos.mpr (hdom a b g h (sub_eq_zero.mp hi).symm)
      · exact le_rfl
    · exact hsupply g (sub_eq_zero.mp hi)
  obtain ⟨t, ht, hineq⟩ := exists_pos_affine_step c slope hc hd
  refine ⟨t, ht, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro a g
      have h := hineq (.inl (a, g))
      dsimp [c, slope, shift] at *
      linarith
    · intro g
      have h := hineq (.inr (.inr (.inr g)))
      dsimp [c, slope] at h
      rw [sum_shift]
      linarith
    · intro a
      have h := hineq (.inr (.inl a))
      dsimp [c, slope] at h
      rw [fweight_shift]
      linarith
  · intro a g hg
    simp [shift, hx.support a g hg, hsupport a g hg]
  · intro a b g hg
    have h := hineq (.inr (.inr (.inl (a, b, g))))
    simp only [c, slope, if_pos hg] at h
    dsimp [shift]
    linarith
  · intro a g hg
    rw [sum_shift, hx.complete a g hg, hfull a g hg]
    ring

/-- A closed bounded polytope of fractional allocations. -/
theorem lp2_isCompact (π : Ranking Agent Good m) (I : Instance Agent Good)
    (τ : Agent → ℕ) : IsCompact {x | π.LP2 I τ x} := by
  have hc : IsClosed {x : FractionalAllocation Agent Good | π.LP2 I τ x} := by
    have heq : {x : FractionalAllocation Agent Good | π.LP2 I τ x} =
        {x | (∀ a g, 0 ≤ x a g) ∧ (∀ g, ∑ a, x a g ≤ 1) ∧
          (∀ a, I.fweight a (x a) ≤ I.budget a) ∧
          (∀ a g, τ a < (π a g).val → x a g = 0) ∧
          (∀ a b g, (π a g).val < τ a → x b g ≤ x a g) ∧
          (∀ a g, (π a g).val < τ a → ∑ b, x b g = 1)} := by
      ext x
      constructor
      · intro h
        exact ⟨h.valid.1, h.valid.2.1, h.valid.2.2, h.support, h.dominates, h.complete⟩
      · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
        exact ⟨⟨h₁, h₂, h₃⟩, h₄, h₅, h₆⟩
    rw [heq]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    repeat' apply IsClosed.inter
    · exact isClosed_iInter fun a => isClosed_iInter fun g =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun g => isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun a => isClosed_le (by unfold Instance.fweight; fun_prop)
        continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun g => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun g =>
        isClosed_iInter fun _ => isClosed_le (by fun_prop) (by fun_prop)
    · exact isClosed_iInter fun a => isClosed_iInter fun g => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : FractionalAllocation Agent Good) 1)).of_isClosed_subset hc
  intro x hx
  constructor
  · intro a g; exact hx.valid.1 a g
  · intro a g; exact hx.valid.le_one x I a g

/-- The maximizer invoked at the start of Lemma 4 exists. -/
theorem exists_edge_maximizer (π : Ranking Agent Good m) (I : Instance Agent Good)
    (τ : Agent → ℕ) (e : Agent → Good) (h : ∃ x, π.LP2 I τ x) :
    ∃ x, π.LP2 I τ x ∧ ∀ y, π.LP2 I τ y → edgeObjective e y ≤ edgeObjective e x := by
  have hc : Continuous (edgeObjective e : FractionalAllocation Agent Good → ℝ) := by
    unfold edgeObjective
    fun_prop
  exact (lp2_isCompact π I τ).exists_isMaxOn h hc.continuousOn

end Ranking

end GeneralizedAssignment
