import GeneralizedAssignment.Fractional
import GeneralizedAssignment.AffinePerturbation
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

set_option linter.unusedSectionVars false

/-!
# The two linear programs

Definitions 3–6 and Proposition 3. Thresholds are zero-based:
`τ a` here is `τ_a - 1` in the paper. Thus internal goods have rank
strictly below `τ a`, and the edge good has rank `τ a`.

The support constraint lets us sum the budget over all goods, instead of
only internal and edge goods. Bounds `x ≤ 1` follow from nonnegativity
and unit supply, rather than being repeated as separate constraints.
-/

open scoped BigOperators

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good] {m : ℕ}

/-- A bijective ranking of the goods for each agent, starting at zero. -/
abbrev Ranking (Agent Good : Type*) (m : ℕ) := Agent → Good ≃ Fin m

namespace Ranking

variable (π : Ranking Agent Good m)

def internalGoods (τ : Agent → ℕ) (a : Agent) : Finset Good :=
  Finset.univ.filter fun g => (π a g).val < τ a

def edgeGoods (τ : Agent → ℕ) (a : Agent) : Finset Good :=
  Finset.univ.filter fun g => (π a g).val = τ a

def Sorted (I : Instance Agent Good) : Prop :=
  ∀ a g h, π a g ≤ π a h → I.density a h ≤ I.density a g

/-- Definition 6: the relaxed program. -/
structure LP2 (I : Instance Agent Good) (τ : Agent → ℕ)
    (x : FractionalAllocation Agent Good) : Prop where
  valid : x.Valid I
  support : ∀ a g, τ a < (π a g).val → x a g = 0
  dominates : ∀ a b g, (π a g).val < τ a → x b g ≤ x a g
  complete : ∀ a g, (π a g).val < τ a → ∑ b, x b g = 1

/-- Definition 5: the original program, with all budgets tight. -/
structure LP1 (I : Instance Agent Good) (τ : Agent → ℕ)
    (x : FractionalAllocation Agent Good) : Prop extends π.LP2 I τ x where
  tight : ∀ a, I.fweight a (x a) = I.budget a

variable {π} {I : Instance Agent Good} {τ : Agent → ℕ}
  {x : FractionalAllocation Agent Good}

/-- Proposition 3 and Lemma 2, using a density-ordered ranking. -/
theorem LP1.densityCertificate (hx : π.LP1 I τ x)
    (hpos : ∀ a g, 0 < I.size a g) (hsorted : π.Sorted I) :
    x.DensityCertificate I := by
  classical
  let r : Agent → ℝ := fun a =>
    if h : τ a < m then I.density a ((π a).symm ⟨τ a, h⟩) else 0
  have hr : ∀ a, 0 ≤ r a := by
    intro a
    dsimp [r]
    split_ifs
    · exact I.density_nonneg _ _
    · exact le_rfl
  have above_internal : ∀ a g, r a * I.size a g < I.val a g →
      (π a g).val < τ a := by
    intro a g hg
    by_cases ht : τ a < m
    · by_contra hlt
      have hle : (⟨τ a, ht⟩ : Fin m) ≤ π a g := Nat.le_of_not_gt hlt
      have hd := hsorted a ((π a).symm ⟨τ a, ht⟩) g (by simpa using hle)
      have hval : I.val a g ≤ r a * I.size a g := by
        apply (div_le_iff₀ (hpos a g)).mp
        simpa [Instance.density, r, ht] using hd
      linarith
    · exact lt_of_lt_of_le (π a g).isLt (Nat.le_of_not_gt ht)
  refine ⟨hx.valid, hx.tight, r, hr, ?_, ?_, ?_⟩
  · intro a g hxg
    by_cases ht : τ a < m
    · have hle : (π a g).val ≤ τ a := by
        by_contra hle
        have hz := hx.support a g (Nat.lt_of_not_ge hle)
        linarith
      have hd := hsorted a g ((π a).symm ⟨τ a, ht⟩) (by simpa using (show π a g ≤ (⟨τ a, ht⟩ : Fin m) from hle))
      apply (le_div_iff₀ (hpos a g)).mp
      simpa [r, ht, Instance.density] using hd
    · simpa [r, ht] using I.val_nonneg a g
  · intro a b g hg
    exact hx.dominates a b g (above_internal a g hg)
  · intro a g hg
    exact hx.complete a g (above_internal a g hg)

theorem LP1.fef (hx : π.LP1 I τ x)
    (hpos : ∀ a g, 0 < I.size a g) (hsorted : π.Sorted I) : x.FEF I :=
  (hx.densityCertificate hpos hsorted).fef x I

/-- The all-zero point witnesses feasibility at the initial thresholds. -/
theorem lp2_initial (I : Instance Agent Good) (π : Ranking Agent Good m) :
    π.LP2 I (fun _ => 0) (fun _ _ => 0) := by
  refine ⟨⟨by simp, by simp, ?_⟩, by simp, ?_, ?_⟩
  · intro a
    simpa [Instance.fweight] using I.budget_nonneg a
  · intro a b g h; omega
  · intro a g h; omega

/-- The final step of Lemma 4: a fully allocated maximal edge can become internal. -/
theorem LP2.promote (hx : π.LP2 I τ x) {k : Agent} {g : Good}
    (hedge : (π k g).val = τ k) (hdom : ∀ b, x b g ≤ x k g)
    (hfull : ∑ b, x b g = 1) :
    π.LP2 I (Function.update τ k (τ k + 1)) x := by
  refine ⟨hx.valid, ?_, ?_, ?_⟩
  · intro a h hs
    by_cases ha : a = k
    · subst a
      simp only [Function.update_self] at hs
      exact hx.support k h (by omega)
    · simp only [Function.update_of_ne ha] at hs
      exact hx.support a h hs
  · intro a b h hi
    by_cases ha : a = k
    · subst a
      simp only [Function.update_self] at hi
      by_cases hold : (π k h).val < τ k
      · exact hx.dominates k b h hold
      · have hEq : h = g := (π k).injective (Fin.ext (by omega))
        subst h
        exact hdom b
    · simp only [Function.update_of_ne ha] at hi
      exact hx.dominates a b h hi
  · intro a h hi
    by_cases ha : a = k
    · subst a
      simp only [Function.update_self] at hi
      by_cases hold : (π k h).val < τ k
      · exact hx.complete k h hold
      · have hEq : h = g := (π k).injective (Fin.ext (by omega))
        subst h
        exact hfull
    · simp only [Function.update_of_ne ha] at hi
      exact hx.complete a h hi

end Ranking

end GeneralizedAssignment
