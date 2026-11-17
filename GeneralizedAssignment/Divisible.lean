import GeneralizedAssignment.LPIncongruity
import GeneralizedAssignment.DummyGood
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

set_option linter.unusedSectionVars false

/-!
# Existence of fractional FEF allocations

The existential part of Theorem 1: the initial relaxed program is
feasible, Lemma 4 advances thresholds, and the fictional good prevents
an infinite sequence of advances. Finite maximization packages this
termination argument without postulating a linear-program solver.
-/

open scoped BigOperators

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

/-- Finite goods admit density-ordered rankings; an arbitrary finite index breaks ties. -/
theorem exists_sortedRanking (I : Instance Agent Good) :
    ∃ π : Ranking Agent Good (Fintype.card Good), π.Sorted I := by
  classical
  have h : ∀ a, ∃ r : Good ≃ Fin (Fintype.card Good),
      ∀ g h, r g ≤ r h → I.density a h ≤ I.density a g := by
    intro a
    let key : Good → ℝ ×ₗ Fin (Fintype.card Good) :=
      fun g => toLex (-I.density a g, Fintype.equivFin Good g)
    have hinj : Function.Injective key := by
      intro g h heq
      apply (Fintype.equivFin Good).injective
      exact congrArg (fun p : ℝ ×ₗ Fin (Fintype.card Good) => (ofLex p).2) heq
    let : LinearOrder Good := LinearOrder.lift' key hinj
    let e : Fin (Fintype.card Good) ≃o Good := monoEquivOfFin Good rfl
    refine ⟨e.symm.toEquiv, ?_⟩
    intro g h hgh
    have hle : g ≤ h := e.symm.le_iff_le.mp hgh
    have hkey : key g ≤ key h := hle
    have hf := Prod.Lex.monotone_fst (key g) (key h) hkey
    change -I.density a g ≤ -I.density a h at hf
    linarith
  choose π hπ using h
  exact ⟨π, hπ⟩

namespace Ranking

variable {m : ℕ}

/-- Lemma 6: a threshold beyond the last rank would fully allocate a blocked good. -/
theorem lp2_threshold_lt (π : Ranking Agent Good m) (I : Instance Agent Good)
    (d : Good) (hblocked : ∀ x : FractionalAllocation Agent Good,
      x.Valid I → (∑ a, x a d) ≠ 1)
    {τ : Agent → ℕ} {x : FractionalAllocation Agent Good}
    (hx : π.LP2 I τ x) (a : Agent) : τ a < m := by
  by_contra h
  have hint : (π a d).val < τ a := lt_of_lt_of_le (π a d).isLt (Nat.le_of_not_gt h)
  exact hblocked x hx.valid (hx.complete a d hint)

/-- Lemmas 4 and 6 force feasibility of the tight program at some thresholds. -/
theorem exists_lp1 (π : Ranking Agent Good m) (I : Instance Agent Good)
    (d : Good) (hblocked : ∀ x : FractionalAllocation Agent Good,
      x.Valid I → (∑ a, x a d) ≠ 1) :
    ∃ τ x, (∀ a, τ a < m) ∧ π.LP1 I τ x := by
  classical
  let candidates : Finset (Agent → Fin (m + 1)) :=
    Finset.univ.filter fun τ => ∃ x, π.LP2 I (fun a => (τ a).val) x
  have hne : candidates.Nonempty := by
    refine ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨fun _ _ => 0, lp2_initial I π⟩
  obtain ⟨τ, hτmem, hmax⟩ := candidates.exists_max_image
    (fun τ => ∑ a, (τ a).val) hne
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hτmem).2
  have hτ : ∀ a, (τ a).val < m := lp2_threshold_lt π I d hblocked hx
  by_cases hdone : ∃ y, π.LP1 I (fun a => (τ a).val) y
  · obtain ⟨y, hy⟩ := hdone
    exact ⟨fun a => (τ a).val, y, hτ, hy⟩
  · obtain ⟨k, y, hy⟩ := lp_incongruity π I (fun a => (τ a).val) hτ ⟨x, hx⟩ hdone
    let τ' : Agent → Fin (m + 1) := Function.update τ k
      ⟨(τ k).val + 1, by have := hτ k; omega⟩
    have hcast : (fun a => (τ' a).val) = Function.update (fun a => (τ a).val) k ((τ k).val + 1) := by
      funext a
      by_cases ha : a = k <;> simp [τ', ha]
    have hτ'mem : τ' ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, y, ?_⟩
      rw [hcast]
      exact hy
    have hincrease : (∑ a, (τ a).val) < ∑ a, (τ' a).val := by
      apply Finset.sum_lt_sum
      · intro a _
        by_cases ha : a = k
        · subst a; simp [τ']
        · simp [τ', ha]
      · exact ⟨k, Finset.mem_univ _, by simp [τ']⟩
    exact False.elim ((not_lt_of_ge (hmax τ' hτ'mem)) hincrease)

end Ranking

namespace FractionalAllocation

/-- Theorem 1, existential guarantee for strictly positive item sizes.
Values and budgets may be zero. Rational data embed directly into this real model. -/
theorem exists_fef (I : Instance Agent Good) (hsize : ∀ a g, 0 < I.size a g) :
    ∃ x : FractionalAllocation Agent Good, x.FEF I := by
  obtain ⟨π, hπ⟩ := exists_sortedRanking I.withDummy
  obtain ⟨τ, x, _, hx⟩ := π.exists_lp1 I.withDummy none
    (fun x hx => dummy_not_full x I hx)
  have hFEF := hx.fef (I.withDummy_size_pos hsize) hπ
  exact ⟨x.restrict, hFEF.restrict x I⟩

end FractionalAllocation

end GeneralizedAssignment
