import GeneralizedAssignment.LinearPrograms

set_option linter.unusedSectionVars false

/-!
# The paper's rank-based density domination property

Definition 4 is stated with a budget sum over internal and edge goods.
For positive sizes, feasibility forces all assignments outside that
prefix to be zero. This connects the literal definition to the LP and
to the cutoff certificate used in the analytic proof of Lemma 2.
-/

open scoped BigOperators

namespace GeneralizedAssignment.Ranking

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good] {m : ℕ}
variable (π : Ranking Agent Good m) (I : Instance Agent Good)

theorem mem_prefix (τ : Agent → ℕ) (a : Agent) (g : Good) :
    g ∈ π.internalGoods τ a ∪ π.edgeGoods τ a ↔ (π a g).val ≤ τ a := by
  simp only [Finset.mem_union, internalGoods, edgeGoods, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

/-- Definition 4, retaining the restricted budget sum and existential thresholds. -/
structure DensityDomination (x : FractionalAllocation Agent Good) : Prop where
  valid : x.Valid I
  witness : ∃ τ : Agent → ℕ, (∀ a, τ a ≤ m) ∧
    (∀ a b g, (π a g).val < τ a → x b g ≤ x a g) ∧
    (∀ a, (∑ g ∈ π.internalGoods τ a ∪ π.edgeGoods τ a, x a g * I.size a g) = I.budget a) ∧
    (∀ a g, (π a g).val < τ a → ∑ b, x b g = 1)

theorem prefix_tight_implies_tight {x : FractionalAllocation Agent Good}
    (hx : x.Valid I) {τ : Agent → ℕ}
    (htight : ∀ a, (∑ g ∈ π.internalGoods τ a ∪ π.edgeGoods τ a,
      x a g * I.size a g) = I.budget a) (a : Agent) : I.fweight a (x a) = I.budget a := by
  have hsum : (∑ g ∈ π.internalGoods τ a ∪ π.edgeGoods τ a, x a g * I.size a g) ≤
      I.fweight a (x a) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun g _ _ => mul_nonneg (hx.1 a g) (I.size_nonneg a g))
  rw [htight] at hsum
  exact le_antisymm (hx.2.2 a) hsum

theorem prefix_tight_implies_support {x : FractionalAllocation Agent Good}
    (hx : x.Valid I) (hsize : ∀ a g, 0 < I.size a g) {τ : Agent → ℕ}
    (htight : ∀ a, (∑ g ∈ π.internalGoods τ a ∪ π.edgeGoods τ a,
      x a g * I.size a g) = I.budget a) :
    ∀ a g, τ a < (π a g).val → x a g = 0 := by
  intro a g hg
  have hout : g ∉ π.internalGoods τ a ∪ π.edgeGoods τ a := by
    rw [π.mem_prefix]
    omega
  have hsum : (∑ h ∈ insert g (π.internalGoods τ a ∪ π.edgeGoods τ a), x a h * I.size a h) ≤
      I.fweight a (x a) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun h _ _ => mul_nonneg (hx.1 a h) (I.size_nonneg a h))
  rw [Finset.sum_insert hout, htight] at hsum
  have hb := hx.2.2 a
  have hn := hx.1 a g
  have hp := hsize a g
  nlinarith

theorem DensityDomination.exists_lp1 {x : FractionalAllocation Agent Good}
    (h : π.DensityDomination I x) (hsize : ∀ a g, 0 < I.size a g) :
    ∃ τ, (∀ a, τ a ≤ m) ∧ π.LP1 I τ x := by
  obtain ⟨τ, hτ, hdom, htight, hfull⟩ := h.witness
  refine ⟨τ, hτ, ⟨⟨h.valid, ?_, hdom, hfull⟩, ?_⟩⟩
  · exact π.prefix_tight_implies_support I h.valid hsize htight
  · exact π.prefix_tight_implies_tight I h.valid htight

/-- Lemma 2 for the literal rank-based Definition 4. -/
theorem DensityDomination.fef {x : FractionalAllocation Agent Good}
    (h : π.DensityDomination I x) (hsize : ∀ a g, 0 < I.size a g) (hsorted : π.Sorted I) :
    x.FEF I := by
  obtain ⟨τ, _, hLP⟩ := h.exists_lp1 π I hsize
  exact hLP.fef hsize hsorted

/-- Proposition 3 for the literal rank-based Definition 4. -/
theorem LP1.densityDomination {τ : Agent → ℕ} {x : FractionalAllocation Agent Good}
    (h : π.LP1 I τ x) (hτ : ∀ a, τ a ≤ m) : π.DensityDomination I x := by
  refine ⟨h.valid, τ, hτ, h.dominates, ?_, h.complete⟩
  intro a
  have heq : (∑ g ∈ π.internalGoods τ a ∪ π.edgeGoods τ a, x a g * I.size a g) =
      I.fweight a (x a) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro g _ hout
    have hg : τ a < (π a g).val := by
      rw [π.mem_prefix] at hout
      omega
    rw [h.support a g hg]
    simp
  rw [heq, h.tight]

end GeneralizedAssignment.Ranking
