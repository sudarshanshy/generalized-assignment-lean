import GeneralizedAssignment.Divisible
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.unusedSectionVars false

/-!
# Fractional existence when some sizes are zero

The density proof uses positive sizes. This module removes that technical
restriction for the existence theorem: add `δ` to each size and `mδ` to
each budget, take a convergent subsequence of FEF allocations, and pass
the inequalities to the limit. Candidate bundles are intersected
coordinatewise with the approximating bundles before taking limits.
-/

open scoped BigOperators Topology
open Filter

noncomputable section

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

namespace Instance

variable (I : Instance Agent Good)

def regularize (δ : ℝ) (hδ : 0 ≤ δ) : Instance Agent Good where
  val := I.val
  size a g := I.size a g + δ
  budget a := I.budget a + δ * Fintype.card Good
  val_nonneg := I.val_nonneg
  size_nonneg a g := add_nonneg (I.size_nonneg a g) hδ
  budget_nonneg a := add_nonneg (I.budget_nonneg a) (mul_nonneg hδ (Nat.cast_nonneg _))

@[simp] theorem regularize_fvalue (δ : ℝ) (hδ : 0 ≤ δ) (a : Agent) (y : Good → ℝ) :
    (I.regularize δ hδ).fvalue a y = I.fvalue a y := rfl

theorem regularize_fweight (δ : ℝ) (hδ : 0 ≤ δ) (a : Agent) (y : Good → ℝ) :
    (I.regularize δ hδ).fweight a y = I.fweight a y + δ * ∑ g, y g := by
  simp [fweight, regularize, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]

theorem regularize_feasible (δ : ℝ) (hδ : 0 ≤ δ) (a : Agent) {y : Good → ℝ}
    (hy : ∀ g, y g ≤ 1) (hF : I.fweight a y ≤ I.budget a) :
    (I.regularize δ hδ).fweight a y ≤ (I.regularize δ hδ).budget a := by
  have hsum : (∑ g, y g) ≤ (Fintype.card Good : ℝ) := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun g _ => hy g)
  rw [regularize_fweight]
  exact add_le_add hF (mul_le_mul_of_nonneg_left hsum hδ)

theorem continuous_fvalue (a : Agent) : Continuous (I.fvalue a) := by
  unfold fvalue
  fun_prop

theorem continuous_fweight (a : Agent) : Continuous (I.fweight a) := by
  unfold fweight
  fun_prop

end Instance

namespace FractionalAllocation

variable (I : Instance Agent Good)

theorem FEF.of_regularize_limit (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδlim : Tendsto δ atTop (𝓝 0)) (u : ℕ → FractionalAllocation Agent Good)
    (hu : ∀ n, (u n).FEF (I.regularize (δ n) (hδ n)))
    {x : FractionalAllocation Agent Good} (hux : Tendsto u atTop (𝓝 x)) : x.FEF I := by
  have hcoord : ∀ a g, Tendsto (fun n => u n a g) atTop (𝓝 (x a g)) := by
    intro a g
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hux a) g
  have hown : ∀ a, Tendsto (fun n => I.fvalue a (u n a)) atTop (𝓝 (I.fvalue a (x a))) := by
    intro a
    exact ((I.continuous_fvalue a).tendsto (x a)).comp (tendsto_pi_nhds.mp hux a)
  have hvalid : x.Valid I := by
    refine ⟨?_, ?_, ?_⟩
    · intro a g
      exact ge_of_tendsto (hcoord a g) (Eventually.of_forall fun n => (hu n).1.1 a g)
    · intro g
      have hsum : Tendsto (fun n => ∑ a, u n a g) atTop (𝓝 (∑ a, x a g)) :=
        tendsto_finsetSum _ fun a _ => hcoord a g
      exact le_of_tendsto hsum (Eventually.of_forall fun n => (hu n).1.2.1 g)
    · intro a
      have hw : Tendsto (fun n => I.fweight a (u n a)) atTop (𝓝 (I.fweight a (x a))) :=
        ((I.continuous_fweight a).tendsto (x a)).comp (tendsto_pi_nhds.mp hux a)
      have hb : Tendsto (fun n => I.budget a + δ n * Fintype.card Good) atTop (𝓝 (I.budget a)) := by
        simpa using tendsto_const_nhds.add (hδlim.mul_const (Fintype.card Good : ℝ))
      apply le_of_tendsto_of_tendsto hw hb
      apply Eventually.of_forall
      intro n
      have hn := (hu n).1.2.2 a
      rw [I.regularize_fweight] at hn
      have hnonneg : 0 ≤ δ n * ∑ g, u n a g :=
        mul_nonneg (hδ n) (Finset.sum_nonneg fun g _ => (hu n).1.1 a g)
      change I.fweight a (u n a) + δ n * ∑ g, u n a g ≤
        I.budget a + δ n * Fintype.card Good at hn
      linarith
  have hcompare : ∀ (a : Agent) (z : Good → ℝ) (zseq : ℕ → Good → ℝ),
      (∀ n g, 0 ≤ zseq n g) → (∀ n g, zseq n g ≤ 1) →
      Tendsto zseq atTop (𝓝 z) →
      (∀ n y, (∀ g, 0 ≤ y g) → (∀ g, y g ≤ zseq n g) →
        (I.regularize (δ n) (hδ n)).fweight a y ≤ (I.regularize (δ n) (hδ n)).budget a →
        I.fvalue a y ≤ I.fvalue a (u n a)) →
      ∀ y, (∀ g, 0 ≤ y g) → (∀ g, y g ≤ z g) →
        I.fweight a y ≤ I.budget a → I.fvalue a y ≤ I.fvalue a (x a) := by
    intro a z zseq hz0 hz1 hzlim hfair y hy hsub hF
    let yseq : ℕ → Good → ℝ := fun n g => min (y g) (zseq n g)
    have hylim : Tendsto yseq atTop (𝓝 y) := by
      apply tendsto_pi_nhds.mpr
      intro g
      have h := (tendsto_const_nhds (x := y g)).min (tendsto_pi_nhds.mp hzlim g)
      simpa only [min_eq_left (hsub g)] using h
    have hyval : Tendsto (fun n => I.fvalue a (yseq n)) atTop (𝓝 (I.fvalue a y)) :=
      ((I.continuous_fvalue a).tendsto y).comp hylim
    apply le_of_tendsto_of_tendsto hyval (hown a)
    apply Eventually.of_forall
    intro n
    apply hfair n (yseq n)
    · intro g
      exact le_min (hy g) (hz0 n g)
    · intro g
      exact min_le_right _ _
    · apply I.regularize_feasible (δ n) (hδ n) a
      · intro g
        exact (min_le_right _ _).trans (hz1 n g)
      · exact (I.fweight_mono a fun g => min_le_left _ _).trans hF
  refine ⟨hvalid, ?_, ?_⟩
  · intro a b
    apply hcompare a (x b) (fun n => u n b)
    · intro n g
      exact (hu n).1.1 b g
    · intro n g
      exact (hu n).1.le_one (u n) _ b g
    · exact tendsto_pi_nhds.mp hux b
    · intro n y hy hsub hF
      exact (hu n).2.1 a b y hy hsub hF
  · intro a
    apply hcompare a x.charity (fun n => (u n).charity)
    · intro n g
      exact (hu n).1.charity_nonneg (u n) _ g
    · intro n g
      exact (hu n).1.charity_le_one (u n) _ g
    · have hc : Continuous (fun z : FractionalAllocation Agent Good => z.charity) := by
        unfold charity
        fun_prop
      exact (hc.tendsto x).comp hux
    · intro n y hy hsub hF
      exact (hu n).2.2 a y hy hsub hF

/-- Theorem 1's existence conclusion for all nonnegative sizes, including zeros. -/
theorem exists_fef_nonnegative : ∃ x : FractionalAllocation Agent Good, x.FEF I := by
  classical
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex : ∀ n, ∃ u : FractionalAllocation Agent Good,
      u.FEF (I.regularize (δ n) (hδpos n).le) := by
    intro n
    apply exists_fef
    intro a g
    exact add_pos_of_nonneg_of_pos (I.size_nonneg a g) (hδpos n)
  choose u hu using hex
  have hcube : ∀ n, u n ∈ Set.Icc (0 : FractionalAllocation Agent Good) 1 := by
    intro n
    exact ⟨fun a g => (hu n).1.1 a g, fun a g => (hu n).1.le_one (u n) _ a g⟩
  obtain ⟨x, _hx, φ, hφ, hconv⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : FractionalAllocation Agent Good) 1)).tendsto_subseq hcube
  refine ⟨x, FEF.of_regularize_limit I (δ ∘ φ) (fun n => (hδpos (φ n)).le)
    (hδlim.comp hφ.tendsto_atTop) (u ∘ φ) (fun n => hu (φ n)) hconv⟩

end FractionalAllocation

end GeneralizedAssignment
