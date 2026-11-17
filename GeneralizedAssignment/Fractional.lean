import GeneralizedAssignment.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.unusedSectionVars false

/-!
# Fractional allocations and density domination

Definition 1 and the analytic comparison at the heart of Lemma 2.
Fractional bundles are functions to the reals, with all nonnegativity,
supply, and budget requirements stated explicitly.
-/

open scoped BigOperators

noncomputable section

namespace GeneralizedAssignment

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

namespace Instance

variable (I : Instance Agent Good)

def fvalue (a : Agent) (y : Good → ℝ) : ℝ := ∑ g, y g * I.val a g
def fweight (a : Agent) (y : Good → ℝ) : ℝ := ∑ g, y g * I.size a g
def density (a : Agent) (g : Good) : ℝ := I.val a g / I.size a g

theorem density_nonneg (a : Agent) (g : Good) : 0 ≤ I.density a g :=
  div_nonneg (I.val_nonneg a g) (I.size_nonneg a g)

theorem fvalue_nonneg (a : Agent) {y : Good → ℝ} (hy : ∀ g, 0 ≤ y g) :
    0 ≤ I.fvalue a y :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hy g) (I.val_nonneg a g)

theorem fweight_nonneg (a : Agent) {y : Good → ℝ} (hy : ∀ g, 0 ≤ y g) :
    0 ≤ I.fweight a y :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hy g) (I.size_nonneg a g)

theorem fvalue_mono (a : Agent) {x y : Good → ℝ} (h : ∀ g, x g ≤ y g) :
    I.fvalue a x ≤ I.fvalue a y :=
  Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (h g) (I.val_nonneg a g)

theorem fweight_mono (a : Agent) {x y : Good → ℝ} (h : ∀ g, x g ≤ y g) :
    I.fweight a x ≤ I.fweight a y :=
  Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (h g) (I.size_nonneg a g)

/-- The exchange inequality in Lemma 2, written without truncated subtraction.
Goods gained in `y` have value/size at most `r`, and goods lost from `x`
have value/size at least `r`. Since `x` fills the budget, `y` cannot be better.
This formulation also allows zero sizes when the stated inequalities hold. -/
theorem density_comparison (a : Agent) {x y : Good → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hy : ∀ g, 0 ≤ y g)
    (htight : I.fweight a x = I.budget a) (hfeas : I.fweight a y ≤ I.budget a)
    (hsupport : ∀ g, 0 < x g → r * I.size a g ≤ I.val a g)
    (hexcess : ∀ g, x g < y g → I.val a g ≤ r * I.size a g) :
    I.fvalue a y ≤ I.fvalue a x := by
  have hpoint : ∀ g, (y g - x g) * I.val a g ≤
      r * ((y g - x g) * I.size a g) := by
    intro g
    by_cases hxy : x g < y g
    · have := mul_le_mul_of_nonneg_left (hexcess g hxy) (sub_nonneg.mpr hxy.le)
      nlinarith
    · have hyx : y g ≤ x g := le_of_not_gt hxy
      by_cases heq : x g = y g
      · simp [heq]
      · have hx : 0 < x g := lt_of_le_of_lt (hy g) (lt_of_le_of_ne hyx (Ne.symm heq))
        have := mul_le_mul_of_nonpos_left (hsupport g hx) (sub_nonpos.mpr hyx)
        nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun g _ => hpoint g
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  change I.fvalue a y - I.fvalue a x ≤ r * (I.fweight a y - I.fweight a x) at hsum
  have hsize : I.fweight a y - I.fweight a x ≤ 0 := by linarith
  have := mul_nonpos_of_nonneg_of_nonpos hr hsize
  linarith

end Instance

abbrev FractionalAllocation (Agent Good : Type*) := Agent → Good → ℝ

namespace FractionalAllocation

variable (x : FractionalAllocation Agent Good) (I : Instance Agent Good)

def Valid : Prop :=
  (∀ a g, 0 ≤ x a g) ∧ (∀ g, ∑ a, x a g ≤ 1) ∧
    ∀ a, I.fweight a (x a) ≤ I.budget a

def charity (g : Good) : ℝ := 1 - ∑ a, x a g

theorem Valid.le_one (hx : x.Valid I) (a : Agent) (g : Good) : x a g ≤ 1 := by
  have hle : x a g ≤ ∑ b, x b g :=
    Finset.single_le_sum (fun b _ => hx.1 b g) (Finset.mem_univ a)
  exact hle.trans (hx.2.1 g)

theorem Valid.charity_nonneg (hx : x.Valid I) (g : Good) : 0 ≤ x.charity g :=
  sub_nonneg.mpr (hx.2.1 g)

theorem Valid.charity_le_one (hx : x.Valid I) (g : Good) : x.charity g ≤ 1 := by
  have hs : 0 ≤ ∑ a, x a g := Finset.sum_nonneg fun a _ => hx.1 a g
  dsimp [charity]
  linarith

/-- Definition 1, including feasibility and the charity comparison. -/
def FEF : Prop := x.Valid I ∧
  (∀ a b y, (∀ g, 0 ≤ y g) → (∀ g, y g ≤ x b g) →
    I.fweight a y ≤ I.budget a → I.fvalue a y ≤ I.fvalue a (x a)) ∧
  (∀ a y, (∀ g, 0 ≤ y g) → (∀ g, y g ≤ x.charity g) →
    I.fweight a y ≤ I.budget a → I.fvalue a y ≤ I.fvalue a (x a))

/-- A density certificate in cutoff form. The rank-based Definition 4 implies
this certificate. Multiplying through by sizes avoids division by zero here. -/
structure DensityCertificate : Prop where
  valid : x.Valid I
  tight : ∀ a, I.fweight a (x a) = I.budget a
  cutoff : ∃ r : Agent → ℝ,
    (∀ a, 0 ≤ r a) ∧
    (∀ a g, 0 < x a g → r a * I.size a g ≤ I.val a g) ∧
    (∀ a b g, r a * I.size a g < I.val a g → x b g ≤ x a g) ∧
    (∀ a g, r a * I.size a g < I.val a g → ∑ b, x b g = 1)

/-- Lemma 2: density domination eliminates feasible envy, including charity. -/
theorem DensityCertificate.fef (h : x.DensityCertificate I) : x.FEF I := by
  obtain ⟨r, hr, hsupp, hdom, hfull⟩ := h.cutoff
  refine ⟨h.valid, ?_, ?_⟩
  · intro a b y hy hsub hfeas
    apply I.density_comparison a (hr a) hy (h.tight a) hfeas (hsupp a)
    intro g hg
    by_contra hv
    exact (not_lt_of_ge ((hsub g).trans (hdom a b g (lt_of_not_ge hv)))) hg
  · intro a y hy hsub hfeas
    apply I.density_comparison a (hr a) hy (h.tight a) hfeas (hsupp a)
    intro g hg
    by_contra hv
    have hzero : x.charity g = 0 := by
      simp [charity, hfull a g (lt_of_not_ge hv)]
    have hle : y g ≤ 0 := by simpa [hzero] using hsub g
    have := h.valid.1 a g
    linarith

end FractionalAllocation

end GeneralizedAssignment
