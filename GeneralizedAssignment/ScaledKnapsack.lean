import GeneralizedAssignment.ValueKnapsack
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false

/-!
# A verified value-scaling knapsack FPTAS

With an integer accuracy parameter `r > 0`, the solver achieves a factor
`1 - 1/r`. Values are scaled by integer division, so the implementation
uses only exact natural-number arithmetic. The dynamic program has at
most `(m + 1) * (m² * r + 1)` cells, independently of the budget and the
magnitudes of the original values.
-/

open scoped BigOperators

namespace GeneralizedAssignment.Knapsack

variable {Good : Type*} [LinearOrder Good]

def eligible (w : Good → ℕ) (S : Finset Good) (C : ℕ) : Finset Good :=
  S.filter fun g => w g ≤ C

theorem feasible_subset_eligible (w : Good → ℕ) {S U : Finset Good} {C : ℕ}
    (hUS : U ⊆ S) (hU : total w U ≤ C) : U ⊆ eligible w S C := by
  intro g hg
  have hsingle := total_mono w (Finset.singleton_subset_iff.mpr hg)
  refine Finset.mem_filter.mpr ⟨hUS hg, ?_⟩
  simpa [total] using hsingle.trans hU

def scaledProfit (v : Good → ℕ) (S : Finset Good) (r : ℕ) (g : Good) : ℕ :=
  v g * (S.card * r) / S.sup v

theorem scaledProfit_le (v : Good → ℕ) (S : Finset Good) (r : ℕ)
    {g : Good} (hg : g ∈ S) : scaledProfit v S r g ≤ S.card * r := by
  exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ (Finset.le_sup hg))

theorem scaled_total_le (v : Good → ℕ) (S : Finset Good) (r : ℕ) :
    total (scaledProfit v S r) S ≤ S.card ^ 2 * r := by
  calc
    total (scaledProfit v S r) S ≤ ∑ _g ∈ S, S.card * r :=
      Finset.sum_le_sum fun _ hg => scaledProfit_le v S r hg
    _ = S.card ^ 2 * r := by simp; ring

theorem scaled_round_down (v : Good → ℕ) (S U : Finset Good) (r : ℕ) :
    S.sup v * total (scaledProfit v S r) U ≤ total v U * (S.card * r) := by
  calc
    S.sup v * total (scaledProfit v S r) U =
        ∑ g ∈ U, S.sup v * scaledProfit v S r g := by
      simp [total, Finset.mul_sum]
    _ ≤ ∑ g ∈ U, v g * (S.card * r) :=
      Finset.sum_le_sum fun g _ => Nat.mul_div_le _ _
    _ = total v U * (S.card * r) := by simp [total, Finset.sum_mul]

theorem scaled_round_up (v : Good → ℕ) (S U : Finset Good) (r : ℕ)
    (hM : 0 < S.sup v) :
    total v U * (S.card * r) ≤
      S.sup v * total (scaledProfit v S r) U + U.card * S.sup v := by
  calc
    total v U * (S.card * r) = ∑ g ∈ U, v g * (S.card * r) := by
      simp [total, Finset.sum_mul]
    _ ≤ ∑ g ∈ U, (S.sup v * scaledProfit v S r g + S.sup v) := by
      apply Finset.sum_le_sum
      intro g _
      have h := (Nat.div_lt_iff_lt_mul hM).mp
        (Nat.lt_succ_self (v g * (S.card * r) / S.sup v))
      dsimp [scaledProfit]
      nlinarith
    _ = S.sup v * total (scaledProfit v S r) U + U.card * S.sup v := by
      simp [total, Finset.sum_add_distrib, Finset.mul_sum]

/-- The value-indexed DP on the individually feasible, scaled items. -/
def scaledSolve (w v : Good → ℕ) (S : Finset Good) (C r : ℕ) : Finset Good :=
  let E := eligible w S C
  valueSolve w (scaledProfit v E r) E C

theorem scaledSolve_subset (w v : Good → ℕ) (S : Finset Good) (C r : ℕ) :
    scaledSolve w v S C r ⊆ S :=
  (valueSolve_correct w (scaledProfit v (eligible w S C) r) _ C).1.trans
    (Finset.filter_subset _ _)

theorem scaledSolve_feasible (w v : Good → ℕ) (S : Finset Good) (C r : ℕ) :
    total w (scaledSolve w v S C r) ≤ C :=
  (valueSolve_correct w (scaledProfit v (eligible w S C) r) _ C).2.1

theorem scaledSolve_guarantee_nat (w v : Good → ℕ) (S : Finset Good) (C r : ℕ)
    (hr : 0 < r) (U : Finset Good) (hUS : U ⊆ S) (hU : total w U ≤ C) :
    r * total v U ≤ r * total v (scaledSolve w v S C r) + total v U := by
  let E := eligible w S C
  let Q := scaledSolve w v S C r
  change r * total v U ≤ r * total v Q + total v U
  have hUE : U ⊆ E := feasible_subset_eligible w hUS hU
  have hQ : Correct w (scaledProfit v E r) E C Q :=
    valueSolve_correct w (scaledProfit v E r) E C
  by_cases hM : 0 < E.sup v
  · have hE : E.Nonempty := by
      by_contra h
      have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he] at hM
    have hm : 0 < E.card := Finset.card_pos.mpr hE
    have hk : 0 < E.card * r := Nat.mul_pos hm hr
    have hopt := hQ.2.2 U hUE hU
    have hdown := scaled_round_down v E Q r
    have hup := scaled_round_up v E U r hM
    have hcard := Finset.card_le_card hUE
    have hadd : r * total v U ≤ r * total v Q + E.sup v := by
      apply Nat.le_of_mul_le_mul_left (c := E.card) _ hm
      nlinarith [Nat.mul_le_mul_left (E.sup v) hopt,
        Nat.mul_le_mul_right (E.sup v) hcard]
    obtain ⟨g, hg, hgv⟩ := Finset.exists_mem_eq_sup E hE v
    have hgC : total w {g} ≤ C := by
      simpa [total] using (Finset.mem_filter.mp hg).2
    have hsingle := hQ.2.2 {g} (Finset.singleton_subset_iff.mpr hg) hgC
    have hscaledg : scaledProfit v E r g = E.card * r := by
      dsimp [scaledProfit]
      rw [← hgv]
      exact Nat.mul_div_cancel_left _ hM
    have hbig : E.card * r ≤ total (scaledProfit v E r) Q := by
      simpa [total, hscaledg] using hsingle
    have hMQ : E.sup v ≤ total v Q := by
      apply Nat.le_of_mul_le_mul_left (c := E.card * r) _ hk
      nlinarith [Nat.mul_le_mul_left (E.sup v) hbig]
    by_cases hMU : E.sup v ≤ total v U
    · omega
    · have hUQ : total v U ≤ total v Q := by omega
      exact (Nat.mul_le_mul_left r hUQ).trans (Nat.le_add_right _ _)
  · have hMzero : E.sup v = 0 := by omega
    have hzero : total v U = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      have h := Finset.le_sup (f := v) (hUE hg)
      omega
    simp [hzero]

/-- Approximation guarantee, in the convention used by the paper's oracle. -/
theorem scaledSolve_guarantee (w v : Good → ℕ) (S : Finset Good) (C r : ℕ)
    (hr : 0 < r) (U : Finset Good) (hUS : U ⊆ S) (hU : total w U ≤ C) :
    (1 - 1 / (r : ℝ)) * (total v U : ℝ) ≤
      (total v (scaledSolve w v S C r) : ℝ) := by
  have hn := scaledSolve_guarantee_nat w v S C r hr U hUS hU
  have h : (r : ℝ) * (total v U : ℝ) ≤
      (r : ℝ) * (total v (scaledSolve w v S C r) : ℝ) + (total v U : ℝ) := by
    exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  apply le_of_mul_le_mul_left (a := (r : ℝ)) _ hrR
  have heq : (r : ℝ) * ((1 - 1 / (r : ℝ)) * (total v U : ℝ)) =
      (r : ℝ) * (total v U : ℝ) - (total v U : ℝ) := by
    field_simp [ne_of_gt hrR]
  rw [heq]
  linarith

/-- A bound on the materialized DP table, independent of numeric input magnitudes. -/
theorem scaledSolve_cells (w v : Good → ℕ) (S : Finset Good) (C r : ℕ) :
    let E := eligible w S C
    cells E.card (total (scaledProfit v E r) E) ≤
      (S.card + 1) * (S.card ^ 2 * r + 1) := by
  let E := eligible w S C
  have hcard : E.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hval := scaled_total_le v E r
  dsimp only
  rw [cells_eq]
  apply Nat.mul_le_mul (Nat.add_le_add_right hcard 1)
  apply Nat.add_le_add_right
  exact hval.trans (Nat.mul_le_mul_right r (Nat.pow_le_pow_left hcard 2))

end GeneralizedAssignment.Knapsack
