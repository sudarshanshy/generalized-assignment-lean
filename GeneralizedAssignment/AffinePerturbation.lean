import GeneralizedAssignment.Basic

set_option linter.unusedSectionVars false

/-!
# A finite affine perturbation lemma

The rigorous form of “choose a sufficiently small positive epsilon” used
twice in the proof of Lemma 4. Inactive inequalities have slack; active
inequalities must have nonpositive directional derivative.
-/

namespace GeneralizedAssignment

theorem affine_small_step {c d : ℝ} (hc : c ≤ 0) (hd : c = 0 → d ≤ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 ≤ t → t ≤ δ → c + t * d ≤ 0 := by
  by_cases hd' : d ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    intro t ht _
    exact add_nonpos hc (mul_nonpos_of_nonneg_of_nonpos ht hd')
  · have hdpos : 0 < d := lt_of_not_ge hd'
    have hcneg : c < 0 := lt_of_le_of_ne hc (fun h => hd' (hd h))
    refine ⟨-c / d, div_pos (neg_pos.mpr hcneg) hdpos, ?_⟩
    intro t _ ht
    have htd : t * d ≤ -c := (le_div_iff₀ hdpos).mp ht
    linarith

theorem finite_affine_small_step {ι : Type*} (s : Finset ι) (c d : ι → ℝ)
    (hc : ∀ i ∈ s, c i ≤ 0) (hd : ∀ i ∈ s, c i = 0 → d i ≤ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 ≤ t → t ≤ δ → ∀ i ∈ s, c i + t * d i ≤ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := affine_small_step (hc i (by simp)) (hd i (by simp))
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih (fun j hj => hc j (by simp [hj]))
      (fun j hj => hd j (by simp [hj]))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro t ht hδ j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h₁ t ht (hδ.trans (min_le_left _ _))
    · exact h₂ t ht (hδ.trans (min_le_right _ _)) j hj

/-- Finitely many affine inequalities can be preserved simultaneously. -/
theorem exists_pos_affine_step {ι : Type*} [Fintype ι] (c d : ι → ℝ)
    (hc : ∀ i, c i ≤ 0) (hd : ∀ i, c i = 0 → d i ≤ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, c i + t * d i ≤ 0 := by
  obtain ⟨δ, hδ, h⟩ := finite_affine_small_step Finset.univ c d
    (fun i _ => hc i) (fun i _ => hd i)
  exact ⟨δ, hδ, fun i => h δ hδ.le le_rfl i (Finset.mem_univ _)⟩

end GeneralizedAssignment
