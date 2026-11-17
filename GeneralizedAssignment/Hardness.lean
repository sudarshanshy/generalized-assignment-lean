import GeneralizedAssignment.NaturalInstance
import GeneralizedAssignment.BinarySearch
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.unusedSectionVars false

/-!
# The knapsack reduction (Appendix C)

The reduction has one agent and two extra goods. The special good has
odd value `2μ + 1`; the original goods have even values; the final good
is infeasible and therefore stays in charity. The allocation returned
by *any* FEFx oracle reveals whether the original knapsack optimum is
at most `μ`. A counted binary search then recovers the optimum.

The reduction is formalized directly. The external complexity-theoretic
fact that knapsack is NP-hard is not assumed as a Lean axiom.
-/

open scoped BigOperators

namespace GeneralizedAssignment

namespace Allocation

/-- An infeasible good left in charity makes every feasible subset strict. -/
theorem FEFx.charity_of_forbidden {Agent Good : Type*} [Fintype Agent] [Fintype Good]
    [DecidableEq Agent] [DecidableEq Good] {A : Allocation Agent Good}
    {I : Instance Agent Good} (hA : A.FEFx I) (a : Agent) {g : Good}
    (hg : g ∈ A.charity) (hbad : ¬ I.Feasible a {g})
    (S : Finset Good) (hS : S ⊆ A.charity) (hF : I.Feasible a S) :
    I.value a S ≤ I.value a (A a) := by
  apply hA.2.2 a S _ hF
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hS, ?_⟩
  intro heq
  have hgS : g ∈ S := heq ▸ hg
  exact hbad (hF.subset I (Finset.singleton_subset_iff.mpr hgS))

end Allocation

namespace Hardness

variable {Good : Type*} [Fintype Good] [LinearOrder Good]

abbrev Item (Good : Type*) := Option (Option Good)

instance itemLinearOrder : LinearOrder (Item Good) :=
  inferInstanceAs (LinearOrder (WithBot (WithBot Good)))

def original : Good ↪ Item Good :=
  ⟨fun g => some (some g), fun _ _ h => Option.some.inj (Option.some.inj h)⟩

@[simp] theorem original_apply (g : Good) : original g = some (some g) := rfl

def special : Item Good := some none
def forbidden : Item Good := none

def lift (S : Finset Good) : Finset (Item Good) := S.map original

def unlift (B : Finset (Item Good)) : Finset Good :=
  Finset.univ.filter fun g => original g ∈ B

@[simp] theorem original_mem_lift (S : Finset Good) (g : Good) :
    original g ∈ lift S ↔ g ∈ S := by simp [lift]

@[simp] theorem forbidden_not_lift (S : Finset Good) :
    (forbidden : Item Good) ∉ lift S := by simp [lift, forbidden, Finset.mem_map]

@[simp] theorem special_not_lift (S : Finset Good) :
    (special : Item Good) ∉ lift S := by simp [lift, special, Finset.mem_map]

theorem lift_unlift {B : Finset (Item Good)}
    (hf : forbidden ∉ B) (hs : special ∉ B) : lift (unlift B) = B := by
  ext g
  cases g with
  | none =>
    have hl : (none : Item Good) ∉ lift (unlift B) := forbidden_not_lift _
    simp only [hl, false_iff]
    exact hf
  | some g =>
    cases g with
    | none =>
      have hl : (some none : Item Good) ∉ lift (unlift B) := special_not_lift _
      simp only [hl, false_iff]
      exact hs
    | some g =>
      change original g ∈ lift (unlift B) ↔ original g ∈ B
      rw [original_mem_lift]
      exact ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

def gadget (w v : Good → ℕ) (W μ : ℕ) : NaturalInstance (Fin 1) (Item Good) where
  val _
    | none => 0
    | some none => 2 * μ + 1
    | some (some g) => 2 * v g
  size _
    | none => W + 1
    | some none => W
    | some (some g) => w g
  budget _ := W

@[simp] theorem gadget_value_lift (w v : Good → ℕ) (W μ : ℕ) (S : Finset Good) :
    (gadget w v W μ).value 0 (lift S) = 2 * Knapsack.total v S := by
  simp [NaturalInstance.value, Knapsack.total, lift, gadget, Finset.mul_sum]

@[simp] theorem gadget_weight_lift (w v : Good → ℕ) (W μ : ℕ) (S : Finset Good) :
    (gadget w v W μ).weight 0 (lift S) = Knapsack.total w S := by
  simp [NaturalInstance.weight, Knapsack.total, lift, gadget]

@[simp] theorem gadget_feasible (w v : Good → ℕ) (W μ : ℕ) (B : Finset (Item Good)) :
    (gadget w v W μ).toReal.Feasible 0 B ↔ (gadget w v W μ).weight 0 B ≤ W := by
  rw [NaturalInstance.real_feasible]
  rfl

theorem forbidden_not_feasible (w v : Good → ℕ) (W μ : ℕ)
    {B : Finset (Item Good)} (hB : (gadget w v W μ).weight 0 B ≤ W) :
    forbidden ∉ B := by
  intro hg
  have hs := Knapsack.total_mono ((gadget w v W μ).size 0)
    (Finset.singleton_subset_iff.mpr hg)
  have h := hs.trans hB
  simp [Knapsack.total, gadget, forbidden] at h

theorem special_alone (w v : Good → ℕ) (W μ : ℕ) (hw : ∀ g, 0 < w g)
    {B : Finset (Item Good)} (hB : (gadget w v W μ).weight 0 B ≤ W)
    (hs : special ∈ B) : B = {special} := by
  have hf := forbidden_not_feasible w v W μ hB
  have herase := Knapsack.total_erase ((gadget w v W μ).size 0) hs
  have hrem : (gadget w v W μ).weight 0 (B.erase special) = 0 := by
    change (gadget w v W μ).weight 0 B = W +
      (gadget w v W μ).weight 0 (B.erase special) at herase
    omega
  have hno : ∀ g, original g ∉ B := by
    intro g hg
    have hmem : original g ∈ B.erase special := by
      exact Finset.mem_erase.mpr ⟨by simp [special], hg⟩
    have hsingle := Knapsack.total_mono ((gadget w v W μ).size 0)
      (Finset.singleton_subset_iff.mpr hmem)
    have hzero : w g ≤ 0 := by
      change w g ≤ (gadget w v W μ).weight 0 (B.erase special) at hsingle
      simpa only [hrem] using hsingle
    exact (Nat.not_lt_of_ge hzero) (hw g)
  apply Finset.Subset.antisymm
  · intro g hg
    rw [Finset.mem_singleton]
    cases g with
    | none => exact False.elim (hf hg)
    | some g =>
      cases g with
      | none => rfl
      | some g => exact False.elim (hno g hg)
  · exact Finset.singleton_subset_iff.mpr hs

@[simp] theorem one_agent_charity (A : Allocation (Fin 1) (Item Good)) (g : Item Good) :
    g ∈ A.charity ↔ g ∉ A 0 := by
  rw [Allocation.mem_charity]
  constructor
  · exact fun h => h 0
  · intro h a
    have ha : a = 0 := Subsingleton.elim _ _
    simpa [ha] using h

def optimumBundle (w v : Good → ℕ) (W : ℕ) : Finset Good :=
  Knapsack.solve w v Finset.univ W

def optimum (w v : Good → ℕ) (W : ℕ) : ℕ :=
  Knapsack.total v (optimumBundle w v W)

theorem optimum_correct (w v : Good → ℕ) (W : ℕ) :
    Knapsack.Correct w v Finset.univ W (optimumBundle w v W) :=
  Knapsack.solve_correct w v Finset.univ W

theorem optimum_le_total (w v : Good → ℕ) (W : ℕ) :
    optimum w v W ≤ Knapsack.total v Finset.univ :=
  Knapsack.total_mono v (Finset.subset_univ _)

/-- The threshold information encoded by any FEFx allocation of the gadget. -/
theorem special_mem_iff (w v : Good → ℕ) (W μ : ℕ) (hw : ∀ g, 0 < w g)
    (A : Allocation (Fin 1) (Item Good))
    (hA : A.FEFx (gadget w v W μ).toReal) :
    special ∈ A 0 ↔ optimum w v W ≤ μ := by
  let N := gadget w v W μ
  have hAF : N.weight 0 (A 0) ≤ W := (gadget_feasible w v W μ _).mp (hA.1.1 0)
  have hf : forbidden ∉ A 0 := forbidden_not_feasible w v W μ hAF
  have hfC : forbidden ∈ A.charity := (one_agent_charity A forbidden).mpr hf
  have hbad : ¬ N.toReal.Feasible 0 {forbidden} := by
    intro h
    exact forbidden_not_feasible w v W μ ((gadget_feasible w v W μ _).mp h)
      (Finset.mem_singleton_self _)
  have hcharity : ∀ S ⊆ A.charity, N.toReal.Feasible 0 S →
      N.value 0 S ≤ N.value 0 (A 0) := by
    intro S hS hF
    have h := hA.charity_of_forbidden 0 hfC hbad S hS hF
    simpa using h
  constructor
  · intro hs
    have hsingle := special_alone w v W μ hw hAF hs
    let O := optimumBundle w v W
    have hOC : lift O ⊆ A.charity := by
      intro g hg
      rw [one_agent_charity, hsingle, Finset.mem_singleton]
      intro heq
      subst g
      exact special_not_lift O hg
    have hOF : N.toReal.Feasible 0 (lift O) := by
      rw [gadget_feasible, gadget_weight_lift]
      exact (optimum_correct w v W).2.1
    have h := hcharity (lift O) hOC hOF
    have hv : N.value 0 (A 0) = 2 * μ + 1 := by
      rw [hsingle]
      simp [N, NaturalInstance.value, Knapsack.total, gadget, special]
    rw [hv] at h
    rw [gadget_value_lift] at h
    change 2 * optimum w v W ≤ 2 * μ + 1 at h
    omega
  · intro hopt
    by_contra hs
    have heq : lift (unlift (A 0)) = A 0 := lift_unlift hf hs
    have hU : Knapsack.total w (unlift (A 0)) ≤ W := by
      rw [← gadget_weight_lift w v W μ, heq]
      exact hAF
    have hval : N.value 0 (A 0) ≤ 2 * optimum w v W := by
      rw [← heq]
      rw [gadget_value_lift]
      exact Nat.mul_le_mul_left 2 ((optimum_correct w v W).2.2 _ (Finset.subset_univ _) hU)
    have hsC : ({special} : Finset (Item Good)) ⊆ A.charity := by
      exact Finset.singleton_subset_iff.mpr ((one_agent_charity A special).mpr hs)
    have hsF : N.toReal.Feasible 0 {special} := by
      rw [gadget_feasible]
      simp [NaturalInstance.weight, Knapsack.total, gadget, special]
    have h := hcharity {special} hsC hsF
    have hlower : 2 * μ + 1 ≤ N.value 0 (A 0) := by
      simpa [N, NaturalInstance.value, Knapsack.total, gadget, special] using h
    omega

/-- Lemma 15: the parity of the allocated value reveals the threshold answer. -/
theorem value_parity (w v : Good → ℕ) (W μ : ℕ) (hw : ∀ g, 0 < w g)
    (A : Allocation (Fin 1) (Item Good))
    (hA : A.FEFx (gadget w v W μ).toReal) :
    (gadget w v W μ).value 0 (A 0) % 2 = if optimum w v W ≤ μ then 1 else 0 := by
  have hAF := (gadget_feasible w v W μ _).mp (hA.1.1 0)
  by_cases hs : special ∈ A 0
  · have hopt := (special_mem_iff w v W μ hw A hA).mp hs
    rw [special_alone w v W μ hw hAF hs]
    simp [hopt, NaturalInstance.value, Knapsack.total, gadget, special, Nat.add_mod]
  · have hopt : ¬ optimum w v W ≤ μ := mt (special_mem_iff w v W μ hw A hA).mpr hs
    have hf := forbidden_not_feasible w v W μ hAF
    rw [← lift_unlift hf hs, gadget_value_lift]
    simp [hopt]

theorem odd_value_iff (w v : Good → ℕ) (W μ : ℕ) (hw : ∀ g, 0 < w g)
    (A : Allocation (Fin 1) (Item Good))
    (hA : A.FEFx (gadget w v W μ).toReal) :
    (gadget w v W μ).value 0 (A 0) % 2 = 1 ↔ optimum w v W ≤ μ := by
  rw [value_parity w v W μ hw A hA]
  split_ifs <;> simp_all

/-- The reduction only needs an oracle for one-agent instances. -/
structure Oracle (Good : Type*) [Fintype Good] [LinearOrder Good] where
  allocate : NaturalInstance (Fin 1) (Item Good) → Allocation (Fin 1) (Item Good)
  fair : ∀ N, (allocate N).FEFx N.toReal

def threshold (O : Oracle Good) (w v : Good → ℕ) (W μ : ℕ) : Prop :=
  (gadget w v W μ).value 0 (O.allocate (gadget w v W μ) 0) % 2 = 1

instance (O : Oracle Good) (w v : Good → ℕ) (W μ : ℕ) :
    Decidable (threshold O w v W μ) := inferInstanceAs (Decidable (_ = _))

theorem threshold_correct (O : Oracle Good) (w v : Good → ℕ) (W : ℕ)
    (hw : ∀ g, 0 < w g) (μ : ℕ) : threshold O w v W μ ↔ optimum w v W ≤ μ :=
  odd_value_iff w v W μ hw _ (O.fair _)

/-- The Cook reduction: binary search using the parity test as its only oracle query. -/
def recoverOptimum (O : Oracle Good) (w v : Good → ℕ) (W : ℕ) : ℕ × ℕ :=
  BinarySearch.recover (threshold O w v W) (Knapsack.total v Finset.univ)

/-- Theorem 5's reduction, including its logarithmic number of FEFx-oracle calls. -/
theorem recoverOptimum_spec (O : Oracle Good) (w v : Good → ℕ) (W : ℕ)
    (hw : ∀ g, 0 < w g) :
    (recoverOptimum O w v W).1 = optimum w v W ∧
      (recoverOptimum O w v W).2 ≤ Nat.log 2 (Knapsack.total v Finset.univ) + 1 := by
  exact BinarySearch.recover_spec _ _ _ (threshold_correct O w v W hw) (optimum_le_total w v W)

theorem gadget_card : Fintype.card (Item Good) = Fintype.card Good + 2 := by
  simp [Item, Fintype.card_option, Nat.add_assoc]

/-- The gadget adds at most one bit to values and sizes. -/
theorem gadget_bit_bounds (w v : Good → ℕ) (W μ L : ℕ)
    (hw : ∀ g, w g < 2 ^ L) (hv : ∀ g, v g < 2 ^ L)
    (hW : W < 2 ^ L) (hμ : μ < 2 ^ L) :
    (∀ g, (gadget w v W μ).val 0 g < 2 ^ (L + 1)) ∧
      (∀ g, (gadget w v W μ).size 0 g ≤ 2 ^ L) := by
  constructor
  · intro g
    cases g with
    | none => simp [gadget]
    | some g =>
      cases g with
      | none => simp only [gadget, pow_succ]; omega
      | some g => simp only [gadget, pow_succ]; have := hv g; omega
  · intro g
    cases g with
    | none => simp only [gadget]; omega
    | some g =>
      cases g with
      | none => exact hW.le
      | some g => exact (hw g).le

end Hardness

end GeneralizedAssignment
