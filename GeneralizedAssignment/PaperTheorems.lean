import GeneralizedAssignment.DensityDomination
import GeneralizedAssignment.FractionalAlgorithm
import GeneralizedAssignment.ZeroSizes
import GeneralizedAssignment.OperationBounds
import GeneralizedAssignment.RationalInputs
import GeneralizedAssignment.Hardness
import GeneralizedAssignment.MatroidConstraints
import GeneralizedAssignment.NashCounterexample

set_option linter.unusedSectionVars false

/-!
# The principal statements, indexed by the paper

This is the entry point for reading the formalization. The substantive
proofs live in the imported modules; these statements collect their
conclusions without adding axioms or solver assumptions.

Theorem 5 is stated as its explicit oracle reduction. The general
NP-hardness of knapsack and a Turing-machine complexity framework are
outside the scope of this development.
-/

open scoped BigOperators

namespace GeneralizedAssignment.Paper

section Finite

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [DecidableEq Agent] [DecidableEq Good]

/-- Theorem 1, existence, with zero sizes also covered. -/
theorem theorem_1 (I : Instance Agent Good) :
    ∃ x : FractionalAllocation Agent Good, x.FEF I :=
  FractionalAllocation.exists_fef_nonnegative I

/-- Theorem 1, Algorithm 1's certificate and polynomial LP-query bound.
The extra fictional good is removed from the returned allocation. -/
theorem theorem_1_algorithm (I : Instance Agent Good) (hsize : ∀ a g, 0 < I.size a g) :
    ∃ π : Ranking Agent (Option Good) (Fintype.card (Option Good)),
      π.Sorted I.withDummy ∧
      ∃ R : π.ThresholdResult I.withDummy (fun _ => 0),
        R.iterations ≤ Fintype.card Agent * Fintype.card Good ∧
        Ranking.lpQueryBound (Agent := Agent) R.iterations ≤
          1 + (Fintype.card Agent + 1) * (Fintype.card Agent * Fintype.card Good) ∧
        R.allocation.restrict.FEF I := by
  obtain ⟨π, hπ⟩ := exists_sortedRanking I.withDummy
  let blocked := fun x hx => FractionalAllocation.dummy_not_full x I hx
  let R := π.fractionalAlgorithm I.withDummy none blocked
  refine ⟨π, hπ, R, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_option, Nat.add_sub_cancel] using
      π.fractionalAlgorithm_iterations_le I.withDummy none blocked
  · simpa only [Fintype.card_option, Nat.add_sub_cancel] using
      π.fractionalAlgorithm_queries_le I.withDummy none blocked
  · exact (R.tight.fef (I.withDummy_size_pos hsize) hπ).restrict R.allocation I

/-- Theorem 2, strengthened to full feasible envy-freeness towards charity. -/
theorem theorem_2 (I : Instance Agent Good) :
    ∃ A : Allocation Agent Good, A.StrongFEFx I := Allocation.exists_strongFEFx I

end Finite

section Ordered

variable {Agent Good : Type*} [Fintype Agent] [Fintype Good]
  [LinearOrder Agent] [LinearOrder Good]

/-- Theorem 3: the executable exact algorithm, its correctness and iteration bound. -/
theorem theorem_3 (N : NaturalInstance Agent Good) :
    N.solveFEFx.FEFx N.toReal ∧ N.run.iterations ≤ N.totalValue ∧
      N.run.queries ≤ (N.totalValue + 1) *
        (Fintype.card Agent * (1 + (Fintype.card Good + 1) ^ 2)) :=
  ⟨N.solveFEFx_fair, N.run_iterations_le, N.run_queries_le⟩

/-- Theorem 4: executable approximation, a polynomial oracle-call bound, and
the accuracy-parameter bound. Table sizes are bounded in `fptas_knapsack_cells`. -/
theorem theorem_4 (N : NaturalInstance Agent Good) (ε : ℚ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    (N.solveFPTAS ε hε₀ hε₁).ApproxFEFx N.toReal (1 - (ε : ℝ)) ∧
      (N.runFPTAS ε hε₀ hε₁).queries ≤
        (5 * Fintype.card Agent * N.valueBits * NaturalInstance.accuracyParameter ε + 1) *
          ((Fintype.card Agent + 1) * (1 + (Fintype.card Good + 1) ^ 2)) ∧
      (NaturalInstance.accuracyParameter ε : ℚ) ≤ 3 / ε :=
  ⟨N.solveFPTAS_fair ε hε₀ hε₁, N.runFPTAS_queries_input_bound ε hε₀ hε₁,
    NaturalInstance.accuracyParameter_bound ε hε₀ hε₁⟩

/-- The exact rational-input version obtained by verified denominator clearing. -/
theorem theorem_3_rational (R : RationalInstance Agent Good) :
    R.solveFEFx.FEFx R.toReal := R.solveFEFx_fair

/-- The rational-input approximation guarantee after verified normalization. -/
theorem theorem_4_rational (R : RationalInstance Agent Good) (ε : ℚ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    (R.solveFPTAS ε hε₀ hε₁).ApproxFEFx R.toReal (1 - (ε : ℝ)) :=
  R.solveFPTAS_fair ε hε₀ hε₁

/-- Theorem 5: a logarithmic-query Cook reduction from knapsack optimization. -/
theorem theorem_5_reduction (O : Hardness.Oracle Good) (w v : Good → ℕ) (W : ℕ)
    (hw : ∀ g, 0 < w g) :
    (Hardness.recoverOptimum O w v W).1 = Hardness.optimum w v W ∧
      (Hardness.recoverOptimum O w v W).2 ≤ Nat.log 2 (Knapsack.total v Finset.univ) + 1 :=
  Hardness.recoverOptimum_spec O w v W hw

/-- Remark 1's existence assertion under heterogeneous matroid constraints. -/
theorem remark_1 (M : Agent → Matroid Good) (I : Instance Agent Good) :
    ∃ A : Allocation Agent Good, (MatroidConstraints.family M).StrongFEFx I 1 A :=
  MatroidConstraints.exists_strongFEFx M I

end Ordered

/-- Claims 16–17: a Nash-welfare maximizer need not be feasibly envy-free. -/
theorem claims_16_17 :
    ∃ x : FractionalAllocation (Fin 2) (Fin 2), x.Valid NashCounterexample.data ∧
      (∀ y, y.Valid NashCounterexample.data →
        NashCounterexample.nashWelfare y ≤ NashCounterexample.nashWelfare x) ∧
      ¬ x.FEF NashCounterexample.data :=
  NashCounterexample.exists_nash_maximizer_not_fef

end GeneralizedAssignment.Paper
