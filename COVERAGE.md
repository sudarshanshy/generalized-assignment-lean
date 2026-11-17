# Paper-to-Lean correspondence

Reference: Barman–Khan–Shyam–Sreenivas, [arXiv:2305.01339v1](https://arxiv.org/abs/2305.01339v1), 2 May 2023. Names below omit the common `GeneralizedAssignment` namespace.

## Definitions

| Paper | Formalization |
|---|---|
| Generalized assignment instance | `Instance` in [Basic.lean](GeneralizedAssignment/Basic.lean); executable `NaturalInstance` and `RationalInstance`. |
| Definition 1: FEF | `FractionalAllocation.FEF` in [Fractional.lean](GeneralizedAssignment/Fractional.lean). Nonnegativity, unit supply, budgets, and charity are explicit. |
| Definition 2: FEFx | `Allocation.FEFx` in [Basic.lean](GeneralizedAssignment/Basic.lean). |
| Definition 3: internal and edge goods | `Ranking.internalGoods`, `Ranking.edgeGoods` in [LinearPrograms.lean](GeneralizedAssignment/LinearPrograms.lean), with zero-based thresholds. |
| Definition 4: density domination | `Ranking.DensityDomination` in [DensityDomination.lean](GeneralizedAssignment/DensityDomination.lean), including the literal restricted budget sum. `FractionalAllocation.DensityCertificate` is the cutoff form used for the value comparison. |
| Definitions 5–6: LP1 and LP2 | `Ranking.LP1`, `Ranking.LP2` in [LinearPrograms.lean](GeneralizedAssignment/LinearPrograms.lean). The explicit support condition makes the full budget sum equal to the prefix sum. |
| Definition 7: envied/minimally envied sets | `Allocation.Envies`, `Envied`, `MinimalEnvied` in [Basic.lean](GeneralizedAssignment/Basic.lean). |
| Definition 8: approximate FEFx | `Allocation.ApproxFEFx` in [Approximate.lean](GeneralizedAssignment/Approximate.lean), parameterized by the factor rather than the error. |
| Definition 9: approximate minimal envy | `Allocation.ApproxMinimalEnvied` in [Approximate.lean](GeneralizedAssignment/Approximate.lean), with the feasible witnessing bundle explicit. |

## Divisible goods

| Paper | Checked declarations |
|---|---|
| Proposition 1 | `FractionalAllocation.FEF.restrict` in [DummyGood.lean](GeneralizedAssignment/DummyGood.lean). |
| Lemma 2 | `Instance.density_comparison`, `FractionalAllocation.DensityCertificate.fef` in [Fractional.lean](GeneralizedAssignment/Fractional.lean); `Ranking.DensityDomination.fef` in [DensityDomination.lean](GeneralizedAssignment/DensityDomination.lean). |
| Proposition 3 | `Ranking.LP1.densityDomination` in [DensityDomination.lean](GeneralizedAssignment/DensityDomination.lean), and `Ranking.LP1.densityCertificate` in [LinearPrograms.lean](GeneralizedAssignment/LinearPrograms.lean). |
| Lemma 4 | `Ranking.lp_incongruity` in [LPIncongruity.lean](GeneralizedAssignment/LPIncongruity.lean). Its objective maximizer is obtained from compactness; it is not assumed. |
| Claim 5 | `Ranking.edge_maximum_exists` in [LPIncongruity.lean](GeneralizedAssignment/LPIncongruity.lean). The donor/recipient perturbation checks every active LP constraint. |
| Lemma 6 | `FractionalAllocation.dummy_not_full` in [DummyGood.lean](GeneralizedAssignment/DummyGood.lean), and `Ranking.lp2_threshold_lt` in [Divisible.lean](GeneralizedAssignment/Divisible.lean). |
| Algorithm 1 | `Ranking.solveThresholds`, `fractionalAlgorithm`, and its trace/query bounds in [FractionalAlgorithm.lean](GeneralizedAssignment/FractionalAlgorithm.lean). |
| Theorem 1 | `FractionalAllocation.exists_fef` in [Divisible.lean](GeneralizedAssignment/Divisible.lean); `Paper.theorem_1_algorithm` in [PaperTheorems.lean](GeneralizedAssignment/PaperTheorems.lean). |
| Zero-size extension | `FractionalAllocation.exists_fef_nonnegative` in [ZeroSizes.lean](GeneralizedAssignment/ZeroSizes.lean), exposed as `Paper.theorem_1`. This is an additional limit argument, not part of the paper's density proof. |

Supporting analytic results are in [AffinePerturbation.lean](GeneralizedAssignment/AffinePerturbation.lean) and [LPGeometry.lean](GeneralizedAssignment/LPGeometry.lean). In particular, `LP2.perturb`, `lp2_isCompact`, and `exists_edge_maximizer` provide the details behind the small-perturbation/maximization argument.

## Indivisible goods

| Paper | Checked declarations |
|---|---|
| Lemma 7 | `Allocation.replace_agentsFEFx` in [Indivisible.lean](GeneralizedAssignment/Indivisible.lean), and `exactRun_invariant` in [Algorithms.lean](GeneralizedAssignment/Algorithms.lean). |
| Lemma 8 | `Allocation.charityFEF_iff`, `StrongFEFx.fefx` in [Basic.lean](GeneralizedAssignment/Basic.lean), used by both exact algorithm implementations. |
| Theorem 2 | `Allocation.exists_strongFEFx`, `exists_fefx` in [Indivisible.lean](GeneralizedAssignment/Indivisible.lean). The finite welfare-maximization proof also works for real values. |
| Lemma 9 | `Allocation.minimalEnvied_of_no_erase` and `MinimalEnvied.envier` in [Indivisible.lean](GeneralizedAssignment/Indivisible.lean); `FiniteDeletion.runAux_spec`; `NaturalInstance.findMinimal`. |
| Algorithms 2–3 | `NaturalInstance.executeAux`, `executeAux_spec`, `findMinimal`, `solveFEFx` in [ExactAlgorithm.lean](GeneralizedAssignment/ExactAlgorithm.lean). |
| Theorem 3 | `NaturalInstance.solveFEFx_fair`, `run_iterations_le`, `run_queries_le`; `exact_knapsack_cells` in [OperationBounds.lean](GeneralizedAssignment/OperationBounds.lean). |
| Proposition 10 | `Allocation.oracle_detects_envy`, `oracle_no_envy` in [Approximate.lean](GeneralizedAssignment/Approximate.lean). |
| Lemma 11 | `Allocation.approxMinimal_of_oracle_stop`, `exists_approxMinimalEnvied`; executable `NaturalInstance.findApproxMinimal` in [ApproximateAlgorithm.lean](GeneralizedAssignment/ApproximateAlgorithm.lean). |
| Claim 12 | `Allocation.ApproxMinimalEnvied.multiplicative` in [Approximate.lean](GeneralizedAssignment/Approximate.lean). |
| Lemma 13 | `Allocation.replace_approxAgentsFEFx` in [Approximate.lean](GeneralizedAssignment/Approximate.lean). |
| Lemma 14 | `Allocation.oracle_termination_charity` in [Approximate.lean](GeneralizedAssignment/Approximate.lean). |
| Algorithms 4–5 | `NaturalInstance.executeApproxAux`, `executeApproxAux_spec`, `findApproxMinimal`, `runApprox` in [ApproximateAlgorithm.lean](GeneralizedAssignment/ApproximateAlgorithm.lean). |
| Theorem 4 | `NaturalInstance.solveFPTAS_fair`, `accuracyParameter_bound`, `runFPTAS_queries_le`, `fptas_knapsack_cells` in [FPTAS.lean](GeneralizedAssignment/FPTAS.lean); input-derived bounds in [OperationBounds.lean](GeneralizedAssignment/OperationBounds.lean). |

The logarithmic potential and its zero-utility case are proved in [ApproximateComplexity.lean](GeneralizedAssignment/ApproximateComplexity.lean). The executable implementations use a proved sufficient fuel bound; a separate proof shows that every completed trace has the stated, much smaller approximation iteration bound.

The knapsack oracle is fully instantiated:

1. [Knapsack.lean](GeneralizedAssignment/Knapsack.lean): exact capacity-indexed DP and optimality against every feasible subset.
2. [ValueKnapsack.lean](GeneralizedAssignment/ValueKnapsack.lean): exact value-indexed DP via minimum-weight complements.
3. [ScaledKnapsack.lean](GeneralizedAssignment/ScaledKnapsack.lean): integer scaling, factor `1-1/r`, and at most `(m+1)*(m²*r+1)` DP cells.
4. [ApproximateOracle.lean](GeneralizedAssignment/ApproximateOracle.lean): equivalence of the executable integer envy test and the paper's real-valued oracle test.
5. [RationalInputs.lean](GeneralizedAssignment/RationalInputs.lean): exact denominator clearing and invariance of all approximate FEFx comparisons.

## Matroids and appendices

| Paper | Checked declarations |
|---|---|
| Remark 1 | [FeasibleFamilies.lean](GeneralizedAssignment/FeasibleFamilies.lean) proves the swapping method for downward-closed feasibility families. [FamilyComplexity.lean](GeneralizedAssignment/FamilyComplexity.lean) proves the approximate iteration/query bounds. [MatroidConstraints.lean](GeneralizedAssignment/MatroidConstraints.lean) instantiates these results with mathlib's `Matroid.Indep`. |
| Lemma 15 | `Hardness.special_mem_iff`, `value_parity`, `odd_value_iff` in [Hardness.lean](GeneralizedAssignment/Hardness.lean). |
| Theorem 5 | `Hardness.recoverOptimum_spec`, `gadget_card`, `gadget_bit_bounds` in [Hardness.lean](GeneralizedAssignment/Hardness.lean), using the counted search in [BinarySearch.lean](GeneralizedAssignment/BinarySearch.lean). This is the explicit reduction, not an assumed hardness proposition. |
| Claim 16 | `NashCounterexample.product_maximal`, `welfare_maximal` in [NashCounterexample.lean](GeneralizedAssignment/NashCounterexample.lean). |
| Claim 17 | `NashCounterexample.optimum_not_fef` and `exists_nash_maximizer_not_fef` in [NashCounterexample.lean](GeneralizedAssignment/NashCounterexample.lean). |

The standard polynomial-time LP and weighted-matroid algorithms, the previously known NP-hardness of knapsack, literature comparisons, and the paper's open questions are not reproved. See the precise computational scope in [README.md](README.md).
