# Generalized assignment and envy-freeness in Lean

A Lean 4 formalization of **Guaranteeing Envy-Freeness under Generalized Assignment Constraints**, by Siddharth Barman, Arindam Khan, Sudarshan Shyam, and K. V. N. Sreenivas, [arXiv:2305.01339v1](https://arxiv.org/abs/2305.01339v1).

The project covers the paper's main mathematical proofs, its allocation algorithms and invariants, the knapsack hardness reduction, the matroid extension, and the Nash-welfare counterexample. It also contains executable exact and approximation algorithms for natural-number and nonnegative rational inputs.

Start with [PaperTheorems.lean](GeneralizedAssignment/PaperTheorems.lean). [COVERAGE.md](COVERAGE.md) maps the paper's numbered statements to the substantive proofs.

The completed build, axiom audit, and executable example results are recorded in [VALIDATION.md](VALIDATION.md).

## Build and run

The project pins **Lean 4.33.1** and **mathlib v4.33.1**. With `elan` installed, run these commands from this directory:

```sh
lake exe cache get
lake build
lake env lean --run Main.lean
```

The last command runs small examples with heterogeneous constraints, zero sizes and budgets, empty agent/good types, and rational data. Agents and goods in those examples are numbered from zero.

The default library build includes [Audit.lean](GeneralizedAssignment/Audit.lean). It checks the transitive axiom dependencies of every declaration in the `GeneralizedAssignment` namespace and rejects anything outside `propext`, `Classical.choice`, and `Quot.sound`. Thus admitted proofs, custom axioms, and compiler-trust proof axioms fail the audit.

The optional `check.py` helper checks selected modules against already-built dependencies. It is a development convenience; `lake build` is the dependency-aware validation command. `cache.py` keeps mathlib downloads in this project's own cache.

## Main results

All names below are in `GeneralizedAssignment.Paper`.

| Declaration | Conclusion |
|---|---|
| `theorem_1` | A feasible envy-free fractional allocation exists, including when some sizes are zero. |
| `theorem_1_algorithm` | For positive sizes, Algorithm 1 has a checked LP/threshold trace, at most `n*m` updates, and at most `1 + (n+1)*n*m` LP feasibility queries. |
| `theorem_2` | An indivisible FEFx allocation exists; the construction gives full feasible envy-freeness towards charity. |
| `theorem_3` | The executable exact algorithm is FEFx, terminates within the total integer welfare bound, and has a polynomial number of knapsack calls per update. |
| `theorem_4` | The executable FPTAS returns `(1-ε)`-FEFx and satisfies the proved query and accuracy-parameter bounds. |
| `theorem_3_rational`, `theorem_4_rational` | Correctness on rational inputs after verified denominator clearing. |
| `theorem_5_reduction` | Any one-agent FEFx oracle recovers a knapsack optimum with logarithmically many oracle calls. |
| `remark_1` | The existence result extends to heterogeneous matroid constraints. The accompanying modules prove the oracle-relative iteration/query bounds. |
| `claims_16_17` | The paper's two-agent Nash-welfare maximizer is not FEF. |

## Executable interfaces

`NaturalInstance Agent Good` stores natural-number values, sizes, and budgets. Finite linearly ordered agent and good types are required for executable choices; `Fin n` and `Fin m` are convenient choices.

```lean
import GeneralizedAssignment

-- Exact allocation:
-- N.solveFEFx
-- N.solveFEFx_fair

-- Approximation with a rational error ε and proofs 0 < ε ≤ 1:
-- N.solveFPTAS ε hε₀ hε₁
-- N.solveFPTAS_fair ε hε₀ hε₁

-- Counts and execution certificates:
-- N.run
-- N.runFPTAS ε hε₀ hε₁
```

`RationalInstance` provides the same allocation interfaces. Its `normalize` function clears denominators separately for each agent's values and constraints. The formal proof shows that this preserves feasibility and every approximate FEFx inequality.

The exact knapsack solver uses a materialized capacity-indexed dynamic-programming table. The approximation solver uses integer value scaling and a materialized value-indexed table. These are implemented and verified here; the approximation oracle is not postulated.

## Computational scope

The development proves algorithm correctness, termination, execution traces, iteration counts, knapsack-call bounds, and bounds on the numbers of DP cells. These are mathematical cost models, not a formal cost semantics for Lean's generated machine code.

Two standard algorithmic ingredients used by the paper remain external:

* **Linear programming:** the LP constraints, key incongruity proof, threshold algorithm, and polynomial feasibility-query bound are formalized. The fractional algorithm is a classical specification; this repository does not implement a polynomial-time LP backend.
* **Matroid optimization:** the fair-allocation proofs and polynomial query bound are formalized relative to an exact maximum-weight independent-set oracle. The standard weighted-matroid optimization algorithm is not reimplemented here.

For **Theorem 5**, the reduction, parity argument, binary-search correctness, query count, and gadget-size bounds are checked. The known NP-hardness of knapsack and a general Turing-machine complexity framework are not reproved. The theorem is deliberately named `theorem_5_reduction` to make that boundary explicit.

The complexity bounds for executable allocation are stated on the normalized integer instance. Rational normalization and its fairness invariance are checked; a separate bit-operation analysis of denominator clearing is not part of the formal statements.

## Modeling details

* Values, sizes, and budgets in the mathematical model are nonnegative reals. Finite empty types and zero budgets/values are allowed.
* Charity is the actual unallocated remainder. It is never an independently chosen bundle.
* `Allocation.FEFx` compares against **strict feasible subsets**. `StrongFEFx` strengthens the charity comparison to all feasible subsets, including charity itself.
* `ApproxFEFx I q` takes the approximation **factor** `q`; `KnapsackOracle I η` takes an **error** `η`.
* Thresholds are zero-based: formal `τ a` is the paper's `τ_a - 1`. In LP modules, `m` counts the goods currently present, including the fictional good when it is added.
* The fictional good has size `1 + ∑ a, B_a`. This supports zero budgets while preserving the obstruction needed for termination.
* The density proof uses positive sizes. A separate compactness argument in `ZeroSizes.lean` extends the existence conclusion to all nonnegative sizes; it does not extend the polynomial LP algorithm to that case.
* The approximate iteration analysis uses `∑ a, log (v_a(A_a) + 1)`, explicitly handling zero initial utilities. It yields the bound `5*n*L/ε` when each total value plus one is at most `2^L`.
* The hardness gadget doubles the original input values inside the construction. This makes the paper's preliminary even-value normalization explicit.

## Layout

* `Basic`, `Fractional`, `LinearPrograms`, `DensityDomination`: definitions and fairness certificates.
* `AffinePerturbation`, `LPGeometry`, `LPIncongruity`, `DummyGood`, `Divisible`, `FractionalAlgorithm`, `ZeroSizes`: the divisible-goods proof.
* `Indivisible`, `Algorithms`, `Approximate`, `ApproximateComplexity`: swapping proofs and iteration bounds.
* `Knapsack`, `ValueKnapsack`, `ScaledKnapsack`, `NaturalInstance`, `FiniteDeletion`, `ExactAlgorithm`, `ApproximateOracle`, `ApproximateAlgorithm`, `FPTAS`, `OperationBounds`, `RationalInputs`: executable algorithms and their proofs.
* `FeasibleFamilies`, `FamilyComplexity`, `MatroidConstraints`: the matroid extension.
* `BinarySearch`, `Hardness`, `NashCounterexample`: the appendices.
* `PaperTheorems`, `Audit`, `Examples`, and `Main.lean`: entry points, trust audit, and runnable examples.
