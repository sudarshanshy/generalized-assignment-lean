# Validation record

Checked on 17 November 2026 with Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on macOS ARM64.

## Complete build

From the project directory:

```sh
LEAN_NUM_THREADS=1 lake --wfail build
```

Result: exit code **0**, `Build completed successfully (2052 jobs).` This includes cached dependency jobs and freshly checked project modules. Warnings were configured to fail the build.

All **36 project library modules** are reachable from the default `GeneralizedAssignment` target. All nine dependency repositories match the revisions in `lake-manifest.json`, with their tracked source files unmodified.

## Axiom audit

The default build runs [Audit.lean](GeneralizedAssignment/Audit.lean), which traverses the transitive axiom dependencies of every declaration in the project namespace.

```text
Axiom audit passed: 1327 project declarations, including 823 theorems.
Allowed axioms: propext, Classical.choice, Quot.sound.
```

These counts include Lean-generated declarations and are not counts of distinct results in the paper. Every checked declaration uses only the three standard axioms above. The audit rejects admitted proofs, custom axioms, and compiler-trust proof axioms. Separate printed dependency reports for the main theorem entry points confirm the same result.

## Executable examples

```sh
LEAN_NUM_THREADS=1 lake env lean --run Main.lean
```

Result: exit code **0**, with this output:

```text
Goods and agents are numbered from zero.
Exact, heterogeneous constraints: [[0], [1]]; iterations=3; knapsack-call bound=34
Exact, zero sizes and budget: [[1], [2]]; iterations=2; knapsack-call bound=28
Exact, no goods: [[], []]; iterations=0; knapsack-call bound=2
Exact, no agents: []; iterations=0; knapsack-call bound=0
3/4-FEFx, heterogeneous constraints: [[0], [1]]; iterations=3; knapsack-call bound=37
Exact, rational inputs: [[1], [2]]
3/4-FEFx, rational inputs: [[1], [2]]
```

These runs exercise the verified implementations. Their universal correctness comes from the Lean proofs; the examples are execution checks, not substitutes for those proofs. Reported knapsack-call counts are the implementation's proved accounting bounds.

The boundary between the formalized results and external complexity-theoretic ingredients is described in [README.md](README.md#computational-scope), with the paper correspondence in [COVERAGE.md](COVERAGE.md).
