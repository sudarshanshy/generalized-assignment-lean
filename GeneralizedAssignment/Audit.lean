import GeneralizedAssignment.PaperTheorems
import GeneralizedAssignment.Examples
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Every declaration in the project namespace is checked transitively.
Only Lean's standard propositional extensionality, classical choice,
and quotient soundness axioms are accepted. In particular, an admitted
proof or a compiler-trust axiom makes this module fail to elaborate.
-/

open Lean Elab Command

run_cmd do
  let declarations := (← getEnv).constants.toList.filter fun (name, _) =>
    (`GeneralizedAssignment).isPrefixOf name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut theoremCount : Nat := 0
  for (name, info) in declarations do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved axiom {axiomName} in the dependencies of {name}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  logInfo m!"Axiom audit passed: {declarations.length} project declarations, including {theoremCount} theorems. Allowed axioms: propext, Classical.choice, Quot.sound."

#print axioms GeneralizedAssignment.Paper.theorem_1
#print axioms GeneralizedAssignment.Paper.theorem_1_algorithm
#print axioms GeneralizedAssignment.Paper.theorem_2
#print axioms GeneralizedAssignment.Paper.theorem_3
#print axioms GeneralizedAssignment.Paper.theorem_4
#print axioms GeneralizedAssignment.Paper.theorem_4_rational
#print axioms GeneralizedAssignment.Paper.theorem_5_reduction
#print axioms GeneralizedAssignment.Paper.remark_1
#print axioms GeneralizedAssignment.Paper.claims_16_17
