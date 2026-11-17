import GeneralizedAssignment.Examples

open GeneralizedAssignment GeneralizedAssignment.Examples

def showExact {n m : ℕ} (label : String) (N : NaturalInstance (Fin n) (Fin m)) : IO Unit := do
  let R := N.run
  IO.println s!"{label}: {reprStr (bundles R.allocation)}; iterations={R.iterations}; knapsack-call bound={R.queries}"

def main : IO Unit := do
  IO.println "Goods and agents are numbered from zero."
  showExact "Exact, heterogeneous constraints" heterogeneous
  showExact "Exact, zero sizes and budget" zeros
  showExact "Exact, no goods" noGoods
  showExact "Exact, no agents" noAgents
  let R := heterogeneous.runFPTAS (1 / 4) (by norm_num) (by norm_num)
  IO.println s!"3/4-FEFx, heterogeneous constraints: {reprStr (bundles R.allocation)}; iterations={R.iterations}; knapsack-call bound={R.queries}"
  let A := rational.solveFEFx
  IO.println s!"Exact, rational inputs: {reprStr (bundles A)}"
  let B := rational.solveFPTAS (1 / 4) (by norm_num) (by norm_num)
  IO.println s!"3/4-FEFx, rational inputs: {reprStr (bundles B)}"
