/-
  ATP Checkers - Main executable

  Can be run on Lean files to detect common formalization errors.
-/

import AtpLinter

def main : IO Unit := do
  IO.println s!"ATP Checkers v{AtpLinter.linterVersion}"
  IO.println "Use #check_atp <declaration> in your Lean file to analyze declarations"
  IO.println ""
  IO.println "Detects:"
  IO.println "  • Truncated Nat subtraction (a - b where b might be > a)"
  IO.println "  • Division by zero (a / b where b might be 0)"
  IO.println "  • Int.toNat truncation (negative integers become 0)"
  IO.println "  • 0-indexed ranges (List.range n gives [0..n-1])"
