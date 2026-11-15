import Erdos112Search
open Erdos112.Search

/-- Runs the two searches of Lemma 8 as a native program and prints the results. -/
def main : IO Unit := do
  IO.println s!"check32 (type (3,2)): no completion = {check32 ()}"
  IO.println s!"check23 (type (2,3)): no completion = {check23 ()}"
