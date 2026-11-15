module

public import Erdos112.Main

/-!
# Solution: `30 ≤ k(6,3) ≤ 32` (Erdős Problem #112)

This module imports the proof. It adds no declaration of its own: every declaration of
`Challenge.lean` is already in the imported modules under the same name.

* The definitions `Erdos112.OGraph`, `OGraph.adj`, `OGraph.IsIndep`, `OGraph.HasTT`,
  `OGraph.Free` and `Erdos112.k3` are in `Erdos112/Defs.lean`, word for word as in
  `Challenge.lean`.
* The theorem `Erdos112.k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32` is proved at the end of
  `Erdos112/Main.lean`, from `Erdos112.k63_ge` (the 29-vertex graph of `Erdos112/Lower.lean`)
  and `Erdos112.k63_le` (the upper-bound argument of `Erdos112/Basic.lean`,
  `Erdos112/LemmaB.lean` and `Erdos112/Upper.lean`, with the kernel-checked case analysis of
  `Erdos112/KSound.lean`).

Comparator checks that `Erdos112.k63_bounds` here has the same statement as in
`Challenge.lean`, built on the same definitions, and that its proof uses only the axioms
`propext`, `Quot.sound` and `Classical.choice`.
-/
