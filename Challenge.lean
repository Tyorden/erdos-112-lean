module

public import Mathlib

@[expose] public section

/-!
# Challenge: `30 ≤ k(6,3) ≤ 32` (Erdős Problem #112)

This file is the whole statement. It imports only Mathlib. The proof is in `Solution.lean`
and the folder `Erdos112/`; `comparator.json` names the one compared theorem,
`Erdos112.k63_bounds`.

## What is stated

Erdős and Rado asked for `k(n,m)`: the least `k` such that every directed graph on `k`
vertices has `n` vertices with no arc between any two of them, or a transitive tournament on
`m` vertices. Here `m = 3`. As in the paper cited below, directed graphs are taken to be
oriented graphs (no loops, at most one arc between two vertices), and a transitive
tournament on 3 vertices is a transitive triangle: `x → y`, `y → z`, `x → z`.

`k3 n` below is `k(n,3)`: the least `k` such that every oriented graph on the `k` vertices
`0, ..., k-1` has an independent set of `n` vertices or a transitive triangle.

The theorem `k63_bounds` says `30 ≤ k(6,3) ≤ 32`. In words: there is an oriented graph on 29
vertices with no transitive triangle and no 6 independent vertices, and every oriented graph
on 32 vertices has one or the other. These are bounds. They do not give the value of
`k(6,3)`, which is 30, 31 or 32, and they do not solve Erdős Problem #112.

## Source

T. S. Orden, "New bounds on the Erdős-Rado number k(6,3)", Theorem 1. Data and code:
https://doi.org/10.5281/zenodo.24064871. The definitions follow Sections 1 and 2 of that
paper, and they are word for word the definitions of `Erdos112/Defs.lean`, the file the
proof uses. (That file also defines `OGraph.adj`, "adjacent", which the statement does not
use and which is left out here.)

## Notes for the reader

* `k3` is defined with `sInf` on the natural numbers, which returns `0` for an empty set. The
  lower bound `30 ≤ k3 6` rules that case out: the set is not empty.
* `IsIndep` asks that no arc joins two members of the set. Loops cannot occur (`asymm` with
  `y = x`), so this is the usual meaning of an independent set.
* `Free n` asks for no independent set of exactly `n` vertices. A larger independent set
  contains one with exactly `n` vertices, so this is the same as "no `n` independent vertices".
* Allowing arcs in both directions between two vertices would not change `k(n,3)`: removing
  one arc of each such pair keeps the independent sets and creates no transitive triangle.
* The only axioms the proof uses are `propext`, `Quot.sound` and `Classical.choice`.
-/

namespace Erdos112

/-- An oriented graph on the vertex type `V` (paper, Section 1, first sentence): a directed
graph with no loops and at most one arc between any two vertices. `arc x y` is the paper's
`x → y`. The single axiom `asymm` gives both conditions (take `y = x` for "no loops"). -/
structure OGraph (V : Type) where
  arc : V → V → Prop
  asymm : ∀ x y, arc x y → ¬ arc y x

namespace OGraph

variable {V : Type} (D : OGraph V)

/-- A set of vertices is independent if no two of its members are adjacent
(paper, Section 2, first paragraph). Stated with arcs: no arc from a member to a member. -/
def IsIndep (T : Finset V) : Prop := ∀ x ∈ T, ∀ y ∈ T, ¬ D.arc x y

/-- The graph contains a transitive triangle: vertices `x, y, z` with
`x → y`, `y → z` and `x → z` (paper, Section 2, first paragraph). -/
def HasTT : Prop := ∃ x y z, D.arc x y ∧ D.arc y z ∧ D.arc x z

/-- `D.Free n` is the paper's "`{I_n, L_3}`-free" (Section 2, second paragraph):
no transitive triangle and no independent set of `n` vertices. -/
def Free (n : ℕ) : Prop := ¬ D.HasTT ∧ ∀ T : Finset V, D.IsIndep T → T.card ≠ n

end OGraph

/-- The Erdős-Rado number `k(n,3)` (paper, Section 1 and Section 2, second paragraph):
the least `k` such that no `{I_n, L_3}`-free oriented graph on `k` vertices exists, that is,
every oriented graph on `k` vertices has an independent set of `n` vertices or a transitive
triangle. Vertices are `Fin k = {0, ..., k-1}`. (If no such `k` existed, `sInf` would return
`0`; the theorems in `Main.lean` show the set is not empty for `n = 6`.) -/
noncomputable def k3 (n : ℕ) : ℕ := sInf {k | ∀ D : OGraph (Fin k), ¬ D.Free n}

/-- **Theorem 1 of the paper**: `30 ≤ k(6,3) ≤ 32`. The lower bound says that some oriented
graph on 29 vertices has no transitive triangle and no independent set of 6 vertices; the
upper bound says that no oriented graph on 32 vertices has both properties. -/
theorem k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32 := by
  sorry

end Erdos112
