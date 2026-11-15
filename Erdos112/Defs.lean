module

public import Mathlib

@[expose] public section

/-!
# Definitions for the Erdős-Rado number k(n,3)

These follow Sections 1 and 2 of the paper "New bounds on the Erdős-Rado number k(6,3)".
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

/-- Two vertices are adjacent if there is an arc between them in either direction
(paper, Section 2, first paragraph). -/
def adj (x y : V) : Prop := D.arc x y ∨ D.arc y x

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

end Erdos112
