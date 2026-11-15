/-!
# The exhaustive search behind Lemma 8 of the paper (code only, no proofs)

This is the backtracking search of Section 4.2 of the paper (file `verify_small.c` of the
deposit), written in Lean. A table records, for every ordered pair of the vertices
`0, ..., 13`, one of four states: undecided, no arc, arc forwards, arc backwards. The search
runs through a list of pairs, tries the three decided states for each, and cuts a branch as
soon as the decided pairs contain a transitive triangle (R1) or four pairwise non-adjacent
vertices (R2). `search` returns `true` exactly when every branch was cut, that is, when the
table has no completion.

The soundness proof is in `SearchSound.lean`. This file imports nothing, so that it can be
compiled to native code quickly.
-/

namespace Erdos112.Search

/-- State of an ordered pair `(i, j)`: undecided, no arc, `i → j`, or `j → i`. -/
inductive PS where
  | undec | non | fwd | bwd
  deriving DecidableEq, Repr, Inhabited

def PS.flip : PS → PS
  | .fwd => .bwd
  | .bwd => .fwd
  | s => s

abbrev Tab := Array PS

@[inline] def idx (i j : Fin 14) : Nat := 14 * i.val + j.val

@[inline] def get (a : Tab) (i j : Fin 14) : PS := a.getD (idx i j) .undec

@[inline] def set (a : Tab) (i j : Fin 14) (s : PS) : Tab :=
  (a.setIfInBounds (idx i j) s).setIfInBounds (idx j i) s.flip

def all14 : List (Fin 14) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- (R1) Given that `u → v` is recorded: is there a third vertex `z` whose pairs with `u` and
`v` are decided and make a transitive triangle with the arc `u → v`? -/
def ttBad (a : Tab) (u v : Fin 14) : Bool :=
  all14.any fun z =>
    let uz := get a u z
    let vz := get a v z
    (uz == .fwd && vz == .fwd) || (uz == .bwd && vz == .bwd) || (uz == .fwd && vz == .bwd)

/-- (R2) Is `{x, y}` contained in a set of four vertices all of whose pairs are recorded as
"no arc"? -/
def indepBad (a : Tab) (x y : Fin 14) : Bool :=
  x != y && get a x y == .non &&
  all14.any fun z =>
    z != x && z != y && get a x z == .non && get a y z == .non &&
    all14.any fun w =>
      decide (z < w) && w != x && w != y && get a x w == .non && get a y w == .non
        && get a z w == .non

/-- `search ps a = true` means: no way of deciding the pairs in `ps`, starting from the table
`a`, survives the rules (R1) and (R2). -/
def search : List (Fin 14 × Fin 14) → Tab → Bool
  | [], _ => false
  | (x, y) :: ps, a =>
    (let a1 := set a x y .non; indepBad a1 x y || search ps a1) &&
    (let a2 := set a x y .fwd; ttBad a2 x y || search ps a2) &&
    (let a3 := set a x y .bwd; ttBad a3 y x || search ps a3)

/-- The table in which exactly the listed pairs are decided. -/
def init (l : List (Fin 14 × Fin 14 × PS)) : Tab :=
  l.foldl (fun a e => set a e.1 e.2.1 e.2.2) (Array.replicate 196 .undec)

/-- Fixed pairs, type (3,2). Vertex 0 is `u`; 1, 2, 3 are its out-neighbours; 4, 5 its
in-neighbours; 6, ..., 13 its non-neighbours. Inside the non-neighbours, 6 is a vertex `w`,
7, 8 are its out-neighbours, 9, 10 its in-neighbours and 11, 12, 13 its non-neighbours. -/
def fixed32 : List (Fin 14 × Fin 14 × PS) :=
  [(0, 1, .fwd), (0, 2, .fwd), (0, 3, .fwd), (0, 4, .bwd), (0, 5, .bwd),
   (0, 6, .non), (0, 7, .non), (0, 8, .non), (0, 9, .non), (0, 10, .non), (0, 11, .non),
   (0, 12, .non), (0, 13, .non),
   (1, 2, .non), (1, 3, .non), (2, 3, .non), (4, 5, .non),
   (6, 7, .fwd), (6, 8, .fwd), (6, 9, .bwd), (6, 10, .bwd),
   (6, 11, .non), (6, 12, .non), (6, 13, .non), (7, 8, .non), (9, 10, .non)]

/-- Fixed pairs, type (2,3): as `fixed32`, but 1, 2 are the out-neighbours of 0 and 3, 4, 5
its in-neighbours. -/
def fixed23 : List (Fin 14 × Fin 14 × PS) :=
  [(0, 1, .fwd), (0, 2, .fwd), (0, 3, .bwd), (0, 4, .bwd), (0, 5, .bwd),
   (0, 6, .non), (0, 7, .non), (0, 8, .non), (0, 9, .non), (0, 10, .non), (0, 11, .non),
   (0, 12, .non), (0, 13, .non),
   (1, 2, .non), (3, 4, .non), (3, 5, .non), (4, 5, .non),
   (6, 7, .fwd), (6, 8, .fwd), (6, 9, .bwd), (6, 10, .bwd),
   (6, 11, .non), (6, 12, .non), (6, 13, .non), (7, 8, .non), (9, 10, .non)]

/-- The undecided pairs inside `{7, ..., 13}`. -/
def pairsJ : List (Fin 14 × Fin 14) :=
  [(11, 12), (11, 13), (12, 13), (7, 9), (7, 10), (8, 9), (8, 10),
   (7, 11), (7, 12), (7, 13), (8, 11), (8, 12), (8, 13),
   (9, 11), (9, 12), (9, 13), (10, 11), (10, 12), (10, 13)]

def row (w : Fin 14) : List (Fin 14 × Fin 14) :=
  [(w, 6), (w, 7), (w, 8), (w, 9), (w, 10), (w, 11), (w, 12), (w, 13)]

/-- Search order, type (3,2). -/
def pairs32 : List (Fin 14 × Fin 14) :=
  pairsJ ++ row 1 ++ row 2 ++ row 3 ++ row 4 ++ [(1, 4), (2, 4), (3, 4)]
    ++ row 5 ++ [(1, 5), (2, 5), (3, 5)]

/-- Search order, type (2,3). -/
def pairs23 : List (Fin 14 × Fin 14) :=
  pairsJ ++ row 3 ++ row 4 ++ row 5 ++ row 1 ++ [(1, 3), (1, 4), (1, 5)]
    ++ row 2 ++ [(2, 3), (2, 4), (2, 5)]

/-- The computation for a vertex of type (3,2). (The `Unit` argument keeps the compiled
program from running the search when the module is loaded.) -/
def check32 (_ : Unit) : Bool := search pairs32 (init fixed32)

/-- The computation for a vertex of type (2,3). -/
def check23 (_ : Unit) : Bool := search pairs23 (init fixed23)

end Erdos112.Search
