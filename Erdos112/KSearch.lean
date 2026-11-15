/-!
# A small search for Lemma 8 that the Lean kernel can evaluate (code only, no proofs)

The vertices `6, ..., 13` (the non-neighbours of the vertex `0`) are called `J 0, ..., J 7`.
A `Row` describes how one vertex `v` is joined to `J 0, ..., J (n-1)`, by three bit masks:
bit `j` of `o` is set when `v → J j`, bit `j` of `i` when `J j → v`, and bit `j` of `n` when
`v` and `J j` are not adjacent.

Step 1 (`jsearch`) lists every way to join `J 1, ..., J 7`, one vertex at a time, to the
vertices before it, with no transitive triangle and no three pairwise non-adjacent vertices.
Step 2 (`stage2`) lists the ways to attach one further vertex to `J 0, ..., J 7` without a
transitive triangle (165 ways for each graph found in step 1), and looks for three attachments
for the three pairwise non-adjacent neighbours of `0` and two attachments for the other two
neighbours that pass a few necessary conditions. `stage2 dir rows = false` says that nothing
passes. The 24 graphs found by step 1 are listed in `KData.lean`, and step 2 is run on each
of them separately (`KCheck*.lean`), so that every kernel computation is small.

Only `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.shiftRight`, `Nat.add`, `Nat.mul` and
`Nat.pow` on numerals are used, which the kernel evaluates with fast arithmetic.
The soundness proof is in `KSound.lean`.
-/

namespace Erdos112.K

structure Row where
  o : Nat
  i : Nat
  n : Nat

/-- `a = 0`. -/
def z (a : Nat) : Bool := Nat.beq a 0

/-- Bit `j` of `m`. -/
def tb (m j : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m j) 1) 1

/-- All rows for a new vertex `v` over the vertices described by the list (whose head is
`J j`), extending the partial row `r` (which covers `J 0, ..., J (j-1)`). State 0: not
adjacent, state 1: `v → J j`, state 2: `J j → v`. A state is dropped when it closes a
transitive triangle with an earlier `J i`, when `allow j state` is false, or (if `chk3`)
when it makes `v`, `J j` and an earlier `J i` pairwise non-adjacent. -/
def gen (chk3 : Bool) (allow : Nat → Nat → Bool) : List Row → Nat → Row → List Row
  | [], _, r => [r]
  | e :: rest, j, r =>
    (if allow j 0 && (!chk3 || z (Nat.land e.n r.n)) then
        gen chk3 allow rest (j + 1) ⟨r.o, r.i, r.n + 2 ^ j⟩ else []) ++
    ((if allow j 1 && z (Nat.land (Nat.lor e.o e.i) r.o) && z (Nat.land e.i r.i) then
        gen chk3 allow rest (j + 1) ⟨r.o + 2 ^ j, r.i, r.n⟩ else []) ++
     (if allow j 2 && z (Nat.land (Nat.lor e.o e.i) r.i) && z (Nat.land e.o r.o) then
        gen chk3 allow rest (j + 1) ⟨r.o, r.i + 2 ^ j, r.n⟩ else []))

/-- The pairs fixed in advance inside `J`: `J 0 → J 1, J 2`; `J 3, J 4 → J 0`; `J 0` is not
adjacent to `J 5, J 6, J 7`; `J 1, J 2` are not adjacent; `J 3, J 4` are not adjacent.
`allowJ v j s` says whether state `s` is allowed for the pair (`J v`, `J j`). -/
def allowJ (v j s : Nat) : Bool :=
  if Nat.beq j 0 then
    if Nat.ble v 2 then Nat.beq s 2 else if Nat.ble v 4 then Nat.beq s 1 else Nat.beq s 0
  else if Nat.beq j 1 && Nat.beq v 2 then Nat.beq s 0
  else if Nat.beq j 3 && Nat.beq v 4 then Nat.beq s 0
  else true

def allowAll (_ _ : Nat) : Bool := true

def row0 : Row := ⟨0, 0, 0⟩

/-- Step 1: extend the rows of `J 0, ..., J (v-1)` by the rows of `m` further vertices in all
ways, and ask `k` at the end. -/
def jsearch (k : List Row → Bool) : Nat → Nat → List Row → Bool
  | 0, _, rows => k rows
  | m + 1, v, rows =>
    (gen true (allowJ v) rows 0 row0).any fun r => jsearch k m (v + 1) (rows ++ [r])

/-- Does the set `M` of `J`-vertices contain two non-adjacent vertices? -/
def nonpair (M : Nat) : List Row → Nat → Bool
  | [], _ => false
  | e :: rest, j => (tb M j && !z (Nat.land e.n M)) || nonpair M rest (j + 1)

/-- Two attached vertices may be non-adjacent: their common non-neighbours in `J` are
pairwise adjacent. -/
def cn (rows : List Row) (a b : Row) : Bool := !nonpair (Nat.land a.n b.n) rows 0

/-- An arc `p → q` between two attached vertices closes no transitive triangle with `J`. -/
def cf (p q : Row) : Bool :=
  z (Nat.land p.o q.o) && z (Nat.land p.i q.i) && z (Nat.land p.o q.i)

/-- The only arc allowed between a "big" and a "small" vertex goes from big to small when
`dir` is true (type (3,2)) and from small to big otherwise (type (2,3)). -/
def cross (dir : Bool) (big small : Row) : Bool := if dir then cf big small else cf small big

def xok (rows : List Row) (dir : Bool) (big small : Row) : Bool :=
  cross dir big small || cn rows big small

def le (a b : Row) : Bool := Nat.ble (a.o * 256 + a.i) (b.o * 256 + b.i)

/-- Step 2. -/
def stage2 (dir : Bool) (rows : List Row) : Bool :=
  let A := gen false allowAll rows 0 row0
  A.any fun a =>
    let Ca := A.filter fun b => le a b && cn rows a b
    Ca.any fun b => Ca.any fun c =>
      le b c && cn rows b c && z (Nat.land (Nat.land a.n b.n) c.n) &&
      (let S := A.filter fun q => xok rows dir a q && xok rows dir b q && xok rows dir c q
       S.any fun q1 => S.any fun q2 => cn rows q1 q2)

def rowEq (a b : Row) : Bool := Nat.beq a.o b.o && Nat.beq a.i b.i && Nat.beq a.n b.n

def rowsEq : List Row → List Row → Bool
  | [], [] => true
  | a :: as, b :: bs => rowEq a b && rowsEq as bs
  | _, _ => false

/-- `covered Js = true` says: every graph on `J` found by step 1 is in the list `Js`. -/
def covered (Js : List (List Row)) : Bool :=
  !(jsearch (fun rows => !(Js.any fun J => rowsEq rows J)) 7 1 [row0])

end Erdos112.K
