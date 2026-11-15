module

public import Lean

/-!
# A local check that `Challenge` and `Solution` state the same theorem

Palomar's verifier runs Comparator in a Linux sandbox. On a machine without that sandbox,
this script gives a weaker local check of the same three facts. It loads the compiled
`Challenge` and `Solution` modules as two separate environments and checks, for each theorem
named on the command line:

1. the theorem has the same universe parameters and the same type in both;
2. every constant its type refers to, and every constant those refer to in turn (through
   types, definition values, constructors and recursor rules), is identical in both; and
3. the proof in `Solution` depends on no axiom other than `propext`, `Quot.sound` and
   `Classical.choice`.

It does not replay proofs through a kernel; `lake build` and the external checkers do that.

Run from the repository root, after `lake build`:

    lake env lean --run tools/CompareStatements.lean Erdos112.k63_bounds
-/

open Lean

/-- The constants an expression mentions. -/
def usedIn (e : Expr) : NameSet := e.getUsedConstantsAsSet

/-- All expressions that make up the statement of a constant: its type, its value if it is a
definition, and the constructors and recursor rules of an inductive type. Theorem proofs are
left out when `proofs` is `false`. -/
def exprsOf (c : ConstantInfo) (proofs : Bool) : List Expr × List Name :=
  match c with
  | .defnInfo v => ([v.type, v.value], [])
  | .opaqueInfo v => ([v.type, v.value], [])
  | .thmInfo v => (if proofs then [v.type, v.value] else [v.type], [])
  | .inductInfo v => ([v.type], v.ctors ++ v.all)
  | .ctorInfo v => ([v.type], [v.induct])
  | .recInfo v => (v.type :: v.rules.map (·.rhs), v.all)
  | .axiomInfo v => ([v.type], [])
  | .quotInfo v => ([v.type], [])

/-- The constants reachable from `roots`. -/
partial def closure (env : Environment) (proofs : Bool) (roots : List Name) : IO NameSet := do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | throw <| IO.userError s!"unknown constant {n}"
    let (es, ns) := exprsOf c proofs
    for e in es do
      for m in (usedIn e).toList do
        if !seen.contains m then todo := m :: todo
    for m in ns do
      if !seen.contains m then todo := m :: todo
  return seen

/-- A short name for the kind of a constant. -/
def kind : ConstantInfo → String
  | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .thmInfo _ => "theorem"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
  | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

/-- Are two constants identical as statements? (Theorem proofs are not compared.) -/
def same (a b : ConstantInfo) : Bool :=
  kind a == kind b && a.levelParams == b.levelParams && a.type == b.type &&
  match a, b with
  | .defnInfo x, .defnInfo y => x.value == y.value && x.safety == y.safety
  | .opaqueInfo x, .opaqueInfo y => x.value == y.value && x.isUnsafe == y.isUnsafe
  | .inductInfo x, .inductInfo y =>
      x.numParams == y.numParams && x.numIndices == y.numIndices && x.ctors == y.ctors &&
      x.all == y.all && x.isUnsafe == y.isUnsafe
  | .ctorInfo x, .ctorInfo y =>
      x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
      x.numFields == y.numFields
  | .recInfo x, .recInfo y =>
      x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.numMotives == y.numMotives && x.numMinors == y.numMinors && x.k == y.k &&
      x.rules.map (·.rhs) == y.rules.map (·.rhs) && x.rules.map (·.ctor) == y.rules.map (·.ctor)
  | .quotInfo x, .quotInfo y => x.kind == y.kind
  | _, _ => true

def permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]

public unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run tools/CompareStatements.lean <theorem> ..."
    return 2
  initSearchPath (← findSysroot)
  let chal ← importModules #[{ module := `Challenge }] {} (trustLevel := 1024)
  let sol ← importModules #[{ module := `Solution }] {} (trustLevel := 1024)
  let mut ok := true
  for a in args do
    let thm := a.toName
    let some c := chal.find? thm | throw <| IO.userError s!"Challenge has no {thm}"
    let some s := sol.find? thm | throw <| IO.userError s!"Solution has no {thm}"
    unless kind s == "theorem" do
      ok := false; IO.println s!"FAIL {thm}: in Solution it is a {kind s}, not a theorem"
    unless c.levelParams == s.levelParams && c.type == s.type do
      ok := false; IO.println s!"FAIL {thm}: the type differs between Challenge and Solution"
    -- 2. everything the statement refers to
    let stmt ← closure chal false (usedIn c.type).toList
    let mut bad := 0
    let mut own : Array Name := #[]
    for n in stmt.toList do
      let some x := chal.find? n | unreachable!
      match sol.find? n with
      | none => bad := bad + 1; IO.println s!"FAIL {n}: missing from Solution"
      | some y =>
        unless same x y do
          bad := bad + 1; IO.println s!"FAIL {n}: differs between Challenge and Solution"
      if (chal.getModuleIdxFor? n).map (chal.header.moduleNames[·]!) == some `Challenge then
        own := own.push n
    if bad > 0 then ok := false
    IO.println s!"{thm}: type identical in Challenge and Solution: {c.levelParams == s.levelParams && c.type == s.type}"
    IO.println s!"{thm}: {stmt.size} constants in the statement's closure, {bad} differ"
    IO.println s!"{thm}: of these, declared in Challenge itself: {own.qsort (·.toString < ·.toString)}"
    -- 3. axioms of the Solution proof
    let all ← closure sol true [thm]
    let axs := all.toList.filter fun n => (sol.find? n).any (kind · == "axiom")
    IO.println s!"{thm}: axioms used by the Solution proof: {axs.toArray.qsort (·.toString < ·.toString)}"
    for n in axs do
      unless permitted.contains n do
        ok := false; IO.println s!"FAIL {thm}: uses the axiom {n}"
    -- the Challenge placeholder really is a placeholder
    let call ← closure chal true [thm]
    IO.println s!"{thm}: Challenge placeholder uses sorryAx: {call.contains ``sorryAx}"
  IO.println (if ok then "RESULT: PASS" else "RESULT: FAIL")
  return if ok then 0 else 1
