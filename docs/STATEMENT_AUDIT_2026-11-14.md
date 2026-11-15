# Independent audit of the Lean 4 formalization of 30 <= k(6,3) <= 32

Auditor: Claude Opus 5.5 (a separate session from the one that wrote the formalization).
Date: 2026-11-14, 17:14 PST. No file in the project was edited; the rebuild was done on a
copy in a scratch directory.

## Verdict: SOUND

The final theorem `Erdos112.k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32` states the paper's
Theorem 1 with the paper's definition of k(n,3). It builds from clean with no `sorry`, and
it depends on the three standard axioms plus exactly two `native_decide` axioms, for the
two search runs of Lemma 8. The lower bound depends on the three standard axioms alone.
I found no blocking problems. The minor notes are at the end.

## 1. Definitions (`Erdos112/Defs.lean`)

```lean
structure OGraph (V : Type) where
  arc : V → V → Prop
  asymm : ∀ x y, arc x y → ¬ arc y x
def adj (x y : V) : Prop := D.arc x y ∨ D.arc y x
def IsIndep (T : Finset V) : Prop := ∀ x ∈ T, ∀ y ∈ T, ¬ D.arc x y
def HasTT : Prop := ∃ x y z, D.arc x y ∧ D.arc y z ∧ D.arc x z
def Free (n : ℕ) : Prop := ¬ D.HasTT ∧ ∀ T : Finset V, D.IsIndep T → T.card ≠ n
noncomputable def k3 (n : ℕ) : ℕ := sInf {k | ∀ D : OGraph (Fin k), ¬ D.Free n}
```

- **Oriented graph.** `asymm` with x = y gives irreflexivity (`arc_irrefl` in Basic.lean
  derives it). So this is loopless with at most one arc per pair, as in the paper (Section 1).
  `arc` is an arbitrary `Prop`. No decidability is assumed, so no graph is left out.
- **Independent set.** No arc from any member to any member, so no arc in either direction.
  Correct. The case x = y is harmless because there are no loops.
- **Transitive triangle.** `x → y`, `y → z`, `x → z`. Distinctness is not required, but it
  follows: asymmetry and irreflexivity rule out any repeated vertex. This matches the paper's
  L_3 (k63_bounds.tex, Section 2: "three vertices x,y,z with x→y, y→z and x→z").
- **Free n.** "no independent set of exactly n vertices". Because independence passes to
  subsets, this is the same as "no independent set of at least n vertices". It matches the
  paper's {I_n, L_3}-free.
- **k3.** The paper (lines 47-49 and 121-122) says: "the least k such that every oriented graph
  on k vertices contains an independent set of n vertices or a transitive tournament on m
  vertices" and "the least k such that no {I_n,L_3}-free oriented graph on k vertices exists".
  `k3 n` is word for word the second form, with vertices `Fin k`. Every finite vertex set of
  size k is in bijection with `Fin k`, so using `Fin k` loses nothing.

**The sInf and monotonicity concerns (checked).**
- *Empty set gives 0.* For the upper bound, `Nat.sInf_le` needs 32 to be in the set, and that
  membership is proved (`k63_le := Nat.sInf_le (fun D => upper_bound (by simp) D)`). For the
  lower bound, `le_csInf` needs the set to be non-empty. That is supplied by
  `⟨36, fun D => not_free_of_bound bound_6_36 (by simp) D⟩`, where 36 comes from the
  computation-free recursion. So the 0 trap is closed on both sides.
- *Monotonicity.* `k3` as a least element does not need it. The two bounds say: 32 is in the
  set, and no k <= 29 is in the set. Then the least element is between 30 and 32. That is
  the paper's statement. Monotonicity is also proved in both directions.
  `upper_bound` covers every vertex type with `32 ≤ Fintype.card V`, so every k >= 32 is in
  the set. `exists_free_of_le` restricts G_29 to its first k vertices, so every k <= 29 is
  outside the set. This matches the paper's sentence that free graphs exist "on every number of
  vertices below k(n,3) and on no number from k(n,3) upwards".
- *Off-by-one in the lower bound.* `lower_bound : ∃ D : OGraph (Fin 29), D.Free 6` shows that 29
  is not in the set. `k63_ge` then argues by contradiction for each k < 30
  (`exists_free_of_le (show k ≤ 29 by omega)`). The result 30 <= k3 6 is correct, with no
  off-by-one error.

## 2. The witness

- SHA-256 of `zenodo_deposit/witness_n29_m6_anneal.txt` (and of the copies in `results/` and
  `paper/ancillary/`): `5c1cc09c6df4a0b6dba4c3171c2eb620c89993b33a097da428ebbd176cacb3fa`.
  It begins `5c1cc09c6df4a0b6`, as the README and the paper (k63_bounds.tex line 280) say.
- A script parsed `rows29` from `Erdos112/Lower.lean` and the 29 data rows of the deposit file.
  The two are identical (29 rows, 140 arcs, same out-neighbour lists in the same order). Lean
  proves the count separately as `G29_arc_count`.
- `G29.arc i j := arcB i.val j.val = true`, with `arcB i j := (rows29.getD i []).contains j`.
  So row i lists the out-neighbours of i, which is the deposit format ("vertex: out-neighbours
  (arc v->w ...)").
- `G29_asymm`, `G29_tt_check` and `check6_true` use `decide +kernel`, which the kernel
  evaluates. `G29_no_indep6` connects `check6` to every 6-element Finset through
  `orderEmbOfFin`. `#print axioms G29_free` shows only the three standard axioms.

## 3. The trusted computation and `search_sound`

`#print axioms` (my clean rebuild, Lean 4.35.0, Mathlib 56a00585...):

```
'Erdos112.G29_free'            : [propext, Classical.choice, Quot.sound]
'Erdos112.lower_bound'         : [propext, Classical.choice, Quot.sound]
'Erdos112.k63_ge'              : [propext, Classical.choice, Quot.sound]
'Erdos112.Search.search_sound' : [propext, Classical.choice, Quot.sound]
'Erdos112.lemmaB'      : [propext, Classical.choice, Quot.sound,
                          Search.check23_true._native.native_decide.ax_1_1,
                          Search.check32_true._native.native_decide.ax_1_1]
'Erdos112.upper_bound', 'Erdos112.k63_le', 'Erdos112.k63_bounds' : the same five
```

Nothing else appears. The two extra axioms are the ones `native_decide` creates for
`theorem check32_true : check32 () = true := by native_decide` and
`theorem check23_true : check23 () = true := by native_decide`.

**`search_sound` is a real connection, not a vacuous one.**

```lean
theorem search_sound (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) :
    ∀ (ps : List (Fin 14 × Fin 14)) (a : Tab), Ext D a → search ps a = false
```

- `search [] _ = false`. Each step requires all three branches (no arc, forward, backward) to
  be cut. The proof follows the branch that agrees with D. In that branch the cut tests are
  shown to be false: `ttBad_sound` turns a hit into a real `HasTT`, and `indepBad_sound` turns
  a hit into a real independent 4-set with card 4. Each proof is checked case by case
  against `Agree`. So `search ps a = true` implies that no {I_4, L_3}-free D agrees with `a`.
  This holds for any list `ps`. Soundness does not depend on the search order or on the list
  covering every pair, so a mistake in `pairs32`/`pairs23` could only make the search return
  `false`, never give a wrong `true`.
- All three hypotheses are used. `hTT` and `hI` are used in the cut cases, and `Ext D a` is
  used through `ext_set`. `Ext` is the real agreement condition for every ordered pair, built
  from the empty table by `ext_empty` and from the fixed pairs by `ext_init`.
- `no_graph32` and `no_graph23` combine `search_sound` with the `native_decide` result.
  `relabel_core` pulls an arbitrary graph on a 14-set back to `Fin 14`. It proves that the
  naming is injective and that `I_4`/`L_3`-freeness carries over. `lemmaB32` and `lemmaB23`
  prove that the named graph agrees with `fixed32`/`fixed23`. Everything outside the two
  `check*_true` theorems is kernel-checked.
- Cross-check: the stand-alone native runner `lemmab` (same Lean definitions) printed
  `no completion = true` twice in 27.3 s, which agrees with the `native_decide` runs.

## 4. Search for checking-weakening constructs

I searched all project sources (`Erdos112/*.lean`, `Erdos112Search.lean`, `Erdos112.lean`,
`Axioms.lean`, `LemmaBMain.lean`) for `sorry`, `admit`, `axiom`, `set_option`,
`implemented_by`, `extern`, `unsafe`, `opaque`, `partial`, `macro`, `elab`, `csimp`,
`skipKernel` and `debug.`. Results:
- No `sorry`, `admit`, `set_option`, `implemented_by`, `@[extern]`, `unsafe`, `opaque`,
  `partial`, `csimp`, macros or elaborators.
- The word "axiom" appears only in comments (Defs.lean line 13; SearchSound.lean line 13).
- `native_decide` appears exactly twice, at SearchSound.lean lines 179 and 182.
- `open scoped Classical` in LemmaB.lean is harmless (Classical.choice is already standard).
- `lakefile.toml`: `precompileModules = true` for `Erdos112Search` only. This changes how
  `native_decide` executes the code (native rather than interpreted). It does not change what
  the kernel checks.
- The dependency checkouts in `.lake/packages` are clean git trees at the commits pinned in
  `lake-manifest.json` (mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; 0 modified tracked
  files in any package).

## 5. Rebuild

On AC power (`pmset`: "Now drawing from 'AC Power'"). I copied the project sources, without
`.lake/build`, to a scratch directory, linked to the same `.lake/packages`, and ran:

- `nice -n 10 lake build`: "Build completed successfully (9058 jobs)", 1 min 21 s wall time.
  Every project module was rebuilt from scratch. The only warning was the Mathlib
  module-system notice on Defs.lean, which is harmless. No errors and no `sorry` warnings.
- `nice -n 10 lake env lean Axioms.lean`: the output shown in section 3.

## Minor notes (none blocking)

1. In wording for the paper or the site, "machine-checked" should come with the
   `native_decide` qualifier for the upper bound. The README already does this. Strictly,
   the trust in `native_decide` is wider than "the compiler". It covers the Lean compiler
   and code generator, the C compiler, the runtime and the hardware, and it also trusts
   that the compiled code matches the definitions the kernel sees. The project has no
   `implemented_by`/`extern` overrides, which removes the usual way that match can fail.
2. Within the trusted part, the search code is ordinary Lean that a reader can audit. Its
   soundness is proved, so the trust is only that it was *executed* correctly. Two other
   results agree with it. The native runner gives the same answer. The paper's separate
   C program (`verify_small.c`, modes glue8/glue8r) reports "0 completions" for the narrower
   case in which B_8 is fixed, and SAT solvers report the same. I did not rerun the C program
   in this audit.
3. The README's "Where the Lean proof differs" section is accurate as far as I checked
   (Lemma 8 fixes less than B_8; both types are searched; nothing is cited). Because every
   intermediate lemma is kernel-checked, any slip in those intermediate statements could
   not make the final theorem false. They only affect how closely the Lean route follows
   the paper.

## What is machine-checked and what is trusted (plain statement)

The Lean 4 proof assistant (version 4.35.0, with Mathlib) checks the statement
30 <= k(6,3) <= 32, where k(6,3) is defined in Lean exactly as in the paper: the least k
such that every oriented graph on k vertices has 6 pairwise non-adjacent vertices or a
transitive triangle. The lower bound, that the 29-vertex graph of the paper (identical to the
deposited file) has neither structure, is checked entirely by Lean's kernel. It uses only
Lean's three standard logical axioms. The upper bound is also proved in Lean, with no gaps
and without citing earlier results. The kernel checks the whole argument, and it checks that
the computer search used in Lemma 8 is correct as a program. The one exception is the two
runs of that search. Lean runs them as compiled native code (`native_decide`, about 27
seconds) and accepts their result. For the upper bound, the trusted base is therefore the
Lean kernel plus the Lean compiler, the C compiler and the machine that ran those two
searches. The paper's separate C program and SAT checks reach the same conclusion for
Lemma 8. Those programs are outside Lean.
