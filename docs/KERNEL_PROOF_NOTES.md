# Kernel-only Lean 4 check of 30 <= k(6,3) <= 32 (Erdős problem #112)

Written 2026-11-14. This folder is a copy of `../lean/` in which the two `native_decide` runs
of Lemma 8 are replaced by computations that the Lean kernel evaluates itself. `../lean/` was
not edited.

## Result

**SUCCESS.** `Erdos112.k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32` now depends only on the three
standard axioms. No `native_decide`, no `sorry`, no new axiom. The statement and the
definitions (`Erdos112/Defs.lean`) are unchanged, byte for byte.

Output of `lake env lean Axioms.lean`:

```
'Erdos112.G29_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.k63_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.K.covered_Js' depends on axioms: [propext]
'Erdos112.K.all32' depends on axioms: [propext]
'Erdos112.K.all23' depends on axioms: [propext]
'Erdos112.Search.no_graph32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.Search.no_graph23' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.lemmaB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.k63_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos112.k63_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In `../lean/` the last five lines also listed the two axioms
`Search.check32_true._native.native_decide.ax_1_1` and
`Search.check23_true._native.native_decide.ax_1_1`. They are gone.

## What is trusted now

The Lean kernel and the three standard axioms, as in every Mathlib proof, and that the
definitions in `Erdos112/Defs.lean` (47 lines) match the paper. The Lean compiler, the C
compiler and native code are no longer trusted for any part of the theorem.

## Approach

The old search decided the 91 pairs of 14 vertices one pair at a time (tens of millions of
nodes). The new search follows Remark 12 of the paper: it works with whole rows. It proves the
same two statements as before, `Search.no_graph32` and `Search.no_graph23` (no
`{I_4, L_3}`-free oriented graph on 14 vertices agrees with the fixed pairs of type (3,2) or
(2,3)), so `LemmaB.lean` and everything after it are used as they were.

Vertex 0 is `u`, vertices 1 to 5 are its neighbours, and `J` = {6, ..., 13} are its eight
non-neighbours. A row records how one vertex is joined to the vertices of `J`, as three bit
masks (out, in, not adjacent).

1. **Step 1, the graph on `J`** (`jsearch` in `KSearch.lean`). The vertices of `J` are added
   one at a time; each new vertex gets every row over the earlier ones that respects the
   fixed pairs and closes no transitive triangle and no set of three pairwise non-adjacent
   vertices. The search finds 24 tables. They are listed in `KData.lean`, and the kernel
   checks that the list is complete (`covered_Js` in `KCover.lean`, one computation).
   As in `../lean/`, the uniqueness of Bermond's graph `B_8` is not used.
2. **Step 2, the five neighbours of `u`** (`stage2` in `KSearch.lean`). For one table, list
   every row over `J` that closes no transitive triangle (165 rows). The three pairwise
   non-adjacent neighbours of `u` must get three rows `a`, `b`, `c` such that no two of them
   share two non-adjacent non-neighbours in `J`, and no vertex of `J` is non-adjacent to all
   three. The other two neighbours must get two rows that fit `a`, `b`, `c` (not adjacent
   with no forbidden common non-neighbours, or joined by the one arc direction that a
   transitive triangle through `u` allows, with no transitive triangle through `J`), and that
   also do not share two non-adjacent non-neighbours. The three rows are tried in sorted
   order only. Step 2 finds nothing, on each of the 24 tables and for both types: these are
   the 48 theorems `s32_00`, ..., `s23_23` in `Erdos112/KCheck/`, each one a
   `decide +kernel`. `all32` and `all23` (`KCheck/All.lean`) collect them.
3. **Soundness** (`KSound.lean`, ordinary proofs). For a graph `D` that agrees with the fixed
   pairs: its table on `J` is reached by step 1 (`jsearch_true`), so it is one of the 24
   (`rowsJ_mem`); the rows of its vertices are in the lists (`gen_mem`, `att_mem`); and the
   rows of the five neighbours of `u` pass every test of step 2 (`stage2_true`), because a
   failed test would give a transitive triangle or four pairwise non-adjacent vertices.
   The sorted order costs nothing: the three vertices are renamed so that their rows are
   sorted. This contradicts step 2 returning `false`.

Why the kernel can do it: the tests are a few operations on small numbers (`Nat.land`,
`Nat.lor`, `Nat.shiftRight`, `Nat.beq`, `Nat.ble`, `Nat.add`, `Nat.pow`), which the kernel
evaluates with fast arithmetic, and the row-based search is small. The computation is split
into 49 pieces so that each one is short and they run in parallel.

## Files

| File | Content |
|---|---|
| `Erdos112/KSearch.lean` | The new search as a Lean program (code only, imports nothing) |
| `Erdos112/KData.lean` | The 24 tables on `J` (data, generated) |
| `Erdos112/KCover.lean` | `covered_Js`: the 24 tables are all that step 1 finds (kernel) |
| `Erdos112/KCheck/A0.lean` ... `A5.lean` | Step 2, type (3,2), four tables per file (kernel) |
| `Erdos112/KCheck/B0.lean` ... `B5.lean` | Step 2, type (2,3), four tables per file (kernel) |
| `Erdos112/KCheck/All.lean` | `all32`, `all23`: step 2 fails on every table |
| `Erdos112/KSound.lean` | Soundness, and the new proofs of `no_graph32`, `no_graph23` |
| `tools/gen_kdata.py`, `tools/j_tables.txt` | Generator of `KData.lean` and `KCheck/*.lean` (not trusted) |

Changed from `../lean/`:

- `Erdos112/SearchSound.lean`: the theorems `check32_true`, `check23_true` (`native_decide`)
  and the old `no_graph32`, `no_graph23` are removed. `search_sound` and `Agree` stay.
- `Erdos112/LemmaB.lean`: imports `Erdos112.KSound` (one line), and one comment.
- `Erdos112/Main.lean`, `Erdos112Search.lean`: comments only.
- `lakefile.toml`: `precompileModules` removed (it was only needed for `native_decide`).
- `Axioms.lean`: prints the new theorems too.
- `Defs.lean`, `Basic.lean`, `Lower.lean`, `Upper.lean`: unchanged.
- `README.md` is the copy of the README of `../lean/` and describes the old state; this file
  describes this folder.

## Timings (16-core Apple laptop, mains power, `nice -n 10`)

- Full check from an empty `.lake/build`: **1 minute 29 seconds** of wall time, 543 seconds of
  CPU time in total (the Mathlib cache is reused, not rebuilt).
- `covered_Js` (step 1): about 2.5 seconds.
- Each of the 48 step 2 theorems: about 9 seconds in the kernel; each `KCheck` file (four
  theorems) takes about 37 seconds, and the 12 files run in parallel.
- `KSound.lean`: about 6 seconds.
- For comparison, a single `decide +kernel` over all 24 tables at once did not finish: the
  kernel stopped with "deterministic timeout" after 5.5 minutes. Splitting by table fixed
  that. No single kernel check takes more than about 10 seconds.
- Writing and checking this version: about 25 minutes, finished 17:41 PST on 2026-11-14
  (the folder was created at 17:23).

## How to re-check

From this folder (`lean_kernel/`):

```
nice -n 10 lake build                   # checks every proof; about 1.5 minutes
nice -n 10 lake env lean Axioms.lean    # prints the axioms; expect only the three standard ones
grep -rn "sorry\|native_decide" Erdos112 Erdos112Search.lean   # only comments mention native_decide
```

To re-check from scratch: `rm -rf .lake/build`, then `nice -n 10 lake build`.

Packages: `.lake/packages` is a symbolic link to `../lean/.lake/packages`, so nothing was
downloaded again (same `lake-manifest.json`: Lean 4.35.0, Mathlib tag `v4.35.0`). To check
this folder on its own, without `../lean/`: delete the link `.lake/packages`, then run
`lake exe cache get` (downloads the compiled Mathlib) and `nice -n 10 lake build`.

To regenerate the data files: `python3 tools/gen_kdata.py` (reads `tools/j_tables.txt`).
The tables in `tools/j_tables.txt` were printed by Lean from `jsearch` itself. The generator
and the data are not trusted: if a table were missing or wrong, `covered_Js` or `all32`,
`all23` would fail to check.

Optional cross-check, the old pair-by-pair search as a native program (about 30 seconds; not
part of the proof):

```
nice -n 10 lake build lemmab && nice -n 10 .lake/build/bin/lemmab
```

It prints `no completion = true` twice.

## Notes

- AI disclosure: this kernel-only version was written by Claude (Anthropic), a large language
  model, at the author's direction. The Lean kernel, not the model, is what checks the proofs.
- Nothing here is committed to git. The paper and `../lean/` were not edited.
- Search sizes, counted with a separate C program during design (not part of the proof):
  step 1 finds 24 tables; each table has 165 rows; over the 24 tables there are 24144 sorted
  pairs and 3168 sorted triples of rows for the three non-adjacent neighbours, 12864
  candidate rows for the other two neighbours, and no surviving pair of them, for each type.
