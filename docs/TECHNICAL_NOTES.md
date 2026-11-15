# Lean 4 check of 30 <= k(6,3) <= 32 (Erdős problem #112)

Machine-checked version of the paper "New bounds on the Erdős-Rado number k(6,3)"
(data and code: https://doi.org/10.5281/zenodo.24064871). Written 2026-11-14.

## Status

**Proved, with no `sorry`.** The final theorem is `Erdos112.k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32`
in `Erdos112/Main.lean`.

- **Lower bound, `30 ≤ k3 6`: fully kernel-checked.** It depends only on Lean's three
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The checks of the 29-vertex
  graph run inside the Lean kernel (`decide +kernel`); `native_decide` is not used.
- **Upper bound, `k3 6 ≤ 32`: proved, trusting the Lean compiler for one computation.**
  The whole argument (Lemmas 2, 4, 8, 9 and Theorem 10 of the paper, and the values
  k(2,3) <= 4, k(3,3) <= 9, k(4,3) <= 15, k(5,3) <= 23 that the paper cites) is checked by the
  kernel, except the two runs of the exhaustive search in Lemma 8, which are proved with
  `native_decide`. See "What is trusted".

## What is proved (file by file)

| File | Content | Paper |
|---|---|---|
| `Erdos112/Defs.lean` | `OGraph` (oriented graph), `adj`, `IsIndep`, `HasTT` (transitive triangle), `Free n` ({I_n, L_3}-free), `k3 n` (the number k(n,3)) | Sections 1, 2 |
| `Erdos112/Basic.lean` | Lemma 2 (`indep_outN`, `indep_inN`, `noIndep_nonN`), the degree-sum identity (`degsum`, equation (4)), Lemma 4 (`count_a`, `count_b`, `count_c`), k(2,3) <= 4, k(3,3) <= 9 and the recursion k(n+1,3) <= k(n,3) + 2n + 1 (`bound_succ`) | Section 2, Remark 13 |
| `Erdos112/Lower.lean` | The graph G_29 (`rows29` is Table 1), `G29_free : G29.Free 6` | Section 3, Appendix A, Theorem 5 |
| `Erdos112Search.lean` | The backtracking search of Lemma 8 as a Lean program (code only) | Section 4.2 |
| `Erdos112/SearchSound.lean` | `search_sound` (kernel-checked: if the search returns `true`, no graph agrees with the fixed pairs), and the two runs `check32_true`, `check23_true` (`native_decide`) | Section 4.2 |
| `Erdos112/LemmaB.lean` | `lemmaB`: every vertex of an {I_4, L_3}-free oriented graph on 14 vertices has degree 6 | Lemma 8 |
| `Erdos112/Upper.lean` | `bound_4_15`, `bound_5_23`, `lemmaA` (Lemma 9, stated as 2e(H) >= 147), `bound_6_32` | Theorem 3, Lemma 9, Theorem 10 |
| `Erdos112/Main.lean` | `lower_bound`, `upper_bound`, `k63_ge`, `k63_le`, `k63_bounds` | Theorems 1, 5, 10 |

Main statements:

```lean
theorem lower_bound : ∃ D : OGraph (Fin 29), D.Free 6
theorem upper_bound {V : Type} [Fintype V] (hV : 32 ≤ Fintype.card V) (D : OGraph V) : ¬ D.Free 6
theorem k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32
```

## What is trusted

1. **The Lean kernel and the three standard axioms**, as in every Mathlib proof.
2. **For the upper bound only: the Lean compiler**, through `native_decide`, in exactly two
   theorems: `Search.check32_true` and `Search.check23_true` (`Erdos112/SearchSound.lean`).
   Each says that the search program, run on a fixed table, returns `true`. `native_decide`
   compiles the program and runs it as native code, and Lean accepts the answer through the
   axiom `Lean.ofReduceBool`. So the trust is: the Lean compiler, the C compiler shipped with
   Lean, and the machine ran `search` correctly. The two runs take about 27 seconds of native
   code together (tens of millions of search nodes), too much to evaluate inside the kernel.
   What is not trusted: that the program is right. Its soundness (`search_sound`) is a
   kernel-checked theorem, and so is the step from an abstract graph to the fixed table
   (`relabel_core`, `lemmaB32`, `lemmaB23`).
3. **The lower bound uses no `native_decide`.** `check6_true`, `G29_tt_check` and `G29_asymm`
   are evaluated by the kernel in a few seconds.
4. **The definitions match the paper.** This is for a human to read: `Erdos112/Defs.lean` is 47
   lines, and each definition carries a comment naming the paper's section.

`#print axioms` output (file `Axioms.lean`):

- `G29_free`, `lower_bound`, `k63_ge`, `Search.search_sound`: `propext`, `Classical.choice`, `Quot.sound`.
- `lemmaB`, `upper_bound`, `k63_le`, `k63_bounds`: the same three, plus the two
  `native_decide` axioms `Search.check32_true._native.native_decide.ax_1_1` and
  `Search.check23_true._native.native_decide.ax_1_1`.

## What remains

Nothing is left as `sorry`. One possible strengthening: replace the two `native_decide` runs by
a kernel-checked proof of Lemma 8 (for example by a smaller search over the 165 ways to attach
one vertex to B_8, as in Remark 12 of the paper, or by checking a SAT certificate in Lean).
That would make the upper bound depend on the kernel alone.

## Where the Lean proof differs from the paper

The statements are the paper's. The route differs in these places, all in the direction of
assuming less:

- **Nothing is cited.** The paper cites k(3,3) = 9, k(4,3) = 15, k(5,3) = 23 and the uniqueness
  of Bermond's graph B_8. Lean proves the upper bounds k(3,3) <= 9, k(4,3) <= 15, k(5,3) <= 23
  (the last one with Lemma 8) and does not use the uniqueness of B_8.
- **Lemma 8 without B_8.** The paper fixes the eight non-neighbours of the degree-5 vertex to be
  B_8. Lean fixes less: inside the eight non-neighbours it names one vertex, its 2 out-neighbours,
  its 2 in-neighbours and its 3 non-neighbours (these numbers are forced, `OGraph.type8`), and
  the search decides all other pairs. So the Lean search contains the paper's search.
- **Both types are searched.** Types (3,2) and (2,3) are two separate runs; the converse
  argument is not used. In Lemma 9 the type (2,4) and in Theorem 10 the type (4,5) are handled
  directly, also without the converse.
- **Induced subgraphs are replaced by vertex sets.** "D[S] is {I_n, L_3}-free" is written
  "D has no transitive triangle and S contains no independent set of n vertices"
  (`NoIndep D S n`), and `Bound n N` says such an S has fewer than N vertices.
- **Arc counts are doubled.** `E D A X` is the sum over x in X of the number of neighbours of x
  in A; for disjoint sets it is e(A,X), and `E D X X` is 2e(X). Lemma 9 reads 2e(H) >= 147.
  In its proof the number t = e(P,Q) is not needed: 2e(H) >= 6 + 36 + s + 84 with s >= 22.
- **The lower bound for `k3`.** `k3 n` is an infimum, so `30 ≤ k3 6` also needs the defining set
  to be non-empty. Lean takes this from the computation-free bound k(6,3) <= 36
  (`bound_6_36`), so the lower bound does not depend on `native_decide`.

## Versions

- Lean 4.35.0 (`lean-toolchain`: `leanprover/lean4:v4.35.0`), installed by elan.
- Mathlib tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
  (pinned in `lake-manifest.json` together with its dependencies).
- The witness table in `Erdos112/Lower.lean` was generated from the deposit file
  `witness_n29_m6_anneal.txt` (SHA-256 begins `5c1cc09c6df4a0b6`, as in the paper).

## How to re-check

Needs elan (https://github.com/leanprover/elan) and about 8 GB of disk. From this folder:

```
lake exe cache get                 # downloads the compiled Mathlib (no Mathlib build needed)
nice -n 10 lake build              # checks every proof; about 1.5 minutes after the cache
nice -n 10 lake env lean Axioms.lean   # prints the axioms each main theorem depends on
grep -rn "sorry" Erdos112 Erdos112Search.lean   # prints nothing
```

Optional, the two searches of Lemma 8 as a stand-alone native program (about 30 seconds):

```
nice -n 10 lake build lemmab && nice -n 10 .lake/build/bin/lemmab
```

It prints `no completion = true` twice.

To re-check from scratch without deleting the Mathlib cache: `rm -rf .lake/build`, then
`nice -n 10 lake build`.

## Time taken

- Writing and checking the formalization: about 35 minutes of wall time on 2026-11-14
  (16:37 to 17:10 PST), including the download of Lean and of the Mathlib cache (about 4 minutes).
- A full check of this project's files after the cache is in place: about 1.5 minutes on a
  16-core Apple laptop. Of this, the two `native_decide` runs take about 27 seconds together and
  the kernel checks of the 29-vertex graph about 6 seconds.

## Notes

- AI disclosure: this formalization was written by Claude (Anthropic), a large language model,
  at the author's direction. The Lean kernel, not the model, is what checks the proofs.
- Nothing here is committed to git, and the paper was not edited.
- `lakefile.toml` sets `precompileModules = true` for the library `Erdos112Search` only. This is
  what lets `native_decide` run the search as native code. Without it the two runs would go
  through Lean's interpreter and take much longer.
