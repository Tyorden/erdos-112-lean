# Erdős Problem #112: a machine-checked proof that 30 ≤ k(6,3) ≤ 32

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24237181.svg)](https://doi.org/10.5281/zenodo.24237181)

**The first machine-checked result on Erdős Problem #112.** This repository contains a complete Lean 4 proof of new bounds on the Erdős-Rado number k(6,3), checked entirely by Lean's kernel: no `sorry`, no `native_decide`, and no axioms beyond Lean's three standard ones.

```lean
theorem Erdos112.k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32
```

Before this work the best bounds that followed from published results were 26 ≤ k(6,3) ≤ 33 (the best lower bound printed explicitly was 18), and every known value of k(n,3) (n = 3, 4, 5) fit the formula n² − n + 3, which predicts 33. The proof shows that the formula breaks at n = 6, and narrows the answer to three possible values.

- **Author:** Tyler Satchel Orden, independent researcher, ORCID [0009-0004-9205-7422](https://orcid.org/0009-0004-9205-7422)
- **Date of this proof:** 14 November 2026. v1.0 (17:22 PST) proved the bounds with two compiled search runs; v1.1 (the same evening) removed them, so the whole proof is checked by Lean's kernel. Archived at Zenodo, https://doi.org/10.5281/zenodo.24237181
- **Paper:** T. S. Orden, *New bounds on the Erdős-Rado number k(6,3)*, submitted to The Electronic Journal of Combinatorics (November 2026). Data and code: https://doi.org/10.5281/zenodo.24064871
- **Problem page:** [Erdős Problem #112](https://www.erdosproblems.com/112); community database entry in [teorth/erdosproblems](https://github.com/teorth/erdosproblems)

## The problem

Erdős and Rado asked for k(n,m): the least k such that every directed graph on k vertices contains either n vertices with no arc between any two of them, or a transitive tournament on m vertices. For m = 3 the exact values were known only up to n = 5: k(3,3) = 9, k(4,3) = 15, k(5,3) = 23 (Bermond; Ihringer, Rajendraprasad and Weinert, 2021).

## What is proved

| | Statement | How it is checked |
|---|---|---|
| Lower bound | an oriented graph on 29 vertices with no transitive triangle and no 6 independent vertices, so k(6,3) ≥ 30 | entirely by Lean's kernel (`decide +kernel`), only Lean's three standard axioms |
| Upper bound | every oriented graph on 32 or more vertices has a transitive triangle or 6 independent vertices, so k(6,3) ≤ 32 | entirely by Lean's kernel, including the exhaustive case analysis of Lemma 8 (49 kernel computations, none over about 10 seconds) |
| Earlier values | k(3,3) ≤ 9, k(4,3) ≤ 15, k(5,3) ≤ 23 | re-proved in Lean, not cited |

`#print axioms Erdos112.k63_bounds` lists only `propext`, `Classical.choice` and `Quot.sound`, the axioms every Mathlib proof uses. Nothing is trusted beyond the Lean kernel: no compiled code, no external solver, no citation of earlier results. The definition of k(n,3) in `Erdos112/Defs.lean` (47 lines) is word for word the paper's: the least k such that every oriented graph on k vertices has n independent vertices or a transitive triangle. The 29-vertex graph in `Erdos112/Lower.lean` is identical to the deposited file `docs/witness_n29_m6_anneal.txt` (SHA-256 `5c1cc09c6df4a0b6dba4c3171c2eb620c89993b33a097da428ebbd176cacb3fa`).

## Priority

As of 14 November 2026, the community database of Erdős problems lists #112 with no formalized solution (`formal_status: unformalized`, data/problems.yaml, updated 12 November 2026), and the public Lean statements of #112 (an open pull request to google-deepmind/formal-conjectures, September 2026, and others) state the problem without proving any bound. To the author's knowledge this is the first machine-checked result on the problem. The bounds narrow k(6,3) to {30, 31, 32}; they do not determine k(n,m), so #112 remains open.

## Check it yourself (about 2 minutes)

Needs [elan](https://github.com/leanprover/elan) and about 8 GB of disk for the compiled Mathlib.

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

`lake build` checks every proof (about 1.5 minutes on a laptop once the Mathlib cache is downloaded). `Axioms.lean` prints the axioms each main theorem depends on. `grep -rn sorry Erdos112` prints nothing. Versions: Lean 4.35.0, Mathlib v4.35.0 (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), pinned in `lake-manifest.json`.

## Files

- `Erdos112/Defs.lean`: oriented graphs, independent sets, transitive triangles, k(n,3)
- `Erdos112/Basic.lean`, `Erdos112/Upper.lean`, `Erdos112/LemmaB.lean`: the upper-bound argument
- `Erdos112/Lower.lean`: the 29-vertex graph and its check
- `Erdos112/KSearch.lean`, `Erdos112/KData.lean`, `Erdos112/KCover.lean`, `Erdos112/KCheck/`, `Erdos112/KSound.lean`: the kernel-checked case analysis of Lemma 8 and its soundness proof (`tools/` holds the untrusted generator of the data tables; the kernel rejects the proof if the data is wrong)
- `Erdos112Search.lean`, `Erdos112/SearchSound.lean`, `LemmaBMain.lean`: the earlier native search of v1.0, kept as an optional cross-check, not used by the proof
- `Erdos112/Main.lean`: the final theorems
- `docs/KERNEL_PROOF_NOTES.md`: how the kernel-only proof of Lemma 8 works (v1.1)
- `docs/TECHNICAL_NOTES.md`: file-by-file map to the paper and where the Lean route differs from the paper (written for v1.0, which used `native_decide` for Lemma 8)
- `docs/STATEMENT_AUDIT_2026-11-14.md`: a separate review that the Lean statement means what the paper says (made on v1.0; the definitions and theorem statements are unchanged in v1.1)

## How to cite

> Tyler Satchel Orden, *Erdős Problem #112: a machine-checked proof that 30 ≤ k(6,3) ≤ 32* (Lean 4), version 1.0, Zenodo, 2026. https://doi.org/10.5281/zenodo.24237181

and the paper (Zenodo record above). A `CITATION.cff` file is included; GitHub shows a "Cite this repository" button.

## Use of AI

Claude (Anthropic), a large language model, assisted this work under my direction: it wrote and checked the Lean code, ran the builds and reviewed the formal statement against the paper; the text is my own and I take full responsibility for it.

## License

MIT (see `LICENSE`).
