# Palomar submission: prepared, not submitted

Prepared 14 November 2026, 18:01 PST. Nothing was pushed and nothing was submitted.
Submitting and registering publish; both are the author's decision.

Rules read (through the GitHub API only): `PalomarRegistry/PalomarPolicy` `CONTRIBUTING.md`
and `docs/specification.md`; `mathlib-initiative/formalization.yaml` (README, template,
schema v0.4); `PalomarRegistry/PalomarTemplate` (the starter layout); `leanprover/comparator`
README; `PalomarRegistry/PalomarSubmission` `toolchains.json` and the two taxonomy files.
The submission site (submit.palomar-registry.org and its `llms.txt`) was not read. See
"Rules stated only on the submission site" below.

## What to submit

| Field | Value |
|---|---|
| Repository | `Tyorden/erdos-112-lean` |
| Commit (full SHA) | `e86685633ba879e3b02f31281dc2c7a8ce996bcc` |
| Branch that holds it (local only, not pushed) | `palomar` |
| Selected project | the repository root |
| Comparator configuration path | `comparator.json` |
| Metadata path | `formalization.yaml` (the default) |
| Authorisation relationship | responsible author and maintainer of the substantive formalisation |

The commit after this one on the branch only adds this file. Submit the SHA in the table,
not the tip of the branch.

## What is compared

`comparator.json`:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["Erdos112.k63_bounds"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

- `Challenge.lean` (91 lines, 4.5 KiB, imports only Mathlib): the definitions `OGraph`,
  `OGraph.IsIndep`, `OGraph.HasTT`, `OGraph.Free`, `k3`, word for word as in
  `Erdos112/Defs.lean`, and `theorem k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32 := by sorry`.
  `OGraph.adj` is left out because the statement does not use it.
- `Solution.lean`: imports `Erdos112.Main`. It declares nothing itself. The definitions and
  `Erdos112.k63_bounds` are already in the imported modules under the same names, so the
  Solution environment holds the same declarations as the Challenge, with the proof.
- How definitions are shared: the Challenge may import only Lean core, Mathlib, Tau Ceti or
  CSLib, so it cannot import `Erdos112/Defs.lean`. It repeats the definitions. Comparator
  then checks that every constant the theorem's statement refers to is identical in the two
  environments.

## What will be published, and when

On submission (before any review), public at once:

- the repository, the commit, the submission identifier and the fact that it was
  mechanically checked, in a public GitHub Actions run with its logs and
  `mechanical-report.json`;
- the declared authorisation relationship, and the optional free-text evidence if any is
  typed in. Palomar publishes no submitter account. Anything typed into the evidence field
  is public.

On registration (only after the review finds no blocking problem and the submitter
consents to that exact review):

- the registry record: title and abstract (`project.name` and `project.description` of
  `formalization.yaml`), author, maintainer, classification, sources, related
  formalizations;
- the rendered `Challenge.lean`;
- a redacted copy of the AI review (the outcome and every material finding; no scores);
- native forks of this repository and of every pinned dependency under `PalomarArchive`,
  with a permanent tag on the commit;
- the reviewer model identifiers, the policy commit and the workflow run.

Registration is permanent. A record cannot be taken down on request; a correction is a new
version. The review passes through GitHub and the model provider and is kept indefinitely
by Palomar even if the submission is withdrawn. Withdrawal is possible at any point before
registration and leaves no public review outcome, but the mechanical run stays public.

The specification says Palomar "has not launched in the sense of inviting submissions",
while registrations made now are already permanent.

## Local checks made on this commit

Machine: macOS, Lean 4.35.0, Mathlib v4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`),
mains power, `nice -n 10`. Rebuilt from a clean checkout of the commit.

| Check | Result |
|---|---|
| `lake build` (Erdos112, Challenge, Solution; 9077 jobs) | passes; the only warning is the `sorry` in `Challenge.lean` |
| `lake env lean Axioms.lean` | `'Erdos112.k63_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `lake env lean --run tools/CompareStatements.lean Erdos112.k63_bounds` | `RESULT: PASS`: type identical in Challenge and Solution; 163 constants in the statement's closure, 0 differ; axioms of the Solution proof: `Classical.choice`, `Quot.sound`, `propext` |
| NanoDa (`nanoda_bin` 0.4.19, bundled with the toolchain) on the export of `Solution` for `Erdos112.k63_bounds`, only the three axioms permitted | "Checked 7429 declarations with no errors", 4 min 33 s |
| con-ron (bundled with the toolchain) on the same export | "accepted 6771 declarations (--verified)", 33 s |
| Module header and 10,000-line check on every `.lean` file | all 31 files start with `module`; the longest has 693 lines |
| `formalization.yaml` | parses; required fields present; description 1,433 characters; both MSC codes and `math.CO` are in Palomar's taxonomy files |

**Comparator itself was not run.** It is built into Lean 4.35.0 as `lake comparator` and is
installed, but it needs the Linux sandbox `bwrap`, which does not exist on macOS (exit code
2: "needs Linux namespaces"). Running it with the sandbox switched off was not permitted in
this session. The statement comparison above (`tools/CompareStatements.lean`) is a local
stand-in for it, and the two independent kernels were run by hand on the export that
Comparator would produce. Palomar runs the real Comparator with NanoDa on its side; that
run is the one that counts.

## Checklist from CONTRIBUTING.md

Section 1, suitability
- [x] Could warrant a research paper: it is the main theorem of a paper submitted to a
  journal. The research area (Ramsey theory of directed graphs) and audience are named.
- [x] Not presented as a solution of a famous open problem: the abstract, the Challenge and
  the README say these are bounds, that k(6,3) is 30, 31 or 32, and that #112 stays open.
- [x] Novelty claim rests on a stated search (the database entry of 12 November 2026 and the
  public Lean statements) and is worded "to the author's knowledge".

Section 2, repository
- [x] `lean-toolchain`: `leanprover/lean4:v4.35.0`; the minimum is `v4.35.0-rc2`.
- [x] Exactly one Lakefile (`lakefile.toml`, valid TOML); `lake-manifest.json` committed.
- [x] Mathlib's own toolchain at the pinned revision is `v4.35.0`, the same as the project's.
- [x] Every `.lean` file uses the module system and has at most 10,000 lines. This needed a
  change to every Lean file (`module`, `public import`, `@[expose] public section`). The
  diff of the proof files is headers only.
- [x] No `.lean` symbolic links; no compiled files outside `.lake`; `.lake` is not committed.
- [x] Challenge and Solution are distinct module names; both files are in the source tree.
- [x] Challenge is under 300 lines and 32 KiB (91 lines, 4.5 KiB), so no size warning, and
  under 100 lines with one compared declaration, so it can be shown inline.
- [x] Challenge imports Mathlib only; every definition has a docstring; the principal claim
  is the one compared theorem; nothing is weakened.
- [x] `comparator.json`: the four required keys, no others; `theorem_names` not empty;
  `permitted_axioms` only the three allowed. No definition holes.
- [x] The proof does not depend on `sorryAx`, `Lean.ofReduceBool` or a custom axiom.
- [x] Every Git dependency in the manifest is a public `https://github.com/owner/repo` URL
  pinned to a 40-character SHA. No submodules, no Git LFS.
- [x] One licence file at the root (`LICENSE`, the standard MIT text); `project.license` is
  `MIT`. Not checked locally: Palomar's own licence detector (no detector is installed here).
- [x] Checkout is far below 500 MiB.

Section 3, `formalization.yaml`
- [x] `version: v0.4`; one top-level mapping; no duplicate or merge keys; under 256 KiB.
- [x] `project.name` (77 characters), `project.description` (1,433), `project.authors`,
  `project.responsible_maintainers`, `project.license`.
- [x] Authors and maintainers are a human only. The AI is recorded under `automation` and
  `review`.
- [x] `classification.arxiv: [math.CO]`; `classification.msc2020: [05C55, 05C20]`.
- [x] `sources`: source-based origin. The paper is `type: paper`, `relationship:
  formalizes`. No `original-proof` entry. The other two entries are `other` and
  `background`.
- [x] `automation.methods`: one entry, `method: agent`. `review.status: agent-reviewed`.
- [x] Scope, known gaps, divergences from the paper, alignment table.
- [x] Narrative account: Challenge module documentation, README, `formalization.yaml`.

Section 4, authorisation
- [ ] The author declares on the form that he is a responsible author and maintainer, and
  proves push access (browser sign-in, or tag plus gist for an agent). Only he can do this.

Sections 5 to 9 describe what Palomar does; nothing to prepare.

## Points that need the author's decision or eye

1. **Publishing at all, now.** Submission makes the mechanical run public; registration is
   permanent; Palomar is not yet inviting submissions.
2. **Where the commit lives.** The rules ask only for a full commit SHA in the public
   repository. They do not ask for it to be on `main` or for the Challenge to be on `main`.
   The commit must be reachable on GitHub, so the branch (or the commit) has to be pushed.
   Choices: push the branch `palomar` and leave `main` at v1.1, or merge into `main` and tag
   v1.2. Merging keeps one line of history; pushing a branch leaves the Zenodo release
   untouched. A later Zenodo version would be needed only if `main` changes.
3. **Every Lean file changed.** The module-system rule is a hard gate. The change is
   headers only and the proof still builds, but the submitted commit is not byte for byte
   release v1.1.
4. **`Solution.lean` declares nothing.** It imports the proof, and the compared theorem is
   `Erdos112.k63_bounds` in `Erdos112/Main.lean`. Comparator works on environments, so this
   should pass, and the local stand-in passes. The template instead restates the theorem in
   `Solution.lean`. To match the template exactly, the theorem in `Main.lean` would have to
   be renamed or moved, which changes the public name used in the README. Not done.
5. **Source origin.** Recorded as "formalizes the author's paper" (source-based). The
   alternative, `original-proof`, is for a result first presented by the formalization; the
   paper was deposited first, so source-based is the accurate one. The paper is not yet
   peer reviewed and the metadata says so.
6. **Wording to read before it is public**: `project.description` (the registry abstract),
   the module documentation at the top of `Challenge.lean` (it includes one remark that is
   not in `Defs.lean`: allowing arcs in both directions would not change k(n,3)), the new
   README section "Statement and proof, compared", and the `automation` block (model
   names taken from the commit trailers; "Claude Code" as the framework; cost "not
   tracked").
7. **Review risk.** The AI review must rate the literature account and research interest
   as adequate. It can search the web. The README and metadata name Bermond and Ihringer,
   Rajendraprasad and Weinert (2021) without full references; full references are in the
   paper. Adding them to `formalization.yaml` would strengthen the literature account.

## Rules stated only on the submission site

CONTRIBUTING.md says submissions go to submit.palomar-registry.org and that an agent should
read `llms.txt` there first: "it documents the endpoints, what each of them proves, and
what registering publishes". Those endpoints, the form's exact fields, and the exact tag
and gist format for the agent route are not in the policy repository. They were not read.

## Steps to submit (the author's, or Claude's after his OK)

1. Read the items under "Points that need the author's decision or eye".
2. Make the commit public. From this clone:
   `git push origin e86685633ba879e3b02f31281dc2c7a8ce996bcc:refs/heads/palomar`
   (this pushes the submission commit only, without this file), or merge into `main` first.
   Before any push: `git ls-files | grep -iE "\.(docx|pdf)$"` must print nothing (it does).
3. Optional, on Linux or in GitHub Actions: run `lake exe cache get` and then
   `lake comparator --config comparator.json` with `bwrap` installed, to see Comparator pass
   before submitting. The PalomarTemplate repository has a CI job that does this.
4. Open https://submit.palomar-registry.org/ in a browser, sign in with GitHub (the account
   with push access to the repository), and enter: repository `Tyorden/erdos-112-lean`,
   commit `e86685633ba879e3b02f31281dc2c7a8ce996bcc`, Comparator path `comparator.json`,
   project at the repository root, relationship "responsible author or maintainer". Leave
   the evidence field empty unless something should be public.
   The agent route (no browser) needs a tag at the commit and a secret gist carrying a
   challenge from the site; its exact form is in `llms.txt`, which has to be read first.
5. The page shows the registry abstract and the compared declaration as a preview. Check
   both.
6. Wait for mechanical verification (public) and then the AI review (private). Read the
   review. If it finds no blocking problem, decide whether to register; consent is to that
   exact review. If it asks for a revision, fix, commit, and submit the new SHA as a new
   submission. Withdrawal is possible until registration.
