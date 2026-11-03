# AGENTS.md — publishing a result to Lemmata

You are an agent asked to add a mathematical result to this archive. This file is the
complete procedure. `README.md` explains the system; `CONTRIBUTING.md` is the same
material for human contributors. Where they differ, the tools are right: every rule below
is enforced by `tools/lemmata.mjs` and `checker/`, and the cluster runs its own copies of
both.

**Goal:** a merge to `main` of `git@github.com:ZIB-IOL/lemmata.git` that the cluster
accepts, after which the result is live at `https://lemmata.iol.berlin/<id>/`.

There is no CI and no one to ask. Run the checks yourself (step 5). If `tools/check.sh`
passes on your machine, the cluster accepts the commit: same checks, same pins.

---

## 0. What a result is here

One entry = one directory pair, linked by a manifest:

```
docs/<id>/contribution.yml        binds labels in the prose to Lean declarations
docs/<id>/index.md                the prose (MyST Markdown)
lean/Lemmata/<LeanName>/Main.lean the formalization (Lean 4 + Mathlib)
```

- `<id>`: lowercase kebab-case, e.g. `prime-infinitude`. It becomes the URL `/<id>/`. It
  cannot change after publication.
- `<LeanName>`: UpperCamelCase, e.g. `PrimeInfinitude`. Namespace `Lemmata.<LeanName>`.
- Reserved, never use as `<id>` (they are site paths): `abs`, `html`, `c`, `changelog`,
  `checked`, `llms`, `index`, `healthz`, `readyz`, `node_modules`, and anything starting with
  `_`. Never use `Shared` as `<LeanName>` (it is for helpers several entries use).

**Published means checked.** The cluster refuses the whole commit if *any* declaration
anywhere in `lean/Lemmata/` uses `sorry` or an axiom other than `propext`,
`Classical.choice`, `Quot.sound`. You cannot publish partial work, and you cannot override
this from the content repository. The one opt-in exception is computation
(`native_decide`), for an entry that declares it; see [Computations](#computations).

## 1. Set up (once)

Requirements: `git`, [elan](https://github.com/leanprover/elan) (installs the pinned Lean
from `lean/lean-toolchain`), Node ≥ 24.

```bash
git clone git@github.com:ZIB-IOL/lemmata.git && cd lemmata
npm ci
( cd lean && lake exe cache get )   # Mathlib's compiled cache, ~7 GB, takes minutes
tools/check.sh                      # must pass on a clean checkout before you change anything
```

Working in several clones? Share only the downloaded dependencies, never the whole
`.lake` (its `build/` holds your compiled modules, and another clone's leftovers would be
audited as yours): `mkdir -p lean/.lake && ln -s /path/to/first/clone/lean/.lake/packages
lean/.lake/packages`.

Never run `lake update`. The dependency set in `lean/lake-manifest.json` is pinned, and the
cluster rejects any commit whose manifest differs from its cache in any package.

### If the repository gets large

Today a full clone is small (1.6 MB, measured 2026-10-26); the large download is Mathlib's
cache (~7 GB), which every clone needs to build Lean. If the repository itself becomes
large, clone it **partially**: Git then fetches older versions of files only when they are
needed, every file of the current version is present, and every local check works as in a
full clone.

```bash
git clone --filter=blob:none git@github.com:ZIB-IOL/lemmata.git
```

A **sparse** checkout (`git clone --filter=blob:none --sparse …`, then
`git sparse-checkout set docs/<id> lean/Lemmata/<LeanName> …`) goes further and leaves out
other entries' files. It is fine for reading or for editing prose, but the local check does
not work in it yet: `lean/Lemmata.lean` imports every entry, and `tools/check.sh` builds and
checks all of them. The tools say so instead of failing obscurely, and refuse to rewrite the
umbrella or to scaffold an entry there (rewriting it would drop the missing entries).
`git sparse-checkout disable` restores the full tree, fetching only what is missing.

## 2. Create the entry

```bash
git checkout -b entry/<id>
node tools/lemmata.mjs new <id> <LeanName> <subject>
```

`<subject>` is the entry's primary **arXiv subject class**, e.g. `math.OC`, `cs.CC`,
`math.CO` -- any class in `docs/subjects.json`, which is arXiv's list as published. Choose
it as you would for an arXiv submission; for the formalization of a paper, take the paper's
primary class. Afterwards, in `contribution.yml`, add further classes as `cross_lists`
(again as on arXiv) and keywords as `topics` from `docs/topics.yml`. If no topic fits, add
one to that file in the same branch:

```yaml
- id: matching-polytopes         # lowercase kebab-case
  title: Matching polytopes
  description: One sentence.     # shown on the topic's page
```

The scaffold writes all three files with placeholders and registers the module in
`lean/Lemmata.lean`. Replace every placeholder; the placeholder theorem `main : True`
must not survive.

## 3. Write the Lean

`lean/Lemmata/<LeanName>/Main.lean`:

```lean
module

public import Mathlib.Order.Basic            -- import only what you use

public section

namespace Lemmata.<LeanName>

-- DOCS_BEGIN_MAIN
/-- Docstring: what the theorem says, in words. -/
theorem my_result (n : ℕ) : n + 0 = n := by simp
-- DOCS_END_MAIN

end Lemmata.<LeanName>
```

Rules (each enforced):

- First line `module` (required), imports as `public import`, body in `public section`.
  Mathlib at this pin uses the module system; plain `import` produces warnings and missing
  modules.
- Module names must exist at the pinned Mathlib. Check with
  `ls lean/.lake/packages/mathlib/Mathlib/...` rather than from memory: for example,
  `Mathlib.Logic.Basic` does **not** exist at this pin.
- Everything inside `namespace Lemmata.<LeanName>`.
- To use another entry, `public import Lemmata.<Other>.Main`. **Never** import the umbrella
  `Lemmata`, and never copy another entry's definitions.
- `-- DOCS_BEGIN_MAIN` and `-- DOCS_END_MAIN` occur exactly once each, in that order. The
  page shows exactly what is between them.
- Exported declarations are public (not `private`), live in this namespace, and are defined
  in this directory's modules.
- More files are fine (`lean/Lemmata/<LeanName>/Lemmas.lean`, …). After adding or removing
  any `.lean` file run `node tools/lemmata.mjs umbrella --write`. Every file is compiled and
  audited, including files nothing imports. Files go in your entry's directory (or in
  `lean/Lemmata/Shared/`), never directly in `lean/Lemmata/`.
- No `sorry`, no `axiom`, no `@[implemented_by]`, no `@[extern]`, anywhere: they leave a
  gap, assert facts, or swap in code the kernel cannot check.
- No `native_decide` (or `decide +native`, `bv_decide`) unless the entry declares
  `native_computation: true`. See [Computations](#computations).

### Computations

`native_decide` (also `decide +native`, `bv_decide`) proves a decidable statement by
compiling and running it during the build. The kernel never checks the result and nobody
re-runs it, so it is allowed only as an explicit opt-in, and results that rely on it are
labelled apart from kernel-checked ones (see the "checked" page, section Computation):

1. **Try `decide +kernel` first.** The kernel evaluates the statement itself and the result
   stays kernel-checked; it is slower, but fine for moderate case checks. Use
   `native_decide` only when that is impractical.
2. Add `native_computation: true` to `contribution.yml`. Without it, a computation tactic in
   the entry's Lean files fails validation. `lean/Lemmata/Shared/` may not use them.
3. `native_decide` on a definition from **another module** -- Mathlib's included, e.g.
   `Nat.Prime 97` -- needs that module's compiled code: import it with
   `public meta import <Module>` (Lean's error says so).
4. Keep each claim small and clearly stated. The page lists every claim with its source
   line and its statement; reviewers re-run it with `tools/check.sh`.

What the label rests on is that opt-in and review, not on a check of how a claim was
produced: the verifier accepts a computation axiom (the form Lean's tactics produce) only in
an entry that declared the flag, and nothing it accepts is ever shown as kernel-checked.

Using another entry's results that rely on computations needs no flag: those results are
marked "kernel-checked, modulo computation" automatically, linking to that entry. Results
that use only the other entry's kernel-checked parts stay kernel-checked.

### Separate statements from proofs (recommended)

Put the **definitions and formal statements** in one module and the **proofs** in another,
so the statement never depends on the proof — only the proof on the statement. This is what
[Lax](https://laxarchive.org/about.html) (`concepts/` vs `proofs/`) and DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) do, and it is
what a reader reviews: the statement is the claim, the proof is the evidence.

```
lean/Lemmata/<LeanName>/
  Statement.lean   definitions and the theorem statements, as `def … : Prop := …`
  Main.lean        `public import Lemmata.<LeanName>.Statement`; the proofs
```

In `Statement.lean`, state the claim as a proposition:

```lean
/-- Composition of implications. -/
def Composition : Prop := ∀ {P Q R : Prop}, (P → Q) → (Q → R) → P → R
```

and in `Main.lean` prove exactly that proposition, and export this theorem:

```lean
theorem composition : Composition := fun hpq hqr hp => hqr (hpq hp)
```

Then the statement a reviewer compares with the prose is short and proof-free, and a
proof can be replaced later without touching what was claimed. This is not enforced —
small entries may keep everything in `Main.lean` — but new entries should follow it.

Fast loop while proving:

```bash
tools/check.sh --no-docs    # build + kernel check + axiom audit, no site render
```

## 4. Write the prose and bind it

`docs/<id>/index.md`:

````markdown
---
title: A short human title
---

```{include} ../_generated/provenance/<id>.md
```

One or two sentences of context.

```{prf:theorem} Name of the result
:label: thm-<id>

The statement in mathematical language, with $\LaTeX$ math.
```

```{prf:proof} of [](#thm-<id>)
:nonumber:

The informal proof.
```

```{literalinclude} ../../lean/Lemmata/<LeanName>/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/<id>.md
```
````

- Keep both `{include}` lines; validation fails without them. The first renders the
  header under the title: the identifier with "copy URL" and "copy BibTeX", the authors
  (computed by the cluster from git history, names only, each linked to an author page at
  `/a/<name>/`), the versions (`v1 <date> · last <date>`, linked to the commit) and the
  abstract. The last is the verification panel, from the verifier's report, collapsed with
  its outcome in the bar, followed by related material, notes and the license. Neither can
  be edited: do not add an `authors:` block, and never write "checked", "verified" or a
  badge yourself.
- The BibTeX (permanent `/abs/` URL, authors, year, arXiv if given, the version commit in
  `note`) is generated; there is nothing to write.
- Under every result bound in `exports`, the page shows its Lean declaration with its
  status and a link to the exact lines checked, and on request its Lean statement: a
  theorem up to `:=` (never the proof), a definition in full. A theorem stated as a named
  `Prop` (`theorem t : MyClaim`, with `def MyClaim : Prop := …` in `Statement.lean`)
  also shows that definition. So **every export must be declared in a way the tools can
  find**: `theorem <name>` / `def <name>` at the start of a line, in the file the verifier
  reports. Write the statement readably; it is what reviewers compare with your prose.
- On the built site (`tools/check.sh`, and in the cluster) proof titles read "Proof of
  Theorem 1", a result whose proof is not directly below it gets a `[↓]` link to it, proofs
  fold by clicking their header, the Lean source starts collapsed, the Lean boxes sit under
  their results, and the right-hand contents follow the section being read. A small script
  does this in the browser; `npm run preview` (MyST's live server) does not run it.
- Every entry ends with **comments** (giscus): one GitHub Discussion per entry in the
  "Comments" category of the content repository, keyed by the entry's directory. There is
  nothing to write; do not add comment sections or links to discussions yourself.
- Your name on the page is the **git author name** of your commits, unless the manifest
  lists `contributors` (step 4). Set it before committing: `git config user.name "Full Name"`.
- Every `prf:proof` names what it proves and carries `:nonumber:`, exactly as above;
  it renders as "Proof (of Theorem 1)" with a link. Validation fails otherwise: MyST
  numbers proofs on their own, so a page with a theorem, a proposition and one proof
  would say "Proof 1" and leave the reader guessing. A proof of several statements
  lists them all: `of [](#prop-<id>-…) and [](#thm-<id>)`.
- **Cite papers with `@key`**, from `docs/references.bib`: `@rothvoss2013matching proved`
  renders as "Rothvoss (2013) proved", `[@wyner1975common]` as "(Wyner, 1975)",
  `[@a; @b]` cites several. MyST lists every work a page cites under "References" at the
  end of the page, in one style for the whole site. **Do not link to papers**
  (`doi.org`, `arxiv.org`) and do not write a References section: `validate` refuses both
  in an entry, and an unknown `@key` anywhere. Links to code, data or a project page are
  fine. A work cited only in passing still needs its `@key`; the page lists only what
  it cites.
- **Adding a work to `references.bib`.** For a paper with a DOI, run
  `node tools/lemmata.mjs doi <DOI>` -- arXiv papers have one too, `10.48550/arXiv.<id>`.
  It fetches the entry from doi.org and gives it the house key (first author, year, first
  title word: `braun2014matching`), which you then cite. The cluster renders
  **without internet**, so every cited work must be in the file; `tools/check.sh` renders
  offline to catch anything that would need the network. Tidy a fetched entry (titles can
  contain HTML such as `<i>b</i>`; write `$b$`) and keep its `doi`.
- Never paste Lean into Markdown by hand; always `literalinclude`.
- Refer to results by label: `[](#thm-implication-composition)`. Labels from other entries work.
- Other environments: `prf:lemma`, `prf:definition`, `prf:corollary`, `prf:proposition`.
  Display equations: `$$ … $$ (eq-<id>-name)`.
- Every page in `docs/<id>/` must be listed in `pages:` below, `index.md` first.

`docs/<id>/contribution.yml`:

```yaml
schema_version: 1
id: <id>                              # = directory name
lean_namespace: Lemmata.<LeanName>
subject: <subject>                    # primary arXiv class, e.g. math.OC (docs/subjects.json)
cross_lists: [<class>, …]             # optional; further arXiv classes, never the primary one
topics: [<topic>, …]                  # optional; ids from docs/topics.yml
arxiv: 2301.01234                     # optional; one id or a list, e.g. [2301.01234v2, math/0601001]
abstract: >-                          # REQUIRED; under the header and on the /abs/ page
  One paragraph stating the result; inline text and $math$ only.
contributors:                         # optional; replaces the names taken from git
  - {name: Ada Lovelace, orcid: 0000-0002-1825-0097}           # one entry per person
  - {first: Ludwig, last: van Beethoven, orcid: 0000-0001-5109-3700}   # multi-part surname
  - Grace Hopper                      #   no ORCID: named, but not linked
ai_use: >-                            # optional; shown at the end of the entry
  Lean proofs drafted with an AI assistant, reviewed and completed by the authors.
acknowledgements: >-                  # optional; shown at the end of the entry
  Supported by the Berlin Mathematics Research Center MATH$^+$.
license: CC-BY-4.0                    # optional; CC-BY-4.0 (default), CC-BY-SA-4.0, CC0-1.0 or Apache-2.0
withdrawn: >-                         # only to withdraw a published entry; the reason
  The bound in the second theorem is wrong; see lemmata:2611.00004 for the correction.
related:                              # optional; derived material, listed at the end
  - {kind: slides, title: "Talk at the MATH+ day", url: "https://example.org/slides.pdf"}
  - {kind: video,  title: "Recording", url: "https://example.org/video"}
native_computation: true              # only if the Lean uses native_decide; see Computations
pages:
  - index.md
exports:                              # at least one theorem
  - name: Lemmata.<LeanName>.my_result
    kind: theorem                     # or: definition
    page: index.md
    label: thm-<id>                   # must contain <id>; must occur exactly once on that page
```

`contributors` is for when the git authors are not the right credit: several people
wrote the result, someone committed on behalf of others, or an agent did the commit.
If present, it replaces the git names in the contributors line and in the BibTeX
`author` field, in the order given; the dates and commit link still come from git.
Write `First Last`, or `{first: …, last: …}` when the surname has several parts (it is
then kept whole in BibTeX: `{van Beethoven}, Ludwig`), or `{name: …}`. Names only — no
emails.

**Give every person's ORCID iD** (`orcid:` in the object form, one per person, as above;
`https://orcid.org/` in front is accepted and dropped). The ORCID is what identifies a
person: a contributor with one gets an author page at `/a/orcid-<ORCID iD>/` listing all their
entries, and their name links to it; a name without one is shown but not linked, because
two people can share a name. The iD is checked (format and its check digit), so a typo
fails validation. Ask the human you work for for each person's ORCID iD; never guess or
look one up and assume it belongs to them. Without the field, the names come from git and
carry no ORCID.

`license` is the licence of the whole entry, prose and Lean, shown under the title and in
`lemmata.json`. Leave it out for **CC BY 4.0**, the default; `CC-BY-SA-4.0`, `CC0-1.0`
and `Apache-2.0` are the only alternatives, and anything else fails validation. When
adapting Apache-licensed material, retain the upstream license and attribution notices,
include a copy of the license (e.g. `docs/<id>/LICENSE.txt`), and identify your changes in
the modified source files. Link the license and any notices from the entry's prose. Do not
contribute text or code you cannot license this way, e.g. passages copied from a paper
whose publisher holds the copyright; ask the human you work for when unsure.

`withdrawn` withdraws a published entry; its text is the reason. **Never delete a published
entry**: its identifier is cited, and other entries may import its Lean. A withdrawn entry
stays at its identifier with a notice under the title and keeps being built and checked, but
leaves the sidebar, the catalog and the subject and topic pages (`lemmata.json` gives it status
`withdrawn`). Correct mistakes by changing the entry instead, where you can. Withdraw only
when the human you work for asks you to; see the About page for the policy.

`ai_use` and `acknowledgements` are short notes rendered at the end of the entry, below the
verification panel. Say honestly how AI tools were used, if at all; there is no default
text. Both are inline only: text, `*emphasis*`, `[links](...)` and math `$...$` /
`$$...$$` (rendered by KaTeX). Directives, code fences, headings, lists and HTML are
refused, a literal dollar must be written `\$`, and each note is at most 2000 characters.
Use a YAML block (`>-`) so math and apostrophes need no quoting.

An entry may also archive the formalization of results **from an existing paper** (preprint
or published); that is welcome, not only new results. Then link the paper with `arxiv` (and
a journal version with `related`, `kind: paper`), and say in the prose which of the paper's
results the entry formalizes, by their numbers in the paper.

`arxiv` links additional material (a paper, a longer write-up) under the title as
`arXiv:<id>` → `https://arxiv.org/abs/<id>`. Give the bare identifier, without an
`arXiv:` prefix; validation checks the format, so a typo fails instead of becoming a
dead link. Unquoted is fine (`2301.10230` keeps its trailing zero).

Each export binds one label in the prose to one Lean declaration. The tools check that the
declaration exists, has that kind, lives in your namespace, and depends only on allowed
axioms. **Nobody can check that the English statement means the same as the Lean
statement.** That is your job, and your reviewer's: state the Lean theorem so that it
visibly says what the prose says, without extra hypotheses the prose omits.

## 5. Check (mandatory)

```bash
tools/check.sh
node tests/browser.mjs docs/_build/html ""    # follows every link; needs: npx playwright install chromium
```

`tools/check.sh` runs, in order and stopping at the first failure:

| Step | Fails when |
|---|---|
| validate | a manifest, subject or topic is wrong, a note uses non-inline markup, a label is missing or duplicated, snippet markers are wrong, the umbrella is stale, an `index.md` lacks one of the two `{include}` lines, `.lemmata/` is committed, a Lean file does not start with `module`, a Lean file contains `axiom`, `@[implemented_by]` or `@[extern]`, a computation tactic is used without `native_computation: true` (or in `lean/Lemmata/Shared/`), or a Lean file sits directly in `lean/Lemmata/` |
| lake build | any module does not compile |
| leanchecker | the kernel rejects a declaration |
| lemmata-check | any declaration uses a disallowed axiom (`sorryAx`, a custom `axiom`, a computation outside an entry with `native_computation: true`), or an export is missing, misclassified, or outside its namespace |
| myst build | a reference does not resolve, an identifier is duplicated, a linked file is missing |

Every failure is printed as `FAIL …` with the file and the reason. Fix the cause. Never
weaken a check, never edit `checker/` or `tools/` to get past one (the cluster ignores
your copies anyway), and never commit `docs/_generated/`, `docs/c/`, `docs/_build/`,
`docs/myst.runtime.yml`, `lean/.lake/` or `out/` (they are git-ignored).

## 6. Submit

**Commit with a public email.** GitHub refuses a push whose commits carry an email the
account keeps private ("push declined due to email privacy restrictions"). Use the account's
noreply address — `git config user.email <id>+<user>@users.noreply.github.com` — before you
commit; the name you set (`user.name`) is the one shown on the page.

```bash
git add -A
git commit -m "<id>: <one line on what is proved>"
git push -u origin entry/<id>
```

Open a pull request against `main` at `https://github.com/ZIB-IOL/lemmata/pulls`
and say what the result is and how the Lean statement corresponds to the prose. **Merging
is publishing**: a human reviews and merges. Do not push to `main` yourself unless you have
been explicitly told to.

## Identifiers and later changes

On its first publication every entry gets a **stable identifier**, `lemmata:YYMM.NNNNN`
(like arXiv), with a landing page `https://lemmata.iol.berlin/abs/YYMM.NNNNN` and the full
entry at `/html/YYMM.NNNNN`. The cluster assigns it;
you do not write it anywhere. It is shown at the top of the page and used as the BibTeX key
and URL. Link to and cite that URL, not the directory-based one.

To change an entry later, open another pull request against the same `docs/<id>/` and
`lean/Lemmata/<LeanName>/`. The identifier stays the same. The header's "last changed"
line and commit link update by themselves; the BibTeX `note` names the commit
of each published version, so earlier citations stay exact. Note substantive corrections
in `docs/changelog.md`.

### After a Lean or Mathlib upgrade

The archive builds with one Lean and Mathlib version. When an upgrade breaks an entry, the
maintainers may **freeze** it: it stays published, marked "last checked with Lean v… on …",
and its Lean code is left out of later builds. A frozen entry can only be shown with its old
result while its files are unchanged. To bring it back, port it to the current version in a
pull request and ask for it to be unfrozen; once it passes, it is current again.

## 7. Confirm it is live

After the merge, the cluster builds the new `main` within about a minute; a build takes
under a minute more. Poll the public status:

```bash
curl -s https://lemmata.iol.berlin/_status.json \
  | jq '{published: .active.sha, main: .head, stale, building, last: .last_attempt.result}'
```

- **Published** when `.active.sha` equals the merged commit (`git rev-parse origin/main`)
  and `.stale` is `false`. Your entry is at `https://lemmata.iol.berlin/<id>/`.
- **Rejected** when `.last_attempt.result` is `"failed"` for that commit.
  `.last_attempt.reason` names the failed step (`fetch`, `build`, `verify`, `render`,
  `upload`) and carries the end of its log. The site stays on the previous version. Fix it
  on a new branch and go back to step 5. Human-readable view: `https://lemmata.iol.berlin/_status`.
- Still `building`, or `waiting-for-mathlib-cache`: poll again in 30 s.

A commit that passed `tools/check.sh` locally and fails in the cluster is a bug in the
system, not in your entry. Report the status output to whoever asked for the work.

---

## Quick reference

```bash
node tools/lemmata.mjs new <id> <LeanName> <subject>    # scaffold; subject: an arXiv class
node tools/lemmata.mjs umbrella --write                 # after adding/removing .lean files
node tools/lemmata.mjs validate                         # structure only, seconds
tools/check.sh --no-docs                                # + build, kernel, axioms
tools/check.sh                                          # everything the cluster does
npm run preview                                         # live preview at :3000 (unverified, no page script)
```

Worked examples to copy from: `docs/implication-composition/` (the reference example:
numbered results, Mermaid, a widget, a Mathlib corollary, a tag), and the real entries
`docs/spanning-tree-min-split/` (several Lean modules, a definition export, AI-use and
acknowledgement notes) and `docs/lagrangian-duality-gap/` (a long single-module proof).

