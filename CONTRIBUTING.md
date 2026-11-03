# Contributing an entry

(Agents: [AGENTS.md](AGENTS.md) is the same procedure as an exact checklist, including
how to confirm publication.)

An entry is a pair: a page in `docs/<id>/` and a Lean module in `lean/Lemmata/<LeanName>/`.

What fits: results worth sharing before or without a paper, and equally the formalization of
results **from a paper**, preprint or published. For the latter, link the paper with `arxiv`
(and a journal version with `related`), state the results as the paper does, and say in the
prose which of its theorems the entry covers; the entry can be as long as the formalization
needs.

## 1. Scaffold

```bash
node tools/lemmata.mjs new prime-infinitude PrimeInfinitude math.NT
```

The last argument is the entry's primary **arXiv subject class** (`math.NT`, `math.OC`,
`cs.CC`, …; arXiv's list is in `docs/subjects.json`), chosen as for an arXiv submission. In
`contribution.yml` you can add `cross_lists` (more arXiv classes) and `topics` (keywords from
`docs/topics.yml`; add a new topic there, with a title and one line of description, in the
same pull request).

This creates `docs/prime-infinitude/{contribution.yml,index.md}` and
`lean/Lemmata/PrimeInfinitude/Main.lean`, and adds the module to the umbrella. The id is
lowercase kebab-case and becomes the URL (`/prime-infinitude/`); the Lean name is
UpperCamelCase. Neither can change after publication. Some ids are reserved because they are
site paths: `abs`, `html`, `c`, `changelog`, `checked`, `llms`, `index`, and anything starting
with `_`; the Lean name `Shared` is reserved for helpers used by several entries.

## 2. Write the Lean

- Every Lean file starts with `module` (required) and uses `public import` (Mathlib uses
  the module system).
- Everything lives in `namespace Lemmata.<LeanName>`.
- Import other entries' modules directly (`public import Lemmata.ImplicationComposition.Main`),
  never the umbrella `Lemmata`. Do not copy another entry's definitions; move shared
  material into `lean/Lemmata/Shared/` in its own pull request.
- No `sorry`, no `axiom`, no `@[implemented_by]` or `@[extern]`. The audit covers every
  declaration in every file, not just the ones you export — a draft helper fails the whole
  archive.
- Computations (`native_decide`, `decide +native`, `bv_decide`) only with
  `native_computation: true` in `contribution.yml`. Their results are not kernel-checked
  and are marked so on the site; prefer `decide +kernel` where it is fast enough.
- `native_decide` on a definition from another module, Mathlib's included, needs
  `public meta import <Module>`. Details in AGENTS.md, section Computations.
- Mark the part to show on the page with `-- DOCS_BEGIN_MAIN` / `-- DOCS_END_MAIN`.
  Each marker must occur exactly once.

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

## 3. Write the page

- State results with `prf:theorem` (or `prf:lemma`, `prf:definition`, …) and give each a
  `:label:` containing your id, e.g. `thm-prime-infinitude`.
- Include the Lean with `literalinclude` from `../../lean/...`. Never paste a proof by hand.
- Write each informal proof as ```` ```{prf:proof} of [](#thm-<id>) ```` with `:nonumber:` on
  the next line, so it reads "Proof (of Theorem 1)" instead of a bare "Proof 1".
  Validation enforces this.
- Refer to other entries' results by label: `[](#thm-implication-composition)`.
- Cite papers with `@key` (narrative, "Rothvoss (2013)") or `[@key]` (parenthetical) from
  `docs/references.bib`; the page lists them under "References" at the end. Don't link to
  papers (`doi.org`, `arxiv.org`) and don't write a references section: validation refuses
  both. Add new works to `references.bib` (key: first author, year, first title word); the
  cluster renders without internet, so every cited work must be there. Details in AGENTS.md.
- Keep both generated includes the scaffold writes: `../_generated/provenance/<id>.md`
  under the title (who contributed, from git — your name is your git author name) and
  `../_generated/verification/<id>.md` at the end (what was checked). Validation requires
  both. Do not add an `authors:` block; the git line replaces it.
- Widgets: an ES module next to the page, loaded with `{anywidget}`. Use only
  `model.get`, `model.set` and `model.on` — there is no kernel. Widgets run in readers'
  browsers and are reviewed as code.

## 4. Bind them in `contribution.yml`

```yaml
schema_version: 1
id: prime-infinitude
lean_namespace: Lemmata.PrimeInfinitude
subject: math.NT             # primary arXiv class: where it is listed (docs/subjects.json)
cross_lists: [math.CO]       # optional: also listed under these arXiv classes
topics: [prime-numbers]      # optional: keywords from docs/topics.yml
arxiv: 2301.01234            # optional: linked under the title; one id or a list
abstract: >-                 # required: one paragraph, under the header and on the /abs/ page
  ...
contributors:                # optional: credit these people instead of the git authors
  - {name: Ada Lovelace, orcid: 0000-0002-1825-0097}
  - {first: Ludwig, last: van Beethoven, orcid: 0000-0001-5109-3700}   # multi-part surname
  - Grace Hopper             # without an ORCID iD: named, not linked
ai_use: >-                   # optional: how AI tools were used (end of the page)
  ...
acknowledgements: >-         # optional: funding, thanks (end of the page); $math$ allowed
  ...
license: CC-BY-4.0           # optional: CC-BY-4.0 (default), CC-BY-SA-4.0, CC0-1.0 or Apache-2.0
withdrawn: >-                # only to withdraw a published entry: the reason
  ...
related:                     # optional: slides, videos, a monograph, code, ... (end of page)
  - {kind: slides, title: "...", url: "https://..."}
native_computation: true     # only if the Lean uses native_decide (see "checked" page)
pages: [index.md]            # first page must be index.md; list every page
exports:
  - name: Lemmata.PrimeInfinitude.exists_infinite_primes
    kind: theorem            # or: definition
    page: index.md
    label: thm-prime-infinitude
```

Rules the tools enforce for these fields:

- `subject` and every `cross_lists` item must be arXiv classes (`docs/subjects.json`), and
  the cross-lists may not repeat the subject; every topic must be in `docs/topics.yml`.
- `arxiv` is the bare identifier (`2301.01234`, `2301.01234v2`, `math/0601001`), without an
  `arXiv:` prefix; the format is checked so a typo cannot become a dead link.
- `abstract` is required. `related` items are `{kind, title, url}`; `kind` is one of
  slides, video, paper, book, notes, code, talk, other, and `url` a plain http(s) URL.
- `abstract`, `ai_use` and `acknowledgements` are inline text only: words, `*emphasis*`,
  `[links](…)` and math `$…$` / `$$…$$`. No directives, code fences, headings, lists or HTML;
  write a literal dollar as `\$`; at most 2000 characters each. Use a YAML block (`>-`).
- `contributors` items are `First Last`, `{name: …}` or `{first: …, last: …}`, one per
  person; names only, no emails. Add each person's **ORCID iD** as `orcid:` (please do):
  with it, the name links to an author page at `/a/orcid-<ORCID iD>/` with all of that person's
  entries; without it, the name is shown unlinked, since a name alone does not identify
  someone. The iD's format and check digit are validated. Get yours at
  [orcid.org](https://orcid.org) if you do not have one.
- `license` covers the whole entry, prose and Lean. Without it the entry is **CC BY 4.0**;
  the other choices are `CC-BY-SA-4.0`, `CC0-1.0` and `Apache-2.0`. It is shown under the
  title. For Apache-licensed adaptations, retain upstream license and attribution notices,
  include the license text (e.g. `docs/<id>/LICENSE.txt`), and identify changes in modified
  source files. Link the license and any notices from the prose. Only contribute what you
  may license this way.
- `withdrawn` (inline text, the reason) withdraws a published entry. Published entries are
  never deleted: they stay at their identifier with a notice and are still built and
  checked, since others cite them and other entries may build on their Lean. They are no
  longer listed. Prefer correcting an entry to withdrawing it.

The URL of an entry is `/<id>/` and does not contain its subject, so reclassifying an entry
later never breaks links to it. Subject pages live at `/s/<class>/` (`/s/math-oc/` for
math.OC) and topic pages at `/t/<topic>/`.

Each export says "this label on this page is formalized by this declaration". The binding
is checked; whether the two say the same thing is what your reviewer checks.

## 5. Check and open a pull request

Do not run `lake update`: the dependency set in `lean/lake-manifest.json` is pinned, and the
build rejects a commit whose manifest differs. Never commit `.lemmata/`, `docs/_generated/`,
`docs/c/`, `docs/abs/` or build output (they are git-ignored). Commit with your GitHub noreply
address (`git config user.email <id>+<user>@users.noreply.github.com`): GitHub refuses pushes
that expose a private email, and `user.name` is the name shown on the page.


```bash
node tools/lemmata.mjs umbrella --write   # if you added or removed Lean files
tools/check.sh
```

If the repository gets large, clone it partially: `git clone --filter=blob:none …` fetches
older versions of files only when they are needed, and every local check works as in a full
clone. A sparse checkout, with only some entries, is fine for reading and prose edits, but
`tools/check.sh` needs every entry (AGENTS.md, "If the repository gets large").

Open a pull request against `main` on [GitHub](https://github.com/ZIB-IOL/lemmata). If
the change matters to readers (a new entry, a correction), add a line to
`docs/changelog.md` in the same pull request. Reviewers read the mathematics, compare the prose
with the Lean statement, and review any JavaScript. Once merged, the entry is live within
a few minutes, or the status page says why not.

## Identifiers, later changes, and Lean upgrades

On first publication an entry gets a stable identifier `lemmata:YYMM.NNNNN` with a landing
page `/abs/YYMM.NNNNN` and the full entry at `/html/YYMM.NNNNN`; cite that. To change an entry
later, open another pull request on the same directories — the identifier stays.

The archive builds with one Lean and Mathlib version. If an upgrade breaks an entry, the
maintainers may **freeze** it: it stays published, marked with the Lean version and date of
its last successful check, and is left out of later builds while its files are unchanged. To
bring it back, port it to the current version and ask for it to be unfrozen.
