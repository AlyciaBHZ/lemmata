---
numbering:
  headings: false
title: Changelog
---

What changed in the archive that a reader should know about: new entries, corrections to
published entries, and changes to what "checked" means. Routine edits are not listed; every
entry shows its own last change and links to the exact commit.

Newest first. Add an item in the same pull request as the change it describes.

## 2026-11-02

- **Licensing:** Entries may use Apache 2.0, so adapted formalizations can retain their upstream licensing.
- **New entry:** [Crossing Decomposition for Subquadratic Noncommutative Circuits](crossing-decomposition/index.md), giving circuits of size $O(n^{5/3})$ for symmetric noncommutative quartics over every field.

## 2026-11-01

- **New entry:** [A three-party Bell polytope that is not a cross-polytope](symmetric-bell-cross-polytope/index.md),
  giving the $(N,m)=(3,17)$ counterexample with at least nineteen distinct extreme points.

## 2026-10-27

- **New entry:** [MinRank Lower Bounds for the Cocubic Reed–Muller Covering Radius](cocubic-covering/index.md), reducing cocubic coset-weight lower bounds to affine MinRank and giving bounds of $32$, $32$, and $34$ in $9$, $10$, and $11$ variables.

## 2026-10-25

- **New entry:** [A quadratic ceiling for common-information bounds on spanning-tree slack matrices](spanning-tree-common-information/index.md),
  giving the explicit $4n^2$ ceiling for full canonical slack and for subtour rows.
- **New entry:** [Common information and hyperplane separation are incomparable](common-information-hsb/index.md),
  with exact separating families, finite conditional-independent seeds, and
  quantified failure of polynomial comparisons for the raw matrix functionals.

## 2026-10-23

- **New entry:** [Symmetric formulations of the spanning-tree polytope](spanning-tree-symmetric-ef/index.md),
  formalizing conditional Hamilton-path LP lower bounds, sharp LP approximations,
  exact quadratic-size SDP formulations, and a nonnegative-outer PSD lower bound.

## 2026-10-22

- **New entry:** [Distributional lower bounds for randomized linear-oracle optimization](distributional-linear-oracle-lower-bounds/index.md).

## 2026-10-21

- **New entry:** [A Square-Root Bound for Asymptotic Tensor Rank](tensor-rank/index.md).

## 2026-10-20

- **Identifiers now follow arXiv's format**, `lemmata:YYMM.NNNNN` (e.g. `lemmata:2610.00003`).
  Each entry has a landing page `/abs/YYMM.NNNNN` (abstract, status, citation) and the full
  entry at `/html/YYMM.NNNNN`. The identifiers issued earlier today in the
  `lemmata:2026.NNNNN` form were replaced.
- Entries can carry an **abstract**, shown on their landing page.
- The verification panel says **kernel-checked** and names the Lean version; the full
  definition moved to [What "checked" means](checked.md).
- Entries that no longer build after a Lean upgrade can be **frozen** by the maintainers:
  they stay published with the version and date of their last successful check.
- Every entry has a **stable identifier** with a permanent URL, shown at the top of the
  page and used in the citation.
- Machine-readable views for search engines and language models: `/llms.txt`,
  `/lemmata.json` (identifiers, Lean declarations, axioms, BibTeX) and a corrected
  `/sitemap.xml`.
- **Moved** to [github.com/ZIB-IOL/lemmata](https://github.com/ZIB-IOL/lemmata). Source and
  commit links on every page now point there.
- Entries can state an **AI use** note and **acknowledgements**, shown at the end of the page.
  First used on [Nonnegative rank of the spanning-tree slack matrix](spanning-tree-min-split/index.md).
- Entries can name their **contributors** explicitly, for the header line and the citation.
- The two minimal examples *Self-implication* and *Antisymmetry of order* were removed;
  [Composition of implications](implication-composition/index.md) remains as the worked example.

## 2026-10-19

- **New entry:** [A Lagrangian duality gap that survives closed convexification](lagrangian-duality-gap/index.md).
- **New entry:** [Nonnegative rank of the spanning-tree slack matrix](spanning-tree-min-split/index.md).
- Entries are grouped into **categories**; every page has a **Cite as** BibTeX entry.
- The archive went live at lemmata.iol.berlin.
