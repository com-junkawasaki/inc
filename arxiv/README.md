# Incidence Theory — arXiv Submission (Source Bundle)

This directory contains the LaTeX sources for the preprint:

"Theory of Incidence — A Fourth Foundation Beyond Set, Category, and Type"

## What to include in the arXiv source

Include only the minimal files required to build the PDF:

- `main.tex`
- `references.bib` (and any figures if added later)

Do not include the Lean/`mathlib4` codebase in the arXiv source bundle. The
formalization and artifacts are referenced via DOI/URL instead (see below).

## Building locally

We recommend latexmk for reproducible local builds.

```bash
latexmk -pdf -interaction=nonstopmode main.tex
```

Notes:

- Tested with TeX Live 2023+ and pdfLaTeX.
- If you add figures, prefer PDF/PNG and keep file sizes small.

## Create the arXiv source bundle

Create a clean archive containing only TeX sources (and figures, if any):

```bash
tar -czvf incidence_theory_arxiv_src.tar.gz main.tex references.bib
```

If figures are present, append them to the command (e.g., `figures/*.pdf`).

## Code and data availability

- Project overview and source repository: https://github.com/junkawasaki/theory-of-incidence
- Archived artifacts (Zenodo DOI): https://doi.org/10.5281/zenodo.17345516

Selected Lean theorems and definitions are provided in the repository; the arXiv
manuscript cites the corresponding files and a commit hash in an appendix.

## Paper overview (short)

The paper presents Incidence Theory as a fourth mathematical foundation that
unifies Set, Category, and Type theories through a relational primitive. Topics
include the axioms (A1–A17), gluing/composition, observational equivalence,
semantic models (ZF, adhesive categories, HoTT), and a linear-algebraic layer
via boundary/Laplacian operators. Examples cover graphs/hypergraphs, concurrent
processes, and biological networks.

