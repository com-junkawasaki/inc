# Exact Descent of Ternary Relations — arXiv source bundle

This directory contains the source and generated PDF for:

> Jun Kawasaki, “Exact Descent of Ternary Relations along Incidence
> Bisimulation Quotients.”

The paper studies exact quotient descent, its coequalizer/reflection universal
property, finite compatibility obstructions, and the 32-orbit simplex
classification. It does not claim a fourth foundation, full ZF/HoTT models, or
universal applicability.

## Files submitted to arXiv

- `main.tex` — self-contained manuscript, including its bibliography;
- `references.bib` — machine-readable bibliography retained as metadata;
- `README.md` — this build and scope note.

The archive `incidence_theory_arxiv_src.tar.gz` must contain exactly current
copies of those three files. The repository verifier compares the archived TeX
and BibTeX byte-for-byte with the working sources.

## Build

The checked local build uses Tectonic:

```bash
tectonic main.tex
```

The manuscript contains an inline `thebibliography`, so the arXiv build does not
depend on a separate BibTeX pass. Recreate the submission bundle with:

```bash
tar -czf incidence_theory_arxiv_src.tar.gz main.tex references.bib README.md
```

From the repository root, validate the manuscript, PDF title, forbidden legacy
claims, and archive synchronization with:

```bash
bash scripts/verify-arxiv-manuscript.sh
```

## Formal evidence and identifiers

- Source and Lean formalization: <https://github.com/com-junkawasaki/inc>
- Stable Zenodo concept DOI: <https://doi.org/10.5281/zenodo.17345515>
- Existing archived version DOI: <https://doi.org/10.5281/zenodo.17345516>
- Lean-to-paper index: `docs/papers/incidence-theorem-index.tsv`
- Scoped completion claims: `docs/completion-claims.tsv`

The existing DOI record predates this rewritten manuscript. A new repository
release must update Zenodo metadata and receive its own version DOI before that
version DOI is inserted into the paper.
