## Zenodo release guide

Follow these steps to publish GitHub releases with an archived DOI on Zenodo.

1. Enable GitHub → Zenodo linking
   - Sign in to Zenodo and connect your GitHub account.
   - In Zenodo, enable this repository for archiving.

2. Prepare metadata in the repo
   - Keep `.zenodo.json` up to date (title, creators, description, license, keywords, related identifiers).
   - Ensure `CITATION.cff` matches the project metadata and license.
   - Confirm `LICENSE` reflects the canonical license.
   - Confirm the stable concept DOI and any existing version DOI are not
     conflated. `10.5281/zenodo.17345515` is the concept DOI currently recorded
     in `CITATION.cff`; `10.5281/zenodo.17345516` identifies an older archived
     version and must not be presented as the DOI of a newly rewritten paper.

3. Verify the formal and paper artifacts

```bash
./verify.sh
cd arxiv
tectonic main.tex
tar -czf incidence_theory_arxiv_src.tar.gz main.tex references.bib README.md
cd ..
bash scripts/verify-arxiv-manuscript.sh
```

   - The manuscript verifier rejects the unsupported legacy title, checks all
     29 theorem-spine groups have a manuscript marker, validates the generated
     PDF title, and compares archived sources byte-for-byte.
   - Do not insert a new version DOI into `arxiv/main.tex` until Zenodo has
     minted it for the corresponding release.

4. Create a versioned Git tag and GitHub Release
   - Use semantic versioning (e.g., `v0.1.0`).
   - Create a GitHub release with notes. Zenodo will automatically archive the release and mint a versioned DOI.

5. Pin the concept DOI badge in `README.md`
   - After the first release, Zenodo provides a concept DOI (stable) and versioned DOIs.
   - Add the badge using the DOI Zenodo provides, for example:

```markdown
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)
```

6. Update related identifiers (optional)
   - If you publish a paper or preprint, add it to `.zenodo.json` under `related_identifiers` with the appropriate relation (e.g., `isSupplementTo`, `isAlternateIdentifier`).

Notes
- Zenodo will read `.zenodo.json` on each release. Prefer concise, plain‑text descriptions.
- If multiple authors are added, include `name` and `affiliation` fields in `creators`.

