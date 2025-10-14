## Zenodo release guide

Follow these steps to publish GitHub releases with an archived DOI on Zenodo.

1. Enable GitHub → Zenodo linking
   - Sign in to Zenodo and connect your GitHub account.
   - In Zenodo, enable this repository for archiving.

2. Prepare metadata in the repo
   - Keep `.zenodo.json` up to date (title, creators, description, license, keywords, related identifiers).
   - Ensure `CITATION.cff` matches the project metadata and license.
   - Confirm `LICENSE` reflects the canonical license.

3. Create a versioned Git tag and GitHub Release
   - Use semantic versioning (e.g., `v0.1.0`).
   - Create a GitHub release with notes. Zenodo will automatically archive the release and mint a versioned DOI.

4. Pin the concept DOI badge in `README.md`
   - After the first release, Zenodo provides a concept DOI (stable) and versioned DOIs.
   - Add the badge using the DOI Zenodo provides, for example:

```markdown
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)
```

5. Update related identifiers (optional)
   - If you publish a paper or preprint, add it to `.zenodo.json` under `related_identifiers` with the appropriate relation (e.g., `isSupplementTo`, `isAlternateIdentifier`).

Notes
- Zenodo will read `.zenodo.json` on each release. Prefer concise, plain‑text descriptions.
- If multiple authors are added, include `name` and `affiliation` fields in `creators`.


