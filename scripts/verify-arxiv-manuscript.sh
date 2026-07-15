#!/usr/bin/env bash
set -euo pipefail

tex="arxiv/main.tex"
bib="arxiv/references.bib"
pdf="arxiv/main.pdf"
archive="arxiv/incidence_theory_arxiv_src.tar.gz"
theorem_map="docs/papers/manuscript-theorem-map.tsv"
theorem_index="docs/papers/incidence-theorem-index.tsv"
citation="CITATION.cff"
zenodo=".zenodo.json"
landing="docs/index.md"

for file in "$tex" "$bib" "$pdf" "$archive" "$theorem_map" "$theorem_index" \
    "$citation" "$zenodo" "$landing"; do
  if [[ ! -f "$file" ]]; then
    echo "arXiv manuscript artifact is missing: $file" >&2
    exit 1
  fi
done

if command -v jq >/dev/null 2>&1; then
  jq -e . "$zenodo" >/dev/null
fi

metadata_files=("$citation" "$zenodo" "$landing" "arxiv/README.md")
for file in "${metadata_files[@]}"; do
  if rg -q -F "A Fourth Foundation" "$file"; then
    echo "public metadata retains unsupported legacy positioning: $file" >&2
    exit 1
  fi
done

if ! rg -q -F "Exact Descent of Ternary Relations along Incidence Bisimulation Quotients" \
    "$citation" "arxiv/README.md"; then
  echo "citation metadata lacks the current paper title" >&2
  exit 1
fi
if ! rg -q -F "10.5281/zenodo.17345515" "$citation" "arxiv/README.md"; then
  echo "stable Zenodo concept DOI is missing from citation metadata" >&2
  exit 1
fi
if ! rg -q -F "10.5281/zenodo.17345516" "arxiv/README.md"; then
  echo "existing Zenodo version DOI is not distinguished in arXiv metadata" >&2
  exit 1
fi

awk -F '\t' -v tex="$tex" '
  FNR == 1 {
    if ($1 != "spine" || $2 != "manuscript_marker") {
      print "invalid manuscript theorem map header" > "/dev/stderr"
      failed = 1
    }
    next
  }
  {
    expected++
    if ($1 != expected || $2 == "") {
      print "invalid manuscript theorem map row " FNR > "/dev/stderr"
      failed = 1
      next
    }
  }
  END {
    if (expected != 29) {
      print "manuscript theorem map must contain 29 rows, got " expected > "/dev/stderr"
      failed = 1
    }
    exit failed
  }
' "$theorem_map"

while IFS=$'\t' read -r spine marker; do
  [[ "$spine" == "spine" ]] && continue
  if ! rg -q -F -- "$marker" "$tex"; then
    echo "manuscript lacks theorem-spine marker $spine: $marker" >&2
    exit 1
  fi
done < "$theorem_map"

if ! diff -u \
    <(awk -F '\t' 'FNR > 1 { print $1 }' "$theorem_index") \
    <(awk -F '\t' 'FNR > 1 { print $1 }' "$theorem_map"); then
  echo "manuscript theorem map and checked theorem index have different spines" >&2
  exit 1
fi

required_source=(
  "Exact Descent of Ternary Relations"
  "Exact descent criterion"
  "Kernel-pair coequalizer"
  "Coordinatewise classification"
  "Structural orbit classification"
  "3n^4"
  "32"
  "We make no priority or formalization-first"
  "29 groups"
)

for marker in "${required_source[@]}"; do
  if ! rg -q -F "$marker" "$tex"; then
    echo "arXiv manuscript lacks required marker: $marker" >&2
    exit 1
  fi
done

forbidden_source=(
  "A Fourth Foundation Beyond Set, Category, and Type"
  "Universal Applicability"
  "Adhesive Category Model"
  "Homotopy Type Theory Model"
  "all category laws"
)

for marker in "${forbidden_source[@]}"; do
  if rg -q -F "$marker" "$tex"; then
    echo "arXiv manuscript retains unsupported legacy claim: $marker" >&2
    exit 1
  fi
done

archive_names="$(tar -tzf "$archive" | sed 's#^\./##' | sort)"
for name in main.tex references.bib README.md; do
  if ! grep -qx "$name" <<<"$archive_names"; then
    echo "arXiv source archive lacks $name" >&2
    exit 1
  fi
done

if ! cmp -s <(tar -xOzf "$archive" main.tex) "$tex"; then
  echo "archived main.tex is stale" >&2
  exit 1
fi
if ! cmp -s <(tar -xOzf "$archive" references.bib) "$bib"; then
  echo "archived references.bib is stale" >&2
  exit 1
fi

if command -v pdftotext >/dev/null 2>&1; then
  pdf_text="$(pdftotext "$pdf" -)"
  if ! grep -q "Exact Descent of Ternary Relations" <<<"$pdf_text"; then
    echo "arXiv PDF does not contain the current title" >&2
    exit 1
  fi
  if grep -q "A Fourth Foundation Beyond Set" <<<"$pdf_text"; then
    echo "arXiv PDF is the unsupported legacy manuscript" >&2
    exit 1
  fi
fi

echo "arXiv manuscript and source archive verified"
