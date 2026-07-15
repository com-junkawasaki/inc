#!/usr/bin/env bash
set -euo pipefail

audit="docs/papers/mechanized-prior-art-audit.md"
review_packet="docs/papers/specialist-review-packet.md"
database_log="docs/papers/public-database-coverage-log.md"
manifest="incidence-theory/lake-manifest.json"

for file in "$audit" "$review_packet" "$database_log" "$manifest"; do
  if [[ ! -f "$file" ]]; then
    echo "mechanized prior-art audit input is missing: $file" >&2
    exit 1
  fi
done

database_markers=(
  "Snapshot date: 2026-07-15"
  "## Query families"
  "incidence structure quotient bisimulation"
  "## Candidate disposition log"
  "Bisimulation Quotient in Inquisitive Modal Logic"
  "## Coverage still external"
)

for marker in "${database_markers[@]}"; do
  if ! rg -q -F "$marker" "$database_log"; then
    echo "public database coverage log lacks required marker: $marker" >&2
    exit 1
  fi
done

mathlib_rev="$(awk '
  /"url": "https:\/\/github.com\/leanprover-community\/mathlib4.git"/ { mathlib = 1 }
  mathlib && /"rev":/ {
    line = $0
    sub(/^.*"rev": "/, "", line)
    sub(/".*$/, "", line)
    print line
    exit
  }
' "$manifest")"

if [[ -z "$mathlib_rev" ]]; then
  echo "cannot read pinned mathlib revision from $manifest" >&2
  exit 1
fi

if ! rg -q -F "$mathlib_rev" "$audit"; then
  echo "mechanized prior-art audit does not name pinned mathlib revision $mathlib_rev" >&2
  exit 1
fi

required_markers=(
  "Lean 4 / mathlib"
  "Isabelle/HOL + AFP"
  "Mizar / MML"
  "Rocq / official package index"
  "evidence of priority"
  "Residual external gate"
)

for marker in "${required_markers[@]}"; do
  if ! rg -q -F "$marker" "$audit"; then
    echo "mechanized prior-art audit lacks required marker: $marker" >&2
    exit 1
  fi
done

review_markers=(
  "Status: ready to send; external review not yet obtained."
  "## Five review questions"
  "## Evidence map"
  "## Required response record"
  "accept with changes"
  "reject positioning"
)

for marker in "${review_markers[@]}"; do
  if ! rg -q -F "$marker" "$review_packet"; then
    echo "specialist review packet lacks required marker: $marker" >&2
    exit 1
  fi
done

echo "mechanized prior-art audit metadata verified"
