#!/usr/bin/env bash
set -euo pipefail

arxiv_pdf="arxiv/main.pdf"
journal_pdf="journal/mscs/draft_Proof_hi.pdf"
readme="journal/mscs/README.md"
letter="journal/mscs/cover-letter.md"
gates="docs/papers/journal-submission-gate.tsv"

for file in "$arxiv_pdf" "$journal_pdf" "$readme" "$letter" "$gates"; do
  if [[ ! -f "$file" ]]; then
    echo "journal package artifact is missing: $file" >&2
    exit 1
  fi
done

if ! cmp -s "$arxiv_pdf" "$journal_pdf"; then
  echo "journal compatibility PDF is stale relative to arxiv/main.pdf" >&2
  exit 1
fi

if command -v pdftotext >/dev/null 2>&1; then
  journal_text="$(pdftotext "$journal_pdf" -)"
  if ! grep -q "Exact Descent of Ternary Relations" <<<"$journal_text"; then
    echo "journal PDF lacks the current paper title" >&2
    exit 1
  fi
  if grep -q "A Fourth Foundation Beyond Set" <<<"$journal_text"; then
    echo "journal PDF retains the unsupported legacy manuscript" >&2
    exit 1
  fi
fi

awk -F '\t' '
  FNR == 1 {
    if ($1 != "gate" || $2 != "status" || $3 != "evidence") {
      print "invalid journal gate header" > "/dev/stderr"
      failed = 1
    }
    next
  }
  {
    if ($1 == "" || $2 == "" || $3 == "") {
      print "incomplete journal gate row " FNR > "/dev/stderr"
      failed = 1
    }
    seen[$1] = $2
  }
  END {
    required[1] = "lean_core"
    required[2] = "paper_theorem_coverage"
    required[3] = "subscription_database_citation_traversal"
    required[4] = "specialist_novelty_review"
    required[5] = "author_submission_metadata"
    for (i = 1; i <= 5; i++) {
      if (!(required[i] in seen)) {
        print "missing journal gate: " required[i] > "/dev/stderr"
        failed = 1
      }
    }
    if (seen["subscription_database_citation_traversal"] != "pending_external" ||
        seen["specialist_novelty_review"] != "pending_external" ||
        seen["author_submission_metadata"] != "pending_author") {
      print "external journal gates must remain explicit until evidence is recorded" > "/dev/stderr"
      failed = 1
    }
    exit failed
  }
' "$gates"

if ! rg -q -F "Status: draft only; external journal gates are not yet passed." "$letter"; then
  echo "cover letter does not expose its unsent draft status" >&2
  exit 1
fi

echo "journal package and external gate status verified"
