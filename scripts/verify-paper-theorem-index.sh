#!/usr/bin/env bash
set -euo pipefail

matrix="docs/completion-claims.tsv"
index="docs/papers/incidence-theorem-index.tsv"
outline="docs/papers/incidence-quotient-outline.md"

for file in "$matrix" "$index" "$outline"; do
  if [[ ! -f "$file" ]]; then
    echo "paper theorem index input is missing: $file" >&2
    exit 1
  fi
done

awk -F '\t' '
  FNR == NR {
    if (FNR > 1 && $1 != "") {
      claimStatus[$1] = $2
    }
    next
  }
  FNR == 1 {
    if ($1 != "spine" || $2 != "title" || $3 != "claims" || $4 != "boundary") {
      print "invalid paper theorem index header" > "/dev/stderr"
      failed = 1
    }
    next
  }
  {
    expected++
    if ($1 != expected) {
      print "paper theorem spine is not consecutive at row " FNR ": expected " expected ", got " $1 > "/dev/stderr"
      failed = 1
    }
    if ($2 == "" || $4 == "") {
      print "paper theorem spine " $1 " lacks a title or scope boundary" > "/dev/stderr"
      failed = 1
    }
    count = split($3, claims, ";")
    if (count == 0 || $3 == "") {
      print "paper theorem spine " $1 " has no checked claim" > "/dev/stderr"
      failed = 1
    }
    for (i = 1; i <= count; i++) {
      claim = claims[i]
      if (!(claim in claimStatus)) {
        print "paper theorem spine " $1 " references unknown claim " claim > "/dev/stderr"
        failed = 1
      } else if (claimStatus[claim] != "checked") {
        print "paper theorem spine " $1 " references non-checked claim " claim > "/dev/stderr"
        failed = 1
      }
    }
  }
  END {
    if (expected != 29) {
      print "paper theorem index must contain exactly 29 spine entries, got " expected > "/dev/stderr"
      failed = 1
    }
    exit failed
  }
' "$matrix" "$index"

awk '
  /^[0-9]+\./ {
    number = $0
    sub(/\..*$/, "", number)
    expected++
    if (number != expected) {
      print "paper outline theorem spine is not consecutive: expected " expected ", got " number > "/dev/stderr"
      failed = 1
    }
  }
  END {
    if (expected != 29) {
      print "paper outline must contain exactly 29 theorem-spine entries, got " expected > "/dev/stderr"
      failed = 1
    }
    exit failed
  }
' "$outline"

echo "paper theorem index verified"
