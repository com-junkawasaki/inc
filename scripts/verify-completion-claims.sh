#!/usr/bin/env bash
set -euo pipefail

matrix="docs/completion-claims.tsv"

if [[ ! -f "$matrix" ]]; then
  echo "completion claim matrix is missing" >&2
  exit 1
fi

failed=0
while IFS=$'\t' read -r id status source declaration scope; do
  [[ "$id" == "id" ]] && continue
  [[ -z "$id" ]] && continue

  if [[ -z "$scope" ]]; then
    echo "claim $id has no scope" >&2
    failed=1
  fi

  case "$status" in
    checked)
      if [[ "$source" == "-" || "$declaration" == "-" ]]; then
        echo "checked claim $id has no evidence" >&2
        failed=1
      elif [[ ! -f "$source" ]]; then
        echo "checked claim $id names missing source $source" >&2
        failed=1
      elif ! rg -F -q "$declaration" "$source"; then
        echo "checked claim $id cannot find '$declaration' in $source" >&2
        failed=1
      fi
      ;;
    deferred|blocked)
      if [[ "$source" != "-" || "$declaration" != "-" ]]; then
        echo "$status claim $id must not masquerade as checked evidence" >&2
        failed=1
      fi
      ;;
    *)
      echo "claim $id has invalid status $status" >&2
      failed=1
      ;;
  esac
done < "$matrix"

if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

echo "completion claim matrix verified"
