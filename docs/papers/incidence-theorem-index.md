# Incidence Theory Lean-to-paper theorem index

The machine-readable index is
[`incidence-theorem-index.tsv`](incidence-theorem-index.tsv).  Its 106 rows map
the numbered theorem spine in `incidence-quotient-outline.md` to checked claim
IDs in `docs/completion-claims.tsv`.  The claim matrix in turn fixes the Lean
source file, declaration name, and exact scope of every item.

This two-step mapping is intentional:

1. the paper outline records the mathematical narrative;
2. the theorem index records which checked claims support each numbered item;
3. the completion claim matrix records the authoritative Lean declaration;
4. `scripts/verify-paper-theorem-index.sh` rejects missing, non-checked, or
   non-consecutive entries, while `scripts/verify-completion-claims.sh` rejects
   missing source declarations.

Run both checks from the repository root:

```sh
bash scripts/verify-completion-claims.sh
bash scripts/verify-paper-theorem-index.sh
```

The `boundary` column is part of the checked index and states the hypothesis or
scope restriction that must remain visible when the corresponding theorem is
written into the paper.  The index does not license claims broader than those
boundaries.
