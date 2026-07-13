# Theory of Incidence

`inc` is a Lean 4 formalization of incidence structures, bisimulation,
translations, internal logic, dependent raw syntax, and selected mathematical
constructions.

Its central interaction primitive is the ternary relation
`resonance i j k`: incidences `i` and `j` resonate with emergent mode `k`.
Resonance may be multi-valued. `selectedMode i j` is only a computable choice
of one mode and preserves compatibility with the historical `glue` API.

The root README is intentionally a short dashboard. Detailed proof history is
kept under [`docs/`](docs/).

## Current status

| Area | Status |
|---|---|
| Incidence core and bisimulation | Checked |
| Ternary resonance primitive | Checked; symmetric physical law is `ResonanceSpec` |
| Concrete consistency models | Checked |
| Translation preservation/reflection | Checked under explicit hypotheses |
| Propositional internal logic | Soundness and completeness checked |
| Dependent raw calculus | Pi, Sigma, Identity, reduction and semantics checked |
| Structural rename/substitution preservation | Complete; certificate inhabited |
| Quotient theory | Conditional general theory plus concrete simplex quotient |
| Existing mathematics | Peano, integers, faithful ordered rational field, Dedekind-complete additive real resonance, HF sets, pairs, trees, paths, simplices, product, sum, quotient |
| Unit-fiber relational semantics | Legacy alignment-dependent API being replaced |
| Integer/rational/analysis reconstruction | Dedekind-complete ordered additive group and compatible signed commutative-ring laws checked; nonzero real inverses/analysis open |

The structural preservation completion certificate is
`incDepRawNormalizedBasicPreservation : IncDepRawNormalizedBasicPreservation`.
It packages total formation/typing renaming, total substitution with proved
lift, and an unconditional closed identity instance.

See [authoritative status](docs/status.md) for scope, evidence, and remaining
work.

## Documentation

- [Current authoritative status](docs/status.md)
- [Proof map](docs/proofs/README.md)
- [Verification guide](docs/verification.md)
- [Proof-completion audit](docs/inc-proof-completion-audit.md)
- [Cycle-41 maturity ADR](docs/adr/2607100600-inc-theory-maturity-cycle41.md)
- [Detailed checked history](docs/history/post-cycle-41.md)
- [Research log](RESEARCH_LOG.md)

## Lean modules

| Module | Subject |
|---|---|
| `IncidenceTheory.lean` | Core incidence structure and bisimulation |
| `Coherent.lean` | Coherent incidence laws |
| `GraphModel.lean` | Concrete graph/finite models |
| `Logic.lean` | Internal propositional logic |
| `Peano.lean`, `HFSets.lean` | Natural numbers and hereditary finite sets |
| `Pairs.lean`, `Tree.lean` | Ordered pairs and trees |
| `PathComplex.lean`, `Simplex.lean` | Paths and simplicial examples |
| `Product.lean`, `Sum.lean`, `Quotient.lean` | Generic constructors |
| `CrossInstance.lean` | Translations, dependent calculus, semantic preservation |

## Verify

From the repository root:

```bash
./verify.sh
```

The verifier builds the Lean project, runs the examples, and rejects unproved
declarations. A successful run currently builds 56 jobs.

## Scope

The checked core does not assert unconditional pushout preservation,
boundary-square-zero, or completeness for arbitrary translations. Such results
require the hypotheses stated by their Lean declarations.

Likewise, structural substitution preservation is complete at the normalized
readiness level, while the older Unit-fiber relational completion and broader
reconstruction of existing mathematics remain separate follow-up work.
