# Authoritative project status

This document records the current state of the checked development. Historical
progress narratives belong in [`history/`](history/), while design decisions
belong in [`adr/`](adr/).

## Checked foundations

- `Incidence.resonance : I → I → I → Prop` is the central relational
  interaction: `resonance i j k` means that `k` is an emergent mode of `i` and
  `j`. It may be multi-valued.
- `Incidence.selectedMode` is the computable compatibility selector backed by
  the historical `glue` field. Every selected mode is proved resonant.
- `ResonanceSpec` supplies physical symmetry, unit modes, and symmetric type
  compatibility. `FunctionalResonanceSpec` additionally states that the
  selector enumerates every mode.
- `finiteIncidence` is a concrete multi-valued symmetric resonance model;
  `natIncidence` is a concrete symmetric functional resonance model; products
  preserve resonance componentwise.
- The incidence core and bisimulation equivalence are formalized in Lean.
- Concrete finite, graph, natural-number, pair, path, cycle, and simplex models
  witness non-vacuity of the implemented fragments.
- General faithfulness criteria and several preservation/reflection theorems
  are checked under explicit structural hypotheses.
- The propositional internal logic has checked soundness and completeness.
- The dependent raw calculus contains Pi, Sigma, Identity, substitution,
  reduction, semantic readiness, and concrete dependent examples.
- Product, sum, and conditional quotient constructors are formalized.

## Structural preservation completion

The normalized structural layer is complete and unconditional.

Evidence in `IncidenceTheory/CrossInstance.lean`:

- `IncDepRawFormationDispatchReady.renameNormalized`
- `IncDepRawTypingDispatchReady.renameNormalized`
- `IncDepRawNormalizedReadinessPreservingSubstitution.lift`
- `IncDepRawFormationDispatchReady.substituteNormalized`
- `IncDepRawTypingDispatchReady.substituteNormalized`
- `incDepRawEmptyNormalizedIdentitySubstitution`
- `IncDepRawNormalizedBasicPreservation`
- `incDepRawNormalizedBasicPreservation`

The completion covers every formation and typing constructor. Dependent
Apply/Pair/Second branches use explicit instantiate/rename or
instantiate/substitute equalities with synchronized casts.

## Conditional or unfinished layers

- Most historical models currently use the default functional resonance
  induced by `glue`. Their public APIs will migrate incrementally to relational
  resonance and `selectedMode` terminology.
- The legacy `IncDepRawUnitRelationalCompletion` depends on coherent readiness
  alignment. Its replacement should consume normalized readiness instead.
- Pushout preservation and generic boundary-square-zero are conditional on the
  categorical or linear hypotheses in their declarations.
- Translation completeness is proved only for the stated fragments and
  observation hypotheses, not for arbitrary translations.
- The general quotient construction requires boundary/glue invariance and
  well-foundedness conditions.

## Existing mathematics reconstruction

Checked constructions include:

- Peano natural numbers
- hereditary finite sets
- ordered pairs and trees
- paths, cycles, and simplices
- products, sums, and conditional quotients
- propositional logic and a dependent Pi/Sigma/Identity fragment

Major remaining areas include integers, rationals, broader algebra, real
analysis, and a larger categorical library.

## Verification evidence

Run `./verify.sh` from the repository root. The verifier performs a full Lean
build, executes examples, and scans for unproved declarations. The latest
completion audit passed all 56 build jobs with no unproved declarations.
