# ADR: Resonance as the central interaction primitive

- Date: 2026-07-12
- Status: accepted, migration in progress

## Decision

The central interaction of an incidence is the ternary relation

```lean
resonance : I → I → I → Prop
```

`resonance i j k` means that `i` and `j` mutually excite or support the
emergent mode `k`. The relation is intentionally allowed to be multi-valued.

The former operation

```lean
glue : I → I → Option I
```

remains temporarily as the implementation of `selectedMode`: a computable
choice of at most one resonant mode. The core requires every selected mode to
be resonant, but does not require every resonant mode to be selected.

## Physical laws

`ResonanceSpec` records the additional physical structure:

- symmetry in the two interacting incidences;
- left and right unit/vacuum modes;
- symmetric compatibility of the two input types and the emergent mode.

These laws are not forced on every legacy incidence. Models that satisfy them
are explicitly certified. `FunctionalResonanceSpec` characterizes the special
case where the selector is complete and resonance has no unselected modes.

## Evidence

- `natIncidence` with addition has a symmetric functional resonance.
- `finiteIncidence` has a symmetric multi-valued resonance: both `leaf` and
  `root` are modes of the pair `(root, root)`, while the selector chooses only
  `root`.
- `incidenceProd` defines resonance componentwise and preserves
  `ResonanceSpec`.

## Consequences

- New theory should state laws using `resonance` rather than `glue`.
- Algorithms may use `selectedMode` when a deterministic representative is
  required.
- Existing glue theorems remain compatibility results and will be migrated
  incrementally.
- Strict associativity of the selector is not promoted to a universal physical
  law. Higher resonance coherence may instead be stated relationally or up to
  bisimulation.
