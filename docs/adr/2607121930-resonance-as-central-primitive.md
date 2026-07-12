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
- `ResonanceRespects` requires modes of related inputs to be matchable in both
  directions; `BisimulationResonanceSpec` applies this to `approxBisim`.
- `ResonanceHomomorphism` preserves every resonant triple and is closed under
  identity and composition. Product projections and the diagonal supply
  nontrivial structural examples.

## Consequences

- New theory should state laws using `resonance` rather than `glue`.
- Algorithms may use `selectedMode` when a deterministic representative is
  required.
- Existing glue theorems remain compatibility results and will be migrated
  incrementally.
- Strict associativity of the selector is not promoted to a universal physical
  law. Higher resonance coherence may instead be stated relationally or up to
  bisimulation.
- Translation and quotient APIs should use `ResonanceHomomorphism` and
  `ResonanceRespects` when their claims concern the interaction itself;
  selector equations remain appropriate only for executable choices.
- `ResonantBehavioralTranslation` is the combined translation interface: it
  preserves boundary shape, bisimulation, and every resonance triple.
  `ResonantBehavioralEmbedding` strengthens it by reflecting resonance.
- On bisimulation quotients, `quotientResonance` means that some representatives
  resonate. Exact recovery on chosen representatives requires
  `QuotientResonanceCongruent`, extensionality in both inputs and the output.
- `AssociativeResonanceSpec` compares existentially reachable output modes from
  `(i resonance j) resonance k` and `i resonance (j resonance k)`. It does not
  privilege a selected intermediate mode. The law holds for Peano resonance and
  is closed under products.
- Internal logic represents a physical statement as the structured atom
  `ResonanceAtom ⟨i, j, k⟩`. Its canonical valuation is exactly
  `resonance i j k`; symmetry, vacuum/unit, and homomorphic transport therefore
  become checked semantic laws without changing the complete propositional
  calculus.
- The dependent-calculus integration boundary is
  `IncDepRawNormalizedResonanceCompletion`: normalized renaming/substitution
  preservation is kept independent from legacy Unit-fiber proof-object
  alignment, while the semantic carrier supplies resonance, relational
  associativity, and quotient congruence. Peano resonance provides the first
  complete instance.
- `finiteIncidence` supplies a second normalized dependent completion. Its
  resonance is associative and quotient-congruent but provably not functional:
  two modes resonate at `(root, root)` while the selector chooses only one.
- The finite model also gives a concrete enumeration of
  `ResonanceAtom FiniteIncidence`, hence full canonical Kripke completeness and
  countermodels for its propositional resonance language. These metatheorems
  quantify over arbitrary atom valuations; restricting completeness to
  valuations satisfying physical resonance laws requires an axiomatized theory
  extension.
- For the two-point multi-valued model, that extension is explicit:
  `finiteResonanceDiagram` is the finite physical theory of all eight triples.
  The physical valuation satisfies it, it characterizes all-resonant
  valuations, and completeness/countermodels are checked relative to it.
- More generally, `FiniteResonancePresentation` generates a complete signed
  diagram from an exhaustive finite triple list and a decision procedure.
  `FinitePhysicalResonanceLogic` proves relative completeness for every such
  presentation with countably coded atoms.
