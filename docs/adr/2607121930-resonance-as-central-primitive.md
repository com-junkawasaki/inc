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
- Completion is closed under incidence products: resonance laws, relational
  associativity, and bisimulation-quotient congruence all transport
  componentwise. The dependent normalized completion exposes this as `.prod`.
- `incidenceSum` must not inherit the default selector-induced relation: doing
  so provably erased unselected component modes. Its explicit `sumResonance`
  now retains all same-side modes, supplies symmetric unit interactions, and
  has a generic `ResonanceSpec` whenever both factors do.
- Unlike products, sums do not preserve the full completion unconditionally.
  A component resonance may generate the designated unit and thereby enable a
  cross-side second step in only one parenthesization; moreover bisimulation
  may identify leaves across sides while resonance remains side-sensitive.
  Both failures have checked finite/Nat counterexamples. Any positive closure
  theorem must assume unit reflection and cross-side observational separation.
- Observational separation has a reusable sufficient form: faithfulness makes
  every bisimulation class a singleton and hence makes any resonance relation
  quotient-congruent. Combined with the existing leafless-side faithfulness
  theorem, this yields a positive sum result for `Nat ⊕ cycleIncidenceFixed`.
- The other required condition is formalized as
  `UnitReflectingResonanceSpec`: the vacuum cannot emerge from two non-vacuum
  inputs. Nat resonance satisfies it, whereas the finite all-mode resonance
  refutes it at `(root, root, leaf)`.
- Integer reconstruction provides a complementary algebraic model:
  `integerIncidence` uses signed toward-zero boundary roles and addition as
  functional associative resonance. Every value resonates with its additive
  inverse at the vacuum, so the model provably refutes unit reflection while
  supporting a genuine group-level interaction absent from naturals.
  Positive and negative predecessor roles are observationally distinct;
  their indexed tags make the whole model faithful, not merely `+1 ≉ -1`.
  Integer resonance is therefore quotient-congruent and instantiates
  `IncDepRawNormalizedResonanceCompletion`.
- Algebraic operations beyond the central interaction can remain relational:
  `DistributiveResonanceSpec` equips an incidence with a multiplicative ternary
  resonance and states its unit, commutativity, associativity, and distribution
  over additive resonance. The integer instance proves these laws from integer
  multiplication and addition.
- Rational reconstruction now quotients positive-denominator integer fractions
  by cross multiplication. Addition and multiplication respect that relation;
  the lifted addition gives a functional associative resonance and embeds the
  integers injectively. Quotient negation supplies additive inverses, while
  multiplication is commutative, unital, associative, and distributive and is
  packaged as `rationalDistributiveResonanceSpec`. The relational
  `FieldResonanceSpec` adds nontriviality and additive/multiplicative inverse
  mode existence without imposing a global inverse selector. Rationals
  instantiate it, and their inverse modes prove left and right multiplication
  cancellation. Rational incidence now observes each nonzero value by a
  value-indexed role on a one-step boundary to zero. A two-level rank proves
  well-foundedness, boundary matching reflects role equality, and
  `rationalIncidence_approxBisim_iff` establishes full faithfulness. Rational
  resonance consequently descends to observational classes and supplies an
  `IncDepRawNormalizedResonanceCompletion`. Replacing the value-indexed role by
  a canonical reduced numerator/denominator observation remains a refinement,
  not a prerequisite for semantic faithfulness.
- Ordered algebra is also relational. `OrderedFieldResonanceSpec` extends the
  field layer by a total partial order, monotonicity of additive resonance, and
  closure of the nonnegative cone under multiplicative resonance. Rational
  cross-multiplication order is representative-independent, instantiates this
  specification, and reflects the ordinary integer order along the embedding.
- The first real-completion layer uses Dedekind cuts over that dense rational
  order. `IncReal` requires a nonempty proper lower set with downward closure
  and no greatest element. Principal rational cuts satisfy these conditions,
  and rational density proves their embedding into `IncReal` injective and
  order-exact. Inclusion of lower cuts is a total order. The union of any
  nonempty upper-bounded family is again a cut and is proved to be its least
  upper bound, establishing Dedekind completeness. Cut arithmetic and real
  analysis remain the next layer rather than being inferred from completeness.
- Dedekind addition is now defined by existential rational sum modes below each
  cut. Density supplies the slack needed for the identity and associativity
  proofs. It is associative, commutative, monotone, preserves principal rational
  addition, and has the principal zero as unit. A faithful value-observed
  `realIncidence` selects this addition as its central resonance; its resonance
  is quotient-congruent and instantiates normalized dependent completion.
- Cut negation is defined by reflected complement witnesses. It is a valid cut,
  involutive, exactly order-reversing, agrees with rational negation on
  principal cuts, and proves the additive inverse law for every cut. The key
  approximation is constructive at the proof level: positive rational steps
  eventually cross any target; a minimal exit index brackets every cut by one
  step. `AdditiveGroupResonanceSpec` packages functional associative resonance
  with a selected inverse mode and is instantiated by integers, rationals, and
  Dedekind reals.
- Real multiplication has begun on the nonnegative cone. Positive rational
  multiplication strictly preserves order, allowing a product cut generated by
  positive member products together with all negative rationals. The resulting
  bundled cone is closed under cut addition with its commutative-monoid laws.
  Its nonnegative product is a valid cut, commutative, associative, has the
  principal one as unit, is zero-absorbing, and is monotone in both inputs.
  Nonzero nonnegative cuts have positive members cofinal above their members;
  together with strict positive sum-bound splitting this proves the forward
  distributive inclusion. The reverse inclusion, signed extension, full distribution,
  and inverse modes remain explicit subsequent obligations.
