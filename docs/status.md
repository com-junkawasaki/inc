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
- `ResonanceRespects` expresses back-and-forth relational congruence, while
  `BisimulationResonanceSpec` specializes it to observational equivalence.
  `ResonanceHomomorphism` has checked identity and composition operations;
  product projections and the diagonal are concrete homomorphisms.
- `ResonantBehavioralTranslation` integrates resonance preservation with the
  existing boundary-shape and bisimulation translation API. Its identity,
  composition, unit laws, and associativity are checked;
  `ResonantBehavioralEmbedding` additionally reflects resonance.
- `quotientResonance` defines the induced existential relation on bisimulation
  classes. `QuotientResonanceCongruent` is the exact three-coordinate
  extensionality condition yielding the representative theorem
  `quotientResonance_mk_iff`; the Peano model satisfies it non-vacuously.
- `AssociativeResonanceSpec` states relational associativity as equality of the
  modes reachable through either parenthesization. Peano addition satisfies it,
  and `incidenceProd` preserves it componentwise.
- `DistributiveResonanceSpec` adds a second multiplicative resonance channel
  with one, symmetry, relational associativity, and distribution over the
  central additive resonance. Integers instantiate the full specification,
  including a checked nontrivial distributivity example.
- The internal propositional logic now has structured `ResonanceAtom` triples,
  interpreted by `resonanceValuation`. Symmetry and unit laws are semantically
  valid formulas, and resonance homomorphisms preserve atomic formulas. The
  bridge to `ResonanceSpec` lives in the coherent layer to avoid a core/logic
  dependency cycle.
- For `finiteIncidence`, all resonance triples are explicitly countably coded.
  The resulting resonance-atom language has checked Kripke completeness,
  consistency/satisfiability equivalence, and canonical countermodels. This is
  propositional completeness over resonance atoms; completeness for only the
  physically lawful valuations remains a separate theory-extension problem.
- That finite theory-extension problem is now solved for the complete concrete
  diagram: `finiteResonanceDiagram` lists all eight physical triples,
  characterizes exactly the all-resonant valuations, is satisfied by the actual
  incidence, and has relative Kripke completeness plus diagram-respecting
  canonical countermodels. A generic completeness theorem for arbitrary
  `ResonanceSpec` models remains open.
- `FiniteResonancePresentation` now generalizes the diagram construction to
  any explicitly finite decidable resonance: true triples become positive
  atoms and false triples become negated atoms. Its diagram characterizes the
  physical valuation exactly. `FinitePhysicalResonanceLogic` combines such a
  presentation with atom coding and supplies relative Kripke completeness and
  canonical countermodels. The two-point model instantiates this generic API.
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
- Existing concrete translation witnesses still need to be upgraded to
  `ResonantBehavioralTranslation` where their boundary and interaction laws
  genuinely agree; some historical glue homomorphisms do not meet this stronger
  specification.
- The legacy `IncDepRawUnitRelationalCompletion` still depends on coherent
  readiness alignment for its Unit-fiber-specific relational naturality.
  Structural preservation has now been separated from that condition:
  `IncDepRawNormalizedResonanceCompletion` packages unconditional normalized
  preservation with resonance, relational associativity, and quotient
  congruence. A complete Nat instance is checked, and legacy certificates have
  a compatibility bridge to the normalized structural theorem.
  A second complete instance uses multi-valued `finiteIncidence`; it is proved
  not to admit any `FunctionalResonanceSpec`, so the new completion is strictly
  more relational than the selector-based special case.
- Normalized resonance completion is compositional under products.
  `quotientResonanceCongruentProd` proves quotient extensionality componentwise,
  and `IncDepRawNormalizedResonanceCompletion.prod` transports every completion
  field. `natIncidence × finiteIncidence` is a checked mixed functional/
  multi-valued instance.
- The sum constructor was audited and corrected: its previous default
  resonance was selector-induced and erased unselected modes of multi-valued
  factors. `sumResonance` now lifts the full same-side relations and adds only
  the required unit interactions; `selected_resonates` and `resonanceSumSpec`
  are checked generically. A concrete theorem confirms that the finite
  `(root, root, leaf)` mode survives the sum. Associativity and quotient
  congruence were then audited and both fail without extra hypotheses:
  `finiteIncidenceSum_not_associativeResonance` exhibits a unit-generating
  intermediate mode available under only one parenthesization, while
  `incidenceSum_nat_not_quotientResonanceCongruent` shows cross-side leaf
  collapse erases the side information used by resonance. Sum completion
  therefore requires explicit unit-reflection and bisimulation-separation
  conditions; it is not an unconditional closure theorem.
- A positive quotient result is now checked: every faithful incidence has
  quotient-congruent resonance (`quotientResonanceCongruent_of_faithful`). Thus
  a sum of faithful factors with a leafless side inherits quotient congruence;
  `natIncidence ⊕ cycleIncidenceFixed` is the concrete witness. The remaining
  sum obstruction is relational associativity/unit creation, not quotient
  descent under these separation hypotheses.
- `UnitReflectingResonanceSpec` now names the missing associativity-side law:
  a resonance producing the unit must have a unit input. Peano addition
  satisfies it; the multi-valued finite model provably does not. This exactly
  classifies the models used by the positive direction and the checked sum
  associativity counterexample. A generic conditional sum-associativity proof
  still requires the full tagged intermediate-mode case analysis.
- Pushout preservation and generic boundary-square-zero are conditional on the
  categorical or linear hypotheses in their declarations.
- Translation completeness is proved only for the stated fragments and
  observation hypotheses, not for arbitrary translations.
- The general quotient construction requires boundary/glue invariance and
  well-foundedness conditions.

## Existing mathematics reconstruction

Checked constructions include:

- Peano natural numbers
- integers with signed predecessor boundaries, additive resonance, zero,
  inverses, additive/multiplicative relational associativity, and distributive
  ring-style resonance
- rationals as positive-denominator integer fractions modulo cross
  multiplication, with an injective integer embedding and quotient-respecting
  addition, negation, and multiplication; additive resonance is commutative,
  unital, associative, and has inverses, multiplication is commutative, unital,
  associative, and distributes over addition; every nonzero rational has a
  multiplicative inverse resonance mode, nonzero multiplication cancels on
  either side, and concrete half addition/multiplication examples are checked;
  cross-multiplication order descends to the quotient, is reflexive,
  antisymmetric, transitive, and total, exactly preserves integer order,
  is translation-monotone under addition, and has a multiplicatively closed
  nonnegative cone; rational density also supplies positive intermediates and
  splits every strict bound below a positive sum into two positive strict
  approximants, preparing the cut-level real distributivity proof
- Dedekind real carriers as inhabited, proper, downward-closed, rounded lower
  rational cuts; cut inclusion is a total order, rational principal cuts are
  well formed, and the rational-to-real embedding is injective and exactly
  preserves/reflects order, using the checked density of rational order; every
  nonempty upper-bounded family has a least upper bound given by union of cuts;
  cut addition is well formed, associative, commutative, monotone, and has the
  principal zero as identity, while the rational embedding preserves addition;
  cut negation is well formed, involutive, reverses order exactly, preserves
  principal rational negation, and supplies additive inverses for every cut;
  an explicit Archimedean finite-step theorem and minimal boundary-exit
  construction provide the approximation needed by the general inverse proof;
  the nonnegative cone is bundled and closed under cut addition, forming a
  commutative additive monoid, and is closed under a well-formed cut product;
  this product is a commutative monoid with principal one, absorbs zero, and is
  monotone in both inputs, based on checked strict multiplication monotonicity
  and positivity reflection for positive rationals; nonzero nonnegative cuts
  have positive members cofinal above every member, nonzero products stay
  nonzero, and common-factor synchronization plus positive-bound splitting
  proves both distributive laws, completing the nonnegative commutative-semiring
  laws; canonical positive and negative parts reconstruct every real exactly,
  and their four-term signed product is commutative, has principal one as its
  identity, absorbs zero, and agrees exactly with the nonnegative cut product
  on nonnegative inputs; all four input-sign quadrants reduce exactly to a
  nonnegative product or its additive negation, providing the case interface
  for signed arithmetic; negation exchanges positive/negative parts and changes
  either product sign, and all eight sign cases reduce signed associativity to
  the checked nonnegative associativity law; additive cancellation and
  difference rearrangement reduce the mixed-sign sum case to nonnegative
  distribution, completing both distributive laws for arbitrary signed inputs;
  four-quadrant nonzero-product analysis proves there are no zero divisors, and
  distribution then gives left/right cancellation by every nonzero factor;
  every nonzero nonnegative real now has a well-formed relational reciprocal
  cut generated by inverse resonances of positive outside rationals, and its
  source product is exactly principal one by a checked inside/outside ratio
  approximation; signed extension supplies left/right inverses for every
  nonzero real, and `realMulResonance` instantiates distributive, field, and
  ordered-field resonance specifications on the Dedekind-complete real order;
  canonical positive/negative magnitudes define absolute value with exact zero
  and triangle laws, while absolute difference defines a symmetric, separated,
  triangle-bounded nonnegative real distance; positive rational radii define
  metric convergence and Cauchy sequences, constant sequences satisfy both,
  and exact rational halving plus the triangle law proves every convergent
  sequence is Cauchy; rounded-cut separation forces any nonnegative real below
  every positive rational radius to be zero, proving metric limits unique;
  distance is negation-invariant and addition-subadditive, so convergent
  sequences remain convergent under termwise negation, addition, and subtraction;
  distance control yields order control, finite prefixes admit inductively
  selected upper bounds, and every Cauchy sequence is globally bounded above
  and below; every tail therefore has a Dedekind supremum, these suprema form a
  decreasing sequence, and each Cauchy radius bounds the distance between a
  suitable sequence term and its corresponding tail supremum; order duality
  through negation constructs arbitrary nonempty bounded infima with their
  greatest-lower-bound law, and the Cauchy limit candidate is now defined as
  the infimum of the tail-supremum family; Cauchy control sandwiches this
  candidate between `a_N-ε` and `a_N+ε`, and half-radius composition proves
  every Cauchy sequence converges to it, completing the real metric space;
  absolute value is multiplicative and 1-Lipschitz by the reverse triangle
  estimate, hence preserves convergence; sequential continuity now has checked
  identity, constant, negation, absolute-value, and composition constructors;
  a value-observed real incidence is faithful, quotient-congruent, and connected
  to normalized dependent resonance completion
- hereditary finite sets
- ordered pairs and trees
- paths, cycles, and simplices
- products, sums, and conditional quotients
- propositional logic and a dependent Pi/Sigma/Identity fragment

Major remaining areas include a canonical reduced-fraction boundary and
computational reciprocal selector, extension of nonnegative cut multiplication
of continuity, compactness, series, and calculus beyond the complete metric layer,
real analysis, broader algebra, and a larger categorical library. Rational
incidence is now observationally faithful:
zero has an empty boundary and every nonzero rational has a one-step boundary
to zero carrying a value-indexed observation role. The checked rank decrease,
boundary extensionality, and `rationalIncidence_approxBisim_iff` prove that
bisimulation is exactly equality. Thus rational resonance is quotient-congruent
and instantiates `IncDepRawNormalizedResonanceCompletion`. This role-indexed
presentation is faithful but is not yet a canonical reduced numerator/
denominator presentation. Integer bisimulation faithfulness is complete:
indexed signed boundary roles give boundary extensionality, and
`integerIncidence_approxBisim_iff` proves observational equivalence is exactly
equality. Consequently integer resonance descends to the bisimulation quotient
and supplies a complete normalized dependent resonance completion.

## Verification evidence

Run `./verify.sh` from the repository root. The verifier performs a full Lean
build, executes examples, and scans for unproved declarations. The latest
completion audit passes all build jobs with no unproved declarations.
