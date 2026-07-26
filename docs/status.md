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
- For every fixed raw dependent context, formation and typing judgments now
  form a single ternary resonance system. Formation and typing are represented
  exactly, derivation-preserving context renamings act functorially, and the
  free-unit Incidence encoding recovers the judgment system up to isomorphism.
  This closes the raw-calculus representation gap.
- A proof-theoretic model interface now gives independent formation and typing
  predicates closed under every raw inference rule. Mutual induction proves
  soundness in every such model; the derivability/term model is exact and least,
  and is stable under well-typed renaming and substitution. Thus term-model
  completeness is checked. Extensional set-valued or CwF semantics, conversion
  and normalization, and a dependent internal language complete for arbitrary
  `ResonanceSpec` models remain open and are not implied by this result.
- Well-formed raw contexts and extensional, well-typed substitutions now form a
  strict category. Derivation witnesses are erased only from morphism equality;
  their existence remains part of every morphism. Raw types reindex with exact
  identity/composition laws, and each context extension carries its display
  projection and generic variable. Substitution pairing exists for every term
  of a reindexed display type and is uniquely characterized by its projection
  and generic components, establishing the comprehension universal property.
  This supplies the contextual-category comprehension core beneath the existing
  set-valued dependent-family semantics. A fully bundled CwF with well-formed
  type and term presheaves remains separate.
- Well-formed types and total typed terms are now explicitly bundled over the
  context category. Both reindex strictly under identity and composition, and
  the typed-term-to-type projection is natural. The exact obstruction to a
  full CwF is checked by a negative theorem: Nat-indexed substitutions into the
  empty context retain irrelevant components, giving distinct identity and
  constant-unit endomorphisms. Hence the empty context is not terminal under
  the present morphism equality. Finite-context extensionalization or canonical
  normalization of irrelevant substitution components is the next required
  construction; no terminal-object or full-CwF claim is made yet.
- That finite-context correction is now constructed. Mutual scopedness
  predicates and derivation theorems prove every well-formed type and well-typed
  term depends only on variables below context length. Substitution on such
  syntax is extensional under agreement on that finite range. Quotienting
  substitutions by this agreement yields a strict corrected context category;
  composition is well defined in both arguments and the empty context is now
  terminal. The preceding negative theorem remains the witness that this
  quotient is necessary. The next CwF step is to descend the type and typed-term
  presheaves and comprehension operations to the corrected category.
- That descent is now complete. Well-formed types and total typed terms reindex
  on finite-support substitution classes independently of representatives,
  satisfy strict identity/composition laws, and have a natural type projection.
  Context extension, display projections, generic variables, pairing, both
  pairing equations, and uniqueness also descend. Hence the corrected category
  now contains terminal context, type/term substitution, and comprehension
  universality together. The remaining CwF task is conventional packaging of
  terms as explicit fibers over the type presheaf and a single bundled interface,
  not another missing substitution or universal-property theorem.
- The dependent term fibers are now explicit rather than represented only by
  the total typed-term space. They reindex over the corrected quotient category,
  the generic variable lies in the exact pullback fiber, and fiber-level pairing
  satisfies projection, genericity, and uniqueness. The capstone
  `incDepRawFiniteCwFTheorem` packages the terminal context, type substitution,
  dependent term substitution, and split comprehension. The syntactic CwF gap
  is therefore closed. What remains semantically is a structure-preserving CwF
  morphism from this syntax into the existing set-valued dependent-family
  interpretation, plus normalization/canonicity and higher identity structure.
- The semantic comparison is now constructed on the fully coherent completed
  fragment. Completed contexts, types, and terms embed into the finite
  syntactic CwF without changing raw syntax and receive the existing set-valued
  interpretation. For every semantically realized raw substitution, syntactic
  reindexing is raw substitution exactly and interpretation commutes with that
  substitution through the certified fiber equivalence. Corresponding
  syntactic and semantic context extensions and pairings satisfy projection
  and generic-variable equations, and the semantic generic component is the
  transported interpretation of the syntactically substituted term. The
  remaining whole-CwF-morphism gates are now narrower and explicit: construct
  coherent completion certificates for every raw CwF judgment and semantic
  realization data for every raw substitution. Neither global coverage result
  is currently claimed. Identity substitution is no longer part of the second
  gap: it is canonically realized for every completed judgment from the
  synthesized coherent telescope and lookup semantics. The two remaining
  global gates are bundled by `IncDepWholeCwFMorphismReadiness`, whose existence
  is proved equivalent to their conjunction. Normalization/canonicity and
  higher identity structure also remain open.
- Semantic-substitution coverage now also contains the fundamental nonidentity
  generator: every completed display type canonically realizes its raw
  successor-variable projection. The semantic map is the set-valued Sigma
  projection, replacement terms are weakened semantic lookups, and the induced
  finite-support class is exactly the syntactic CwF display projection.
  Realized substitutions are now also closed under composition: raw components,
  semantic assignment maps, and replacement interpretations compose, and the
  induced finite-support morphism is exactly categorical composition. Thus
  composites of already realized generators no longer form a separate gap.
  What remains is construction of target-independent realizations for enough
  generators (in particular arbitrary pairing components) to cover every raw
  substitution; closure alone does not prove that coverage.
- Completed-term comprehension pairings are now realized as well. Given a
  realized base substitution, a completed target term supplies the newest raw
  component, the Sigma-valued semantic assignment map, and its semantic
  replacement; older replacements are inherited from the base. The recovered
  finite morphism is exactly the syntactic CwF pairing. The residual coverage
  gap is sharper: an arbitrary source-side head component need not be the
  reindexing of any target term, so it requires a general source-term semantic
  realization and a coherence comparison with the reindexed target type.
- That general source-side pairing is now constructed conditionally on exactly
  those data. A coherent target formation, its substitution fiber equivalence,
  and a semantic source head produce a target-independent realization whose
  projection and generic equations hold and whose finite class is exactly the
  quotient-CwF pairing. Pairing shape and coherence are therefore no longer a
  residual obstruction. The remaining global substitution gate is the uniform
  supply of formation-substitution results and semantic typing results for all
  well-typed source components.
- Every raw substitution is now proved to have the required recursive pairing
  shape. Its canonical tail is obtained by dropping the newest component; the
  newest component is typed in the display family reindexed by that tail.
  Re-pairing recovers the component function exactly, the proof-erased
  substitution exactly, and the finite quotient morphism exactly as CwF
  pairing. Because raw substitutions retain proof-relevant derivations, raw
  structure equality before proof erasure is not asserted. Combined with the
  general semantic pairing theorem, this shows that the remaining coverage gap
  is semantic supply, not a missing syntactic generation theorem.
- Semantic coverage now has a checked recursive induction principle as well.
  Realization is invariant under replacing proof-relevant typing witnesses
  while retaining the same term function; empty targets are automatic; and a
  realized canonical tail plus semantic data for the actual source head
  realizes the original substitution. The remaining gate is therefore exactly
  uniform per-head synthesis. One further semantic-strengthening question is
  now explicit: the basic realization record stores maps and replacement terms
  but does not itself require a lookup-by-lookup coherence equation relating
  them. Existing identity, projection, pairing, and composition constructors
  satisfy their stated equations, but a strengthened global interface should
  package that coherence rather than rely on constructor provenance.
- That strengthened interface is now present. For every target lookup it stores
  a fiber equivalence from the replacement family to the target lookup family
  reindexed along the semantic map, together with equality of the transported
  replacement term and reindexed target variable. Generic identity
  substitutions and completed display projections inhabit the interface while
  retaining the exact target semantic tree. Strengthened pairing and
  composition closure are still required before the recursive coverage
  induction can be upgraded wholesale to this intrinsic interface.
- Strengthened pairing and composition closure are now proved. Composition
  reindexes each later lookup equivalence along the earlier semantic map and
  derives term coherence from transport naturality. General source-side pairing
  uses the head formation equivalence for the newest lookup and inherits all
  older lookup coherence. The recursive syntactic decomposition, semantic
  pairing step, and intrinsic coherence closure now align; uniform synthesis of
  formation-substitution and typing semantic data for every source head is the
  remaining substitution-coverage obligation.
- The public whole-CwF readiness boundary is now strengthened accordingly.
  Relative to a fixed completion model, every target is anchored to its
  canonical synthesized semantic context and substitutions must satisfy the
  intrinsic lookup-coherent interface. This coherent coverage implies the
  previous basic coverage, and strengthened readiness is proved equivalent to
  the conjunction of global judgment completion and coherent substitution
  coverage. Thus the old weaker record is retained for compatibility but no
  longer serves as the strongest advertised totality standard.
- The recursive coverage induction now lands directly in that strongest
  interface. Coherent proof-witness transport preserves the semantic map and
  target tree, empty targets are coherent automatically, and the arbitrary
  head/tail extension step realizes the original proof-relevant substitution
  with every lookup equation intact. No compatibility bridge remains between
  recursive generation and the strengthened coverage gate; uniform per-head
  semantic synthesis is the sole substitution-side premise.
- The propositional resonance language now has a carrier-independent law
  schema for symmetry, both unit laws, and type compatibility. Its semantic
  models are characterized exactly, the physical valuation models the schema
  exactly when a `ResonanceSpec` exists, and every finitary natural-deduction
  proof from schema instances is sound in every law model. This removes finite
  enumeration from general axiomatization and soundness. Strong Kripke
  completeness for the potentially infinite schema remains open.
- The same general law schema now has an explicit Kripke semantics. Every law
  axiom is forced at every world of every lawful model, so arbitrary finitary
  derivations from the schema are Kripke-sound without carrier enumeration.
  Strong completeness is characterized exactly by the remaining canonical
  countermodel property: every nonderivable formula must fail at some world of
  a lawful model. That construction, rather than soundness or the statement of
  the semantic target, is the remaining infinite-schema gap.
- That canonical-countermodel gap is now discharged for every countably coded
  resonance-atom language, including genuinely infinite carriers. A finite-
  support theorem makes schema derivability deductively closed; a relative
  avoidance chain produces a prime theory containing every law instance; and
  its canonical upper cone is lawful and satisfies the truth lemma. Hence
  lawful Kripke validity is exactly schema derivability under
  `CountableAtomCoding`. An enumeration-free theorem for uncountable atom
  languages remains outside the checked result.
- The countability boundary is now removed by an independent Zorn construction.
  Maximal finitary theory extensions are proved deductively closed and prime;
  they supply enumeration-free relative prime extensions, implication-failure
  future worlds, and the canonical truth lemma for arbitrary atom types.
  Applying this to the complete resonance-law schema gives lawful
  countermodels and strong Kripke completeness for arbitrary same-universe
  resonance carriers. The theorem is classical and uses choice; no choice-free
  or predicative completeness claim is made.
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

## Scoped reference-foundation completion

`ReferenceFoundation.completeFoundationCertificate` is the checked capstone
for ADR-2607141850. It bundles:

- hereditary-finite interpretation, syntactic preservation/reflection, and a
  nontrivial incidence witness;
- the Mathlib `ZFSet` model of the selected actual-infinity schema and its
  relative consistency theorem;
- layered prime/Henkin worlds, implication and universal counterworlds, a
  varying-domain canonical model, its truth lemma, and Kripke completeness for
  constant-free contexts and conclusions.

The constant-free restriction is intentional: object-language formulas are
separated from auxiliary Henkin constants introduced at later world levels.
This capstone does not assert full ZF, completeness for formulas containing
object constants, or the consistency of Lean itself.

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
- Normalized resonance completion is also conditionally compositional under
  sums. `IncDepRawNormalizedResonanceCompletion.sum` takes the exact minimal
  quotient obligation and combines it with the checked sum resonance and
  associativity laws; `sumOfFaithfulNoSharedLeaves` derives that obligation
  from the stronger reusable separation criterion.
  `natCycleSumNormalizedResonanceCompletion` is a concrete witness:
  the left Nat factor has exact, unit-reflecting resonance and the faithful
  fixed-cycle right factor is leafless.
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
  descent under these separation hypotheses. Conversely,
  `incidenceSumQuotientCongruentRightFaithful` proves that quotient descent
  forces the right factor to be bisimulation-faithful, and
  `incidenceSumQuotientCongruentLeftUnitSeparated` forces the left unit's
  observational class to be a singleton, while
  `incidenceSumQuotientCongruentCrossSeparated` rules out every cross-tag
  bisimulation. `SumQuotientControlSpec` packages these representative-control
  laws together with left projection, and
  `incidenceSum_quotientResonanceCongruent_of_control` transports left-factor
  quotient congruence without requiring global left faithfulness. Conversely,
  `incidenceSum_quotientResonanceCongruent_iff_control` proves that this
  certificate is necessary whenever same-side sum bisimulation projects to the
  left factor. `incidenceSum_project_left_iff_typeReflecting` proves that this
  projection is exactly equivalent to `SumLeftTypeReflecting`, yielding the
  carrier-independent theorem
  `incidenceSum_quotientResonanceCongruent_iff_control_of_typeReflecting`.
  `incidenceSum_quotientResonanceCongruent_iff_control_graphType` then
  discharges type reflection automatically for `GraphType`. Thus the quotient
  gap is completely characterized under the precise information-preservation
  boundary imposed by the sum's constant type map (and left-factor quotient
  congruence). The faithful/leafless theorem is likewise generalized to
  arbitrary type carriers under left/right type reflection; leaflessness
  remains one sufficient mechanism for constructing the control certificate.
  `SumQuotient.lean` gives this certificate an intrinsic quotient meaning.
  `sumQuotientControl_iff_classifier_invariant` identifies it exactly with
  bisimulation invariance of the canonical classifier carrying the left
  quotient class, the left-unit bit, and the exact right representative.
  `sumQuotientControl_iff_classifier_factorsUniquely` then applies the general
  bisimulation-quotient universal property to characterize control by unique
  factorization. Consequently
  `incidenceSum_quotientResonanceCongruent_iff_classifier_factorsUniquely`
  restates sum quotient descent itself as that universal property under the
  already-proved type-reflection boundary. The Nat/fixed-cycle sum provides a
  checked non-vacuous instance.
  This set-level result is lifted to the established category of ternary
  resonance systems by `sumQuotientClassifierResonanceSystem` and
  `sumQuotientClassifierResonanceHom`. The target carries the direct-image
  (hence least classifier-preserving) resonance. The theorem
  `sumQuotientControl_iff_classifier_resonanceHom_factorsUniquely` identifies
  control exactly with unique factorization by a resonance-preserving morphism,
  and
  `incidenceSum_quotientResonanceCongruent_iff_classifier_resonanceHom_factorsUniquely`
  connects that categorical universal property back to quotient congruence.
  `natCycleSumQuotientClassifierResonanceHomFactorsUniquely` verifies the
  categorical statement on the concrete Nat/fixed-cycle sum.
  `SumQuotientImage.lean` removes unreachable classifier values and closes the
  remaining comparison gap. `sumQuotientClassifier_eq_iff_approxBisim` proves
  that control makes the classifier kernel exactly bisimilarity. The induced
  quotient-to-image resonance morphism is proved bijective and bundled as
  `sumBisimulationQuotientIsoClassifierImage`; its inverse preserves resonance,
  and `sumBisimulationQuotientIsoClassifierImage_resonance_iff` exposes exact
  preservation/reflection. The direct-image relation is separately proved
  minimal among classifier-preserving ternary relations. A concrete
  `natCycleSumBisimulationQuotientIsoClassifierImage` instantiates the full
  isomorphism.
  `SumQuotientNaturality.lean` bundles resonance- and bisimulation-preserving
  sum maps, proves their quotient/image maps preserve identities and
  composition, and establishes the comparison square on all such maps.
  `ControlledSumObject` is an actual category;
  `controlledSumQuotientFunctor` and
  `controlledSumClassifierImageFunctor` are functors into ternary resonance
  systems, related by the checked natural isomorphism
  `controlledSumQuotientClassifierImageNatIso`. Its Nat/fixed-cycle component
  is definitionally the concrete isomorphism above.
- `QuotientRelationPresentation` supplies a general generation theorem rather
  than another model-specific congruence proof. Any ternary relation declared
  on the existing bisimulation quotient and containing selected glue outputs
  pulls back to a resonance on the original carrier. Boundary, type, glue, and
  bisimulation remain definitionally unchanged, while
  `QuotientRelationPresentation.exactDescent` proves exact descent
  automatically and `quotientResonance_eq` recovers the declared quotient
  relation exactly. Applying this to the source's existential quotient
  resonance gives `bisimulationResonanceSaturation`. It contains the original
  resonance, is least among all three-coordinate bisimulation-congruent
  extensions, fixes exactly already-congruent resonance, and is idempotent.
  Thus arbitrary relational resonance now has a canonical exact-descent
  completion without asserting that the full `Incidence` structure descends to
  the quotient carrier.
- `ResonanceSaturation.lean` upgrades this completion to a reflection.
  `ResonanceExtension inc` orders all resonance relations over one fixed
  boundary/type/glue skeleton that contain its selected outputs.
  `resonanceSaturationClosure` is a standard mathlib `ClosureOperator`, with
  monotonicity, extensivity, and idempotence checked separately. Its closed
  objects are exactly the quotient-congruent extensions.
  `resonanceSaturationReflection` packages saturation and inclusion of those
  closed objects as a `GaloisInsertion`; equivalently, it is a reflector between
  the associated thin categories and supplies the corresponding idempotent
  monad. This first formulation is fiberwise over a fixed incidence skeleton.
- `GlobalResonanceSaturation.lean` removes the fixed-carrier restriction. For
  each role type, `GlobalResonanceObject` allows carriers and cell types to
  vary, while `GlobalResonanceHom` preserves unit, selected glue, boundary
  occurrences, resonance, and bisimulation. These form a category;
  `globalResonanceSaturationFunctor` acts on both objects and carrier-changing
  morphisms, has the natural unit `globalResonanceSaturationUnit`, and satisfies
  `Sat² ≅ Sat`. Quotient-congruent objects form a full-on-homs structured
  subcategory. `globalResonanceSaturationAdjunction` proves that saturation into
  this subcategory is left adjoint to inclusion, and
  `globalResonanceSaturation_factorization_unique` exposes the corresponding
  unique factorization. The non-surjective map from the one-point trivial
  incidence to the two-point trivial incidence is a checked genuinely
  carrier-changing witness. This fixed-role, forward-boundary category remains
  available as the weaker morphism class.
- `RoleChangingResonanceSaturation.lean` supplies the stronger global category.
  Its objects allow carrier, role, and cell type to vary. Morphisms map all
  three sorts, preserve unit/glue/resonance/bisimulation, and satisfy an iff for
  membership of every mapped boundary occurrence. Identity and composition,
  saturation functoriality, the natural unit, `Sat² ≅ Sat`, the congruent
  subcategory, `roleChangingSaturationAdjunction`, and unique factorization are
  all checked. A non-surjective one-point/`GraphRole` to two-point/`Unit`
  morphism witnesses simultaneous carrier and role change. Boundary exactness
  is scoped to mapped occurrences in this category.
- `BoundarySurjectiveSaturation.lean` adds the complementary global coverage
  law: every boundary occurrence at every target cell has a source
  cell/occurrence preimage. These stronger maps form a category, saturation
  preserves them, and the natural unit, `Sat² ≅ Sat`, congruent subcategory,
  adjunction, and unique factorization all lift unchanged. The one-point/
  `GraphRole` to two-point/`Unit` example remains carrier-nonsurjective while
  satisfying global boundary coverage because the target boundaries are empty.
  Thus boundary data—not necessarily empty-boundary carrier points—are
  essentially surjective.
- `CarrierSurjectiveSaturation.lean` adds carrier surjectivity to the global
  boundary-coverage law. The resulting strongest morphism class is again
  closed under identity and composition, and saturation retains its functor,
  natural unit, `Sat² ≅ Sat`, congruent subcategory, adjunction, and unique
  factorization. A two-point/`GraphRole` to one-point/`Unit` morphism is checked
  surjective and noninjective, so this category is not merely a groupoid of
  relabelings. Weaker morphism categories remain useful and are retained.
- `SaturationLogic.lean` connects the reflector to the internal resonance
  language and the existing `IncProof` translation. The positive fragment
  generated by truth, falsity, atoms, conjunction, and disjunction is preserved
  unconditionally from a source into its saturation. Full semantic
  preservation and reflection, including implication, is equivalent to source
  quotient congruence and also to bisimulation invariance of every source
  formula. Every formula is invariant in the saturated model. The ordinary
  simplex supplies a strict atom-level witness: `v1/face/face` becomes true
  only after saturation. Under explicit agreement of encoded resonance truth,
  both positive preservation and the full conservativity criterion transfer to
  `ReferenceFoundation.IncProof.Formula.RealizeWith`.
- `DependentSaturation.lean` connects saturation to the normalized dependent
  Pi/Sigma/Id completion. An `IncDepRawNormalizedResonanceCompletion` already
  carries associativity and quotient congruence; the latter makes its resonance
  a saturation fixed point. The completion therefore transfers with the same
  `IncDepRawNormalizedBasicPreservation`, and formation/typing renaming and
  substitution results are definitionally unchanged. Pairing it with the
  public `IncDepCompletionModel` yields `IncDepSaturationCompletion`:
  `interpretTyping` is exactly unchanged and the semantic substitution-
  coherence theorem remains checked after saturation. The Nat normalized
  completion instantiates pointwise resonance fixedness. This is a
  conservativity/transport theorem for existing completions, not a claim that
  saturation creates associativity for arbitrary resonance.
- `AssociativeSaturation.lean` identifies a sufficient nontrivial extension
  beyond fixed completions. `saturationResonanceSpec` preserves symmetry,
  units, and type compatibility unconditionally. If source modes transport
  along bisimilar input representatives (`BisimulationResonanceSpec`),
  `saturationAssociativeResonanceSpec` transports relational associativity.
  `IncDepRawSaturatableResonanceCompletion` therefore needs structural
  preservation, resonance laws, associativity, and mode transport but not
  quotient congruence; saturation supplies congruence and constructs a full
  normalized dependent completion. The two-point trivial incidence is a
  strict witness: it has total bisimulation, transport, and associativity but
  is not quotient-congruent; saturation adds the `true/true/false` mode and
  remains associative. Associativity without mode transport is not claimed.
- `QuotientAssociativity.lean` removes that remaining uncertainty by stating
  the exact arbitrary-resonance criterion at the correct level.
  `QuotientResonanceAssociative` asks whether the existential relation on
  bisimulation classes is associative, without requiring it to descend
  exactly. `saturation_associative_iff_quotientResonanceAssociative` proves this
  is necessary and sufficient for saturated associativity. Mode transport is
  therefore a sufficient source-level route to the quotient condition, not a
  necessary hypothesis. `IncDepRawQuotientAssociativeCompletion` uses the exact
  quotient condition directly to generate a normalized saturated dependent
  completion.
- `AssociativityObstruction.lean` turns failure of the exact condition into a
  finite certificate problem. A directional candidate stores four carrier
  values; it obstructs when one parenthesization has a saturated two-step chain
  and the other has none. Obstruction absence is equivalent to both saturated
  associativity and `QuotientResonanceAssociative`. For finite carriers,
  `finiteSaturationAssociativityObstructions` lists every candidate and its
  emptiness is necessary and sufficient. The Bool strict-saturation example
  has an empty table. This first table is classically decidable and
  noncomputable.
- `ExecutableAssociativityObstruction.lean` closes the native-enumeration gap.
  `ExecutableSaturationPresentation` accepts exact Bool checkers for source
  bisimulation and resonance. Nested finite searches decide saturated modes,
  left/right two-step chains, and directional obstruction certificates, each
  with an `= true ↔` semantic correctness theorem. The resulting executable
  obstruction table is empty exactly when quotient resonance is associative.
  `native_decide` evaluates the Bool strict-saturation table to empty.
  Automorphism-orbit and support-minimal compression remain a separate
  optimization rather than a correctness gap.
- `TernaryInteractionRepresentation.lean` closes the first general
  representation gap. Every small ternary relational system is represented by
  freely adjoining an Incidence unit; resonance is preserved and reflected
  exactly on the original data sector. Relation-preserving maps extend to a
  faithful functor into carrier-changing Incidence objects, and the source is
  recovered from the nonunit sector up to a categorical isomorphism. This is
  not yet a representation theorem for arbitrary categories or dependent type
  theories, and the constructed boundary/type structure is deliberately
  trivial.
- `CategoryInteractionRepresentation.lean` specializes the general theorem to
  every small category. Endpoint-tagged arrows carry a ternary relation that
  holds exactly for categorical composition; the relation is single-valued
  and its two existential parenthesizations are equivalent. Every functor
  induces a relation-preserving map with checked identity and composition
  laws, and the resulting Incidence representation recovers the composition
  system from its nonunit sector. Reconstruction as an internal category,
  fullness on functors, and higher-category representation remain outside this
  theorem.
- `InternalCategoryRecovery.lean` strengthens composition representation to
  recovery of the typed categorical data. Objects are equivalent to the image
  of the identity-arrow embedding; for every object pair, the original hom
  type is equivalent to the source/target fiber of represented arrows. Under
  these equivalences, Incidence resonance agrees exactly with categorical
  composition. The certificate uses the known identity embedding and endpoint
  projections; intrinsic identities and scoped fullness are supplied by the
  following layers. Univalence and higher coherence remain open.
- `IntrinsicCategoryRecovery.lean` removes the externally specified identity
  image from object recovery. An arrow is intrinsically unital when its
  endpoints agree and it satisfies universal left/right unit laws for the
  ternary composition relation. This predicate is proved equivalent to being
  the identity arrow on its source, so the object type is equivalent to the
  intrinsic identity subtype. Endpoint projections remain explicit; scoped
  fullness is supplied by the following layer. Univalence and higher
  coherence remain open.
- `CategoryInteractionFullness.lean` closes the precisely scoped functor
  fullness gap. A functorial category-composition homomorphism is described by
  object and hom actions satisfying identity and composition laws; it is not
  defined by postulating an inducing functor. Every such homomorphism recovers
  a unique functor, the category-composition map is faithful, and an arbitrary
  resonance homomorphism lies in its image exactly when it admits this
  structure. Unrestricted relation-hom fullness is intentionally not claimed:
  a bare ternary homomorphism need not preserve endpoints or identities.
  Endpoint elimination is supplied by the following pure relational recovery
  layer. Univalence and higher coherence remain open.
- `PureRelationalCategoryRecovery.lean` removes endpoint projections from the
  recovery specification. A pure identity is defined only by the condition
  that every defined left or right composite is unchanged, and this is proved
  equivalent to being a categorical identity. Each arrow's source and target
  identities are characterized uniquely by left/right resonance. Consequently
  objects, hom fibers, and composition are recovered using predicates that
  mention only the ternary relation and carrier equality. The following
  recognition layer characterizes a sufficient and category-necessary axiom
  interface; univalence and higher coherence remain open.
- `RelationalCategoryRecognition.lean` supplies the reverse construction.
  Functional ternary systems with self-composing pure identities, unique
  source/target identities, both directions of composability, endpoint
  stability, and relational
  associativity canonically form a Lean category. Every small-category
  composition system satisfies the interface. Every source carrier element is
  covered by a typed reconstructed hom, and resonance on typed homs is exactly
  reconstructed composition. Axiom independence/minimality, a bundled
  equivalence with reconstruction is supplied at the ternary-system level by
  the following layer. Axiom independence/minimality, univalence, and higher
  coherence remain open.
- `RelationalCategoryRoundTrip.lean` closes the system-level reconstruction
  gap. Unique endpoint identities encode every original carrier element as an
  endpoint-tagged arrow of the reconstructed category; decoding takes the
  underlying typed hom. The maps are mutually inverse, resonance is preserved
  and reflected exactly, and they form an isomorphism of ternary resonance
  systems. The added `resonance_composable` axiom is essential to exclude extra
  modes on endpoint-incompatible pairs. Morphism-level functoriality is supplied
  by the following layer; a bundled equivalence of categories, axiom
  minimality, univalence, and higher coherence remain open.
- `RelationalCategoryFunctoriality.lean` adds the morphism layer. Recognized
  ternary systems and maps preserving resonance and pure identities form a
  category. Such maps preserve source/target identities and induce functors
  between reconstructed categories, strictly respecting identities and
  composition. Encoding and decoding commute with every recognized morphism,
  so the system round trip is natural on homs. The following layer packages
  these maps into a single `Cat`-valued functor. A bundled categorical
  equivalence, axiom minimality, univalence, and higher coherence remain open.
- `CategoryReconstructionFunctor.lean` packages the object and morphism actions
  into one universe-explicit functor from recognized ternary systems to
  mathlib's `Cat`. Its object action is exactly the pure-identity reconstructed
  category and its map action is exactly the previously proved reconstructed
  functor; encoding naturality is retained in the capstone. The inverse
  direction is supplied by the following layer; natural isomorphisms of
  endofunctors and categorical equivalence remain open.
- `CategoryRecognitionFunctor.lean` packages the reverse direction. Every
  mathlib `Cat` object is sent to its category-composition system with checked
  recognition axioms, and every functor maps endpoint-tagged arrows while
  preserving resonance and pure identities. Identity and composition laws are
  exact, yielding a functor from `Cat` to recognized ternary systems. Both
  directional functors now exist. The following layer supplies the recognized
  side composite natural isomorphism; the Cat-side composite and resulting
  categorical equivalence remain open.
- `RecognizedRoundTripNaturalIso.lean` upgrades the system round trip to the
  categorical morphism level. Encoding and decoding preserve pure identities,
  hence form recognized-system isomorphisms, and their previously checked
  naturality assembles into
  `𝟭 ≅ relationalCategoryReconstructionFunctor ⋙ categoryRecognitionFunctor`.
  The following layers supply the Cat-side equivalence objectwise and exact
  functor naturality; a strict Cat-valued natural isomorphism remains open.
- `CatRoundTripEquivalence.lean` constructs the canonical functor from every
  small category to its pure-identity reconstructed category. It is proved
  faithful, full, and essentially surjective, and mathlib therefore produces a
  category equivalence for every `Cat` object. This closes the category-level
  round trip objectwise. The following layer supplies exact functor naturality;
  a strict Cat-valued natural isomorphism and single global 1-categorical
  equivalence remain open.
- `CatRoundTripNaturality.lean` proves that the canonical equivalence functors
  commute with every original functor. The two paths are equal as functors and
  the equality is exposed separately on objects and dependent homs. Thus the
  Cat-side equivalences are natural in the bicategorical sense relevant to
  equivalences of categories. A natural isomorphism in the ordinary
  1-category `Cat` would require strict category isomorphisms as components;
  that stronger packaging is not claimed.
- `RelationalCategoryComparison.lean` bundles the exact comparison level into
  one checked structure: both directional functors, the recognized-side natural
  isomorphism, every Cat-side category equivalence, the chosen canonical
  equivalence functors, and their naturality squares. This capstone prevents an
  objectwise equivalence from being overstated as a strict isomorphism in
  ordinary `Cat`. Native bicategorical pseudonatural-equivalence packaging,
  axiom minimality, univalence, and higher coherence remain open.
- `UnitReflectingResonanceSpec` now names the missing associativity-side law:
  a resonance producing the unit must have a unit input. Peano addition
  satisfies it; the multi-valued finite model provably does not. This exactly
  classifies the models used by the positive direction and the checked sum
  associativity counterexample. The new general necessity theorem
  `incidenceSumAssociativeLeftUnitReflecting` proves that associativity of any
  nonempty sum forces the left factor to be unit-reflecting. A generic
  sufficient-condition proof only needs to rule out producing the unit from a
  unit and a non-unit input. `UnitOutputExactResonanceSpec` isolates this weaker
  local law; full `ExactUnitResonanceSpec` and functional resonance both imply
  it. `extraUnitModeIncidence` proves the weakening is strict: it has an
  additional non-selected `unit × unit` mode, satisfies the new law and
  unit-reflection, but admits no `ExactUnitResonanceSpec`. Its sum with Nat is
  associatively resonant. `associativeResonanceSumSpec` completes the tagged
  intermediate-mode case analysis and proves the conditional closure theorem;
  `natSumAssociativeResonanceSpec` is a concrete checked instance. Associativity
  also reflects to both factors. It independently forces both unit-reflection
  and exact unit-output on the left. `incidenceSum_associative_iff` combines all
  four necessary conditions with closure into a complete characterization
  under only the ordinary left `ResonanceSpec`; the right incidence's
  designated unit supplies the required witness internally.
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

Coherent context readiness and canonical context semantics are now aligned in
one dependent telescope. Its raw erasure is exactly the pre-existing canonical
semantic result/tree package, eliminating proof-object drift at this boundary.
The remaining global-coverage premise is uniform formation and typing semantic
synthesis for each arbitrary source-side head term.

The source-head gate is now factored more sharply: canonical preservation
already synthesizes every required formation-substitution fiber from the
coherent tail realization. Only the semantic term interpreting the arbitrary
well-typed source head remains assumed. This typing-only coverage constructs
the exact general pairing package and one coherent recursive extension.

Semantic substitutions now also have a two-sided coherent form retaining both
the source and target semantic trees. This corrects the prior asymmetry that
prevented structural interpretation of arbitrary source-side terms. Identity,
empty-target realization, proof-witness transport, and head extension all
preserve the exact source telescope. The remaining typing discharge is now
localized to coherent readiness plus semantic-type alignment.

That final local discharge is now factored and proved relatively: canonical
typing dispatch interprets a coherently ready source head along identity on the
retained source tree, and a fiber equivalence transports the term into the
formation fiber generated along the semantic tail. Coverage of these precise
readiness/alignment witnesses implies the previous typing-only semantic gate.
What remains is their uniform construction for every raw substitution head.

The local head mechanism is now also closed globally: recursion over any
coherent target telescope builds a two-sided coherent realization for every raw
substitution and preserves the supplied source semantic result/tree exactly.
This global theorem currently returns an existential target semantic result.
Identifying it with the canonical completion-model target synthesis is the
remaining target-anchoring equality gate.

The target-anchoring law is now stated at its exact dispatcher boundary:
canonical formation target semantics must be independent of source context,
substitution, source interpretation, and replacement witnesses when the target
tree is fixed. Base and unit satisfy this definitionally, and the general law
gives the required identity-dispatch equality for every arbitrary head. Pi,
Sigma, and Identity remain a mutual formation/typing invariance induction.

The mutual induction is now prepared with checked local motives. Typing output
uses a dependent Sigma package containing both its target semantic type and
term, so outputs from different source-side runs admit ordinary equality.
Global formation invariance is equivalent to universal local invariance, and
the base/unit motive cases are closed. The remaining work is precisely the
Pi/Sigma/Identity and typing constructor handlers of the mutual recursor.

The typing-unit constructor is now closed as well. The variable case exposed a
genuine model-interface gap: `IncDepRawVariableSubstitutionProvider` currently
permits arbitrary target-variable choices and carries no source-independence
law. The exact missing law is now formalized, and it suffices to close the
variable typing motive from formation invariance. It is not claimed derivable
from the weaker provider interface.

Strict Pi and Sigma formation constructors now have checked target-projection
equations: each target result is definitionally the semantic Pi or Sigma of the
recursive domain and codomain target results. The remaining closure proof is
therefore narrowed to transporting the codomain run across domain equality and
reconciling lifted replacements on the extended target tree.

Domain and codomain target results are now bundled in one dependent Sigma
package, with the codomain indexed by the domain's exact extended semantic
context. Pi and Sigma semantic formations are ordinary functions of this
package, and strict dispatch agrees with those functions definitionally. The
remaining dependent transport is exactly package equality, after which outer
constructor equality follows by `congrArg`.

Pi and Sigma formation target invariance is now closed recursively. Domain
equality is transported through a canonical dependent target-package function,
and codomain invariance anchors both lifted executions to identity dispatch.
The remaining mutual-induction cases are Identity formation and the nontrivial
typing constructors; variable typing keeps its explicit provider-naturality
hypothesis.

Identity formation now has an exact dependent target package containing its
carrier interpretation and both endpoints. The strict dispatch equation and
package congruence are checked. This exposes a second provider boundary:
pre-normalization typing invariance cannot control endpoint transports chosen
by an arbitrary rebase provider. The required normalized endpoint
source-independence law is explicit, and it conditionally closes the Identity
formation case without claiming it follows from weaker hypotheses.

The rebase boundary is now sharpened structurally. The unrestricted global
provider is already formally uninhabited at universe zero, whereas a provider
scoped to results with provenance from one shared canonical formation is
constructed unconditionally in every universe. A canonical typing-normalization
operation now uses this realizable provider and returns its requested formation
result definitionally. The development already contains a provider-free
canonical mutual dispatcher carrying provenance recursively. The remaining gap
is therefore narrower and more precise: migrate the target-invariance layer
from the obsolete unrestricted preservation interface to that scoped
dispatcher.

Target invariance is now dispatcher-parametric. The formation and typing
objectives no longer mention the obsolete unrestricted rebase hypothesis, and
the old formation statement is proved to be exactly a specialization of the
new interface. Both objectives are instantiated on the existing scoped
canonical strict preservation dispatcher. This removes vacuity from the stated
migration target; the next proof obligation is constructor-by-constructor
closure for that scoped dispatcher.

The scoped canonical formation proof now closes base, unit, Pi, and Sigma.
Base/unit are definitional; Pi/Sigma satisfy explicit recursive target-package
laws definitionally, and a dispatcher-parametric transport proof closes them
from their induction hypotheses. This is the first non-obsolete target-
invariance constructor chain, because it runs on the provider-free scoped
dispatcher rather than the uninhabited global-rebase interface. Identity
formation and typing constructors remain.

The scoped typing induction now has a local motive and a checked global/local
equivalence. Unit typing is target-invariant definitionally. Variable typing is
closed under an explicit scoped source-independence law, preserving the honest
boundary caused by the deliberately arbitrary variable provider. This supplies
the endpoint induction hypotheses needed for the next Identity-formation proof;
the compound typing constructors remain open.

The scoped Identity endpoint mismatch is now resolved at the carrier-fiber
level. Canonical fold agreement proves equality between a typing dispatch's
formation result and the independently computed carrier formation result.
Endpoint terms transport along this equality, and the transported term remains
heterogeneously equal to the original. The remaining Identity obligation is
not endpoint typing itself but coherence between the independently evaluated
typing recursors, their readiness transports, and the outer mutual formation
recursor. That equation is now formalized exactly as
`IncDepScopedIdentityRecursivePathCoherence`; it is not yet derived from the
current generated-agreement provider.

The independently evaluated Identity target package is now invariant whenever
its carrier formation and both endpoint typings are invariant. The proof joins
the two endpoint `HEq`s into equality of the dependent Sigma package. Combined
with `IncDepScopedIdentityRecursivePathCoherence`, this closes scoped Identity
formation target invariance. Thus the remaining Identity gap is reduced from a
constructor proof to derivation of one explicit mutual-recursion path law from
a strengthened generated-agreement provider.

All scoped formation constructors are now assembled into one global theorem.
Using the mutual readiness recursor, base, unit, Pi, Sigma, and Identity imply
global formation target invariance from exactly two premises: global scoped
typing target invariance and Identity recursive path coherence. This separates
the remaining work cleanly: the formation induction itself is complete; typing
constructor closure and derivation of the path law remain.

The formation component of typing target invariance is now discharged
uniformly. Canonical formation/typing fold agreement identifies each scoped
typing dispatch's formation result with the independent formation dispatch;
formation target invariance then transports that equality between arbitrary
and identity replacements. Consequently lambda, application, pairing,
projection, and reflexivity no longer carry separate formation obligations:
only their target-term `HEq` components remain.

The public scoped typing target term is now proved definitionally equal (as a
heterogeneous equality) to its recursively generated anchored normal form for
every typing derivation. This removes dispatcher opacity from all remaining
constructor cases. In the Lambda case, expansion exposes one precise residual
law: the aligned body term selected inside mutual recursion must agree with the
body term transported to the independently dispatched formation. That law is
recorded as `IncDepScopedLambdaRecursiveTermCoherence`; it is not inferred from
formation-only generated agreement.

The Lambda constructor is now closed conditionally at both levels. A dependent
target package binds its domain formation, codomain formation over the exact
extension, and transported body term. Domain formation invariance and full body
typing invariance make these packages equal; Lambda abstraction preserves that
equality heterogeneously. Combined with the inherited Pi formation result, this
proves full scoped Lambda typing target invariance from the single explicit
`IncDepScopedLambdaRecursiveTermCoherence` premise. The remaining work for
Lambda is derivation of that premise from a term-sensitive generated-agreement
provider, rather than further constructor algebra.

The Refl constructor now has the analogous dependent package theorem. Its
carrier semantic formation and transported endpoint term are jointly invariant;
reflexivity maps package equality to heterogeneous equality of proof terms. The
term-only Refl case initially exposes one recursive term law. That law is now
derived from Identity path coherence: once the target formations are aligned,
the semantic terms inhabit Identity-witness fibers and agree pointwise by proof
irrelevance. The full Refl typing case therefore needs no independent Refl
coherence premise; only the already isolated Identity path law remains.

Application now has its exact dependent target package. A new generic cast
transports typing targets directly to any equal semantic formation, rather than
requiring a strict dispatch wrapper. The Apply package records the domain,
codomain, aligned function and argument, independent result formation, and the
instantiation equality connecting them; equality of packages preserves the
transported application term up to `HEq`. The scoped recursive instantiate-
agreement provider now proves the exact instantiation equality, and a general
formation-cast term-preservation theorem transports it through the public
scoped dispatcher boundary. The remaining Apply step is package invariance and
final target-term closure. The public dispatcher now also assembles the full
external Apply package unconditionally from that proved equality, so no
additional existence premise remains at the package-construction boundary.

Run `./verify.sh` from the repository root. The verifier performs a full Lean
build, executes examples, and scans for unproved declarations. The latest
completion audit passes all build jobs with no unproved declarations.
