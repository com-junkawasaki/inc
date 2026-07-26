# Exact resonance descent along incidence bisimulation quotients

## Proposed abstract

We study when an independently supplied ternary resonance relation on an incidence structure survives
behavioral identification. We prove that exact descent to the bisimulation
quotient is equivalent to a representative-independence congruence condition,
that the descended relation is unique, and that every bisimulation-invariant
resonance homomorphism factors uniquely through the quotient. All results are
machine checked in Lean. A coproduct of natural-number incidence structures
gives an explicit obstruction, while a seven-element simplex model gives a
non-faithful quotient with three behavioral classes on which resonance does
descend. Beyond the standard congruence-quotient mechanism, we give a
coordinatewise finite obstruction classification and executable classification
of support-minimal certificates modulo structure-preserving automorphisms.

## Theorem spine

1. Define incidence structures, bisimulation, ternary resonance systems, and
   resonance homomorphisms.
2. Exact descent criterion:
   `ResonanceRelationDescendsExactly I ↔ QuotientResonanceCongruent I`.
3. Representation uniqueness: any exact descended relation equals
   `quotientResonance I`.
4. Universal property: invariant resonance homomorphisms admit a unique lift.
5. Obstruction: the natural-number coproduct admits no exact resonance
   quotient.
6. Nontrivial model: the saturated simplex has exactly three shape classes,
   is non-faithful, and admits exact resonance descent.
7. Finite obstruction classification: on a finite carrier, exact descent holds
   exactly when the finite set of six-representative obstruction certificates
   is empty. The ordinary simplex selector supplies an explicit certificate.
8. Coordinatewise classification: global ternary congruence is equivalent to
   congruence separately in the left, right, and output coordinates. This
   replaces an `n^6` finite search by three tagged `n^4` local searches.
9. Isomorphism classes of local certificates: swapping the bisimilar pair is a
   fixed-point-free involution on obstructions. Quotienting by this action gives
   two-element obstruction orbits, and exact descent is equivalent to absence
   of an obstruction orbit.
10. Structural obstruction generators: for graph-functional resonance,
    selector disagreement on bisimilar inputs and non-singleton selected-output
    classes generate local obstructions. Exact descent therefore forces
    selector invariance and singleton selected-output classes.
11. Minimal obstruction theorem: every failed finite exact descent has a
    support-cardinality-minimal local obstruction. Every obstruction has
    support size at least two, and the ordinary simplex selector realizes this
    sharp bound using only `v0` and `v1`. Resonance-bisimulation automorphisms
    preserve obstruction status, support size, and minimality. Their identity,
    inverse, and composition induce an orbit quotient, and exact descent is
    equivalent to absence of an obstructing automorphism orbit. For finite
    decidable models, all automorphisms and all support-minimal obstruction
    orbits are executable finite tables; this table is empty iff exact descent
    holds. The simplex computation has 12 automorphisms and 32 minimal-
    obstruction orbits, checked by native evaluation. The 32 orbits partition
    into five coordinate-and-shape families with counts 8, 4, 4, 12, and 4.
    Within these families, coordinate, shape, distinguished-unit position, and
    slot-equality data form an orbit-constant signature with exactly 32 normal
    forms.
12. Relational descent criterion: exact descent is equivalent to mode transport
    along bisimilar inputs together with saturation of output modes under
    bisimilarity. This connects the quotient theorem to the existing
    coalgebra-style `ResonanceRespects` condition.
13. Categorical representation: ternary resonance systems and preserving maps
    have identities and associative composition. The bisimulation quotient is
    the coequalizer of the two projections from the bisimulation kernel-pair
    resonance system.
14. Standard categorical formulation: the resonance systems form a mathlib
    category; the quotient cocone is a `Cofork`, its universal property is an
    `IsColimit`, and the induced hom equivalence is natural under
    postcomposition.
15. A non-saturated geometric model: simplex cells resonate in either input
    dimension. The seven-cell simplex collapses to the three vertex/edge/face
    classes, vertex/face interaction has exactly the corresponding two shape
    modes, and the quotient relation is represented by
    `output = left ∨ output = right` on shapes.
16. Generic class-mode representation theorem: every surjective behavioral
    classification whose kernel is bisimulation and whose selector stays in an
    input class induces an exact relational incidence quotient represented by
    `outputClass = leftClass ∨ outputClass = rightClass`. The simplex model is
    an instance rather than an isolated construction.
17. Free algebraic incidence theorem: unit-normal binary trees over generators
    form an Incidence with empty well-founded boundary and graph resonance.
    Every generator map into a total-glue Incidence extends uniquely to a
    unit-and-glue preserving morphism, and hence to a resonance homomorphism.
18. Logical necessity theorem: in the propositional language generated by a
    ternary resonance atom, truth, falsity, conjunction, disjunction, and
    implication, invariance of every formula under pointwise bisimilar
    valuations is equivalent to exact quotient descent. The converse already
    follows from the single formula `resonance(left,right,output)`.
19. Reference-foundation integration: valuations translate this observation
    language into the existing conservative `IncProof.Formula` syntax. The
    translation commutes with its `forget` retraction, preserves semantics for
    every agreeing physical interpretation, and yields the same exact-descent
    iff invariance theorem inside the translated syntax.
20. Presented free incidence theorem: arbitrary irreflexive generator-boundary
    lists and ternary resonance generators induce a genuine Incidence on the
    unit-normal tree carrier. Every target algebra interpreting those generators
    receives a unique glue-, boundary-, and resonance-preserving fold.
21. Equational presentation theorem: specified term equations generate the least
    glue congruence. Boundary descent and quotient irreflexivity construct a
    genuine quotient Incidence; resonance congruence gives exact relational
    descent; and every equation-satisfying target fold factors uniquely through
    the quotient as a morphism preserving unit, glue, boundary endpoints, and
    the full relational resonance. Exact boundary descent, quotient-boundary
    well-foundedness, and exact resonance descent each have an iff criterion,
    combined in a single quotient-admissibility certificate.
22. Congruence reflection theorem: a ternary resonance system equipped with a
    setoid congruence has an exact quotient system. Its projection is universal
    among congruence-invariant resonance homomorphisms. Resonance-congruent
    incidence bisimulation quotients instantiate this abstract reflection.
23. Functorial graded-family theorem: every behavioral cell grading satisfying
    the class-mode hypotheses has exact descent and a grade-level quotient
    representation. Grade-preserving maps induce resonance homomorphisms and
    preserve identity and composition. The simplex shape model is an instance.
24. Categorical adjunction: congruenced ternary resonance systems form a
    category. Exact quotient and equality-congruence embedding are functors,
    and the quotient functor is left adjoint to the embedding via the natural
    reflection hom-set equivalence.
25. Infinite path instance: the conventional simplicial path has exactly two
    behavioral grades, node and edge.  Its class-mode incidence has exact
    descent and the grade-level quotient representation without finite
    enumeration, providing a second graded-family member beyond the triangle.
26. Bounded graded-boundary theorem: if labelled boundaries lower dimension by
    exactly one, positive-dimensional cells have a boundary, and equal-grade
    cells have mutually matching boundary profiles, then bisimulation is
    exactly equality of bounded dimension.  Such a profile automatically
    yields the graded exact quotient.  The triangle's 0/1/2 grading is rebuilt
    through this theorem.
27. Standard simplicial-family theorem: a downward-closed decidable family of
    nonempty finite vertex sets has a genuine codimension-one incidence.  Its
    cells are bisimilar exactly when their dimensions agree, and the subtype of
    represented dimensions automatically supplies a surjective grading and an
    exact class-mode quotient.  Ordinary finite simplicial complexes are a
    direct special case.
28. Categorical incidence-hypergraph representation: every boundary occurrence
    defines an incidence point between its endpoint cell and source cell,
    producing a three-sorted diagram `IncidencePoint → Vertex` and
    `IncidencePoint → Edge`. Boundary-preserving structured morphisms induce
    commuting maps of these diagrams, and the construction preserves identity
    and composition. This is a forgetful encoding: role, sign, multiplicity,
    glue, and resonance are not recoverable from the resulting hypergraph alone.
29. Reversible reaction-network model: signed reactant/product boundaries encode
    `A → B` and `B → A`, while an independent relational resonance records
    the molecular modes exposed by interacting reaction modes. Bisimulation has
    exactly the molecule and reaction classes, resonance descends exactly to
    this quotient, and the model is both non-faithful and genuinely
    multi-valued. This is a structural Petri-net-style toy model, not a
    mass-action kinetic or rate-equation semantics.
30. Controlled-sum quotient natural isomorphism: for sums equipped with the
    exact representative-control certificate, the canonical classifier factors
    uniquely through the bisimulation quotient. Restricting to its reachable
    image gives an isomorphism of ternary resonance systems. Resonance- and
    bisimulation-preserving sum maps make the quotient and image assignments
    functors, and the comparison isomorphisms form a natural isomorphism. This
    is conditional on control and is not an unconditional coproduct theorem.
31. Canonical congruence saturation: any ternary relation declared directly on
    a behavioral quotient pulls back to the original carrier with automatic
    exact descent. Applying this to the source's existential quotient relation
    gives an extensive, least, and idempotent completion of resonance under
    three-coordinate bisimulation congruence. It preserves boundary, type, glue,
    and hence bisimulation; it does not construct an `Incidence` on the quotient
    carrier.
32. Resonance-saturation reflection: resonance extensions of a fixed incidence
    skeleton form a partial order under inclusion. Canonical saturation is a
    standard closure operator whose closed objects are exactly the
    quotient-congruent extensions. Saturation and inclusion of closed objects
    form a Galois insertion, hence a reflector between the associated thin
    categories and an idempotent monad on the ambient thin category. This
    fiberwise result is extended to carrier-changing morphisms in item 33.
33. Global saturation adjunction: for each fixed role type, incidences with
    varying carriers and cell types and maps preserving unit, glue, boundary,
    resonance, and bisimulation form a category. Saturation is an endofunctor
    with a natural unit and `Sat² ≅ Sat`. Restricting its codomain to
    quotient-congruent objects makes it left adjoint to inclusion; every map
    into a congruent target factors uniquely through the saturation unit. Role-
    changing morphisms and reflection of boundary occurrences are outside the
    present category.
34. Role-changing exact-boundary adjunction: incidences with varying carriers,
    role types, and cell types form a category whose morphisms preserve unit,
    glue, resonance, bisimulation, and preserve/reflect membership of every
    mapped boundary occurrence. Saturation again defines an idempotent functor
    left adjoint to inclusion of quotient-congruent objects, with unique
    factorization. A non-surjective one-point-to-two-point example also changes
    `GraphRole` to `Unit`. Exactness is asserted for mapped occurrences, not
    essential surjectivity onto every target boundary occurrence.
35. Globally boundary-surjective adjunction: strengthen the role-changing exact
    maps by requiring every target boundary occurrence, at every target cell,
    to have a source cell/occurrence preimage. These maps again form a category,
    saturation preserves them, and the congruent-object inclusion has
    saturation as its left adjoint with unique factorization. The concrete
    role-changing one-point-to-two-point map is still carrier-nonsurjective but
    covers all target boundary data. Empty-boundary target cells need not be in
    the carrier image.
36. Carrier-and-boundary-surjective adjunction: additionally require the
    carrier map itself to be surjective. Identity and composition preserve this
    strongest morphism class, saturation remains an idempotent functor and left
    adjoint to inclusion of congruent objects, and unique factorization holds.
    A two-point/`GraphRole` to one-point/`Unit` example is surjective but
    noninjective, so the category is not restricted to isomorphisms.
37. Saturation internal-logic conservativity: the implication-free positive
    resonance language is preserved from every incidence into its saturation.
    Preservation and reflection for the full language, including implication,
    hold exactly when the source resonance is already quotient-congruent; this
    is also equivalent to bisimulation invariance of every source formula.
    Every formula is invariant after saturation. The ordinary simplex gives a
    strict atom-level change, and the same preservation/conservativity results
    transfer through the existing `IncProof` translation under explicit
    semantic-agreement assumptions.
38. Dependent-calculus saturation conservativity: every existing
    `IncDepRawNormalizedResonanceCompletion` transfers to saturation. Its
    quotient-congruence field makes resonance pointwise fixed, while formation
    and typing renaming/substitution results remain definitionally unchanged.
    Pairing this completion with the public dependent semantic interpreter
    leaves every interpreted completed typing and its substitution-coherence
    proof unchanged. The Nat completion is a concrete witness. This transfers
    existing associativity and congruence; it does not synthesize them for an
    arbitrary resonance.
39. Associative saturation completion: saturation preserves every
    `ResonanceSpec`, and preserves relational associativity when source modes
    transport along bisimilar inputs. Therefore structural preservation,
    resonance laws, associativity, and bisimulation transport suffice to
    generate a normalized dependent completion; saturation supplies the
    missing quotient congruence. The two-point trivial incidence is a strict
    noncongruent example: saturation adds the `true/true/false` mode while
    retaining associativity. No associativity theorem is claimed without the
    transport hypothesis.
40. Exact quotient-associativity criterion: define associativity directly for
    the existential `quotientResonance`, without assuming exact descent. The
    saturated carrier is associative if and only if this quotient relation is
    associative. Source associativity plus bisimulation mode transport implies
    the quotient condition, but is only a sufficient criterion. Structural
    preservation, source resonance laws, and quotient associativity directly
    generate a normalized saturated dependent completion.
41. Saturation-associativity obstruction classification: a directional
    four-value certificate consists of a two-step saturated resonance chain
    for one parenthesization and nonexistence of a chain for the other.
    Absence of such certificates is equivalent both to saturated associativity
    and quotient-resonance associativity. On finite carriers all candidates form
    a finite table, whose emptiness is the exact decision criterion. The Bool
    strict-saturation example has an empty table. The current table uses
    classical decidability rather than a native executable enumerator.
42. Executable associativity-obstruction decision: exact Boolean checkers for
    source bisimulation and resonance induce verified finite checkers for
    saturated modes, left/right two-step chains, and directional obstruction
    candidates. Filtering all candidates yields an executable table whose
    emptiness is equivalent to quotient associativity. The Bool strict-
    saturation table is evaluated empty with `native_decide`. Automorphism-
    orbit and support-minimal compression are not included in this step.
43. Ternary interaction representation: freely adjoining a unit represents
    every small ternary relational system as an Incidence object. The original
    relation is preserved and reflected exactly on the data sector, morphisms
    extend to a faithful functor, and restriction to the nonunit sector
    recovers the source system up to isomorphism. This does not yet represent
    arbitrary categories or dependent type theories, and the representation's
    boundary and cell-type structure is intentionally trivial.
44. Small-category composition representation: endpoint-tagged arrows of any
    small category form a ternary system in which resonance holds exactly for
    categorical composition. The relation is functional and relationally
    associative, every functor preserves it, and the general ternary
    representation embeds it into Incidence and recovers it up to isomorphism.
    This represents the composition theory, not yet a reconstructed internal
    category or a higher category.
45. Internal category recovery: objects are recovered as the identity-arrow
    image, and each original hom type is equivalent to the represented
    source/target endpoint fiber. Under these equivalences, Incidence resonance
    agrees exactly with categorical composition. The result uses the known
    identity embedding and endpoint projections. Items 46 and 47 separately
    provide intrinsic identities and scoped fullness; univalence and higher
    coherence remain outside this theorem.
46. Intrinsic identity and object recovery: endpoint equality together with
    universal left/right unit laws for the ternary composition relation
    characterizes identity arrows exactly. Consequently the original object
    type is equivalent to the subtype of intrinsically identified arrows. The
    predicate still uses endpoint projections. Item 47 supplies scoped
    fullness; univalence and higher coherence are not part of this theorem.
47. Scoped fullness and exact functor image: a functorial category-composition
    homomorphism consists of explicit object and hom actions satisfying the
    identity and composition laws, together with its induced resonance map.
    Every such homomorphism is induced by a unique functor, and an arbitrary
    ternary-resonance homomorphism lies in the functor image exactly when it
    admits this structure. This is an exact essential-image theorem, not
    unrestricted fullness for relation maps that may discard endpoints or
    identities.
48. Pure relational category recovery: an arrow is an identity exactly when
    every defined left or right composite with it is unchanged, a condition
    mentioning only the ternary composition relation. Source and target
    identities are then the unique pure identities composing with an arrow on
    the left and right. Objects, hom fibers, and composition are recovered
    from these predicates. This removes endpoint projections from the recovery
    specification, but does not recognize which arbitrary ternary systems arise
    from categories or establish univalence or higher coherence.
49. Relational category recognition: functionality, self-composing pure
    identities, unique relational source and target identities, both directions
    of composability, endpoint stability, and relational associativity form a sufficient axiom
    interface for an abstract ternary system to construct a category. Every
    small-category composition system satisfies these axioms. In the
    reconstructed category every source carrier element occurs as a typed hom,
    and resonance on typed homs agrees exactly with categorical composition.
    The theorem does not yet prove minimality of the axioms, univalence, or
    higher-category coherence.
50. Relational category system round trip: unique relational endpoints encode
    every source carrier element as an endpoint-tagged arrow of the reconstructed
    category, and taking the underlying hom decodes it. These maps are inverse,
    preserve and reflect resonance exactly, and form an isomorphism between the
    original ternary system and the reconstructed category's composition
    system. The construction uses classical choice and is not yet an
    equivalence between categories of all recognized systems and categories.
51. Functorial relational category reconstruction: recognized systems and maps
    preserving resonance and pure identities form a category. Every such map
    preserves relational endpoints and induces a functor between reconstructed
    categories; identity and composition are preserved exactly. The round-trip
    encoding and decoding commute with these maps. This establishes
    morphism-level naturality. Item 52 supplies the single universe-explicit
    functor into `Cat`; a bundled categorical equivalence remains outside this
    theorem.
52. Cat-valued reconstruction functor: the object-wise reconstructed categories
    and morphism-wise reconstructed functors assemble into one functor from the
    category of recognized ternary systems to mathlib's category `Cat`. Its
    object and morphism actions are exact and retain the round-trip encoding
    naturality. Item 53 supplies the inverse-direction functor; natural
    isomorphisms of the composites and a categorical equivalence are not part
    of this theorem.
53. Category recognition inverse-direction functor: every small category is
    sent to its recognized ternary composition system, and every functor is
    sent to the induced map on endpoint-tagged arrows. Pure identities,
    resonance, identity maps, and composition are preserved, producing one
    functor from `Cat` to recognized ternary systems. The two functors are now
    both present. Item 54 bundles the recognized-side composite natural
    isomorphism; the Cat-side composite remains separate.
54. Recognized-system round-trip natural isomorphism: encoding and decoding
    preserve pure identities as well as resonance, so each system round-trip
    isomorphism is an isomorphism in the category of recognized systems. The
    previously proved morphism naturality assembles these components into
    `𝟭 ≅ reconstruction ⋙ recognition`. The Cat-side natural isomorphism and
    final categorical equivalence are not part of this theorem.
55. Category round-trip equivalence: the canonical functor sends an original
    object to its pure identity arrow and an original morphism to its relational
    endpoint fiber. It is faithful, full, and essentially surjective; therefore
    every small category is equivalent to the category reconstructed from its
    ternary composition system. This is an objectwise category equivalence, not
    yet a Cat-valued natural isomorphism or a global equivalence of model
    categories. Item 56 supplies exact functor naturality.
56. Category round-trip functor naturality: for every original functor, applying
    the canonical category round-trip embedding before or after its induced
    reconstructed functor gives equal functors. The equality is checked on both
    objects and dependent homs. This provides naturality of the objectwise
    category equivalences while retaining the distinction between equivalence
    of categories and strict isomorphism in the 1-category `Cat`.
57. Relational-category comparison capstone: both directional functors, the
    recognized-system natural isomorphism, the Cat-side objectwise category
    equivalences, and their exact naturality squares are bundled into one typed
    comparison package. The package intentionally stops short of calling this a
    1-categorical equivalence: isomorphisms in ordinary `Cat` are stricter than
    equivalences of categories. A native bicategorical pseudonatural-equivalence
    package is the remaining categorical packaging step.
58. Dependent judgment interaction representation: for every fixed raw
    dependent context, tagged raw types and terms form a ternary interaction
    system whose diagonal type modes are exactly formation derivations and
    whose term/type modes are exactly typing derivations. Derivation-preserving
    context renamings induce resonance homomorphisms and preserve identity and
    composition exactly. The free-unit Incidence representation preserves both
    judgments and recovers the original interaction system after removing the
    adjoined unit. This represents the existing raw Pi/Sigma/Identity calculus;
    it does not establish an internal-language completeness theorem for every
    `ResonanceSpec`.
59. General resonance-law internal language: a carrier-independent axiom
    schema expresses symmetry, both unit laws, and exclusion of every
    type-incompatible resonance atom. Its models are exactly the symmetric,
    unital, type-compatible valuations, and the physical valuation satisfies
    all schema instances exactly when the Incidence admits a `ResonanceSpec`.
    Derivability is finitary—each proof uses a finite list of schema
    instances—and is sound in every law model. This removes the finite-carrier
    restriction from axiomatization and soundness; strong Kripke completeness
    for the potentially infinite schema remains a separate theorem.
60. General resonance-law Kripke semantics: a lawful Kripke model is one whose
    valuation is symmetric, unital, and type-compatible at every world. Every
    schema axiom is forced at every such world—including all future worlds
    quantified by implication and negation—and every finitary schema proof is
    Kripke-sound. Strong completeness is reduced exactly to a canonical-model
    obligation: each nonderivable formula must have a lawful Kripke model and a
    world where it is not forced. This equivalence exposes, but does not yet
    discharge, the infinite-schema countermodel construction.
61. Countable infinite-schema strong completeness: schema-relative proofs have
    finite support and form a deductively closed theory. A relative avoidance
    chain extends this theory to a prime theory containing every law axiom while
    excluding any nonderivable formula. Restricting the canonical model to the
    upper cone of that prime theory preserves the truth lemma and makes every
    world a resonance-law model, yielding the required countermodel. Therefore
    lawful Kripke validity is equivalent to derivability for every finite or
    infinite resonance-atom language equipped with `CountableAtomCoding`.
    Enumeration-free completeness for uncountable atom languages is not proved.
62. Enumeration-free resonance-law completeness: finitary extensions of an
    arbitrary deductively closed theory are ordered by inclusion. Unions bound
    nonempty chains because every proof context is finite, so Zorn's lemma
    supplies a maximal extension. Maximality yields deductive closure and
    disjunction primeness, giving relative prime extensions and implication-
    failure futures without any formula schedule. The resulting canonical
    truth lemma and lawful upper-cone countermodels prove strong resonance-law
    completeness for arbitrary same-universe carriers. This construction is
    classical and does not claim a choice-free or predicative result.
63. Dependent judgment proof-theoretic semantics: a model supplies predicates
    for formation and typing and is closed under every raw Pi, Sigma, Identity,
    variable, unit, lambda, application, pairing, projection, and reflexivity
    rule. Mutual induction proves every raw derivation sound in every such
    model. The syntactic model is exact and least among these models, and its
    judgments are stable under well-typed renaming and substitution. This is
    term-model completeness for inference-rule models; it does not construct an
    extensional set-valued interpretation, a CwF/comprehension semantics,
    definitional equality, normalization, or higher identity coherence.
64. Dependent contextual-category comprehension: well-formed raw contexts are objects
    and well-typed substitutions, with derivation witnesses erased but their
    existence retained, are morphisms. Substitution identity and composition
    satisfy the category laws strictly. Raw dependent types reindex
    contravariantly with exact identity and composition laws, while context
    extension supplies the display projection and generic variable. A base
    substitution and a term of the reindexed display type pair uniquely into
    the extended context, proving the comprehension universal property. A
    fully bundled CwF with well-formed type and term presheaves is not yet
    claimed.
65. Dependent type-and-term presheaves and terminal residual: well-formed raw
    types reindex contravariantly along context substitutions with strict
    identity and composition laws. The total family of typed terms has the
    same laws, and its type projection commutes exactly with reindexing. The
    remaining CwF obstruction is also machine-checked rather than merely
    documented: substitutions into an empty context still contain unconstrained
    values at every natural index, so identity and constant-unit endomorphisms
    are distinct. Thus the current empty context is not terminal. A finite-
    context extensional quotient or canonical normalization of irrelevant
    substitution components is required before a full CwF theorem.
66. Dependent scoped syntax and finite-support substitution: mutually defined
    depth predicates bound all de Bruijn variables in raw types and terms.
    Every lookup position lies below context length; mutual induction proves
    every formation and typing derivation scoped. Therefore two substitutions
    agreeing on the finitely many context variables act identically on every
    well-formed type and well-typed term. This is the exact congruence theorem
    required to quotient away irrelevant Nat-indexed components.
67. Finite-support context quotient and terminal object: substitutions are
    identified when they agree at every position in their finite target
    context. Scopedness proves composition respects this relation in both
    arguments, so quotient substitutions form a strict category. All maps into
    the empty context are equal in the quotient, making it terminal and
    discharging the obstruction isolated in spine 65. The type and term
    presheaves still need to be descended to this corrected quotient category
    before a full CwF package is claimed.
68. Finite-support type and typed-term presheaves: well-formed types and total
    typed terms reindex directly along substitution classes, not chosen
    representatives. Scoped substitution congruence proves both definitions
    well defined. Identity and contravariant composition laws hold strictly,
    and the total typed-term projection to types commutes exactly with
    reindexing. The dependent term family is represented by this natural total
    space rather than a separately named fiber bundle.
69. Finite-support comprehension universality: every quotient-context type has
    an extended context, display projection, and well-typed generic variable.
    A substitution and term of the reindexed type pair into the extension; the
    projection and generic equations hold in the quotient, and any candidate
    with those components equals the pairing. Thus terminal context, type and
    term reindexing, and comprehension universality all live in one corrected
    category. Only conventional dependent-fiber packaging remains before using
    a standard bundled-CwF interface.
70. Bundled finite syntactic category with families: the natural total
    typed-term space is replaced by explicit dependent fibers over each type.
    These fibers reindex along quotient substitutions with identity and
    composition laws stated by heterogeneous equality across propositionally
    equal fibers. The generic variable inhabits exactly the reindexed display
    type, and fiber-level pairing satisfies both equations and uniqueness. A
    single certificate now packages terminal context, Ty/Tm substitution, and
    split comprehension. This closes the syntactic CwF construction; a
    structure-preserving morphism into the existing set-valued semantics is a
    separate semantic-comparison theorem.
71. Completed-fragment CwF semantic comparison: every fully coherent completed
    typing judgment embeds into the finite syntactic CwF without changing its
    raw context, type, or term, and simultaneously receives the existing
    set-valued context/type/term interpretation. The interpretation is coherent
    with semantic identity substitution. The exact extension gate is recorded
    as existence of a fully coherent certificate for the unchanged raw
    judgment. This is deliberately not a morphism from the whole raw CwF:
    arbitrary-substitution and comprehension naturality, plus completion of
    every raw judgment, remain to be proved.
72. Completed-fragment substitution naturality: a semantic realization of a
    raw substitution records source and target context interpretations, the
    semantic substitution, and semantic replacements for every target
    variable. It induces the corresponding finite-support CwF morphism, whose
    reindexed term is exactly raw substitution. The general mutual dispatcher
    proves that interpreting the substituted term equals semantically
    substituting the original interpretation. Coverage of every raw
    substitution and comprehension naturality remain explicit gates, so this
    is not yet a whole-CwF morphism.
73. Completed-fragment comprehension naturality: every completed display type
    selects corresponding finite-syntactic and set-valued context extensions.
    For a semantically realized substitution, the same completed term produces
    pairings on both sides. Both projection equations hold; the syntactic
    generic component is raw substitution exactly, while the semantic generic
    component is the fiber-transported interpretation of that substituted
    term. Thus comprehension is preserved on the completed realized fragment.
    Global completion and semantic-substitution coverage remain the precise
    gates before these local comparisons assemble into a whole-CwF morphism.
74. Whole-CwF morphism readiness boundary: coherent telescope synthesis gives
    every completed judgment a canonical semantic realization of its identity
    substitution, including semantic lookup replacements. All checked local
    judgment, arbitrary-substitution, and comprehension laws are packaged with
    an exact totality boundary. Promotion to a whole-CwF morphism requires
    precisely two global coverage statements: every finite-CwF term admits a
    coherent completion, and every raw substitution into a completed judgment
    admits semantic realization data. Neither global statement is inferred
    from the local laws or claimed here.
75. Completed display-projection semantics: every completed display type
    extends its coherent source telescope and canonically realizes the raw
    successor-variable projection. Its semantic map is exactly the set-valued
    Sigma projection, and every replacement is the corresponding semantic
    lookup weakened along that projection. The induced finite-support morphism
    equals the syntactic CwF display projection. Thus nonidentity coverage now
    includes the fundamental comprehension projection; arbitrary substitutions
    and global judgment completion remain open.
76. Semantic-substitution composition and finite functoriality: well-typed raw
    substitutions compose by term substitution, their semantic assignment maps
    compose as functions, and their replacement interpretations compose by
    reindexing. A target-judgment-independent realization interface makes this
    closure reusable: any completed realization may be precomposed by such a
    realization into its source context. The resulting finite-support map is
    exactly categorical composition in the syntactic context category. This is
    a closure theorem, not a construction of realizations for arbitrary raw
    substitutions; arbitrary coverage and global judgment completion remain
    open.
77. Completed-term semantic pairing realization: a realized base substitution
    and completed target term determine a well-typed raw comprehension pairing.
    Its target-independent semantic realization extends the assignment map by
    the interpreted substituted term, uses that term as the newest replacement,
    and inherits all older replacements from the base realization. The induced
    finite-support morphism is exactly the syntactic CwF pairing. An arbitrary
    substitution head need not arise by reindexing a target term, so this
    generator theorem does not by itself establish global substitution
    coverage.
78. General source-side semantic pairing realization: an arbitrary well-typed
    source head may extend any target-independent realized base substitution,
    provided a coherent target formation, its substitution fiber equivalence,
    and a semantic interpretation of the source head are supplied. Transport
    across that equivalence gives the Sigma-valued semantic pairing; semantic
    projection and generic-variable equations hold, and the induced finite
    map is exactly the quotient-CwF pairing. Thus arbitrary pairing shape is no
    longer an obstruction. Global substitution coverage is reduced to uniform
    construction of the explicit formation and source-term semantic data.
79. Canonical raw-substitution pairing decomposition: every substitution into
    an extended target has a canonical tail and a newest component typed in the
    reindexed display family. Re-pairing them recovers the term function
    exactly, the proof-erased extensional substitution exactly, and the finite
    quotient morphism as the CwF comprehension pairing. Raw substitutions
    retain proof-relevant typing derivations, so equality of the proof-relevant
    structures themselves is deliberately not claimed. Together with spine 78,
    this reduces semantic substitution coverage recursively to uniform semantic
    formation and typing data for each head component.
80. Recursive semantic-substitution realization induction: realization data
    transport across changes of proof-relevant typing witnesses when the term
    function is unchanged. Every substitution into the empty target has a
    canonical realization, and a realized canonical tail plus the general
    formation/typing semantics of the actual source head realizes the original
    proof-relevant substitution. This supplies the exact recursive induction
    principle for global coverage. The uniform per-head semantic synthesis
    required to discharge every induction step remains a separate gate.
81. Intrinsic lookup-coherent semantic substitutions: strengthen a semantic
    realization by retaining its target semantic tree and, for every lookup, a
    fiber equivalence between the chosen replacement family and the target
    lookup family reindexed by the semantic assignment map. Transporting the
    replacement term across this equivalence must equal the reindexed target
    variable. Identity substitutions and completed display projections satisfy
    this interface with exact target-tree preservation. Strengthened pairing
    and composition closure, followed by uniform per-head synthesis, remain the
    next coverage tasks.
82. Lookup-coherent pairing and composition closure: target-independent basic
    realizations compose generically. Intrinsic lookup coherence is preserved
    under composition by reindexing the later fiber equivalence along the
    earlier semantic map and applying transport naturality. General source-side
    pairing is coherent at the newest lookup by its formation equivalence and
    at every older lookup by inherited base coherence. Semantic assignment maps
    remain exactly function composition and Sigma pairing. Uniform per-head
    semantic synthesis is now the sole remaining substitution-coverage gate.
83. Strengthened coherent whole-CwF readiness boundary: fix a completion model
    and anchor every substitution target to the canonical semantic context it
    synthesizes. Global coverage now requires the intrinsic lookup-coherent
    interface, not merely a map and replacement terms. Forgetting coherence
    recovers the previous completed-substitution and whole-CwF readiness gates,
    while strengthened readiness is exactly equivalent to judgment completion
    conjoined with canonical coherent substitution coverage. Neither global
    gate is proved; uniform judgment completion and per-head semantic synthesis
    remain the precise totality obligations.
84. Recursive lookup-coherent substitution induction: transport of a coherent
    realization across proof-witness changes preserves both its semantic map
    and exact target tree. Empty targets have canonical coherent realizations,
    and a coherent canonical tail plus general semantic data for the actual
    source head realizes the original proof-relevant substitution with all
    lookup equations intact. Thus the full recursive coverage mechanism now
    lands in the strengthened interface. Uniform per-head formation and typing
    semantic synthesis is its sole remaining substitution premise.

85. Readiness-aligned context semantic synthesis: a dependent semantic telescope
    is indexed by the exact coherent formation-readiness telescope that generated
    it. Canonical synthesis constructs this aligned tree, and raw erasure is
    package-exact with the existing semantic synthesis. This closes readiness/
    semantics proof-object drift; uniform source-head semantic synthesis remains
    the next global-coverage premise.

86. Exact source-head semantic coverage boundary: canonical preservation already
    synthesizes the formation-substitution fiber from a coherent tail. The sole
    local assumption is therefore a semantic term for each arbitrary well-typed
    source head. That typing-only assumption constructs the exact general pairing
    package and closes one coherent recursive extension step for the original
    proof-relevant substitution.

87. Two-sided coherent semantic substitutions: the strengthened realization
    retains semantic trees at both endpoints, rather than only the target tree.
    Identity, empty targets, proof-witness replacement, and arbitrary head
    extension preserve the exact source telescope. This supplies the structural
    input needed for source-head typing interpretation; coherent readiness and
    semantic-type alignment remain to be discharged.

88. Source-head readiness and type-alignment discharge: coherent typing
    readiness interprets the actual source head by identity dispatch on the
    retained source tree. A fiber equivalence transports that term into the
    source formation produced by the semantic tail dispatch. Global coverage
    of these readiness/alignment witnesses therefore discharges the previous
    typing-only source-head semantic assumption exactly.

89. Global two-sided substitution realization: the arbitrary-head extension is
    iterated over every coherent target telescope. Typing-only coverage, and
    therefore readiness/alignment coverage, realizes every raw substitution
    while preserving the supplied source semantic result and tree exactly. The
    resulting target interpretation is existential; equality with canonical
    target synthesis is the remaining anchoring gate.

90. Formation target-invariance boundary: the precise anchoring law removes all
    dependence of target formation semantics on source-side substitution data.
    Base and unit satisfy it definitionally, and the general law identifies each
    arbitrary source-head target formation with identity dispatch on the same
    target tree. Pi, Sigma, and Identity require the mutual formation/typing
    induction that remains open.

91. Mutual target-invariance induction motives: target semantic type and term
    outputs of typing dispatch are bundled dependently, permitting ordinary
    equality across source-side runs. Formation and typing invariance become the
    two motives of the existing mutual readiness recursor. Global formation
    invariance is exactly universal local invariance; base and unit motives are
    closed. Typing unit is also closed. Variable closure is proved from an
    explicit source-independence law, which is necessary because the existing
    variable provider interface otherwise permits arbitrary target choices.

92. Pi/Sigma constructor target equations: strict Pi and Sigma formation
    dispatch have target projections definitionally equal to the corresponding
    semantic constructors applied to their recursive domain and codomain target
    results. Thus outer target equality is reduced to recursive equality plus
    the dependent transport of extended trees and lifted replacements.

93. Dependent formation target packages: a Sigma package binds the recursive
    domain target formation to the codomain formation over its exact extended
    context. Pi and Sigma targets are ordinary functions of this package, so
    package equality yields constructor equality by congruence. Strict dispatch
    outputs agree definitionally with these packaged functions.

94. Recursive Pi/Sigma target invariance: domain target equality is mapped
    through a canonical dependent-package function, while both codomain runs
    are anchored to identity dispatch on their respective extended target
    trees. Package congruence closes the full local target-invariance motive for
    Pi and Sigma. Identity formation and the remaining typing constructors stay
    outside this theorem.

95. Identity target package and normalization boundary: a dependent package
    binds the carrier semantic interpretation and both endpoints in its exact
    fiber. Strict Identity dispatch is definitionally the Identity constructor
    applied to that package, and package equality implies outer formation
    equality. The current arbitrary rebase provider need not preserve endpoint
    choices across sources, so normalized endpoint source-independence is
    exposed as the exact additional law; under it, recursive carrier and typing
    invariance close the Identity formation case.

96. Canonical-provenance-scoped rebase: the unrestricted provider required by
    the earlier preservation interface is already proved uninhabited at
    universe zero. A scoped provider instead accepts two results together with
    provenance from one shared canonical fiber; canonical uniqueness constructs
    its rebase automatically in every universe. The corresponding typing
    normalization targets the requested formation definitionally and removes
    the impossible global assumption from this local operation. The existing
    provider-free canonical mutual dispatcher is the migration target; the
    target-invariance layer still has to be restated over that dispatcher.

97. Dispatcher-parametric target invariance: formation and typing invariance
    are defined directly for any strict mutual dispatcher, with a localized
    formation motive and global/local equivalence. The old statement is exactly
    its specialization to the obsolete preservation dispatcher. The existing
    scoped canonical strict dispatcher is now the explicit authoritative target
    of both invariance objectives, without importing the impossible global
    rebase assumption. Constructor closure for this dispatcher remains open.

98. Scoped canonical base/unit/Pi/Sigma target invariance: base and unit close
    definitionally on the provider-free scoped dispatcher. Pi and Sigma expose
    their recursively generated dependent target packages definitionally. A
    dispatcher-parametric package proof transports domain equality and compares
    both codomain runs to identity dispatch on their exact extended trees,
    closing both constructors. Identity formation and typing remain.

99. Scoped typing target-invariance base and variable boundary: the typing
    objective is localized at one coherent typing derivation and is equivalent
    to its global dispatcher-parametric form. Unit typing closes definitionally
    on the scoped canonical dispatcher. Variable typing closes under the exact
    source-independence law for the deliberately unconstrained variable
    provider. Canonical formation/typing agreement additionally proves, for
    every typing constructor at once, that formation target invariance supplies
    the formation component of typing target invariance. The remaining compound
    typing obligations are therefore target-term equations only.

100. Scoped Identity endpoint alignment: canonical formation/typing agreement
     identifies the formation fiber returned by each scoped typing dispatch
     with the independently dispatched carrier formation, including across
     distinct readiness witnesses. Each endpoint term is transported into that
     exact carrier fiber, with heterogeneous equality back to the original
     endpoint. The remaining Identity step---coherence of the two independently
     evaluated readiness transports with the outer mutual-recursion Identity
     package---is stated as an exact law rather than left informal.

101. Scoped Identity package equality and conditional closure: independently
     dispatched carrier and endpoints assemble into a dependent Identity target
     package. Carrier formation equality and the two endpoint heterogeneous
     equalities imply equality of these packages. Under the exact mutual-
     recursion path-coherence law, package congruence closes scoped Identity
     formation target invariance. Derivation of that law from strengthened
     generated agreement remains open.

102. Global scoped formation target invariance: a mutual recursor uses the
     dispatcher-parametric formation motive and a trivial auxiliary typing
     motive to combine base, unit, Pi, Sigma, and Identity. Therefore global
     scoped typing target invariance and the exact Identity recursive path law
     imply target invariance for every coherent formation derivation. Those two
     premises remain explicit.

103. Scoped typing recursive normalization and Lambda boundary: the target term
     returned by the public scoped typing dispatcher is definitionally the term
     in its recursively generated anchored output. Constructor proofs can thus
     work on the recursive normal form without an additional abstraction gap.
     For Lambda, the remaining obstruction is now the exact transport equation
     aligning the mutual-recursion body term with the independently dispatched
     formation-aligned body term; bare formation agreement does not provide
     equality of those term choices.

104. Scoped Lambda target-package invariance and conditional closure: canonical
     anchoring transfers target invariance from typing back to its indexed
     formation, and public term invariance is equivalent to invariance of the
     recursive normal form. A dependent Sigma package binds each Lambda domain,
     codomain, and formation-aligned body term. Domain formation and body typing
     invariance imply equality of these packages. Under the exact Lambda
     recursive term-coherence law, package congruence closes both the target-term
     and complete typing-invariance cases for Lambda.

105. Scoped Refl target-package invariance and conditional closure: a carrier
     formation target and its formation-aligned endpoint term form a dependent
     Sigma package. Carrier and endpoint invariance imply equality of these
     packages. Identity path coherence aligns the outer target formation with
     the package formation; all inhabitants of the resulting Identity fibers
     are pointwise equal by proof irrelevance. Hence the Refl recursive term law
     is derived rather than assumed, and the complete Refl typing constructor
     requires only the already isolated Identity path-coherence premise.

106. Scoped Apply target package and instantiation boundary: target-term
     transport is generalized from strict dispatch wrappers to arbitrary equal
     semantic formation targets. The Apply package binds a domain, dependent
     codomain, function term, argument term, independent result formation, and
     the equality identifying codomain instantiation with that result. Its
     transported application term is congruent under package equality. The
     scoped recursive provider supplies the instantiation equality, and a
     formation-cast preservation lemma transports it through the public
     dispatcher boundary, where the full external Apply package is now
     constructed unconditionally. The remaining Apply proof is package
     invariance and final target-term closure.

## Required strengthening before submission

- If targeting an applied journal, extend the completed structural reversible-
  reaction model with rates, execution semantics, or empirical domain data;
  none of those are required for the scoped mathematical arXiv paper.
- Complete subscription-database and cited-reference traversal beyond the
  primary-source chain, relational-quotient comparison, functorial boundary
  encoding, mechanized audit, and public database coverage log; obtain the
  requested specialist review of the novelty boundary.

The reproducible Lean-to-paper theorem index is now maintained in
`incidence-theorem-index.tsv` and checked against the completion claim matrix.
The former computational bridge to `(2+2+4)+4+(2+2)+(3*4)+4 = 32` is also
replaced by the explicit card-independent structural equivalence; native
enumeration remains only as an independent executable check.

## Claims that must not enter the abstract yet

- a classification of all incidence/resonance structures;
- an adjunction between a category of presentations and a category of
  Incidence algebras (the objectwise fully structured universal property is
  proved);
- a modal quotient rule internalized as an equivalence of `IncProof.Derives`
  judgments (syntax, forget-retraction, semantics, and necessity are integrated);
- novelty over all existing coalgebraic quotient theorems.
