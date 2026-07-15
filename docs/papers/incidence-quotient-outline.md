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
