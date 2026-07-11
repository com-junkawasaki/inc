# Theory of Incidence

This repository develops a Lean 4 core for incidence structures: relations
whose boundaries consist of labelled, oriented endpoints.

## Checked status

The checked Lean development is in [`incidence-theory/`](./incidence-theory).
It currently establishes:

- finite list boundaries, sign cases, and positive multiplicities;
- rank-based exclusion of direct boundary cycles;
- guarded gluing unit laws, type preservation, and conditional associativity;
- bisimilarity as an equivalence relation, with observable equality embedded
  into bisimilarity;
- computed boundary matrices and Laplacians, with general `BᵀB` symmetry and
  nonnegative diagonal entries; finite row-list append/cons decomposition is
  also proved, along with diagonal monotonicity under row extension; and
- a concrete triangle model, including checked matrix entries and a checked
  `∂² = 0` calculation.
- a finite, well-founded, nonempty-boundary Lean model (`leaf ← root`) that
  satisfies the current structure invariants, rank decrease, gluing laws, and
  finite `∂² = 0`; its role-erasure is also a concrete witness of the legacy
  layered A2/A6–A10/A16–A17 interfaces, with computed matrix and Laplacian.
  Its linear observations are proved complete for bisimilarity.
- a propositional internal-logic fragment over incidence atoms, with natural
  deduction, semantic soundness, context weakening, and truth-preserving
  translation theorems; atom maps also transport formulas, contexts, and
  derivations.  Arbitrary atom translations reflect consistency from the
  translated theory back to the source; split-injective translations preserve
  and reflect both consistency and avoidance of any designated formula
  exactly, alongside derivability and semantic consequence.  Its intuitionistic
  Kripke semantics, persistence theorem, and
  Kripke soundness theorem are checked; atom translations pull Kripke models
  back and preserve formula and context forcing exactly. Assumption substitution and cut are
  also proved syntactically.  A one-world Kripke model proves relative
  consistency of the empty internal-logic context, while a two-world model
  proves that excluded middle is not derivable (while its double-negated form
  is derived). Prime theories and the
  canonical Kripke model are defined; its truth lemma is proved from a
  recurrent formula schedule.  The one-step
  consistency-preserving choice of a formula or its negation is proved, along
  with its finite-list iteration and finite prime-disjunction property.
  Given an explicit exhaustive formula enumeration, an infinite Lindenbaum
  chain is defined; every finite stage stays consistent and every formula is
  eventually decided. Its limit is constructed as a closed, consistent prime
  theory. The chain is also available from every consistent finite context,
  which is preserved through all stages while formulas are decided; its limit
  is a prime theory containing that context.
  Relative countermodel steps for implication and disjunction are also proved.
  A recurrent disjunction-saturation chain is additionally defined for a
  forbidden conclusion; it contains its base context while its limit continues
  to avoid that conclusion, yielding a closed consistent prime-theory relative
  extension of every finite base that does not derive the forbidden formula.
  In particular, a finite-context failure of `p → q` has a prime-theory
  witness containing the context and `p`, while omitting `q`; this witness
  conservatively preserves every derivable consequence of the finite context.
  For prime theories presented by a finite derivational basis, the extension
  is proved to contain the entire source theory, giving the canonical
  implication witness on that fragment.
  Finite support over an arbitrary prime source theory is formalized, so the
  relative construction supplies a full prime extension (not just a finite
  fragment).  Consequently, the canonical truth lemma and canonical and
  same-universe Kripke completeness are checked from a recurrent formula
  schedule, without a separate extension axiom.  Every supplied exhaustive
  `FormulaEnumeration` now constructs that schedule by a checked triangular
  traversal, so these results are directly available from the project's
  existing enumeration input.
  A concrete decoder/encoder supplies such an enumeration for `Bool` atoms,
  so the full Kripke completeness equivalence is directly instantiated for a
  language with two distinguishable incidence atoms, and is transported to
  the actual `FiniteIncidence` atoms `leaf` and `root`.
  The construction is now generalized to `Fin n` for every finite atom
  language, including the zero-atom case.
  The same coding directly supplies the complete Kripke semantics for the
  countably infinite `Nat` atom language.
  More generally, every atom encoder/decoder retraction supplies the required
  formula enumeration and hence the corresponding Kripke-completeness theorem.
  These countable atom presentations are closed under disjoint sums and
  Cartesian products by explicit parity and diagonal codings.  Consequently,
  the internal languages carried by countably presented `incidenceSum` and
  `incidenceProd` constructions inherit full Kripke completeness compositionally.
  Their consistent finite contexts have Kripke models and canonical prime-theory
  worlds, and every underivable sequent has an explicit canonical counterworld.
  `CountablyPresentedIncidence` now packages an actual `Incidence` together with
  this coding, exposing completeness, model existence, and countermodels directly
  from the incidence object.  `natIncidence` is the first concrete instance of
  this bridge, with checked completeness and consistency/model equivalence.
  The generic `incidenceProd` and `incidenceSum` constructors lift to this packaged
  level, so composing presented incidence structures simultaneously composes their
  carrier, countable internal language, and checked Kripke completeness theorem.
  This is instantiated non-vacuously for both `natIncidence × natIncidence` and
  `natIncidence ⊕ natIncidence`: consistent contexts have Kripke models, and every
  underivable formula has a canonical prime-theory counterworld in each language.
  In the converse direction, every nonderivable finite sequent has a checked
  canonical prime-theory counterworld for the supplied coding.
  For every supplied formula enumeration, a finite context is
  derivationally consistent exactly when it is Kripke-satisfiable; equivalently,
  it is satisfied at a world of the canonical prime-theory model.  Thus the
  consistency result includes an explicit general model-existence theorem,
  rather than only the empty-context example.
  User-facing consistency/model-existence equivalences are instantiated for
  every `Fin n`, `Nat`, `Bool`, and the concrete `FiniteIncidence` atom
  language, both for arbitrary Kripke models and canonical worlds.
  Public instances expose this counterworld construction for `Fin n`, `Bool`,
  `Nat`, and the concrete `FiniteIncidence` atom language.
  For the concrete `root` atom, excluded middle is shown underivable and
  Kripke-invalid, while its double-negated form is derivable.
  Each formula has a finite subformula closure, and a consistent context has a
  finite extension deciding every formula in that closure; its disjunction
  subformulas satisfy a derivable prime-choice law.  The derivable closure of
  each finite extension is formalized as a deductively closed theory and is
  bundled as a finite prime theory (consistent, decisive, and prime on that
  finite language).
- an extensional two-atom finite-set fragment: membership is encoded by set
  boundaries; union, intersection, complement, and difference have proved
  Boolean-algebra laws, and boundary membership represents each operation.
  These facts are bundled as a checked `SetIncidence` Boolean-fragment model
  certificate.
- arbitrary finite-basis extensional sets (`BitSet n`), with checked Boolean
  operations (union, intersection, complement, difference), complement laws,
  distributivity, and De Morgan's law proved pointwise over `Fin n`; boundary
  membership exactly represents set membership and preserves these operations;
  equal boundaries are exactly equal finite sets.
- recursive hereditarily finite set syntax as a well-founded incidence model,
  with structural-boundary rank decrease and associative gluing; its big union
  satisfies the syntactic membership law `x ∈ ⋃s ↔ ∃ y ∈ s, x ∈ y`. Big union
  descends to the recursive quotient with the same exact membership law.
  A finite powerset presentation is also defined syntactically, with its
  insertion-step membership decomposition and subset soundness proved. Every
  syntactic subset has an extensionally equal representative in that finite
  powerset (so duplicate/order-sensitive presentations do not weaken the
  extensional claim).
  Kuratowski ordered pairs and finite Cartesian products are also constructed
  syntactically, with the exact `x ∈ s × t` ordered-pair membership law.
  Cartesian product now descends to the recursive extensional quotient too,
  with the same exact ordered-pair membership characterization.
  It is empty in either empty factor, distributes over binary union in either
  coordinate, is monotone, and reflects each factor under the necessary
  nonemptiness hypothesis.
  Under the same nonemptiness condition it also reflects the product subset
  order coordinatewise.
  Its interaction with powerset is checked at singleton representatives:
  `⟨{a},{b}⟩ ∈ P(s)×P(t)` holds exactly when `a∈s` and `b∈t`.
  In particular, singleton products normalize exactly as
  `{a}×{b} = {⟨a,b⟩}` on the quotient.
  The bundled recursive finite-set fragment model records product zero,
  monotonicity and union-distribution laws alongside `⋃P(s)=s`.
  Within the powerset image, unions have the exact least-upper-bound law;
  the development deliberately does not equate `P(s∪t)` with `P(s)∪P(t)`.
  Singleton and Kuratowski ordered-pair constructions also descend to the
  recursive extensional quotient, with their exact outer membership laws;
  unordered-pair equality is classified and ordered pairs are injective.
  The finite powerset construction now also descends to that quotient with
  the exact law `x ∈ power(s) ↔ x ⊆ s`.
  It is injective (`power(s)=power(t) → s=t`) and satisfies
  `power(∅) = {∅}` on the quotient.
  It reflects subset (`power(s) ⊆ power(t) ↔ s ⊆ t`), satisfies
  `⋃ power(s) = s`, and provides the expected upper-bound law for unions of
  powersets.
  Its internal von Neumann ordinals additionally satisfy `⋃(n+1)=n` and the
  binary union law `m ∪ n = max(m,n)`; internal inclusion is exactly natural
  number `≤`, while strict inclusion is exactly `<`, with the induced
  equality/trichotomy and union algebra laws.
  Relations are represented as sets of ordered pairs; singleton graphs are
  proved relational and functional, with an exact application iff law.
  The identity graph on every finite internal ordinal is also a checked
  total relation/function with its exact finite-domain application specification.
  A finite-domain successor graph is likewise functional and total, with
  application `m ↦ m + 1` proved internally.
  More generally, finite shift graphs implement `m ↦ m + k`; shift by zero is
  proved equal to the identity graph and shift by one to the successor graph.
  Their pointwise composition is proved to add offsets.
  A bounded two-input addition graph is now constructed as an internal HF set
  of ordered input/output pairs.  Its exact application law is
  `⟨m,n⟩ ↦ m+n` for both inputs below the bound, and the graph is proved
  functional and total on that finite square domain.
  The same construction is carried out independently for multiplication,
  with exact law `⟨m,n⟩ ↦ m*n` and checked functionality and totality on
  every bounded finite square.  Both internal application relations satisfy
  commutativity: swapping the two encoded inputs preserves and reflects
  application to every output.  Evaluation on encoded naturals is classified
  by an output-equality iff, from which the left/right additive identity,
  multiplicative zero, and multiplicative identity laws are proved internally.
  With explicit bounds covering intermediate results, both operations are
  associative and multiplication distributes over addition from both sides;
  these theorems certify every intermediate graph application as well as
  equality of the two final internal ordinals.  Addition has left and right
  cancellation; multiplication has both cancellation laws for a positive
  common factor, and an internal product evaluates to zero exactly when one
  encoded factor is zero.  Internal ordinal inclusion is preserved and
  reflected by adding a common summand and by multiplying with a positive
  common factor; addition and multiplication are monotone jointly in both
  arguments.  The corresponding preservation-and-reflection equivalences are
  also proved for strict internal inclusion (proper subset), so these common
  summand/factor maps are order embeddings for both `≤` and `<`.
  Bounded exponentiation is likewise represented by an internal graph with
  exact application law `⟨m,n⟩ ↦ m^n`, functionality, and totality. Its
  evaluation iff yields the internal laws `m^0=1`, `m^1=m`, `1^n=1`, and
  `0^n=0` for positive `n`.  Exponent addition and multiplication are linked
  to the three internal arithmetic graphs by checked computation diagrams:
  `a^(m+n)=a^m*a^n` and `a^(m*n)=(a^m)^n`, including every intermediate
  addition, multiplication, and power application.  The product law
  `(a*b)^n=a^n*b^n` is checked in the same form.  Powers are monotone in the
  base and, for positive bases, in the exponent; positive exponents and bases
  greater than one give the corresponding inclusion-reflection equivalences
  for both ordinary and strict inclusion.  Under those same hypotheses, equal
  outputs of the internal power graph cancel respectively to equal bases or
  equal exponents.
  Signed integers now have an internal HF carrier representation as a
  Kuratowski pair of a sign tag and a natural magnitude.  Positive/nonnegative
  and negative encodings are disjoint, the embedding from `Int` is injective,
  and every value satisfying the integer-code predicate has a unique integer
  representation.  A bounded internal negation graph covers both sign branches
  with exact law `z ↦ -z`; it is functional and total on its represented
  bounded domain, and the encoding satisfies double negation.  Integer
  addition and multiplication are built from a reusable finite binary-operation
  graph construction over the signed window.  Both have exact laws
  `⟨x,y⟩ ↦ x+y` and `⟨x,y⟩ ↦ x*y`, and are functional and total on
  their bounded two-dimensional domains.  Evaluation on concrete integer codes
  has an output-equality iff; both operations are commutative, addition has
  left/right zero and additive-inverse laws, and multiplication has left/right
  zero and one laws, all stated as internal graph applications.  With explicit
  window hypotheses for intermediate values, addition and multiplication are
  associative and multiplication distributes over addition from both sides;
  the proofs certify the complete internal computation diagrams.  Addition
  has left and right cancellation, multiplication cancels a common nonzero
  factor from either side, and an internal product evaluates to zero exactly
  when one of its encoded integer factors is zero.  A bounded subtraction graph
  is also defined from the same reusable binary-operation construction; it has
  an exact `⟨x,y⟩ ↦ x-y` evaluation law, is functional and total on its window,
  computes `x-x=0` and `x-0=x`, and is certified as inverse to adding the
  subtracted argument whenever the intermediate difference lies in the window.
  It also computes `0-x=-x`, has left and right cancellation, and a checked
  three-stage graph diagram identifies subtraction internally with negation
  followed by addition: `x-y = x+(-y)`.  Integer order is represented by a
  bounded characteristic graph `⟨x,y⟩ ↦ 1/0`; application evaluates to `1`
  exactly when `x≤y`.  The graph is functional and total on its window, and
  reflexivity, transitivity, and antisymmetry are proved from graph applications.
  Order is compatible with the internal arithmetic: adding a common offset
  preserves it, negation reverses it, and multiplication by an internally
  certified nonnegative factor preserves it, subject only to the explicit
  finite-window hypotheses for the resulting values.  The comparison graph is
  a linear order: every encoded pair is comparable, comparison in both
  directions is equivalent to equality of the represented integers, and adding
  a common offset both preserves and reflects comparison.  Strict order is
  reconstructed solely from graph evidence (`x≤y` succeeds while `y≤x` does
  not), with exact equivalence to `x<y`; irreflexivity, transitivity,
  asymmetry, additive preservation/reflection, and trichotomy are all checked.
  Negation reverses strict order, while multiplication by a factor certified
  internally as strictly positive preserves it, again with explicit bounds on
  both products.  As a nontrivial arithmetic application, every internally
  represented square is nonnegative, and a fully checked graph computation
  proves that `x*x + y*y = 0` forces both encoded integers `x` and `y` to be zero.
  Bounded integer divisibility is reconstructed from the multiplication graph,
  with an exact factor-existence law.  It is reflexive and transitive when the
  composed factor remains in the finite window; `1` divides every represented
  integer, while `0` divides exactly `0`.  Common divisors are closed under
  addition, remain divisors after multiplying the dividend, and survive
  negation, with precisely the factor-sum/product/negation window obligations
  exposed by the finite presentation.  Common divisors are also closed under
  subtraction and, more generally, under two-term integer linear combinations
  `a*x + b*y` whenever the combined witness factor remains represented.  A
  bounded Bézout certificate packages internal coefficients witnessing
  `a*x+b*y=1`; every common internal divisor then divides `1`.  Internally,
  dividing `1` is proved equivalent to being exactly `1` or `-1`, so every such
  common divisor is a unit rather than merely being labeled as one.  This is instantiated by a
  kernel-checked certificate `2·(-1)+3·1=1`, so every represented common divisor
  of `2` and `3` divides `1` whenever its combined witness remains in the window.
  The certificate is exposed as bounded internal coprimality; a general coprime
  pair has only `±1` as common represented divisors, and `2` and `3` are proved
  coprime with that explicit unit-divisor conclusion.  A bounded internal form
  of Euclid's lemma is also proved: if `a,b` have a Bézout coprimality witness
  and `a` divides `b*c`, then `a` divides `c`, with the resulting factor witness
  constructed explicitly inside the finite window.
  Their relational-composition presentation has exact two- and three-stage
  application laws and finite-domain totality; binary and three-stage
  composite presentations are extensionally unique and coherent.
  On every nonempty finite ordinal, this action is faithful: equality of
  shift graphs reflects equality of offsets and gives graph-level left
  cancellation for addition.
  On the image of a finite shift it has a checked inverse law: output
  `m + k` uniquely recovers the input ordinal `m`; no false total inverse is
  asserted outside that image.
  On the quotient, binary union is idempotent, `⋃{s,t}=s∪t`, and big union
  preserves empty and distributes over binary union; binary union is also the
  least upper bound for the extensional subset order.
  Respectful predicates also provide quotient-safe relative difference:
  filtering and its complement partition a set and are disjoint; this is the
  checked intersection/difference fragment available without asserting an
  unproved representative-independent binary intersection operation.
  Predicate complement, conjunction, and disjunction satisfy involution and
  De Morgan/filter laws on the quotient.
- an extensional quotient of recursive finite sets, with union proved
  well-defined on equivalence classes.
- a stable recursive extensional quotient, with pairing and respectful
  decidable separation proved well-defined on equivalence classes; both
  arguments are proved members of the constructed pair, and filtered
  membership is exactly membership plus the respectful predicate; true/false
  filters are respectively identity and empty, and filtering distributes over
  binary union; successive filters compose by predicate conjunction. A membership-tree rank proves
  foundation in the form `¬ (s ∈ s)` on the recursive quotient; recursive
  equality preserves this rank, so it descends to extensional classes.  The
  quotient membership relation itself is proved well-founded, yielding the
  set-theoretic foundation statement for every nonempty recursive set. These
  checked laws are bundled as an explicit finite set-fragment model (not a
  claim of full ZF).
- von Neumann naturals embed into the recursive quotient: their rank is their
  index, their membership is exactly `<`, the embedding is injective, every
  member of a finite ordinal is classified as an earlier ordinal, and these
  ordinals are internally transitive and linearly ordered by membership. Their successor is reconstructed as
  `n ∪ {n}` using the checked pair and union operations. This is an internal
  infinite sequence, not yet an infinity-set axiom.
- recursive extensional union with proved associative, commutative, and empty
  identity laws.
- quotient-level membership for recursive sets, with empty-set exclusion,
  embeddings of each union summand, and extensionality proved as theorems.
- the `inc_to_set` translation packaged as a functor from the discrete
  incidence carrier category to the category of types.  It is always faithful
  but never full or essentially surjective; explicit morphisms and objects
  outside its image are constructed.  Every translated fiber is classified
  exactly: nullary incidences give `ULift Bool`, non-nullary incidences give
  `ULift Unit`.  Consequently the Boolean boundary-shape code is a complete
  invariant for this translation.  For an arbitrary carrier map, preservation
  of that code, existence of a boundary-shape translation, pointwise fiber
  equivalence, and natural isomorphism of the induced Set-valued functors are
  all proved equivalent.
- a general bisimulation-quotient theory.  The quotient map is always
  surjective, and is injective (equivalently bijective) exactly when the
  incidence is bisimulation-faithful; non-faithfulness is exactly witnessed by
  two distinct points collapsing to one quotient class.  Maps out of the
  quotient satisfy the expected universal property: factorization exists
  exactly for bisimulation-invariant maps and is unique, with checked beta,
  identity, and composition laws for the canonical lift.
  `BisimulationQuotientClassification` now produces an explicit type
  equivalence between the quotient and any complete classification target.
  A proposed classifier extends to such a complete classification exactly
  when its equality kernel is bisimilarity and it is surjective.
  Any two such targets are connected by a unique classification-preserving
  equivalence, with identity, composition, symmetry, and target-transport
  coherence laws.  The seven-element simplex model instantiates this result
  as an explicit equivalence with its three shape classes, including computed
  inverse representatives for vertex, edge, and face.

The minimal category/functor/pushout vocabulary is also formalized. A functor
is proved to map a pushout cocone to a commuting cocone; preservation of the
universal property is represented explicitly by `PushoutPreserving`. Functor
composition, cospan-map identity/composition laws, and composition of
pushout-preserving translations are checked. Any two pushout apexes of the
same cospan are connected by a constructed unique isomorphism.
The terminal category supplies a concrete pushout-preserving identity
translation, while the trivial incidence model supplies concrete T2–T4
witnesses.

Pushout universality and generic boundary-square-zero need additional
categorical or linear hypotheses.  Linear-observation completeness and the
boundary-shape/Set translation preservation-and-reflection results are proved
under their explicit hypotheses; they are not asserted for arbitrary
translations.
For example, `BoundaryRowBalanced` is now the explicit checked hypothesis
under which the derived Laplacian has zero row and column sums.
Pointwise boundary equality transports this balance condition and its
zero-sum Laplacian consequences between incidence models.
They are not unconditional theorems in the present Lean core.

The former A11–A13 gap is now represented by the optional
`BisimulationNormalizationSpec`: it records glue congruence modulo
bisimilarity and a sound, idempotent normalization.  The finite incidence
model instantiates it with identity normalization.  A14–A15 remain separate
categorical specifications rather than fields of the base incidence record:
`PushoutPreservingFamily` quantifies preservation over every source pushout,
with checked identity and composition laws and a terminal-category witness.

The finite model is evidence of satisfiability of this **implemented finite
fragment relative to Lean**. It is not yet a ZF-model proof or a relative
consistency proof for a full incidence theory.

## Verify

```bash
./verify.sh
```

or, from `incidence-theory/`:

```bash
lake build
lake exe incidence-theory
```

The checker accepts no `sorry` or Lean `axiom` declarations in the current
Lean source tree.

## Scope

The papers and older web material in this repository describe broader research
directions. The Lean source is authoritative for the current formalized scope.
