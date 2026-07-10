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
  derivations.  Its intuitionistic Kripke semantics, persistence theorem, and
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
  In the converse direction, every nonderivable finite sequent has a checked
  canonical prime-theory counterworld for the supplied coding.
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

The minimal category/functor/pushout vocabulary is also formalized. A functor
is proved to map a pushout cocone to a commuting cocone; preservation of the
universal property is represented explicitly by `PushoutPreserving`. Functor
composition, cospan-map identity/composition laws, and composition of
pushout-preserving translations are checked. Any two pushout apexes of the
same cospan are connected by a constructed unique isomorphism.
The terminal category supplies a concrete pushout-preserving identity
translation, while the trivial incidence model supplies concrete T2–T4
witnesses.

Pushout universality, generic boundary-square-zero, linear completeness, and
  translation preservation need additional categorical or linear hypotheses.
For example, `BoundaryRowBalanced` is now the explicit checked hypothesis
under which the derived Laplacian has zero row and column sums.
Pointwise boundary equality transports this balance condition and its
zero-sum Laplacian consequences between incidence models.
They are not unconditional theorems in the present Lean core.

The former A11–A13 gap is now represented by the optional
`BisimulationNormalizationSpec`: it records glue congruence modulo
bisimilarity and a sound, idempotent normalization.  The finite incidence
model instantiates it with identity normalization.  A14–A15 remain separate
categorical specifications rather than fields of the base incidence record.

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
