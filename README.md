# Theory of Incidence

> The cycle-41 maturity ADR remains a historical snapshot. Its 2026-07-11
> addendum records the now-checked Kripke completeness, compositional internal
> logic, HF integer arithmetic/order/number theory, and current remaining
> research boundary.

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
  exactly, alongside derivability and semantic consequence.  A concrete
  Incidence-boundary semantics now interprets an atom as true exactly when its
  boundary is inhabited; natural-deduction soundness specializes directly to
  this observation, and translations preserving boundary inhabitation preserve
  formula and context truth iff.  Such translations are packaged as
  `IncidenceBoundaryObservationEmbedding`, with identity, composition, and
  functorial truth laws.  Boundary-observation semantic consequence is defined
  directly on an Incidence; derivations are sound for it, and observation
  embeddings preserve and reflect translated entailment iff.  The existing
  `Nat → PathId.node` boundary-natural map is a concrete embedding and preserves
  every translated formula's truth and every finite sequent's entailment iff.
  For `natIncidence`, atom `n` is true exactly
  when `n≠0`, including a checked negation of the zero atom.  This single
  boundary-derived valuation is intentionally not claimed complete: excluded
  middle is valid in it but remains intuitionistically underivable, a checked
  generic counterexample instantiated at the `natIncidence` zero atom.  Full
  completeness belongs to the all-model Kripke semantics below.  Boundary truth
  also interacts exactly with the generic constructors: a product atom has an
  inhabited boundary iff either component does, while an atom injected into an
  incidence sum has boundary truth exactly when its source-side atom does.  The
  dual leaf valuation (truth means empty boundary) is sound for derivations and
  makes a product atom true exactly when both component atoms are leaves; sum
  injections again preserve and reflect the corresponding source-side truth.
  Thus the same constructors induce checked OR behavior for boundary presence
  and AND behavior for leafhood.  These observations are constructively dual
  for every Incidence atom: boundary presence holds exactly when leafhood does
  not, and leafhood holds exactly when boundary presence does not; the atom
  semantics inherits the same checked negation relation.  Consequently every
  boundary-observation embedding automatically preserves and reflects leaf
  valuation, leaf-formula truth, leaf-context satisfaction, and leaf semantic
  consequence as well.  Derivations are sound for leaf entailment, and the full
  dual transport is instantiated for the `Nat → PathId.node` embedding.  Its intuitionistic
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
  Work toward removing the global countability requirement now has a checked
  finite-support layer: every formula exposes its finite atom list, every
  context and sequent expose their combined finite support, and atom maps that
  agree only on that support are proved to induce identical formulas and
  contexts.  In particular, an encode/decode pair need be a left inverse only
  on the displayed sequent support for formula and context translation to
  round-trip exactly.  Constructing the corresponding finite code/retraction
  is now checked as well: for every nonempty finite support, `List.idxOf` and
  `List.getD` give an `ULift Nat` coding whose decode/encode law holds on that
  support (the lift keeps arbitrary atom universes aligned with `Formula.map`).
  `ULift Nat` has an explicit global countable coding, so the existing Kripke
  completeness theorem applies to the translated sequent.  If that translated
  sequent is semantically valid, its derivation decodes back to a derivation of
  the original sequent using only the support-local roundtrip law.  What
  remained was validity transport; the existing Kripke pullback/map theorem
  supplies it directly.  Consequently every nonempty atom carrier with lawful
  decidable equality—countable or uncountable—now satisfies the full theorem
  `KripkeEntails ↔ Derives` for every finite sequent, without any global atom
  enumeration.  Only the genuinely empty atom type remains as a separate
  universe-polymorphic branch (the concrete `Fin 0` language was already
  complete).  That final branch is now closed too: a generic formula
  enumeration is constructed from an explicit emptiness eliminator at any
  universe.  A classical empty/nonempty split yields
  `kripke_entails_iff_derives_arbitrary_atoms`, proving full propositional
  Kripke completeness for every lawful decidable-equality atom carrier with no
  countability or nonemptiness hypothesis.  Every `Incidence` with its existing
  `DecidableEq` carrier obtains this theorem directly through
  `Incidence.internalLogic_complete_arbitrary`; countable presentations remain
  useful for explicit canonical enumeration/countermodel APIs, not for the
  completeness equivalence itself.
  The arbitrary-carrier result now also provides the model-theoretic forms:
  non-derivability is equivalent to existence of a Kripke countermodel,
  derivability is equivalent to absence of one, and derivational consistency
  is equivalent to Kripke satisfiability.  Every Incidence receives the latter
  equivalence directly.  Countable presentations remain relevant specifically
  when a countermodel inside the explicit canonical prime-theory model is
  required, rather than merely an existential Kripke countermodel.
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
- incidence-indexed dependent families, their dependent sums (`Σ`) and
  dependent products (`Π`), reindexing, family morphisms and family
  isomorphisms are reconstructed with identity/composition laws and induced
  equivalences.  Boundary-observation embeddings now also pull such families
  back; the induced maps on total spaces and sections satisfy checked
  composition laws.  This is a concrete dependent-type fragment of the
  internal language.  It now includes an identity family over any pair-carrier
  Incidence, universe-correctly represented by a lifted equality witness, with
  reflexivity, symmetry, transitivity, dependent transport, and the J
  eliminator.  Transport has reflexivity and composition laws and J has its
  beta law.  On `natIncidence × natIncidence`, the identity fiber at `(0,0)` is
  inhabited while the fiber at `(0,1)` is proved empty, so the construction is
  nontrivial.  This is not yet a completeness theorem for a full dependent
  type theory.
  The identity layer is connected to substitution rather than left isolated:
  identity witnesses are unique, functions act on them by `congrArg`, this
  action preserves identity and composition, symmetry is involutive, and
  transport is natural with respect to every dependent-family morphism.  These
  are the core equality/substitution coherence laws needed before adding a
  full telescope syntax and typing judgment.  A semantic context calculus is
  now present as well: contexts carry assignment types, dependent extension is
  a Sigma type, substitutions are assignment maps with identity/associative
  composition, and types and terms reindex functorially.  Extended contexts
  expose their projection and variable, while substitution extension satisfies
  both projection and variable beta laws.  This semantic calculus now has
  genuinely dependent connectives over context extension: dependent Pi with
  lambda/application and beta/eta laws, and dependent Sigma with pairing,
  first/second projections, both beta laws, and eta.  Codomains are indexed by
  the extended assignment `⟨environment, value⟩`, rather than being ordinary
  nondependent function or product types.  Base substitutions lift canonically
  to extended contexts, commuting with projection and the newest variable.
  Dependent Pi and Sigma formation are stable under this lift, and substitution
  is natural for Pi lambda/application as well as Sigma pairing and both
  projections.  Contextual identity types are now formed from any two terms of
  one contextual type; reflexivity, transport, J, the transport-reflexivity and
  J beta laws are checked, and identity formation and reflexivity commute with
  base substitution.  Thus Pi, Sigma, and identity satisfy the semantic
  context-substitution discipline.  What remains is an independent raw
  telescope/term syntax and inductive typing judgment whose interpretation is
  this checked semantic calculus.  The first independent raw layer is now
  implemented: de Bruijn variables, unit, products, functions, pairing,
  projections, lambda, and application; context lookup and typing are
  inductive derivation data, with deterministic lookup.  A universe-polymorphic
  interpretation maps base types to arbitrary semantic types, typed contexts
  to heterogeneous environments, and every typing derivation to a value of
  its interpreted type.  Closed identity and product-swap programs have
  checked typing derivations and evaluate respectively to the identity
  function and component exchange.  Dependent raw constructors remain.
  Weakening is now established through a reusable general renaming calculus:
  a renaming carries a de Bruijn index map plus lookup preservation, lifts
  correctly under binders, acts structurally on terms, and preserves every
  typing derivation.  Insertion at the context head is the `Nat.succ`
  specialization, and identity renaming is proved neutral on all terms.
  Simultaneous typed substitution is now implemented too: a substitution maps
  every target variable to a source term together with its typing derivation;
  lifting under a binder fixes the newest variable and weakens every replaced
  older term.  Structural substitution preserves typing for every rule, and
  identity substitution is neutral on all raw terms.  Its environment layer
  recursively evaluates a typed substitution to a target
  heterogeneous environment, and every variable lookup is proved to agree
  with evaluation of its replacement term.  Renamings now pull semantic
  environments back, lookup and term evaluation are natural under that
  pullback, and lifting a renaming commutes with environment extension.
  Consequently weakening preserves evaluation.  The analogous lifted typed
  substitution/environment law is proved as well, including the lambda binder,
  and the full semantic substitution theorem holds for every typing rule:
  evaluating a substituted derivation equals evaluating the original
  derivation in the induced target environment.
  A separate genuinely dependent raw telescope layer is now present too.
  Raw types contain dependent Pi, dependent Sigma, and identity types whose
  endpoints are raw terms; raw terms contain lambda/application, dependent
  pairs/projections, and reflexivity.  Capture-avoiding renaming and simultaneous
  substitution act mutually on types and terms, and codomain instantiation is
  used by application and both dependent projections.  Mutually inductive type
  formation and term typing judgments enforce that Pi/Sigma codomains are
  checked in the extended context and that identity endpoints share a type.
  The closed term `incDepRawDependentRefl` inhabits
  `Pi (x : Unit), Id Unit x x`, and instantiating that codomain at unit computes
  to `Id Unit unit unit`.  The remaining bridge is preservation of these
  dependent judgments under renaming/substitution and their interpretation into
  the checked semantic Pi/Sigma/identity context calculus.
  As the first preservation prerequisite, identity renaming and identity
  simultaneous substitution are proved neutral on every dependent raw type and
  term by mutual structural recursion.  The lifted identity replacement under a
  binder is proved extensionally equal to the variable replacement, so these
  laws cover Pi/Sigma codomains and lambda bodies rather than only closed syntax.
  Renaming composition is also proved mutually for all dependent types and terms.
  The proof includes the nontrivial binder equation saying that lifting a
  composite index map equals composing the lifted maps, establishing the
  functorial syntax law needed by telescope renamings.
  Dependent variable lookup now enforces the correct scope invariant: the newest
  variable in `A :: Gamma` has type `A` weakened into the extended context,
  rather than the unshifted tail-context expression.  On this invariant a
  type-aware telescope renaming packages an index map with lookup preservation
  at the renamed type.  Identity, target weakening, and binder lift are
  constructed, with the lift proof checking both the newest and older-variable
  cases against dependent type renaming composition.
  Dependent lookup is type-deterministic: a fixed telescope and de Bruijn
  position cannot yield two different weakened raw types.  This is proved by
  induction through arbitrary telescope depth and is the index-alignment fact
  used by the forthcoming typing-preservation proof.
  Renaming after simultaneous substitution now satisfies a general fusion law
  on every dependent raw type and term: it equals substitution by the pointwise
  renamed replacements.  The binder proof establishes that renaming a lifted
  replacement is the same as lifting the renamed replacement, so the theorem
  covers nested Pi/Sigma types and lambdas without a closed-term restriction.
  The converse fusion law is checked too: substituting after a renaming equals
  direct substitution by the replacement composed with the index map.  Combining
  both directions yields codomain-instantiation naturality: renaming an
  instantiated dependent type equals first renaming the codomain under the
  lifted map and then instantiating it with the renamed argument.  This aligns
  the result types required by dependent application and second projection.
  Type formation and term typing are now preserved by every type-aware
  telescope renaming.  The proof is mutual across formation and typing,
  lifts the telescope map through Pi/Sigma binders, and covers every term rule,
  including dependent application, pairing, second projection, and identity
  reflexivity.  Instantiation naturality supplies the required transports for
  all dependent result types, so this is a full judgment-preservation theorem,
  not merely weakening of closed examples.
  A type-aware dependent simultaneous substitution is now packaged as a term
  replacement map together with typing of every replacement at the lookup type
  transformed by that same map.  Identity substitution and binder lift are
  constructed.  The lift fixes the newest variable, weakens every older
  replacement through the renamed source telescope, and uses both fusion laws
  to align the weakened lookup types.  This provides the substitution object
  required for full dependent formation/typing preservation.
  Simultaneous substitution composition is proved mutually for every dependent
  type and term, including the lifted-composition equation under binders.  It
  yields substitution naturality of codomain instantiation.  Using these laws,
  type formation and term typing are preserved by every typed dependent
  substitution.  The mutual proof covers Pi/Sigma formation and binders,
  application, dependent pairing and both projections, identity formation, and
  reflexivity.  Thus the raw dependent calculus now has full renaming and
  substitution judgment preservation; its remaining major bridge is semantic
  interpretation and soundness in the contextual Pi/Sigma/Id model.
  The semantic bridge now has a first end-to-end dependent witness.  The raw
  closed inhabitant `Pi (x : Unit), Id Unit x x` is mirrored in the semantic
  context calculus using context extension, the newest variable, contextual
  identity formation, reflexivity, and Pi lambda.  Applying that semantic term
  to unit is proved definitionally equal to semantic reflexivity.  This checks
  the intended raw-to-semantic constructor alignment and beta computation while
  the general derivation interpreter remains to be completed.
  The bridge also covers dependent Sigma: the raw pair inhabiting
  `Sigma (x : Unit), Id Unit x x` and both of its typed projections are checked,
  and the corresponding semantic dependent pair is built from the same unit and
  reflexivity data.  Its first and second projections satisfy their semantic beta
  laws definitionally.  Concrete raw/semantic alignment is therefore exercised
  for Pi, Sigma, and identity rather than for only one dependent connective.
  The raw dependent calculus now has an explicit one-step operational semantics.
  It contains Pi beta, both Sigma projection beta rules, and congruence rules for
  function/argument positions, pair components, and projections.  The closed
  dependent reflexivity application reduces to `refl unit`, while the two
  projections of the dependent pair reduce to `unit` and `refl unit`.
  These checked raw reduction witnesses match the semantic beta equalities and
  provide the relation for the forthcoming general reduction-soundness theorem.
  Because reduced terms can occur inside dependent result types, subject
  reduction is stated with explicit conversion rather than false literal syntax
  equality.  Term definitional equality is the reflexive, symmetric, transitive
  closure of one-step reduction; type definitional equality is closed under
  Pi, Sigma, and identity formation, including equality of identity endpoints.
  A conversion-aware typing judgment admits both term and type conversion.
  Every one-step reduction preserves typing in this judgment, and the Pi beta
  and both Sigma beta examples instantiate the theorem without assumptions.
  For the three closed dependent beta programs, reduction soundness is now
  bundled rather than reported as parallel facts: each checked certificate
  contains the raw definitional equality and the corresponding equality of
  semantic contextual terms.  These certificates cover Pi application and both
  Sigma projections.  They are concrete instances of the intended general
  semantic reduction theorem; generality still depends on the derivation
  interpreter rather than being claimed from the examples alone.
  Operational reduction is stable under the full structural discipline as well.
  Term instantiation commutes with both renaming and simultaneous substitution,
  including the lifted map below a binder.  Consequently every one-step
  reduction can be renamed or simultaneously substituted to obtain another
  valid one-step reduction.  The proof covers Pi beta's substituted body and all
  congruence rules, connecting computation to the previously checked judgment
  preservation infrastructure.
  A reflexive-transitive multi-step reduction is now defined with checked
  transitivity.  Multi-step reduction remains stable under arbitrary renaming
  and simultaneous substitution, embeds into term definitional equality, and
  satisfies conversion-aware subject reduction.  This fixes the operational
  side of the eventual semantic soundness statement at normalization-sequence
  scope rather than only at one isolated beta step.
  Definitional equality is packaged as a setoid on all dependent raw terms, and
  its quotient gives a canonical computation model.  The quotient map is a
  general evaluator whose value is invariant under every definitional equality,
  one-step reduction, and multi-step reduction.  The dependent Pi and Sigma
  examples instantiate this soundness result.  This is an all-term syntactic
  quotient semantics; it does not replace the still-pending interpretation into
  the external contextual Pi/Sigma/identity model.
  The domain of the forthcoming contextual interpreter is now made explicit.
  A bare typing derivation does not itself certify that its telescope and result
  type are well formed, so `IncDepRawCertifiedTyping` packages all three pieces:
  context well-formedness, type formation, and term typing.  Closed certification
  is constructed for the dependent Pi/reflexivity and Sigma/pair examples.
  Certified judgments are preserved by type-aware renaming and typed dependent
  substitution whenever the destination/source telescope is certified.  This
  removes an implicit premise that previously prevented a well-typed general
  semantic interpreter signature.
  The semantic result API now works over arbitrary certified telescopes.  A
  well-formed raw context is assigned a semantic context, context extension is
  realized by semantic dependent extension, and a certified open judgment is
  assigned a contextual type together with a term of that type.  The earlier
  closed result embeds into this general API with proof-index-aware elimination
  of the unique empty-context derivation; the dependent Pi and Sigma examples
  are checked through that embedding.  The recursive constructor interpreter
  producing these results from a certified judgment alone remains pending.
  The now-complete mutual substitution-preservation interpreter instead starts
  from an explicit semantic context tree, substitution semantics, replacement
  interpretation, and the documented provider hypotheses.  It proves the
  recursive semantic step once those inputs exist; it does not synthesize them
  from bare certification.
  This boundary is now a checked API rather than prose.
  `IncDepRawCertifiedCanonicalSemanticInput` packages, for one certified
  judgment, its semantic context result/tree, coherent readiness, and canonical
  preservation hypotheses.  `interpretCertifiedCanonical` consumes exactly this
  package and returns the strict semantic result with its coherence theorem.
  `IncDepRawCertifiedCanonicalSemanticSynthesizer` quantifies that construction
  over every certified judgment; given such a synthesizer,
  `interpretCertified` is the unconditional-looking general interpreter and
  `interpretCertified_coherent` proves its semantic substitution law.  Thus the
  remaining synthesis problem has an exact Lean type and no longer includes the
  already-complete recursive interpretation itself.
  The boundary is inhabited for the closed dependent-pair example by
  `incDepRawDependentPairCanonicalSemanticInput`.  It supplies the empty context
  semantics, the pair's coherent readiness tree, and the explicit canonical
  hypotheses.  `interpretCertifiedDependentPair` proves by `rfl` that interpreting
  this certified input is exactly the previously checked
  `preserveDependentPair` result.  Hence the synthesis package is executable and
  composes definitionally with the preservation implementation; the remaining
  universal task is producing such packages uniformly, not repairing their API.
  Synthesis is now factored into global and local obligations.
  `IncDepRawCertifiedCanonicalSemanticWitness` contains only the judgment-local
  semantic context result/tree and coherent readiness.  Its synthesizer quantifies
  those witnesses over certified judgments, while `withHypotheses` attaches one
  shared canonical preservation environment to all of them.
  `interpretCertifiedWithWitness` and its coherence theorem consume this split
  interface directly.  Consequently provider construction is no longer repeated
  per judgment, and the remaining syntax-directed task is isolated to producing
  context trees and coherent readiness witnesses.
  Those local obligations are now split once more.  A
  `IncDepRawContextSemanticTreeSynthesizer` handles telescope semantics, while a
  `IncDepRawCertifiedCoherentReadinessSynthesizer` handles the proof-indexed
  syntax tree; `ofComponents` combines them.  Context synthesis itself is
  structural: `IncDepRawContextHeadSemanticProvider` only interprets one
  well-formed head type over an already interpreted tail, and
  `synthesizeContext` recursively builds the complete semantic context and tree.
  `ofHeadProvider` then combines this with readiness synthesis.  The remaining
  local construction problem is therefore reduced to head-formation semantics
  plus coherent-readiness generation, rather than whole-context assembly.
  The readiness boundary now records exactly which certification level can
  support structural synthesis.  `IncDepRawDeepCoherentReadinessProvider`
  receives the recursive `IncDepRawTypingDeeplyWellFormed` certificate, and
  `synthesizeCertified` produces readiness for a `DeepCertifiedTyping`.
  `synthesizeDeep` connects that result, with either a context-tree synthesizer
  or a head provider, directly to the existing canonical semantic witness.
  Ordinary `CertifiedTyping` deliberately cannot use this bridge: its fields
  certify only the outer context, result type, and typing derivation and do not
  contain recursively formed premises.  The remaining readiness theorem is
  thus precisely construction from deep syntax certificates, not an unjustified
  extraction from the weaker certificate.  One former gap in that construction
  is now closed: `IncDepRawSubstitution.instantiate` is the checked one-variable
  substitution determined by a typed argument, and
  `IncDepRawWellFormed.instantiate` proves that substituting it into a
  well-formed binder codomain produces a well-formed instantiated result.  The
  result formations needed by apply, pair, and second are therefore derivable
  from their codomain formation and argument typing rather than new assumptions.
  The final certification boundary is now represented directly by
  `IncDepRawCoherentlyCertifiedTyping`.  It extends the ordinary certificate
  with readiness indexed by exactly the certificate's typing and result
  formation.  `toWitness` obtains the entire judgment-local semantic witness
  from context synthesis alone, and `interpretCoherentlyCertified` plus
  `interpretCoherentlyCertified_coherent` give the canonical interpretation and
  its semantic-term equation.  Thus readiness is no longer a separate uniform
  synthesizer assumption for coherently certified syntax; after certification,
  only telescope/head semantics and the shared preservation environment remain.
  This also records an important negative boundary: neither deep
  well-formedness nor the older semantic-readiness tree alone indexes every
  identity endpoint by the same formation proof, so silently coercing either to
  coherent certification would assert coherence that its type does not contain.
  Coherent telescope synthesis is now closed as well.
  `IncDepRawCoherentContext.WellFormed` stores coherent readiness at every head;
  its `synthesize` recursion interprets the tail, runs the already-proved
  canonical formation-preservation dispatcher at the identity substitution, and
  extends the semantic context with the resulting head family.  No separate
  head-semantic provider is needed.  Finally,
  `IncDepRawFullyCoherentCertifiedTyping` combines that telescope certificate
  with coherent term certification.  `toInput`,
  `interpretFullyCoherentCertified`, and its coherence theorem provide an
  end-to-end interpretation with no judgment-local synthesis assumptions at
  all.  Only the shared canonical preservation hypotheses remain global.  This
  closes the local synthesis branch for the fully coherent certification level;
  weaker raw certificates remain intentionally weaker rather than being given
  fabricated coherence evidence.
  The remaining global boundary is now internalized as model lawfulness rather
  than repeated theorem parameters.  `IncDepRawLawfulSubstitutionFiberModel`
  extends the semantic model with variable substitution, readiness alignment,
  and formation rebase laws.  Its `preservation` is the complete canonical
  mutual substitution dispatcher, while `interpretFullyCertified` and its
  coherence theorem expose the final public path from fully coherent syntax to
  semantics without any additional arguments.  The stronger
  `IncDepRawEqualityLawfulSubstitutionFiberModel` replaces the rebase law by
  literal uniqueness of formation-preservation results and converts to the
  lawful model automatically.  These are genuine semantic model laws, not
  syntax-local obligations: readiness alignment cannot be derived merely from
  the output index, because dependent elimination can hide different internal
  derivations behind the same instantiated result type.
  Concrete-model construction has also been separated from an inessential
  choice.  `withUnitBase` replaces every primitive base type by the explicit
  family `ULift Unit` while preserving typing-formation, Pi/Sigma transport
  coherence, and all canonical preservation laws; simp theorems expose both the
  concrete carrier and unchanged laws.  Hence choosing interpretations for raw
  base indices is not a remaining consistency obstacle.  The genuine concrete
  model work is now confined to dependent transport coherence and the global
  variable/alignment/rebase laws.  An attempted derivation of dependent Sigma
  round trips from fiber inverse laws alone also exposed the precise issue:
  dependent `Eq.mp` transport naturality is required, so the current
  Pi/Sigma-coherence fields must not be reported as redundant until those
  transport equations are proved.
  The identity-transport case is now fully concrete rather than assumed.
  `IncFiberEquiv.identity` and `IncDependentFiberEquiv.identity` give literal
  identity equivalences, and `IncDependentPiApplicationFiberEquiv.identity`
  proves both function round trips plus application compatibility, while
  `IncDependentSigmaFiberEquiv.identity` proves both dependent-pair round trips.
  All laws reduce by `rfl`.  Thus the coherence interfaces are inhabited and
  computational for identity substitution—the case used by the certified
  interpreter.  What remains for a substitution-complete concrete model is the
  genuinely non-identity reindexing/transport case, not the basic Pi/Sigma
  constructors themselves.
  A model audit then removed a larger apparent obligation entirely.
  `IncDepRawSubstitutionFiberModel.typingFormation` quantified over every
  semantic-readiness derivation, but its accessor and field had no consumers in
  either preservation implementation.  Coherent readiness already carries the
  exact result formation used by every recursive branch.  The unused field and
  accessor are deleted, and `withUnitBase` now preserves only the genuinely used
  Pi/Sigma coherence data.  Consequently a concrete substitution-fiber model no
  longer has to reconstruct formation evidence from the weaker, unindexed
  semantic-readiness syntax; its core data is exactly a base interpretation plus
  dependent Pi and Sigma transport coherence.
  Dependent Sigma coherence is now no longer model data.  The two general
  theorems `sigmaBackward_forward` and `sigmaForward_backward` use Sigma
  extensionality, heterogeneous equality, `cast_heq`, and the underlying fiber
  inverse laws to discharge the nontrivial `Eq.mp` transports.  They assemble
  `IncDependentSigmaFiberEquiv.ofDependent`, and
  `IncDepRawSigmaSubstitutionCoherence.canonical` supplies every raw
  substitution instance.  All previous `model.sigmaCoherence` consumers now use
  that canonical proof, and the field has been deleted.  After Unit-base
  normalization, the substitution-fiber model's only remaining semantic datum
  is therefore general dependent-Pi application coherence.
  That last core field is now gone too.  General
  `piBackward_forward` and `piForward_backward` theorems combine function
  extensionality with the same HEq/cast argument, and
  `piForward_apply_source` proves application compatibility.  They build
  `IncDependentPiApplicationFiberEquiv.ofDependent` and the raw
  `IncDepRawPiSubstitutionCoherence.canonical`; every former
  `model.piCoherence` use now selects this theorem.  Consequently
  `IncDepRawSubstitutionFiberModel` contains only `baseModel`.  The explicit
  `incDepRawUnitSubstitutionFiberModel` is therefore a complete concrete
  substitution-fiber model, not a conditional shell, and
  `withUnitBase_eq_unit` proves that every universe-zero model normalizes to it.
  The remaining work for a fully lawful model is now exclusively the canonical
  preservation-law layer (variable substitution, readiness alignment, and
  formation rebase/equality), not construction of the semantic Pi/Sigma model.
  A countermodel audit shows that the existing global rebase/equality
  interfaces are too strong and must not be treated as outstanding axioms to
  prove.  `IncDepRawFormationSemanticResult` intentionally permits an arbitrary
  contextual family, so the same empty-context base formation admits one fiber
  result using `Unit` and another using `Bool`.  The checked theorems
  `incDepRaw_no_global_formation_fiber_equality_provider` and
  `incDepRaw_no_global_formation_fiber_rebase_provider` prove, at universe zero,
  that neither literal equality nor even a fiber equivalence can be supplied
  uniformly for all such results: either would make `Bool` a subsingleton.
  Therefore the old `LawfulSubstitutionFiberModel` interface is retained only as
  an explicit record of the over-strong boundary; it is not evidence that a
  lawful concrete model exists.  Preservation lawfulness must instead quantify
  over results generated by the canonical interpreter/dispatcher (or carry a
  provenance invariant), where arbitrary Unit/Bool reinterpretations are
  excluded.  This correction narrows the next proof task and removes a formerly
  impossible completion criterion.
  The corrected provenance-scoped design is now implemented for the first two
  formation constructors.  `IncDepRawCanonicalBaseFormationFiberResult` and
  `IncDepRawCanonicalUnitFormationFiberResult` assert that a result is literally
  the output of `model.base` or `model.unit`; canonical constructors inhabit
  these predicates.  Their `unique` theorems prove equality of any two
  provenance-carrying results, so the arbitrary Unit/Bool counterexample cannot
  enter this API.  `IncDepRawFormationSubstitutionFiberRebase.ofEq` then turns
  that scoped equality into the required natural rebase.  This establishes the
  base and unit cases of the replacement for the impossible global provider;
  the same provenance discipline must now be propagated through Pi, Sigma,
  identity, and the mutual typing fold.
  That propagation now covers every formation constructor.  The generic
  `IncDepRawCanonicalFormationFiberResult canonical result` records equality to
  any fixed canonical output and supplies constructor-independent `canonical`,
  `unique`, and `rebase` operations.  `IncDepRawCanonicalPiFormationFiberResult`
  and `IncDepRawCanonicalSigmaFormationFiberResult` fix their output to
  `model.pi`/`model.sigma` applied to the chosen domain and codomain results;
  `IncDepRawCanonicalIdentityFormationFiberResult` similarly fixes the output
  to `model.identity` applied to the chosen type and endpoint typing results.
  Together with the base/unit predicates, all five formation cases now have a
  provenance-scoped equality/rebase route.  The remaining integration work is
  to make the mutual dispatcher return these provenance witnesses alongside its
  formation and typing results, so recursive calls compare generated outputs
  rather than arbitrary semantic inhabitants.
  Constructor-level dispatcher integration is now complete for formations.
  `IncDepRawCanonicalStrictFormationSubstitutionDispatchResult` wraps the
  existing strict result with its fixed canonical fiber result and a provenance
  proof.  `dispatchCanonicalBaseFormation`,
  `dispatchCanonicalUnitFormation`, `dispatchCanonicalPiFormation`,
  `dispatchCanonicalSigmaFormation`, and
  `dispatchCanonicalIdentityFormation` cover all five readiness constructors;
  each reuses the checked strict dispatcher and its provenance is definitionally
  `rfl`.  This leaves existing APIs untouched while making generated-result
  uniqueness available to a new mutual fold.  The next integration layer is the
  typing wrapper—especially variable lookup—followed by replacing broad rebase
  calls in the recursive fold with the scoped provenance rebase.
  Typing provenance integration has begun at the two leaves that determine
  whether arbitrary results can enter the mutual recursion.
  `IncDepRawCanonicalStrictTypingSubstitutionDispatchResult` pairs a strict
  typing result with provenance for its formation result.
  `dispatchCanonicalTypingUnit` creates both components canonically, while
  `dispatchCanonicalVariable` consumes a provenance-carrying formation result
  from the formation fold and preserves that exact witness through lookup
  dispatch.  Thus the variable handler cannot substitute an unrelated semantic
  family.  The generic `withFormationProvenance` constructor lifts any existing
  strict typing result once its formation provenance is known, allowing lambda,
  apply, pair, projections, and reflexivity to reuse their checked builders
  rather than duplicate semantic proofs.
  The three composite typing constructors whose result formation is a direct
  canonical constructor are now integrated too.
  `dispatchCanonicalLambda` records the Pi formation built from the domain and
  body results, `dispatchProvenancedPairCanonical` records the Sigma formation
  built from domain/codomain results, and `dispatchCanonicalRefl` records the
  identity formation built from the term result.  Each delegates term semantics
  to the existing strict builder and adds an `rfl` formation-provenance witness.
  Together with Unit and Variable, five of the eight typing constructors now
  produce provenance-carrying results.  Apply, First, and Second remain because
  their result formation is selected from, or instantiated from, a recursive
  premise and therefore must propagate an incoming provenance witness rather
  than create a fresh outer constructor witness.
  Those final three cases are now complete.  `dispatchProvenancedFirst` consumes
  the provenance-carrying domain formation result and transfers the identical
  witness to the projection result.  `dispatchProvenancedApplyCanonical` fixes
  its formation result to the canonical codomain instantiation along the
  argument semantics, and `dispatchProvenancedSecondCanonical` does the same
  along the semantic first projection; both witnesses are `rfl` because the
  existing canonical builders already return those exact results.  All eight
  typing constructors—Variable, Unit, Lambda, Apply, Pair, First, Second, and
  Refl—therefore have provenance-aware checked builders.  The remaining step is
  recursor-level wiring: define mutual motives that return these wrappers and
  replace the old unrestricted rebase provider at recursive alignment sites.
  The provenance-aware recursor now has executable motives and its first four
  formation handlers.  `IncDepRawSomeCanonicalStrictFormationSubstitutionDispatchResult`
  and its typing analogue existentially package the canonical result because
  that result depends on recursive outputs.  The new canonical formation and
  typing fold motives return these packages.  `canonicalMutualFoldBase` and
  `canonicalMutualFoldUnitFormation` establish the leaves, while
  `canonicalMutualFoldPi` and `canonicalMutualFoldSigma` open the recursive
  domain package, build the lifted semantic context/replacements, open the
  codomain package, and return the corresponding provenance-aware constructor.
  These four handlers require no global rebase or result-equality provider.
  Identity is the remaining formation handler because its endpoint typing
  results must first be aligned to the canonical type result using scoped
  provenance.
  Three typing recursor handlers are now wired as well.
  `canonicalMutualFoldVariable` consumes the formation IH package and preserves
  its exact existential canonical result through lookup dispatch;
  `canonicalMutualFoldTypingUnit` creates the unit package directly; and
  `canonicalMutualFoldLambda` recursively interprets the domain, extends the
  context and replacements, interprets the body, and packages the resulting
  canonical Pi formation.  None requires readiness alignment or rebase.
  Together with the four formation handlers, seven of the thirteen mutual
  recursor branches now execute in the provenance-scoped fold.  The remaining
  branches expose the central invariant still to encode: recursive typing
  canonical results must be identified with the corresponding independently
  computed formation IH canonical result before Apply, Pair, projections,
  Identity, and Refl can consume them.
  That central invariant now has a checked local API.
  `IncDepRawCanonicalFormationTypingAgreement formation typing` states only that
  the existential canonical outputs of one generated formation package and one
  generated typing package coincide.  From this scoped statement,
  `result_eq` derives equality of the actual fiber results by composing their
  provenance proofs, `rebase` constructs the natural rebase, and
  `typingResultAligned` casts the typing fiber result to the exact formation-IH
  result.  This is the direct replacement for the impossible global rebase
  provider: it neither quantifies over arbitrary semantic inhabitants nor asks
  unrelated Unit and Bool interpretations to be equivalent.  Remaining recursor
  work is now precisely the construction of these local agreements in the six
  dependent branches.
  The typing fold now carries that invariant intrinsically.
  `IncDepRawAlignedCanonicalTypingFoldResult` contains the corresponding
  provenance-aware formation package, the typing package, and their local
  agreement; the aligned typing fold motive returns this structure.
  `alignedCanonicalMutualFoldVariable` reuses its formation IH,
  `alignedCanonicalMutualFoldTypingUnit` constructs matching unit packages, and
  `alignedCanonicalMutualFoldLambda` demonstrates the nontrivial recursive case:
  it uses the body agreement to cast body typing semantics to the exact body
  formation result, then builds both outer Pi packages from that same result, so
  the new agreement is `rfl`.  This is an executable replacement of global
  rebase inside recursion, not merely a proposed interface.  Apply, Pair,
  projections, Identity, and Refl can now consume aligned typing IHs directly.
  Readiness-index transport for those remaining branches is now provenance-safe.
  `IncDepRawCanonicalStrictFormationSubstitutionDispatchResult.castReady` and
  the corresponding existential-package operation change only the readiness
  index, preserving the canonical result and provenance.  The local
  formation/typing agreement has `castFormationReady`, which carries the same
  canonical equality across that index change.  Hence the existing readiness
  alignment provider, where still needed for proof-index reconciliation, no
  longer grants any semantic rebase power: it cannot change a fiber result or
  introduce an arbitrary interpretation.  The remaining Identity/Refl issue is
  solely proving equality of the canonical outputs computed by two recursive
  paths after their readiness indices have been aligned.
  That equality is now consumed through a fold-scoped interface and the Identity
  formation branch no longer uses global rebase.  `IncDepRawCanonicalFoldAgreement`
  compares only the outputs obtained by applying one formation IH and one
  aligned typing IH to the same semantic tree and replacements.
  `canonicalMutualFoldIdentityOfAgreements` accepts one such agreement for each
  endpoint, casts endpoint typing fiber results to the exact canonical type
  result, performs readiness-index casts without changing semantics, and builds
  the outer canonical identity result.  The handler typechecks with no
  unrestricted formation-result provider.  The remaining task is constructing
  these fold agreements recursively for every typing derivation; once supplied,
  Identity itself is complete.
  The first recursive agreement constructors are now checked.  Variable reuses
  its formation IH definitionally, Unit generates the same canonical unit family
  on both sides, and Lambda derives codomain-result equality by chaining the
  aligned body's local agreement with the provenance of both independently
  computed formation packages.  Thus Lambda does not assume a global semantic
  equality provider.  Refl is now checked as well: it feeds the same local
  type/term agreement into both endpoints of the canonical Identity formation,
  then constructs semantic reflexivity in that exact family.  The remaining
  agreement constructors are Apply, Pair, First, and Second, followed by their
  assembly into the mutual dispatcher.  First is now checked too: the Sigma
  pair agreement supplies the exact semantic pair fiber, while the domain
  formation package and its provenance are reused unchanged as the projection's
  result family.  Only the instantiate-dependent Apply, Pair, and Second
  agreement branches remain before dispatcher assembly.
  Their common remaining boundary is now represented directly rather than by a
  global rebase.  `IncDepRawCanonicalFormationFoldAgreement` compares the
  canonical outputs of two formation motives only at the same tree and
  replacements.  `IncDepRawCanonicalInstantiateSubstitutionFoldMotive` builds
  the canonical instantiated family from domain, codomain, and an argument fold
  agreement.  Apply, Pair, and Second can therefore share one fold-local
  instantiate agreement while retaining provenance for both recursive paths.
  The Pair branch now realizes that design end to end.  It transports the
  independently recursive result family to the canonical instantiated family by
  chaining structural provenance, the fold-local canonical equality, and
  instantiate provenance.  The second component is then cast into that exact
  dependent fiber and paired semantically.  Only Apply and Second remain.
  Apply is now complete as well.  Its actual dispatch formation is the canonical
  instantiated family, while its existential package deliberately exposes the
  independently recursive result IH canonical.  The fold-local instantiate
  equality supplies exactly the provenance connecting those two layers, so the
  application result agrees with the result formation IH without global rebase.
  Second, the final constructor-level agreement branch, is now checked.  It
  derives the semantic first projection from the Sigma pair agreement, uses that
  projection as the argument of the canonical instantiate motive, and connects
  the resulting dependent family to the independently recursive result IH with
  the same fold-local provenance chain.  All eight typing constructors now have
  aligned canonical handlers and fold-agreement constructors.  The remaining
  integration step is one mutual recursion that generates these agreements
  (including instantiate agreements) and exposes the total dispatcher.
  The instantiate-specific non-structural input to that recursion has an exact interface:
  `IncDepRawCanonicalInstantiateFoldAgreementProvider`.  It does not compare
  arbitrary semantic fibers.  For the same domain, codomain, argument, and
  recursive IHs, it identifies only the raw result-formation canonical output
  with `IncDepRawCanonicalInstantiateSubstitutionFoldMotive`.  Apply, Pair, and
  Second share this one substitution-naturality obligation; every other
  constructor agreement is generated structurally.
  The mutual-recursion outputs are now packaged as
  `IncDepRawCanonicalFormationFoldOutput` and
  `IncDepRawCanonicalTypingFoldOutput`; the latter keeps its formation motive,
  aligned typing motive, and local agreement inseparable.  A direct recursor
  assembly also exposed one final invariant: when the same formation is reached
  through a parent formation premise and a child typing premise, those two
  independently recursive formation motives need a fold-local formation
  agreement.  This is an index-sharing obligation, not semantic rebase, and is
  the next field required by the total mutual output.
  `IncDepRawCanonicalFoldAgreement.retargetFormation` now consumes exactly that
  field.  Given a fold-local agreement between two formation paths, it moves an
  existing typing agreement from one path to the other by transitivity of their
  canonical equalities.  It performs no fiber transport or semantic rebase and
  is the primitive used to reconnect independently recursive Identity/Refl,
  function, argument, and pair premises to their parent formation IHs.
  Attempting to derive the parent Pi agreement exposed the second and final
  dependent boundary: equality of domain fiber results changes the types of the
  extended semantic tree and lifted replacements on which codomain IHs run.
  `IncDepRawCanonicalDependentFormationFoldAgreementProvider` isolates precisely
  this transport naturality for Pi and Sigma.  The total recursion therefore has
  two scoped inputs—instantiate naturality and dependent-extension naturality—
  neither of which grants arbitrary semantic equality or rebase.
  The dependent provider now covers Identity formation too.  A type-path
  agreement retargets both endpoint typing agreements to the second type path,
  after which the provider compares the two canonical Identity folds.  Together
  with reflexive Base/Unit cases, its Pi, Sigma, and Identity fields cover every
  formation constructor needed by the mutual path-congruence recursion.
  Formation fold agreements now form an explicit equivalence calculus:
  `refl`, `symm`, and `trans` are checked.  Base and Unit paths close by
  reflexivity, provider-produced dependent agreements can be reoriented, and
  parent/child paths can be chained before `retargetFormation` moves the typing
  agreement.  These are the algebraic operations required by the final mutual
  output's formation-path field.
  Retargeting is now lifted to the bundle level by
  `IncDepRawCanonicalTypingFoldOutput.retargetFormation`, which preserves the
  aligned typing motive while replacing its formation motive and rebuilding the
  agreement.  Bundle constructors for Variable, Unit, and Lambda are checked;
  Lambda composes the domain formation output with the body bundle's own
  formation path, returning its Pi formation, aligned typing result, and
  agreement together.  These are the first three handlers in the final recursor
  at the exact output type it will expose.
  Formation agreements now permit distinct coherent-readiness proof indices on
  their two sides; their canonical fibers still have the same underlying type.
  `castReady` plus `castReadyAgreement` changes only that proof index, allowing
  Lambda to normalize its body path safely.  Bundle constructors for First and
  Refl are also checked: each retargets its child typing bundle to the parent
  formation path and then invokes the already-proved constructor handler.  Five
  of eight typing rules now operate entirely at bundle level.
  Apply, Pair, and Second now complete the bundle layer, so all eight typing
  rules return `IncDepRawCanonicalTypingFoldOutput`.  Apply retargets function
  and argument bundles to Pi and domain paths; Pair retargets its two components
  to domain and instantiated-result paths.  Second internally constructs the
  corresponding First bundle and reuses its agreement as the argument of the
  canonical instantiate motive.  The remaining step is the final mutual
  recursor assembly that generates formation-path agreements through the scoped
  providers and feeds these eight checked bundle handlers.
  The public endpoint of that assembly is now fixed as
  `IncDepRawCanonicalMutualFoldDispatcher`.  An inhabitant returns formation and
  typing bundles for every coherent readiness tree.  Its projections expose
  canonical formation preservation, aligned typing preservation, their local
  agreement theorem, and an `IncDepRawStrictMutualSubstitutionDispatcher` for
  compatibility with the existing API.  Consequently the remaining task is
  inhabiting this one interface by mutual recursion, not redesigning the
  preservation theorem or its consumers.
  Formation-side bundle constructors are now complete too.  Base, Unit, Pi, and
  Sigma package their canonical folds directly; Identity retargets both endpoint
  typing bundles to the chosen type path before constructing its formation
  output.  Together with the eight typing bundle constructors, all thirteen
  handlers required by the mutual readiness recursor now exist at the final
  dispatcher output types.  Only the recursive production of the path-agreement
  arguments between independently reached premises remains.
  The conditional total construction is now checked.
  `canonicalFormationFold` and `canonicalTypingFold` apply all thirteen bundle
  handlers through Lean's mutual readiness recursors, and
  `canonicalMutualFoldDispatcher` packages both projections.  Given the scoped
  instantiate-agreement and path-agreement providers, it is an actual inhabitant
  of `IncDepRawCanonicalMutualFoldDispatcher`, hence immediately yields the
  canonical preservation and strict-dispatch projections above.  The sole
  remaining proof is constructing the path-agreement provider from the already
  isolated dependent Pi/Sigma/Identity congruence laws rather than assuming it.
  The conditional theorem is now exposed as a usable model API.
  `IncDepRawCanonicalMutualFoldHypotheses` collects the variable, readiness,
  instantiate-agreement, and path-agreement inputs;
  `canonicalMutualFoldDispatcherOfHypotheses` builds the canonical dispatcher,
  while `strictPreservationOfCanonicalFoldHypotheses` projects the existing
  strict preservation interface in one call.  Thus conditional preservation is
  complete as an API; unconditional completion is exactly provider inhabitation.
  The genuinely required property is now separated from the external provider's
  broad call signature.  `IncDepRawCanonicalMutualFoldDispatcher.Lawful` asks
  only that a generated dispatcher's own formation and typing projections agree
  on each shared raw formation.  `canonicalMutualFoldDispatcher_lawful` proves
  the conditional construction satisfies this intrinsic law.  Unconditional
  completion is therefore the construction of this lawful mutual fixed point,
  rather than a claim that arbitrary user-authored fold outputs are equal.
  `IncDepRawCanonicalLawfulMutualFold` now packages that fixed-point shape as a
  first-class result: a dispatcher and its intrinsic law are stored together.
  `canonicalLawfulMutualFoldOfHypotheses` constructs the package under the scoped
  hypotheses, while `.strict` and `.pathAgreement` let consumers obtain strict
  preservation and coherence without retaining or reusing the external path
  provider.  The remaining unconditional theorem is precisely construction of
  this package without the path-provider field.
  The provider-free fixed point now has a concrete construction strategy.
  `IncDepRawCanonicalAnchoredTypingFoldOutput` indexes a typing result directly
  by the formation output generated alongside it, storing an agreement with
  that exact `.fold` rather than an independently chosen formation motive.
  Conversion to the public typing bundle and an `.anchor` operation are checked.
  A direct mutual recursion can therefore return formation outputs and anchored
  typing outputs together, making path agreement structural data and eliminating
  the external path provider from the recursive call graph.
  `IncDepRawCanonicalAnchoredTypingFoldResult` closes the typing-side mutual
  motive by storing both the formation output itself and the typing output
  anchored to it.  Conversions in both directions are checked, including
  `toAnchoredResult`.  The next recursor motive can therefore be stated without
  referring to an external formation function or path provider in its result
  type; every parent receives the exact child formation output as recursive data.
  Provider-free anchored handlers are now checked for Variable and Unit.  Both
  anchor definitionally to their recursively supplied or canonical formation
  output, so no path provider is involved.  Formation outputs also support a
  readiness-only cast.  The attempted Lambda lift identified its exact next
  obligation: the Pi congruence provider must consume transparent codomain
  projections rather than eta-expanded conversions; no unproved Lambda code is
  retained.
  Exact anchored handlers are now checked for Lambda, First, and Refl as well as
  the two leaves.  They construct their Pi, domain, or Identity formation output
  and their typing agreement from the same fold expressions, so the anchor is
  structural rather than supplied afterward.  Provider-free anchored coverage
  is therefore five of eight typing rules; unlike the earlier ordinary bundles,
  these results retain the formation output object needed by the final fixed
  point directly.
  Apply, Pair, and Second now complete exact anchored coverage: all eight typing
  rules return `IncDepRawCanonicalAnchoredTypingFoldResult` without a path
  provider.  Apply consumes function/argument anchors, Pair consumes first/second
  anchors, and Second constructs and reuses an anchored First result internally.
  The only remaining naturality input in these dependent branches is the scoped
  instantiate-agreement provider.  The final direct mutual recursion now only
  has to connect the five formation handlers to these eight anchored handlers.
  Lean does not allow the second function in a mutual declaration to mention the
  first function in its dependent result type, so the provider-free fixed point
  is now represented by `IncDepRawCanonicalAnchoredMutualFoldDispatcher`: its
  later `typing` field can depend on its earlier `formation` field directly.
  Conversion to the public dispatcher is checked.  The precise remaining law is
  `ReadinessLawful`, asserting only that formation evaluation is insensitive to
  the choice of coherent-readiness proof.  With that law,
  `toLawfulMutualFold` produces the fully lawful package.
  A computational sufficient condition is now formalized as
  `ReadinessStable`: casting a formation output along the readiness equality
  must equal evaluation at the target readiness proof.  `castReady_canonical`
  proves such casts preserve the canonical result, and
  `ReadinessStable.toLawful` derives the fold-local readiness agreement.  Thus
  the remaining readiness theorem is a structural proof that the final
  formation recursion commutes with proof-index casts, not a new semantic law.
  That structural theorem is now closed generically.  For any anchored
  dispatcher, eliminating the readiness equality reduces the casted output
  equation to reflexivity, so `readinessStable` requires no additional model
  hypothesis.  `toLawfulMutualFoldCanonical` consequently promotes every
  anchored dispatcher to a lawful mutual fold using only readiness alignment.
  The sole remaining construction is the anchored dispatcher itself.
  The anchored fixed-point API is now connected end to end under the scoped
  inputs.  `canonicalAnchoredMutualFoldDispatcher` anchors the two recursive
  projections at identical readiness indices, and `canonicalLawfulMutualFold`
  promotes it using the generic readiness-stability theorem.  The hypotheses
  record has a matching anchored constructor.  Ordinary, anchored, lawful, and
  strict preservation projections are therefore all checked; unconditional
  completion is now solely removal of the external path-agreement provider.
  The exact provider-free theorem target is now a Lean type.
  `IncDepRawCanonicalProviderFreeMutualFoldHypotheses` contains no unrestricted
  path provider.  Its original variable, readiness, and instantiate inputs are
  now joined by the model-indexed Pi/Sigma dependent-formation laws and the
  generated-Identity law exposed by the complete-certificate proof.
  `IncDepRawCanonicalProviderFreeMutualFoldWitness` stores the anchored
  dispatcher, and its `.lawful` and `.strict` projections derive lawful
  canonical and strict preservation automatically.  The remaining proof is the
  inhabitation of this single witness type.
  The old conditional implementation now maps into this exact target via
  `providerFreeMutualFoldWitnessOfPathProvider`; the corresponding `Nonempty`
  theorem is checked as well.  Thus the witness is not a disconnected
  specification: supplying the former path provider reproduces the implemented
  anchored/lawful/strict pipeline.  The only missing argument in the final
  theorem is literally that provider parameter.
  Generated-output certificates now begin the direct construction that removes
  that parameter.  Formation Base and Unit certificates are canonical leaves;
  Pi and Sigma certificates compose certificates for their domain and codomain.
  `Generated.agreement` proves any two such generated formation outputs agree,
  recursively invoking only the scoped dependent-formation agreement laws for
  Pi and Sigma.  Variable and Unit typing results have matching anchored
  certificates.  Identity formation is the remaining point at which these two
  certificate families must become genuinely mutual; after that mutualization,
  the six composite typing certificates and the anchored dispatcher can be
  assembled without an unrestricted path-agreement provider.
  The recursive motives are now packaged explicitly as
  `IncDepRawCanonicalGeneratedFormationFoldOutput` and
  `IncDepRawCanonicalGeneratedAnchoredTypingFoldResult`: each stores the output
  together with its generated-provenance proof at the same dependent readiness
  index.  Checked package constructors cover formation Base/Unit/Pi/Sigma and
  typing Variable/Unit.  This removes the need to project an output and later
  reconstruct which indexed certificate belongs to it when the final mutual
  recursor is assembled.
  Typing provenance is now also indexed directly by the exact generated
  formation output through `AnchoredTypingFoldOutput.Generated`.  Its checked
  constructors cover Variable, Unit, and recursively Lambda.  The corresponding
  `GeneratedAnchoredTypingFoldOutput` motive packages (1) the generated result
  formation, (2) the typing output anchored to precisely that formation, and
  (3) its syntax-directed provenance.  This exact index removes the readiness
  proof mismatch exposed by the older result wrapper and is the motive needed
  by the remaining dependent typing constructors.
  Generated formation uniqueness now also crosses propositionally equal
  readiness witnesses via `Generated.agreementAcrossReady`; the proof casts one
  generated output, applies structural uniqueness, and discharges the cast with
  the canonical-result transport theorem.  Anchored typing outputs have a
  provenance-preserving scoped `retarget` constructor.  Using these two pieces,
  the First projection is checked end to end: its recursively generated pair
  output is aligned to the freshly generated canonical Sigma formation and the
  result remains generated.  Provider-free typing coverage is therefore now
  Variable, Unit, Lambda, and First (4/8).
  Apply now uses the same scoped alignment twice: the recursively generated
  function is retargeted to the newly generated Pi formation and the argument
  to the generated domain formation.  The exact anchored Apply handler then
  consumes those outputs together with the generated result formation and the
  scoped instantiate-agreement input.  Both retarget provenance proofs are
  retained by the output certificate, raising provider-free typing coverage to
  5/8 without introducing a global path-agreement provider.
  Pair and Second are now checked by the same mechanism.  Pair independently
  aligns its first and second terms to the generated domain and instantiated
  result formations, then returns the generated Sigma formation.  Second aligns
  its pair to that generated Sigma and preserves the separately generated
  instantiated result formation.  Both branches retain the scoped instantiate
  agreement and all retarget provenance.  Provider-free typing coverage is now
  7/8; Refl is the only remaining typing constructor and shares its unresolved
  mutual dependency with Identity formation.
  That final dependency is now closed without reimplementing the seven ordinary
  branches.  Refl extends the already recursive anchored typing provenance and
  consumes the generated provenance of its term.  Formation provenance then
  gains a `CompletelyGenerated` closure: ordinary Base/Unit/Pi/Sigma outputs are
  embedded unchanged, while Identity consumes a completely generated underlying
  type and generated left/right endpoint typings.  The exact Identity formation
  builder shares the same anchored endpoints used by Refl.  Constructor-level
  provider-free certificates therefore cover formation 5/5 and typing 8/8.
  The remaining work is packaging this complete closure as the two motives of
  the final structural recursor and projecting its anchored dispatcher.
  Those complete motives are now explicit packages:
  `CompletelyGeneratedFormationFoldOutput` and
  `CompletelyGeneratedAnchoredTypingFoldOutput`.  Every ordinary generated
  package lifts into them without rebuilding its output.  Exact-index
  `completelyGeneratedIdentityExact` and `completelyGeneratedReflExact`
  construct the final two branches and preserve both formation completeness and
  typing provenance.  The remaining recursor obligation is now specifically
  the complete-agreement lemma that aligns independently recursive endpoint
  packages to the underlying type package before invoking these exact builders.
  Complete formation uniqueness is now proved structurally, and this proof
  exposes one precise law that the earlier dependent-formation interface did
  not contain.  Its Identity clause compares a fixed pair of endpoint semantic
  terms while changing only the underlying type output; independently recursive
  Identity branches may also produce different endpoint semantic terms.
  `GeneratedIdentityFoldAgreementProvider` isolates exactly this latter
  naturality, quantified only over two generated Identity outputs rather than
  arbitrary semantic fibers.  Given it and the existing Pi/Sigma dependent
  agreement laws, `CompletelyGenerated.agreement` covers ordinary/ordinary and
  Identity/Identity cases, with mixed constructor cases eliminated by the
  indexed syntax.  The final dispatcher can therefore use a strictly scoped
  Identity law, but that law must still be inhabited or added honestly to the
  final hypotheses; it is not derivable from proof irrelevance.
  Complete agreement now also crosses distinct readiness witnesses by canonical
  transport, exactly as the ordinary generated agreement does.  The final
  hypotheses record is consequently indexed by the semantic model and lists
  all five scoped inputs explicitly: variable replacement, readiness alignment,
  instantiate agreement, dependent Pi/Sigma agreement, and generated Identity
  agreement.  “Provider-free” here means free of the former unrestricted
  arbitrary-output path provider; it does not mean that dependent semantic
  naturality laws have been silently derived.
  General (not merely exact-index) complete Identity and Refl handlers are now
  checked.  Each compares the independently recursive endpoint formation with
  the chosen underlying type via complete agreement across readiness, retargets
  the anchored endpoint output with a provenance certificate, and invokes the
  exact builder.  Thus no caller of the final recursor must manually align
  Identity endpoints.  Before assembling that recursor, the complete formation
  closure must be normalized from its current “ordinary output or Identity”
  presentation to explicit Base/Unit/Pi/Sigma/Identity constructors so that an
  Identity formation may itself occur recursively inside a later Pi or Sigma.
  That normalization is now checked as `RecursivelyGenerated`.  Its five
  constructors are exactly Base, Unit, Pi, Sigma, and Identity; Pi and Sigma
  consume recursively generated children, so nested Identity types are no
  longer excluded.  Structural agreement covers all five matching cases using
  the scoped Pi/Sigma and generated-Identity laws, and both provenance and
  agreement transport across readiness witnesses.  The corresponding
  `RecursivelyGeneratedFormationFoldOutput` package is now the formation motive
  for the final recursor.  The next step is to replace the typing package's
  temporary complete-formation field with this recursive-normal-form package.
  The typing motive now uses that normal form directly as
  `RecursivelyGeneratedAnchoredTypingFoldOutput`.  Ordinary generated formation
  evidence converts structurally to recursive evidence, so the existing seven
  non-Refl typing package builders are reusable without semantic reconstruction.
  New recursive-normal-form Identity and Refl handlers align endpoint packages
  with `RecursivelyGenerated.agreementAcrossReady`, preserve retarget
  provenance, and return recursive formation packages.  Consequently nested
  Identity formations remain closed through both the formation and typing
  motives; the two motive types needed by the final recursor are now available.
  Final-motive handlers now directly cover formation Base, Unit, Pi, and Sigma
  plus typing Variable, Unit, and Lambda.  Pi/Sigma compose recursive-normal-form
  child packages, and Lambda returns a recursive Pi formation while retaining
  the body's typing provenance.  These seven handlers no longer pass through
  the temporary generated/complete packages.  The remaining recursor handlers
  are Identity, Apply, Pair, First, Second, and Refl; the exact/general Identity
  and Refl implementations already exist, while the four dependent typing
  handlers require only the established recursive agreement alignment pattern.
  Those four handlers are now ported.  Apply aligns its function and argument
  to recursive Pi/domain outputs; Pair aligns both components to recursive
  domain/result outputs; First and Second align their pair to a recursive Sigma
  output.  Scoped retarget provenance and instantiate agreement are retained.
  Together with recursive Identity and Refl, all 13 final-motive handlers are
  checked.  The remaining construction is wiring them into the mutual readiness
  recursor and projecting the anchored dispatcher and witness.
  That construction is now complete.  `recursivelyGeneratedFormationFold` and
  `recursivelyGeneratedTypingFold` supply all 13 handlers to the two projections
  of the mutual readiness recursor.  The typing projection is finally aligned
  with the independently computed formation projection using recursive
  generated agreement, producing `providerFreeAnchoredMutualFoldDispatcher`.
  `providerFreeMutualFoldWitness` directly inhabits the public witness type and
  the corresponding `Nonempty` theorem requires no old path provider.  Its
  existing `.lawful` and `.strict` projections therefore yield canonical lawful
  and strict substitution preservation from the five scoped hypotheses alone.
  The former `...OfPathProvider` bridge remains only as compatibility evidence;
  it is no longer the only inhabitant construction.
  Client-facing preservation entry points now expose this construction directly.
  `providerFreeCanonicalLawfulPreservation` returns the lawful mutual fold,
  `providerFreeCanonicalStrictPreservation` returns the strict substitution
  dispatcher, and `providerFreeCanonicalPreservation_pathAgreement` states the
  formation/typing coherence theorem for arbitrary coherent derivations.  None
  of these APIs accepts or reconstructs the former unrestricted path provider.
  `IncDepRawProviderFreeLawfulSubstitutionFiberModel` now packages a semantic
  model with exactly those five scoped laws.  Its `.witness`,
  `.lawfulPreservation`, `.strictPreservation`, and `.pathAgreement` projections
  make the final theorem available without repeatedly threading the hypotheses.
  The Unit-base model is not declared lawful merely because its primitive base
  carrier is `ULift Unit`: dependent Pi/Sigma/Identity families introduce
  function and dependent-pair semantics whose naturality still requires proof.
  A concrete inhabitant must discharge those five fields rather than relying on
  an unsound blanket subsingleton assumption.
  The five-field record is now split along the actual reuse boundary.
  `ProviderFreeNaturalityLaws` contains only the three new obligations:
  instantiate agreement, dependent Pi/Sigma agreement, and generated Identity
  agreement.  `ProviderFreeMutualFoldHypotheses.ofPreservation` reuses variable
  replacement and readiness alignment from the established canonical
  preservation hypotheses, while `toPreservationCore` provides the reverse core
  projection when a rebase law is available.  Existing lawful models can be
  upgraded with `.toProviderFree` by supplying only this three-law naturality
  fragment.  Concrete-model work is therefore no longer counted as five
  independent proofs.
  The three-law fragment is also split into separately checkable model
  components: `InstantiateNaturalModel`, `DependentFormationNaturalModel`, and
  `GeneratedIdentityNaturalModel`.  `NaturalityLaws.ofComponents` assembles them,
  and the inverse component projections are provided.  This split is semantically
  necessary: expanding canonical Pi/Sigma shows that the codomain fold runs on
  an extended context tree built from the domain's full formation result, while
  child fold agreement equates only canonical outputs.  Hence Pi/Sigma
  naturality is not derivable generically from the present child agreement and
  must be proved by a model law (or by strengthening the agreement invariant).
  A first strengthening is now formalized as
  `StrongFormationFoldAgreement`, which equates the complete canonical dispatch
  package and projects canonically to the existing weak agreement.  This still
  does not make Pi/Sigma congruence automatic: eliminating the domain package
  equality leaves dependent index equations for the extended tree and lifted
  replacements.  Lean correctly rejects plain equality elimination there.
  Therefore a successful generic derivation would need a heterogeneous/
  transport-coherent invariant (or explicit model coherence), not merely a
  stronger homogeneous equality of returned packages.
  `HeterogeneousFormationFoldAgreement` now formalizes the HEq layer and has
  checked bridges from strong agreement and back to strong/weak agreement at a
  common readiness index.  Testing Pi congruence against this layer shows that
  HEq of returned packages alone is still insufficient: the codomain agreement
  must relate evaluations at a pair of extended trees/replacements connected by
  the domain transport, rather than quantify only over one definitionally shared
  input.  The next generic invariant must therefore be relational in its inputs,
  not merely heterogeneous in its outputs.
  `RelationalFormationFoldAgreement` now implements that input-relational
  shape.  It compares two evaluations with independently indexed source/target
  semantic results, substitution results, context trees, and replacement
  packages, requiring HEq evidence at every layer before relating the outputs.
  Reflexivity and the diagonal projection to heterogeneous output agreement are
  checked.  The extra HEq premises for semantic context and substitution results
  are essential: tree/replacement HEq alone does not allow dependent elimination
  because their type families need not be injective.  This relation is now the
  candidate invariant for a generic Pi/Sigma congruence proof.
  `DependentAssemblyCoherenceProvider` now states the corresponding constructor
  law at exactly this relational level: Pi and Sigma must preserve relational
  agreement through context extension.  Its checked `piWeak` and `sigmaWeak`
  bridges recover the existing canonical formation agreement by diagonalizing
  the relational result through HEq/strong equality.  This separates two tasks
  cleanly: recursive certificates should produce relational child agreement,
  while a model proves only that its dependent constructors preserve it.
  Ordinary generated formation certificates now produce this relational
  agreement recursively.  Base and Unit use relational reflexivity; Pi and
  Sigma invoke the assembly-coherence laws on recursively obtained child
  relations.  `Generated.agreementOfAssembly` then diagonalizes the result back
  to the public weak agreement without the old dependent-formation provider.
  `DependentAssemblyNaturalModel` exposes this stronger model component beside
  the legacy weak component.  The remaining closure step is the corresponding
  relational law for generated Identity, after which recursively generated
  formations can use the stronger route at arbitrary depth.
  That Identity closure is now checked.
  `GeneratedIdentityAssemblyCoherenceProvider` states relational preservation
  for two generated Identity formations and projects to the legacy weak Identity
  law.  `RecursivelyGenerated.relationalAgreement` combines it with dependent
  assembly coherence over all five formation constructors, including nested
  Identity under Pi/Sigma; `agreementOfAssembly` recovers the public weak result.
  `GeneratedIdentityAssemblyNaturalModel` exposes the stronger Identity component.
  Thus the recursive agreement layer no longer intrinsically needs the two weak
  dependent/Identity providers; migrating the final dispatcher to these stronger
  assembly components is now an API rewiring task.
  The readiness-crossing version of this assembly-only agreement is now checked
  as `agreementAcrossReadyOfAssembly`.  Strong inputs are collected in
  `ProviderFreeAssemblyNaturalityLaws` and
  `ProviderFreeAssemblyHypotheses`: variable/readiness are reused from existing
  preservation, while the naturality fragment contains instantiate agreement,
  dependent assembly coherence, and generated Identity assembly coherence.
  These records contain neither legacy weak dependent/Identity providers nor an
  unrestricted path provider.  They are now the target inputs for the alternate
  final dispatcher.
  `RecursiveGeneratedAgreementProvider` now abstracts the single alignment
  operation actually consumed by recursive typing handlers.  `ofWeak` implements
  it from the legacy dependent/Identity laws, while `ofAssembly` implements the
  same service from relational assembly laws.  Both handle readiness transport
  internally.  Refactoring handlers to consume this service will switch the
  final dispatcher to the strong route without duplicating the six handlers that
  align recursive formation outputs.
  Identity and Refl now consume this agreement service directly.  The existing
  weak-law recursor is preserved by constructing `ofWeak` at its handler sites,
  so the refactor changes no public behavior while removing direct weak-provider
  coupling from those two handlers.  Apply, Pair, First, and Second remain to be
  switched to the same service before an assembly-only recursor can reuse the
  full handler set.
  That handler refactor is now complete.  Apply, Pair, First, and Second join
  Identity/Refl in consuming only `RecursiveGeneratedAgreementProvider`; every
  weak-law recursor call site explicitly supplies `ofWeak`.  No final-motive
  handler mentions the legacy dependent-formation or generated-Identity weak
  provider types anymore.  The assembly-only dispatcher can therefore reuse all
  13 handlers by supplying `ofAssembly`; only the recursor input bundle/wiring
  remains.
  `RecursiveFoldInputs` now provides that common bundle: variable replacement,
  readiness alignment, instantiate agreement, and the abstract recursive
  agreement service.  `RecursiveFoldInputs.ofWeak` and `.ofAssembly` normalize
  the two public hypothesis families into exactly the same internal type.  The
  recursor body can now be defined once with no knowledge of whether alignment
  came from legacy weak laws or relational assembly coherence.
  The common formation projection is now implemented as
  `recursivelyGeneratedFormationFoldOfInputs`, supplying all 13 shared handlers
  to the readiness recursor through `RecursiveFoldInputs`.  The
  `...FormationFoldOfAssembly` wrapper proves that assembly-only hypotheses can
  already construct the full recursive formation fold without any weak-law
  record.  The matching common typing projection is the remaining half before
  the assembly-only anchored dispatcher can be exposed.
  The common typing projection and assembly wrapper are now checked as
  `recursivelyGeneratedTypingFoldOfInputs` and `...OfAssembly`.  Together with
  the common formation projection they construct
  `assemblyAnchoredMutualFoldDispatcher`, including the final independent
  formation/typing alignment through the assembly agreement service.
  `AssemblyMutualFoldWitness` is directly inhabited and has lawful and strict
  projections.  The alternate strong route is therefore end-to-end: it uses no
  legacy weak dependent/Identity provider and no unrestricted path provider.
  `IncDepRawAssemblyLawfulSubstitutionFiberModel` now packages a semantic model
  with these strong assembly hypotheses.  Its witness, lawful preservation,
  strict preservation, and path-agreement projections are checked.  An existing
  `IncDepRawLawfulSubstitutionFiberModel` upgrades through `.toAssemblyLawful`
  after supplying only the three strong naturality laws.  This is the concrete
  model completion target for the strong route.
  Strong naturality is now fully componentized as well.
  `ProviderFreeAssemblyNaturalityLaws.ofComponents` assembles the independently
  proved instantiate, dependent-assembly, and Identity-assembly model laws; the
  three inverse projections and checked round-trip theorems preserve each
  component definitionally.  `AssemblyLawfulSubstitutionFiberModel.ofComponents`
  combines those pieces with the existing preservation core in one call.  A
  concrete model can therefore land each law separately and becomes fully
  usable immediately when the third component is supplied.
  Concrete-law development can now be staged explicitly.  `Stage1` stores the
  established preservation core plus instantiate naturality; `.withDependent`
  adds dependent assembly coherence as `Stage2`; `.complete` accepts generated
  Identity assembly coherence and returns the full assembly-lawful model.  This
  makes partial concrete-model progress a typed artifact rather than an
  all-or-nothing record construction.
  Instantiation now has a relational form too:
  `InstantiateAssemblyCoherenceProvider` relates the result formation fold to
  the canonical instantiate motive in heterogeneous environments and projects
  to the legacy weak instantiate provider.  `ProviderFreeRelationalNaturalityLaws`
  collects relational instantiate, dependent-constructor, and Identity laws at
  one transport-coherent level; `.toAssembly` performs the sole weak
  diagonalization needed by the existing typing constructors.
  `AssemblyHypotheses.ofRelational` and
  `AssemblyLawfulSubstitutionFiberModel.ofRelational` expose the end-to-end path
  from this uniform strong law bundle.
  The uniform relational bundle is now componentized without falling back to
  weak instantiate types.  `InstantiateAssemblyNaturalModel`, the existing
  dependent/Identity assembly components, and
  `RelationalNaturalityLaws.ofComponents` provide assembly/projection APIs.
  `RelationalStage1` stores preservation plus relational instantiate coherence,
  `.withDependent` forms `RelationalStage2`, and `.complete` adds Identity
  assembly coherence and produces the assembly-lawful model.  A concrete model
  can therefore be developed end to end without ever constructing a legacy weak
  naturality record.
  The type-formation half of that recursive fold now has compositional builders.
  Base types become constant contextual families supplied by a base model, unit
  becomes the lifted unit family, Pi and Sigma combine domain and codomain results
  across semantic context extension, and identity formation combines an
  interpreted type with two semantic terms.  All five raw formation constructors
  therefore have checked targets in the contextual calculus; lookup and term
  recursion remain before the builders can be assembled automatically.
  The term-typing half now has matching compositional builders.  A typing result
  is indexed by its raw derivation, interpreted context, and semantic contextual
  type.  Builders map unit, lambda/application, dependent pairing, both Sigma
  projections, and reflexivity directly to the corresponding semantic operators;
  the application, pair-second, and second-projection results retain their true
  dependent fibers.  A variable builder consumes an interpreted lookup term.
  Thus every term constructor has a checked semantic target, leaving recursive
  lookup interpretation as the core missing piece of the automatic fold.
  Lookup interpretation is now represented recursively as well.  The newest
  variable is interpreted by the semantic extension variable at the reindexed
  head family; an older variable reindexes its tail lookup type and substitutes
  its tail semantic term along the extension projection.  The resulting lookup
  certificate converts directly to the variable typing-result builder.  This
  handles arbitrary de Bruijn depth without flattening dependent types.  What
  remains for the automatic fold is coordinating context/type/term proof indices
  in one mutual recursion, rather than defining any missing constructor case.
  That proof-index requirement is now represented explicitly by deep typing
  certification.  It mirrors every typing rule and records formation evidence
  for all hidden intermediate domains and codomains, recursively certifying each
  subderivation.  `IncDepRawDeepCertifiedTyping` combines this evidence with the
  previously certified context, result type, and root typing.  The dependent
  Pi/reflexivity and Sigma/pair examples are deeply certified.  This supplies the
  intermediate formation data that application and projection branches of the
  mutual semantic fold could not recover from root certification alone.
  Semantic contexts now retain their constructor history in a dependent tree:
  the empty node records the empty semantic context, while each extension stores
  the tail tree and the interpreted head formation.  Structural recursion over
  this tree implements lookup interpretation automatically.  The empty case is
  impossible, the newest case returns the semantic extension variable, and the
  older case recursively interprets the tail lookup before projection reindexing.
  Arbitrary-depth variables therefore no longer require a manually supplied
  semantic term; the remaining fold work is coordinating formation and typing
  recursion around this context tree.
  Formation and typing are now also equipped with mutually recursive semantic-
  readiness evidence.  Formation readiness descends through base/unit/Pi/Sigma
  and, for identity types, recursively carries readiness of both endpoint typing
  derivations.  Typing readiness mirrors every term rule and its subderivations.
  The dependent Pi/reflexivity and Sigma/pair examples have complete formation
  and typing readiness trees.  This supplies a structurally decreasing mutual
  recursion domain for identity formation, where the earlier one-directional
  deep-typing evidence alone could not interpret endpoint terms.
  The context-tree lookup fold is validated beyond the newest-variable case by
  a two-variable unit telescope.  Both context extensions and their formation
  results are built through the general APIs.  Automatic interpretation of the
  newest lookup evaluates definitionally to `assignment.2`; interpretation of
  the older lookup evaluates to `assignment.1.2`.  This is a nontrivial check
  that recursive projection/reindexing follows de Bruijn depth correctly rather
  than accidentally returning the newest value at every level.
  Semantic readiness is being tightened from mere termination evidence to a
  coherent fold index.  Variable nodes now carry readiness of their looked-up
  type formation, and reflexivity nodes carry readiness of the underlying type
  formation in addition to the endpoint term.  The existing Pi and Sigma trees
  were reconstructed with these stronger constructors.  The fold can therefore
  recover the semantic type of variables and reflexivity without guessing it
  from an independently produced term result.
  The remaining typing-readiness branches now carry the same coherence data.
  Lambda stores codomain formation readiness; application, dependent pairing,
  and both projections store readiness for their hidden domain and codomain
  formations.  Named, shared readiness proofs for the unit variable and its
  identity codomain keep proof indices identical across the Pi and Sigma example
  trees.  Every typing branch can now locally reconstruct the semantic Pi/Sigma
  formation it consumes instead of relying on an unrelated external result.
  The strengthened branches are instantiated on actual dependent redexes:
  readiness trees are checked for applying the dependent reflexivity function
  and for both projections of the dependent Sigma pair.  These examples exercise
  the hidden domain/codomain readiness carried by application, first projection,
  and second projection, rather than validating only lambda and pair formation.
  Semantic readiness now folds back to ordinary deep well-formedness for every
  typing branch.  The forgetful structural recursion extracts all variable,
  binder, hidden-domain/codomain, pair/projection, and reflexivity formation
  evidence.  A generic constructor combines any certified judgment and its
  readiness tree into a deep-certified judgment.  This proves inside Lean that
  the stronger semantic index is coherent with, and strictly supplies, the
  previously required intermediate well-formedness data.
  The first executable branches of the semantic typing fold are now exposed on
  context trees.  `interpretVariable` turns any lookup directly into a typing-
  indexed semantic result via recursive lookup interpretation, and
  `interpretUnit` produces the unit typing result in any interpreted context.
  On the two-variable telescope, both newest and older variable typing results
  are generated automatically and evaluate to `assignment.2` and
  `assignment.1.2`; a unit result is generated in the same open context.
  Composite fold paths now execute too.  For dependent Pi, the implementation
  chains context extension, variable interpretation, reflexivity, lambda, and
  application builders; the resulting application is definitionally semantic
  reflexivity.  For dependent Sigma, unit and the correctly indexed reflexivity
  fiber feed the pair builder, then both projection builders; their results are
  definitionally unit and reflexivity.  Thus every non-atomic term builder is
  exercised in an end-to-end typed semantic construction, including dependent
  fiber index alignment.
  A general return type for the readiness-driven typing fold is now fixed.
  `IncDepRawReadyTypingSemanticResult` binds one semantic-readiness derivation to
  one semantic context tree and packages the inferred contextual type with the
  typing-indexed semantic result.  Certificates are constructed for the
  dependent Pi function, its application, the dependent Sigma pair, and both
  projections.  The recursive fold can now target a checked dependent sigma
  result rather than an informal existential specification.
  The ready-result constructor algebra now directly implements variable, unit,
  reflexivity, and lambda branches.  Variable consumes the context-tree lookup
  fold; unit is context-polymorphic; reflexivity builds contextual identity from
  its child certificate.  Lambda consumes an interpreted domain, extends the
  context tree, and uses the body's inferred dependent semantic type as the Pi
  codomain.  These are generic constructors over arbitrary telescopes, not only
  packages of the closed examples.
  The ready-result algebra now also implements application, dependent pairing,
  and both projections.  These constructors consume shape-indexed Pi/Sigma child
  results plus the domain/codomain readiness carried by their raw branches, and
  return correctly instantiated dependent fibers.  Together with variable,
  unit, reflexivity, and lambda, every typing-readiness constructor now has a
  generic semantic-result constructor over arbitrary context trees.
  The algebra's computation soundness is now generic as well.  For arbitrary
  interpreted contexts, dependent domains/codomains, body and argument results,
  applying a semantic lambda is definitionally the body in the extended
  assignment.  For arbitrary dependent pair components, first and second
  projection are definitionally the corresponding semantic components.  These
  Pi and both Sigma beta theorems no longer depend on the closed unit examples.
  Multi-step soundness is now evaluator-parametric.  For any carrier and any raw
  term evaluator, a proof that each one-step reduction maps to equality lifts by
  induction to all multi-step reductions and to the full reflexive/symmetric/
  transitive definitional equality.  The canonical computation quotient is
  re-established as one instance.  The future contextual interpreter therefore
  only needs to discharge primitive one-step soundness; the closure theorem is
  already generic.
  This contract is packaged as `IncDepRawSoundEvaluator`, bundling a carrier,
  evaluation map, and primitive one-step soundness.  Multi-step and definitional-
  equality soundness are reusable methods of every such model.  The canonical
  computation quotient instantiates the interface and its evaluator is proved
  definitionally equal to the existing quotient map.  A contextual interpreter
  can therefore become a sound model by supplying exactly these interface fields.
  Generic contextual laws now extend beyond beta: every Pi-typed semantic result
  satisfies eta, every Sigma-typed result is definitionally equal to the pair of
  its projections, and identity J applied to interpreted reflexivity satisfies
  its beta rule for arbitrary dependent motives.  Pi, Sigma, and identity thus
  expose their principal beta/eta/elimination equations uniformly on typing-
  indexed semantic results in arbitrary interpreted contexts.
  The recursive interpreter's missing invariant is now represented explicitly by
  `IncDepRawTypingFormationSemanticResult`: the formation interpretation of a raw
  type and the typing interpretation of a term are packaged over literally the
  same semantic family.  `align` isolates the exact semantic-type equality needed
  at a recursive boundary, while certified Unit and reflexivity constructors
  preserve the invariant without an unchecked cast.  The remaining composite
  branches must prove that raw instantiation/renaming agrees with semantic
  reindexing; that substitution-coherence theorem, rather than structural
  recursion itself, is now the precise blocker for the total dispatcher.
  Semantic instantiation itself is now canonical: `Substitution.instantiate`
  extends the identity environment by an interpreted argument, with checked
  projection and variable equations, and `instantiateFiber` reindexes dependent
  types and terms along that substitution.  Application, dependent pairing, and
  second projection builders all use this one normal form instead of separate
  anonymous fiber functions.  Thus every composite typing branch now exposes the
  exact semantic operation that the raw `Type.instantiate` substitution theorem
  must commute with.
  General substitutions now cross the same bridge.  An
  `IncDepRawSubstitutionSemanticResult` indexes a semantic assignment map by its
  raw substitution and by interpreted source and target contexts.  Identity and
  binder lift are constructed; lift consumes exactly the domain-family coherence
  equality and transports the newest value along it.  Its projection and newest-
  variable computation laws are checked, providing the two lookup cases required
  by a substitution-coherence induction.  What remains is to lift these local
  equations through every formation and typing constructor.
  Formation-level substitution coherence now has its own dependent result type,
  `IncDepRawFormationSubstitutionSemanticResult`, retaining the target formation,
  its raw-substituted source formation, both semantic interpretations, and their
  reindexing equation.  Base families and Unit close this result directly.  The
  attempted dependent-Pi composition also sharpens the next invariant: equality
  of domain families alone does not determine the transport used by a dependent
  codomain in intensional Lean.  Composite coherence must therefore retain an
  explicit fiber transport (and its computation law), not merely a family
  equality; no univalence or unchecked equality axiom is assumed.
  That transport layer is now formalized by `IncFiberEquiv` and
  `IncTypeInContext.FiberEquiv`.  It carries forward/backward maps with both
  inverse laws pointwise, supports reflexivity, symmetry, composition and
  reindexing, and transports semantic terms with checked round-trip equations.
  Existing formation-substitution equalities embed into this stronger interface,
  so subsequent Pi/Sigma coherence can consume explicit fiber maps rather than
  attempting invalid dependent rewriting.
  Dependent function transport is now explicit as well.
  `IncDependentFiberEquiv` relates each source codomain fiber to the target fiber
  over the forwarded domain value; `piForward` and `piBackward` transport
  dependent functions in both directions.  Forward transport sends a target
  argument backward, transports the result fiber, then uses the domain inverse
  law to land in the requested target fiber.  Both application equations are
  checked definitionally, establishing the operational core needed by the Pi
  formation and lambda/application coherence branches.
  The same dependent equivalence now transports Sigma pairs.  `sigmaForward`
  maps the first component and then its dependent second fiber;
  `sigmaBackward` reverses the first component and uses the domain inverse law
  before reversing the second fiber.  The forward pair equation is checked
  definitionally, supplying the constructive core for dependent pair and
  projection coherence without collapsing indices.
  First projection commutes definitionally with this transport.
  The dependent second projection likewise computes to the corresponding
  codomain-fiber forward map, so both Sigma eliminators now have checked
  transport equations.
  Identity coherence has started at the fiber level: an equivalence maps equality
  witnesses by congruence of its forward map, and mapped reflexivity computes to
  reflexivity definitionally.  This is the introduction/computation core for the
  forthcoming Id formation and J coherence branch.
  Equality witnesses now transport backward as well, with the corresponding
  reflexivity computation rule, completing the bidirectional identity-fiber API.
  Forward equality transport also preserves transitive composition, giving the
  path-composition law needed by iterated identity elimination.
  It also preserves path reversal, so reflexivity, composition, and symmetry are
  all respected by identity transport.
  Backward transport now preserves composition and reversal too, making the
  identity groupoid laws symmetric in both directions.
  These path maps are now lifted to the actual `IncIdentityType` representation,
  `ULift (PLift equality)`, in both directions.  Both lifted reflexivity equations
  compute definitionally, connecting the abstract groupoid API to semantic Id
  witnesses used by the interpreter.
  The lifted maps now act on contextual identity terms through
  `IncIdentityTerm.map` and `mapBackward`.  Both preserve reflexivity
  definitionally, and `J_map_refl` proves that eliminating a transported
  reflexivity witness computes to the target reflexivity case.  Thus the
  fiber-equivalence layer is connected to the semantic Id introduction and J
  computation rules; general motive transport for arbitrary witnesses remains
  part of the composite Id substitution-coherence branch.
  That arbitrary-witness step is now explicit as `IncIdentityJMap`: it packages
  a map between source and target motives together with preservation of the
  reflexivity case.  `IncIdentityJMap.eliminate` proves the pointwise path-
  induction law, and `IncIdentityTerm.J_map` lifts it to contextual terms,
  showing that J commutes with transported identity witnesses.  The remaining
  Id bridge is to construct this motive map recursively in the raw formation/
  substitution interpreter, rather than postulate it as branch input.
  The raw Id-formation branch now has its explicit transport invariant.
  `IncIdentityType.fiberEquivalence` builds an equivalence between identity
  families from a base-family equivalence plus coherence of both endpoints;
  its forward computation maps the source path and composes the two endpoint
  equations.  `IncDepRawIdentityFormationSubstitutionFiberResult` packages the
  underlying raw type result, all four endpoint interpretations, and their two
  substitution equations, and derives the substituted Id-family equivalence.
  This removes the Id composite branch's former dependence on literal family
  equality.  The remaining recursive step is producing the two endpoint
  equations from typing-substitution coherence automatically.
  Formation substitution now also has a uniform explicit interface,
  `IncDepRawFormationSubstitutionFiberResult`; equality-based results embed into
  it, while the Id branch constructs it directly.  The parallel
  `IncDepRawTypingSubstitutionFiberResult` carries target/source term
  interpretations and their transport equation.  Two such typing results build
  the Id-formation endpoint package automatically.  Unit closes the first
  typing branch definitionally, and the refl branch now recursively derives its
  Id formation and proves transported-reflexivity coherence (using proof
  irrelevance only for equality witnesses).  Variable, Pi/Sigma introduction
  and elimination branches remain to complete the typing-substitution fold.
  The variable branch now has a correctly substitution-aware invariant:
  `IncDepRawVariableSubstitutionFiberResult` relates the target lookup variable
  not to another lookup, but to the semantic interpretation of the arbitrary
  source replacement certified by `substitution.preserves lookup`.  It stores
  their fiber-transport equation and converts directly to the uniform typing
  result.  This distinction is essential because a general substitution may
  replace a variable by any well-typed term.  The remaining lookup recursion is
  to generate this result for identity and for the newest/older cases of lifted
  substitutions, using the existing lift projection/variable equations.
  The equality-to-fiber boundary used by the newest lookup case is now checked:
  `FiberEquiv.ofEq_forward` and `ofEq_transport_apply` prove that explicit
  forward transport is exactly `Eq.mp (congrFun coherence assignment)`.
  `lift_variable_fiber` then rewrites the existing lifted-substitution variable
  law into that fiber-forward form.  Consequently the newest-variable value
  equation is closed without an unchecked cast; packaging its reindexed lookup
  formation, followed by the recursive older-variable case, remains.
  Fiber transport is now natural under every context substitution:
  `FiberEquiv.reindex_transport` proves that transporting a substituted term is
  definitionally the same as substituting a transported term.
  `lift_older_transport` combines this law, the prior term-coherence equation,
  and the lifted projection equation to prove the binder-weakened older-term
  equation.  Thus both newest and older lookup cases now have checked term-level
  transport laws; only their raw lookup-formation result packaging remains
  before the variable branch can be inserted into the automatic fold.
  The missing lookup-formation package is now explicit as
  `IncDepRawReadyVariableFormationSemanticResult`.  It retains the semantic
  interpretation of the variable's raw type and an equality aligning that
  family with the context tree's lookup family.  Its `toTypingFormation`
  conversion produces a formation and variable typing over literally the same
  semantic type, while `variableAligned` exposes that aligned result through
  the existing readiness API.  The remaining automation task is recursively
  constructing this alignment for the context tree's newest/older cases, then
  feeding it to the variable-substitution result already established above.
  Binder weakening is now available uniformly for both semantic formations and
  typings.  `IncDepRawFormationSemanticResult.weaken` interprets raw weakening
  by identity-renaming into an extended context as semantic reindexing along
  the context projection.  `IncDepRawTypingSemanticResult.weaken` performs the
  corresponding operation on terms, with both computation equations checked
  definitionally.  This is the shared missing constructor for the older lookup
  alignment and for subsequent Pi/Sigma binder recursion; readiness preservation
  under this rename is the next proof-index layer to connect.
  Readiness renaming now closes its atomic cases: `renameBase`, formation
  `renameUnit`, and typing `renameUnit` construct renamed witnesses directly.
  Auditing the full mutual recursion exposed the exact composite obstruction:
  application, pairing, and second projection carry proof indices transported
  by `instantiate_rename`, so the renamed derivations are propositionally rather
  than definitionally the corresponding constructor derivations.  The remaining
  readiness layer must retain those index equalities explicitly, together with
  a mutual termination measure, before the Pi/Sigma/Id cases can be assembled.
  The rename interface has now been refactored to avoid demanding equality of
  derivation objects.  `IncDepRawFormationRenamedReadyResult` and
  `IncDepRawTypingRenamedReadyResult` existentially retain a derivation of the
  renamed raw judgment together with its readiness witness.  Atomic Base/Unit
  constructors inhabit these results, and formation Pi/Sigma composition now
  closes using the lifted renaming.  This absorbs harmless derivation-choice
  differences while preserving the exact renamed term/type indices.  Typing
  Pi/Sigma/Id constructors still need explicit handling of their
  `instantiate_rename` type equalities.
  The derivation-independent API now also closes variable readiness, identity
  formation, lambda typing, first projection, and reflexivity typing.  These
  constructors compose the renamed child derivations directly and retain their
  readiness evidence.  Of the eight typing-readiness constructors, only the
  three genuinely index-transporting cases—application, dependent pairing, and
  second projection—remain; the other five now rename without any derivation
  equality assumption.
  Application readiness now handles its non-definitional result index.  The
  renamed application derivation and its readiness witness are first packed as
  a dependent `Sigma`, then transported together along
  `IncDepRawType.instantiate_rename`.  This preserves their dependency while
  producing the canonical renamed application judgment.  Six of eight typing
  branches are now closed; dependent pairing and second projection remain and
  use the same dependent-package technique in the opposite rewrite directions.
  Those final two branches are now closed.  Dependent pairing transports the
  renamed second component and its readiness witness forward along
  `instantiate_rename` before constructing the pair.  Second projection packs
  the projected derivation and readiness, simplifies term renaming under
  `first`, and transports the package backward to the canonical instantiated
  result type.  Therefore all eight typing-readiness constructors and all five
  formation-readiness constructors now have proof-index-independent rename
  combinators.  What remains is assembling these combinators into the total
  mutual recursive dispatcher and then connecting it to lookup substitution.
  The total mutual dispatcher is now complete.  The two `renameResult`
  functions use direct constructor pattern matching on formation and typing
  readiness, allowing Lean's structural equation compiler to recognize every
  recursive call across the mutual inductives.  They dispatch all 5 formation
  and all 8 typing cases to the checked combinators above, with no partial
  definition, custom termination axiom, or unchecked cast.  The remaining
  bridge is now specifically lookup-substitution recursion and its semantic
  alignment, rather than readiness renaming itself.
  The dispatcher is now specialized to binder extension by formation and typing
  `weakenResult`.  Each chooses identity renaming followed by target weakening
  and returns the corresponding renamed-readiness package for an arbitrary
  readiness tree.  The older lookup branch can therefore reuse the total
  dispatcher instead of reproducing constructor recursion; its remaining work
  is only to align this raw weakened result with the semantic projection result.
  That alignment is now constructed for both formations and typings by the
  renamed-result `weakenSemantic` operations.  They retain whichever renamed
  derivation the total dispatcher selected while interpreting its family by
  projection reindexing and its term by projection substitution.  The term
  computation equation is definitional.  Thus semantic weakening no longer
  depends on equality with the canonical proof object; the remaining older
  lookup step is to package this aligned result with the lookup recursion itself.
  The lookup recursion now has both alignment constructors.
  `IncDepRawReadyVariableFormationSemanticResult.here` weakens the head
  formation into its own extended context and closes the newest-variable
  alignment definitionally.  `there` reuses the total readiness weakening and
  semantic weakening of the tail formation, then preserves its lookup equality
  by projection reindexing.  Thus newest and older raw lookup formations are now
  recursively aligned with the context tree; the next step is combining this
  result with substitution-preserved replacement typings.
  That composition now has a checked constructor,
  `toVariableSubstitution`.  It obtains the target variable interpretation from
  the aligned lookup package, explicitly aligns the independently produced
  target formation interpretation, and combines it with the semantic source
  replacement certified by `substitution.preserves lookup`.  The resulting
  `IncDepRawVariableSubstitutionFiberResult` feeds the uniform typing result via
  `toTyping`; lookup substitution recursion now needs to supply only the source
  replacement interpretation and its final transport equation.
  Source replacements are now collected by
  `IncDepRawSubstitutionReplacementSemanticResult`, a dependent semantic
  environment assigning every target lookup the semantic type and typing result
  of the source term certified by `substitution.preserves`.  Its accessors expose
  both components, and `typingResultAligned` transports a replacement result to
  the source family selected by formation-substitution recursion.  This fixes
  the output shape for recursive replacement interpretation; identity/lift
  constructors for the environment and the final variable equation remain.
  The identity replacement environment is now constructed from a context
  semantic tree.  Every lookup is interpreted by the tree and its semantic
  type/term is assigned to the corresponding proof produced by raw identity
  substitution.  `identity_term` checks definitionally that the environment's
  replacement is exactly the context lookup term.  The remaining environment
  constructor is binder lift, split into newest and older lookup cases.
  Binder lift is now implemented for the replacement environment.  The newest
  lookup is interpreted as the extended source-context variable over the
  substituted domain; an older lookup reindexes its previous replacement type
  and substitutes its previous replacement term along the source projection.
  `lift_here_term` verifies the newest computation rule definitionally.  Identity
  and lift constructors are therefore both available; the remaining variable
  work is the final fiber-transport equation connecting this environment to the
  target lookup interpretation.
  The older replacement computation rule is now exported as
  `lift_there_term`: looking up an older variable in the lifted environment is
  definitionally the previous replacement term substituted along the source
  projection.  Together with `lift_here_term`, both environment branches now
  expose the exact normal forms required by `lift_variable_fiber` and
  `lift_older_transport`.  The next step is packaging those two existing
  equations into the final variable-coherence recursion.
  The final newest-variable equation is now proved as `lift_here_fiber`.
  Evaluating the lifted replacement environment's `here` term and applying the
  domain equality's explicit fiber forward map yields exactly the target
  extended variable evaluated under the lifted semantic substitution.  This
  completes the newest variable branch end-to-end; only the recursive older
  branch must now combine `lift_there_term` with `lift_older_transport`.
  The recursive older equation is now closed as `lift_there_fiber`.  Given the
  previous replacement/target-term coherence, it reindexes the family
  equivalence along the source projection and proves that the lifted
  environment's older replacement agrees with the target older term under the
  lifted semantic substitution.  Together with `lift_here_fiber`, both final
  variable-coherence branches are checked; the next task is assembling them
  with lookup formation alignment into the variable branch of the total
  substitution dispatcher.
  The variable branch now has a single integration constructor,
  `toTypingSubstitution`.  It combines the aligned target lookup formation, the
  formation-substitution fiber result, the replacement environment, explicit
  source/target family alignments, and the final term equation, then returns the
  uniform `IncDepRawTypingSubstitutionFiberResult` directly.  Intermediate casts
  and variable packages are hidden inside the checked API.  The remaining total
  dispatcher work is to recursively supply these formation results and
  equations for each typing constructor.
  Auditing the Pi formation branch identified a sharper invariant boundary.
  Pointwise `IncDependentFiberEquiv` alone does not imply that `piForward` and
  `piBackward` are inverse: transporting across the domain inverse changes the
  source index, and coherence between the codomain equivalences at those two
  indices is additional data.  `IncDependentPiFiberEquiv` now records both Pi
  round-trip laws explicitly and `toFiberEquiv` produces the resulting function-
  space equivalence.  Pi formation substitution must recursively construct this
  stronger coherence rather than assume pointwise fiber maps suffice.
  This stronger Pi invariant is now lifted to contextual families by
  `IncDependentPiTypeInContextFiberEquiv`.  It stores a coherent dependent Pi
  equivalence at every context assignment, using the pointwise domain fiber
  equivalence and the two codomain families.  `piFiberEquivalence` converts it
  into an `IncTypeInContext.FiberEquiv` between the corresponding `IncPiType`
  families.  Raw Pi formation substitution now consumes the recursive domain
  result, both codomain interpretations, and a coherent
  `IncDependentPiFiberEquiv` at every source assignment.
  `IncDepRawPiFormationSubstitutionFiberResult` packages these data and
  `toFormationFiberResult` produces the uniform formation-substitution fiber
  result.  The fiberwise boundary correctly accommodates the equality transport
  in the raw lifted substitution.
  Dependent Sigma formation now has the parallel checked path.
  `IncDependentSigmaFiberEquiv` records the two dependent-pair round trips, and
  `IncDepRawSigmaFormationSubstitutionFiberResult` combines it with recursive
  domain and codomain interpretations.  Its `toFormationFiberResult` closes the
  Sigma formation constructor under the same uniform substitution interface.
  Direct `IncDepRawFormationSubstitutionFiberResult.base` and `.unit`
  constructors now put the two leaf cases on that interface as well, so all five
  formation shapes have a checked uniform-result constructor.
  Binder recursion is no longer restricted to definitionally equal domain
  interpretations.  `IncDepRawSubstitutionSemanticResult.liftFiber` lifts a raw
  substitution using an arbitrary domain `FiberEquiv`; its projection and newest-
  variable equations are definitional.  `liftFiber_ofEq` proves that this is a
  conservative extension of the previous equality-based lift.  This supplies the
  semantic substitution needed to recurse into Pi/Sigma codomains.
  That recursion is now wired into the formation API.  A domain result exposes
  `liftSubstitution`; Pi and Sigma `ofCodomainResult` constructors consume a
  formation-substitution result recursively computed under that lift.  The
  direct uniform `.pi` and `.sigma` constructors then return the parent result,
  leaving only the genuinely necessary dependent round-trip coherence as branch
  input.
  Identity is direct as well: `.identity` consumes the recursive type result and
  the two endpoint typing-substitution results, derives endpoint transport
  equations from them, and returns the uniform parent formation result.  Thus
  base, unit, Pi, Sigma, and identity now all expose dispatcher-ready direct
  constructors.
  The dependent maps used by Pi/Sigma are now canonical rather than merely
  compatible by convention.  Their `dependentEquiv` constructors take the
  codomain map directly from the recursively computed codomain result, while
  `ofCodomainCoherence` asks only for the two unavoidable round-trip laws.  This
  preserves the map identity needed by lambda, pair, and projection substitution
  branches.
  Lambda substitution is now closed end to end.  The general
  `piForward_eq_of_pointwise` lemma lifts pointwise codomain transport to an
  equality of dependent functions.  The uniform `.lambda` constructor combines
  recursive domain, codomain, and body results with the Pi round-trip laws and
  derives the final substituted-lambda coherence without an extra term equation.
  The first Sigma projection substitution branch is also closed.  Its uniform
  `.first` constructor applies `Sigma.fst` to the recursive pair coherence; the
  canonical Sigma forward map computes definitionally on the first component,
  yielding exactly the recursive domain transport equation.
  Instantiated dependent families now have their own substitution bridge.
  `instantiateFiberEquivalence` evaluates the recursive codomain equivalence at
  the source argument, transports its target endpoint along the recursive domain
  term coherence, and composes the two fiber equivalences.  This is the semantic
  formation result required by application, dependent pairing, and the second
  Sigma projection.
  The semantic bridge can now be returned to an arbitrary raw formation proof
  index.  `IncDepRawAlignedFormationSubstitutionFiberResult` records source and
  target formation interpretations, their equalities with canonical semantic
  families, and the canonical middle equivalence.  `toFormationFiberResult`
  composes the two endpoint transports with that equivalence, producing the
  uniform raw formation-substitution result needed by eliminator result types.
  `IncDepRawFormationSubstitutionFiberResult.instantiate` now performs this whole
  construction directly from recursive domain/codomain results, argument
  coherence, actual instantiated formation interpretations, and their endpoint
  alignments.  On terms, `sigmaForward_second_eq_of_eq` extracts the correctly
  transported second-component equality from equality of dependent pairs.  These
  are the two proof components required by the second Sigma projection branch.
  They are now integrated by the uniform `.second` constructor.  It selects the
  canonical instantiated result type, derives first-component coherence from the
  recursive pair result, and proves second-component transport with
  `sigmaForward_second_eq_of_eq`.  The exact substituted source derivation is now
  assigned that canonical projection term directly, so no external alignment is
  required.
  Dependent pair introduction is integrated too.  The general
  `sigmaForward_eq_of_components` lemma reconstructs equality of dependent pairs
  from domain equality and the transported codomain equality.  The uniform
  `.pair` constructor obtains both from the recursive first and second results
  and the canonical instantiated equivalence.  The exact substituted source
  derivation receives the canonical pair term internally, with no alignment input.
  Application substitution is now integrated.  Pi round-trip laws alone do not
  identify evaluation of `piForward` at a transported argument with the
  recursively supplied codomain map, so `piForward_apply_transport` isolates the
  necessary evaluation-coherence law.  The uniform `.apply` constructor combines
  that law with recursive function and argument results and the canonical
  instantiated formation result.  Its exact substituted source derivation is
  interpreted by the canonical application term internally.
  Binder coherence is now packaged for recursive dispatch.  The stronger
  `IncDependentPiApplicationFiberEquiv` combines Pi round trips with its
  evaluation law.  `IncDepRawPiSubstitutionCoherence` and
  `IncDepRawSigmaSubstitutionCoherence` collect the corresponding invariant at
  every context assignment; `ofApplicationCoherence` and `ofCoherence` turn each
  single package into the uniform formation result.
  The Pi package exposes named accessors for both round trips and forward
  evaluation, while `.piCoherent` and `.sigmaCoherent` return the parent uniform
  formation result directly.  A dispatcher can therefore share one coherence
  object between formation and all associated typing branches without unpacking
  or duplicating laws.
  The package stores laws specifically for the canonical dependent map built from
  the recursive codomain result—it cannot substitute an unrelated equivalent map.
  Both `.lambda` and `.apply` now consume this single package directly.
  Sigma follows the same canonical-law design: its package stores the two laws
  for the recursive codomain map, and `.pair`, `.first`, and `.second` each
  consume that one object.  All dependent typing branches now share their
  binder coherence with formation through a uniform package boundary.
  The remaining external data for total recursion now has one model interface.
  `IncDepRawSubstitutionFiberModel` contains the base-type interpretation and
  canonical Pi/Sigma coherence providers for arbitrary recursive domain and
  codomain results.  Its `.base` and `.unit` methods already dispatch both leaf
  formation cases.  Its `.pi` and `.sigma` methods now obtain the appropriate
  package from the provider and return the uniform parent result directly, so all
  four non-identity formation branches are model-dispatched.
  Identity is now model-dispatched from the recursive type and two endpoint
  typing results, completing all five formation shapes.  On the typing side,
  `.typingUnit` and `.refl` expose the two non-binder leaf constructors through
  the same model API.  This constructor algebra is now consumed by the checked
  mutual structural dispatcher `preserveFormation`/`preserveTyping` and its
  canonical variant; this sentence previously described that dispatcher as
  pending and is retained here only with its current completed status.
  Pi typing is model-dispatched as well.  `model.lambda` and `model.apply` obtain
  the canonical Pi package internally and consume only recursive child results
  (plus the raw instantiated formation required by application).  The dispatcher
  no longer carries Pi laws through either typing branch.
  Sigma typing is model-dispatched too: `model.pair`, `model.first`, and
  `model.second` obtain the canonical Sigma package internally.  Together with
  unit, refl, lambda, and apply, every non-variable typing constructor is now in
  the model algebra.  Variable dispatch remains the lookup/replacement bridge.
  That final constructor is now exposed as `model.variable`, combining the
  recursively selected type result with lookup formation alignment, the
  replacement environment, and the final variable equation.  All eight typing
  shapes and all five formation shapes therefore have model-algebra methods; the
  remaining integration task is the mutual structural recursion that selects
  them from readiness evidence.
  That audit exposed one missing input: readiness for apply, pair, and second did
  not retain formation readiness for their instantiated output type.  The model
  now supplies `typingFormation`, with `formationForTyping` as its accessor, for
  every typing readiness witness.  The dispatcher can therefore obtain and
  recursively interpret eliminator result formations instead of assuming them.
  Replacement environments now lift along general fiber equivalences too.
  `IncDepRawSubstitutionReplacementSemanticResult.liftFiber` mirrors semantic
  `liftFiber`, and `liftResult` specializes it to a recursive domain formation
  result.  Binder recursion can therefore lift the semantic substitution and its
  replacement interpretation together, without falling back to type equality.
  The generalized lift now has stable rewrite laws:
  `liftResult_here_term`, `liftResult_there_term`, and
  `liftResult_here_fiber`.  The first two compute newest and older replacement
  terms; the third identifies the newest term after domain forward transport
  with the target extended variable under the fiber-lifted substitution.  The
  binder variable recursion's newest branch is therefore closed generically.
  The older branch is now generic too.  `liftFiber_older_transport` proves
  naturality of any family/term coherence under the fiber-lifted binder, and
  `liftResult_there_fiber` applies it to older replacements.  Here and there
  replacement coherence are both available without equality-based lifting.
  A total structural dispatcher now runs for the non-identity formation spine.
  `IncDepRawNonIdentityFormationReady` mirrors base, unit, Pi, and Sigma readiness;
  `dispatchSubstitution` recursively computes domain results, fiber-lifts the
  substitution for codomains, and calls the model algebra.  `toSemanticReady`
  embeds this evidence into the existing readiness API.  Identity remains the
  point where formation and typing recursion must become mutual.
  That boundary now has an explicit composition operation.
  `dispatchIdentitySubstitution` structurally dispatches the non-identity type
  spine and combines the resulting type interpretation with recursively supplied
  left/right typing results through `model.identity`.  Mutual recursion only has
  to produce the two endpoint results at this boundary.
  The full finite mutual spine is now represented by
  `IncDepRawFormationDispatchReady` and `IncDepRawTypingDispatchReady`.  They
  mirror all five formation and eight typing constructors, allow nested identity
  formation, and retain instantiated output formations for apply, pair, and
  second.  Mutual `toSemanticReady` functions embed the strengthened trees into
  the existing readiness API while forgetting only that extra output evidence.
  Variable-specific alignment is isolated behind
  `IncDepRawVariableSubstitutionProvider`.  Its `dispatchVariable` operation
  receives the lookup, strengthened type readiness, target context tree,
  recursive type result, and replacement environment, and returns the uniform
  variable result.  The mutual dispatcher now has exactly two external inputs:
  the substitution fiber model and this lookup provider.
  Typing recursion now has a proof-index-safe dependent return package:
  `IncDepRawTypingSubstitutionDispatchResult` carries its own output formation
  proof, strengthened readiness, formation result, and typing result.  Its source
  and target semantic families are exposed by accessors.  `dispatchTypingUnit`
  and the variable provider's `dispatchResult` implement the two actual leaf
  cases without identifying distinct formation derivations.
  Recursive package combinators now cover refl and lambda.
  `dispatchRefl` turns a child typing package into its identity formation and
  reflexivity result.  `dispatchLambda` combines a recursive domain result with a
  body package computed under its lifted substitution, returning the Pi formation
  and lambda typing result together.  These validate the package shape across
  both the formation/typing boundary and a binder boundary.
  Proof-index alignment is now an explicit checked operation rather than an
  implicit assumption.  `castFormation` transports a typing-substitution result
  only along equality of complete formation fiber results, and
  `typingResultAligned` exposes that operation at the recursive package boundary.
  The remaining apply/pair/projection branches can therefore state precisely
  which recursively computed formation result must agree with their canonical
  Pi, Sigma, or instantiated result.
  The four remaining non-leaf package combinators are now implemented:
  `dispatchApply`, `dispatchPair`, `dispatchFirst`, and `dispatchSecond` align
  their child packages with the canonical Pi/Sigma/instantiated fiber results,
  invoke the already checked semantic constructor, and return the corresponding
  output formation and typing result together.  The full mutual dispatcher still
  has to synthesize the explicit formation-proof and fiber-result alignment
  witnesses accepted by these combinators; those obligations are no longer
  hidden inside the semantic rules.
  The two-part obligation is now packaged as
  `IncDepRawTypingSubstitutionDispatchAlignment`: it records equality of the
  formation derivations and heterogeneous equality of their complete fiber
  results.  Its `typingResult` eliminator performs the checked transport, while
  `exact` discharges reflexive recursive cases.  This is the alignment object the
  mutual dispatcher must construct, instead of passing unrelated equalities.
  All four dependent branch combinators now consume these alignment objects
  directly.  `IncDepRawTypingSubstitutionAlignedDispatchResult` additionally
  packages a recursive result together with its alignment to an externally
  expected canonical result; its `typingResult` projects the transported term.
  `dispatchFirstAligned` proves the first real branch inhabits this stronger
  return type definitionally, establishing the output shape for mutual recursion.
  The stronger return type now covers every dependent non-leaf branch through
  `dispatchApplyAligned`, `dispatchPairAligned`, and `dispatchSecondAligned` as
  well.  `secondCanonical` names the dependent second-projection formation
  calculation so the dispatcher and its alignment certificate share literally
  the same result.  All four branch outputs therefore expose their canonical
  formation result without a post-hoc semantic cast.
  The remaining global alignment issue is now removed at the syntax boundary by
  mutually indexed coherent readiness trees:
  `IncDepRawCoherentFormationDispatchReady` and
  `IncDepRawCoherentTypingDispatchReady`.  A typing readiness is indexed by its
  exact output formation derivation, so application functions, arguments, pairs,
  projections, identity endpoints, and binder bodies must use the parent rule's
  very same formation evidence.  A mutual `toDispatchReady`/`toDispatchPair`
  fold recovers the earlier readiness API while simultaneously returning the
  exact output-formation readiness.  This is necessary because raw formation
  derivations live in `Type`, not proof-irrelevant `Prop`.
  `formationReady` now recovers that exact coherent formation subtree from any
  coherent typing tree.  Consequently the remaining total-dispatch obligation
  is semantic rather than syntactic: canonical instantiated fiber results made
  by application and second projection must be rebased to the independently
  structural interpretation of the same output formation.  They need not be
  definitionally equal, so the next theorem must construct an explicit fiber
  equivalence and transport the typing result along it.
  That semantic transport layer is now implemented as
  `IncDepRawFormationSubstitutionFiberRebase`.  It carries source and target
  fiber equivalences plus the naturality square relating both to substitution.
  `IncDepRawTypingSubstitutionFiberResult.rebase` transports both semantic terms
  and proves the substituted-term coherence in the new formation result.
  Reflexive and transitive rebase witnesses are checked, so several recursive
  normalization steps can be composed without collapsing them to equality.
  The pre-existing aligned instantiate package is now connected to this layer.
  `canonicalFiberResult` exposes its canonical endpoint, while
  `toCanonicalRebase` and `fromCanonicalRebase` give checked rebases in both
  directions between the structural and canonical formation results.
  `rebaseToCanonical` and `rebaseFromCanonical` lift those witnesses directly to
  typing-substitution results.  Application and second projection can therefore
  cross the instantiate boundary without requiring definitional equality.
  The exact recursive obligation is now represented by
  `IncDepRawInstantiateFormationAlignment`: only the source and target structural
  families must be identified with their canonical instantiated families.
  `toAlignedResult` combines those endpoint equations with the already proved
  canonical substitution equivalence.  The canonical result itself has a
  definitionally reflexive `canonical` witness, confirming that this interface
  adds no assumption in the normal constructor path.
  The application and second-projection semantic constructors now have rebased
  variants, `applyRebased` and `secondRebased`.  Each first constructs the checked
  canonical typing result, then transports it through an instantiate alignment
  to the selected structural output formation.  Thus both eliminators can return
  a result usable by structural mutual recursion rather than stopping at an
  isolated canonical family.
  Package-level `dispatchApplyStructural` and `dispatchSecondStructural` now
  expose those rebased eliminators to the recursive dispatcher.  They consume
  aligned child packages, the structurally computed output formation, and its
  two-endpoint instantiate witness, then return a complete dispatch package
  whose formation and typing results share the same rebased fiber equivalence.
  Dependent pair introduction now has `pairRebased`: a second component already
  interpreted over a structural instantiated formation is transported first to
  the aligned formation and then to the canonical family before invoking the
  checked pair rule.  This branch also exposes an important final obligation:
  endpoint family equalities alone do not identify two substitution fiber
  equivalences, so a structural-to-aligned rebase witness is required explicitly.
  `dispatchPairStructural` lifts this construction to the recursive package
  level.  It accepts independently dispatched first and second components,
  aligns the second with the structural instantiated result, applies the explicit
  structural-to-aligned rebase, and returns a Sigma package already aligned with
  `model.sigma`.  All three dependent rules that cross an instantiate boundary
  (apply, pair, second) now have structural package APIs.
  The complete instantiate obligation is now bundled as
  `IncDepRawInstantiateFormationCoherence`, combining the two endpoint equations
  with the structural-to-aligned substitution rebase.  Its canonical constructor
  is definitionally reflexive for all three components.  `pairCoherent` consumes
  this one object, so recursive callers no longer manage the endpoint alignment
  and equivalence-square proof separately.
  `applyCoherent` and `secondCoherent` now consume the same bundle too.  Together
  with `pairCoherent`, all three instantiate-crossing semantic rules have one
  uniform coherence interface; their rule-specific code only supplies the
  argument term and its already proved substitution equation.
  Package-level `dispatchApplyCoherent` and `dispatchSecondCoherent` complete the
  same unification above the semantic layer.  Alongside
  `dispatchPairStructural`/`pairCoherent`, a mutual dispatcher can now pass one
  instantiate-coherence object through every dependent branch without unpacking
  its endpoint or naturality fields.
  The remaining theorem input is now fixed as
  `IncDepRawInstantiateFormationCoherenceProvider`.  Its single `provide` field
  turns a structurally interpreted instantiated formation, the domain/codomain
  results, and an argument substitution equation into the complete coherence
  bundle.  `dispatch` is the uniform call boundary.  This does not assume the
  provider exists; it isolates exactly the theorem that must be constructed to
  close the total mutual fold for arbitrary structural outputs.
  Fiber rebases are now symmetric as well as reflexive and transitive.
  `IncDepRawFormationSubstitutionFiberRebase.symm` derives the reverse naturality
  square using the inverse laws of both endpoint equivalences, and
  `rebaseSymm` transports a typing result back along it.  A coherent dependent
  branch can therefore return the provider's exact structural formation result,
  rather than remaining on the intermediate aligned equivalence.
  `applyStructuralExact` and `secondStructuralExact` now perform that final
  reverse rebase in the actual dependent eliminators.  Their result type is the
  provider's original structural formation result exactly—not merely a formation
  with the same endpoints.  This removes the last result-type mismatch that
  prevented their direct use in a structurally recursive typing fold.
  The package-level coherent eliminators now preserve that exactness too:
  `dispatchApplyCoherent` and `dispatchSecondCoherent` store the supplied
  structural result directly in `formationResult` and use the exact low-level
  typing result.  A parent recursive rule can therefore align either package to
  the same structural result by reflexivity.
  `IncDepRawTypingSubstitutionAlignedDispatchResult.exact` now performs that
  reflexive lift for any package, and `exact_typingResult` proves its transported
  typing result computes definitionally to the original one.  Exact structural
  recursive outputs can therefore be promoted to the aligned return type with no
  semantic work or proof term normalization.
  A second, purely syntactic obligation exposed by the mutual-fold audit is now
  isolated as `IncDepRawCoherentReadinessAlignmentProvider`.  It identifies two
  coherent formation or typing readiness trees with the same exact derivation
  index.  A direct mutual induction is insufficient because apply/projection
  constructors hide domain and codomain indices; those hidden-index equalities
  must be established before readiness proof uniqueness can be implemented.
  A constructive alternative is now available as
  `IncDepRawStrictTypingDispatchReady`.  It indexes a coherent typing tree by the
  exact coherent formation-readiness evidence chosen by its parent and stores the
  equality to the tree's derived `formationReady`.  `ofCoherent`, `toCoherent`,
  `toDispatchReady`, and `formationDispatchReady` connect it to all earlier APIs.
  A total dispatcher can therefore consume a strict tree and avoid assuming
  global readiness proof uniqueness.
  Strict constructors now cover all eight typing rules: variable, unit, lambda,
  application, pair, both projections, and reflexivity.  Each constructor either
  returns the parent's requested formation-readiness evidence definitionally or,
  for the binder case, eliminates the body's stored equality once.  The full
  strict typing syntax tree can therefore be built compositionally without the
  global alignment provider.
  `identityStrict` now constructs Identity formation readiness only from endpoint
  typing trees indexed by the same type readiness, and the strict reflexivity
  constructor uses it.  `castFormationReady` transports a strict typing tree
  along an explicit equality of readiness evidence.  Nested Identity nodes and
  the occasional equality exposed by binder decomposition can therefore remain
  inside the strict discipline.
  The semantic return type for this tree is now formalized as
  `IncDepRawStrictTypingSubstitutionDispatchResult`.  It fixes the formation proof
  through the strict readiness index and stores only its exact formation result
  and typing result; `toDispatchResult` forgets that extra precision.  The unit
  leaf is implemented end to end by `dispatchStrictUnit`, establishing the first
  branch of the strict total fold.
  Three more strict branches are now implemented end to end:
  `dispatchStrictVariable` connects the lookup provider to the exact type result,
  `dispatchStrictRefl` builds Identity formation and reflexivity from one child,
  and `dispatchStrictLambda` combines an exact domain result with a body result
  under the lifted substitution.  The strict fold now covers both leaves, the
  Identity recursion edge, and the binder recursion edge.
  Strict semantic constructors now cover the remaining four rules too:
  `dispatchStrictApply`, `dispatchStrictPair`, `dispatchStrictFirst`, and
  `dispatchStrictSecond`.  Apply and second return the coherence provider's exact
  structural result; pair rebases its independently dispatched second component
  before returning `model.sigma`; first consumes that exact Sigma result directly.
  Every one of the eight typing constructors now has a checked strict-result
  combinator.  What remains is assembling them into the single recursive fold.
  The formation side now has the parallel exact return type
  `IncDepRawStrictFormationSubstitutionDispatchResult` and checked constructors
  for base, unit, Pi, Sigma, and Identity.  Pi/Sigma lift the substitution for the
  codomain result; Identity consumes endpoint typing results already aligned to
  its exact type result.  Both halves of the intended mutual fold therefore have
  complete constructor APIs.
  The remaining cross-branch equality obligation is now explicit as
  `IncDepRawFormationSubstitutionFiberRebaseProvider`: it supplies a natural
  fiber rebase between two semantic results for the same syntactic formation.
  `rebaseFormation` and `normalizeFormation` transport an already checked strict
  typing result onto a selected formation result.  This is the normalization
  interface needed when Identity endpoints or sibling typing branches independently
  recurse over the same formation; the future preservation fold will take this
  semantic coherence as an explicit hypothesis instead of assuming proof-result
  uniqueness silently.
  `IncDepRawStrictTypingSubstitutionDispatcher` now fixes the recursive typing
  interface, and `foldStrictFormation` is the first complete recursive half of
  the preservation construction.  It covers all five formation constructors:
  Pi and Sigma extend the target semantic context and lift replacements before
  recursing into the codomain, while Identity dispatches both endpoint typings,
  normalizes them onto the recursively selected type result, and transports the
  resulting readiness index back to the parent's exact tree.  The remaining
  assembly task is an implementation of that dispatcher by recursion over all
  eight coherent typing constructors.
  The opposite boundary is now explicit too:
  `IncDepRawStrictFormationSubstitutionDispatcher` packages formation dispatch,
  and `strictFormationDispatcher` turns the checked formation fold into that
  interface.  `IncDepRawStrictMutualSubstitutionDispatcher` records the final
  paired object.  Formation and typing recursion therefore now meet through
  symmetric, proof-indexed interfaces; constructing the typing half and tying
  this pair is the remaining mutual-recursion step.
  The typing half now has checked fold branches for variable, unit,
  reflexivity, and lambda.  Variable recursively obtains its exact type result
  before consulting the replacement provider; reflexivity aligns its recursive
  term with the selected type result; lambda performs the full binder protocol
  (domain dispatch, semantic-context extension, replacement lifting, codomain
  dispatch, and body normalization).
  Apply, pair, first, and second now have checked fold branches as well.  Each
  independently dispatches domain, lifted codomain, and (where needed) the
  instantiated structural result; recursive term results are normalized onto
  the exact Pi, Sigma, domain, or instantiated fiber before the strict semantic
  constructor is invoked.  Apply, pair, and second obtain their natural
  instantiate square from the explicit coherence provider.  All eight typing
  rules therefore have both low-level strict constructors and fold-level branch
  combinators.  Only the single recursor that selects these branches and ties it
  to the formation dispatcher remains in the preservation assembly.
  That selector is now implemented as `foldStrictTyping`: it structurally
  recurses over the coherent typing readiness tree, invokes the corresponding
  one of all eight checked branches, and transports each constructed strict
  readiness back to the exact input index.  Reflexivity exercises the full
  two-stage transport (formation readiness, then strict typing readiness).
  `strictTypingDispatcher` packages this recursor as the interface consumed by
  the formation fold.  Thus both recursive halves and both adapters are checked;
  the remaining step is tying the two dispatcher values into one well-founded
  mutual definition and exposing its preservation projections.
  The mutual-recursion route is now fixed at the type level by
  `IncDepRawStrictFormationSubstitutionFoldMotive` and
  `IncDepRawStrictTypingSubstitutionFoldMotive`.  These are the two motives for
  Lean's generated mutual recursor over coherent formation/typing readiness;
  each motive quantifies the source substitution semantics, target context tree,
  and replacement interpretation and returns the exact strict result.  The
  generated recursor supplies formation handlers with typing induction hypotheses
  and typing handlers with formation induction hypotheses, so the final knot can
  be structural rather than relying on an opaque recursive dispatcher value.
  Nine of the mutual recursor's thirteen handlers are now implemented directly
  against those motives.  All five formation handlers (base, unit, Pi, Sigma,
  Identity) are checked, including Identity's two typing induction hypotheses.
  Four typing handlers (variable, unit, lambda, reflexivity) are also checked;
  lambda consumes domain and body induction hypotheses under the lifted semantic
  context, and reflexivity performs exact type normalization.  The remaining
  recursor work is the four dependent typing handlers: apply, pair, first, second.
  Those final four handlers are now checked, completing all thirteen mutual
  handlers.  `preserveFormation` and `preserveTyping` apply Lean's generated
  mutual recursor to them and return exact substitution-fiber semantics for every
  coherent formation or typing tree.  `preservationDispatcher` bundles both
  projections as one `IncDepRawStrictMutualSubstitutionDispatcher`.  This closes
  the structural substitution-preservation fold for the dependent raw calculus,
  relative to its explicitly listed semantic providers (variable replacement,
  readiness alignment, fiber rebase, and instantiate coherence); none of those
  obligations is hidden as proof irrelevance or an axiom.
  The preservation projections now expose definitional computation theorems for
  base and unit formation, unit typing, Pi formation, and variable typing.
  All five proofs are `rfl`: the Pi equation visibly calls the two recursive
  formation projections (lifting occurs inside its checked handler), and the
  variable equation visibly consumes the recursive type-formation result before
  invoking the replacement provider.  These equations make the theorem usable
  by rewriting without unfolding the large generated mutual recursor.
  One apparent preservation hypothesis has now been eliminated:
  `IncDepRawCoherentReadinessAlignmentProvider.toStrictTyping` constructs strict
  typing-readiness alignment from coherent alignment.  Equality of the coherent
  tree is supplied by the existing provider; the remaining structure field is
  itself an equality proof and is unique by proof irrelevance.
  `preservationDispatcherAligned` is therefore the preferred bundle constructor
  and no longer asks callers for a separate strict-alignment provider.
  By contrast, coherent readiness alignment itself is not currently derivable by
  plain constructor induction.  The attempted mutual uniqueness proof closes the
  base, unit, Pi, Sigma, Identity, variable, lambda, first, and reflexivity shapes,
  but dependent elimination fails at apply, pair, and second: two readiness trees
  with the same outer judgment may hide propositionally related yet non-
  definitionally equal codomain/instantiation indices.  The coherent alignment
  provider therefore remains an honest coherence hypothesis; treating it as
  automatic proof irrelevance would overstate what Lean has checked.
  The remaining assumptions are collected in
  `IncDepRawSubstitutionPreservationHypotheses`: variable replacement, coherent
  readiness alignment, general formation-fiber rebase, and instantiate
  coherence.  `model.preservation hypotheses` is the concise public constructor
  for the complete mutual dispatcher.  Instantiate coherence is not derivable
  from general rebase alone: its alignment component asks for literal semantic-
  type equalities, whereas a rebase supplies fiber equivalences.  The package
  makes this precise boundary visible at every use site.
  The canonical subcase is nevertheless fully inhabited without assumptions:
  `incDepRawCanonicalInstantiateFormationCoherenceProvider` supplies coherence
  whenever the structural result is exactly `instantiateCanonical`.  Its
  alignment equalities and both rebase equivalences are reflexive.  This
  separates the constructive canonical fragment from the additional task of
  relating an independently dispatched structural result to the canonical one.
  The three dependent typing rules that need instantiation now expose matching
  canonical strict constructors:
  `dispatchStrictApplyCanonical`, `dispatchStrictPairCanonical`, and
  `dispatchStrictSecondCanonical`.  They return or consume
  `instantiateCanonical` directly and require no instantiate-coherence provider.
  The general preservation fold still follows the independently dispatched
  structural formation tree, but clients that choose canonical formation results
  can now execute all three dependent rules in the provider-free fragment.
  This choice now extends through the entire mutual recursion.
  `preserveFormationCanonical` and `preserveTypingCanonical` replace the three
  dependent handlers with their canonical versions, and
  `preservationCanonical` bundles them.  Its hypotheses structure has only three
  fields—variable replacement, coherent readiness alignment, and general fiber
  rebase—so instantiate coherence has been removed from the complete canonical
  preservation theorem, not merely from isolated constructors.  The general
  four-hypothesis theorem remains available when an independently dispatched
  structural result must be preserved exactly.
  A second route now reduces the fiber-rebase implementation burden.
  `IncDepRawFormationSubstitutionFiberEqualityProvider.toRebase` turns literal
  uniqueness of semantic formation results into the required source/target fiber
  equivalences and naturality square; after rewriting the two results equal, all
  three are reflexive.  `preservationCanonicalOfEquality` accepts this stronger
  but often easier-to-prove uniqueness interface.  Concrete semantic models can
  therefore establish result proof-uniqueness instead of constructing every
  rebase component manually.
  The canonical bundle also has generic projection equations,
  `preservationCanonical_formation` and `preservationCanonical_typing`.  Both are
  definitional (`rfl`) and expose the corresponding mutual-recursion projection
  for any readiness tree, context semantics, and replacement interpretation.
  Downstream proofs can now rewrite through the compact bundle API without
  unfolding either the dispatcher records or the generated recursors.
  `preserveEmptyUnitIdentity` is the first concrete end-to-end use of that
  bundle: it feeds the empty semantic-context tree and its identity replacement
  interpretation through canonical typing preservation for the unit judgment.
  The checked projection theorems show by `rfl` that its formation result is
  `model.unit` and its typing result is `model.typingUnit`.  This confirms the
  public bundle, identity substitution semantics, replacement semantics, mutual
  recursor, and strict return type compose without an adapter or hidden cast.
  The source and target terms of this preserved unit are now proved by `rfl` to
  equal `incDepRawEmptyContextSemanticTree.interpretUnit`; this is the first
  direct bridge from the substitution-preservation API back to the pre-existing
  context-tree interpreter.  Such literal equality is intentionally claimed only
  for the provider-independent leaf.  For terms whose variable or rebase branches
  consult supplied providers, the stable general statement remains the exported
  transport/substitution coherence unless stronger provider canonicity is given.
  `preserveUnitIdentityLambda` is the first binder-level example.  It constructs
  coherent readiness for `λ (x : Unit), x`, preserves it under the empty
  identity substitution, extends the semantic context for the body, lifts the
  replacement interpretation, and reaches the variable-provider branch.
  `preserveUnitIdentityLambda_coherent` then extracts the checked equality between
  transporting the source lambda and substituting the target lambda.  Unlike the
  unit leaf example, this path genuinely exercises binder recursion and variable
  replacement.
  `preserveUnitVariableRefl` adds the first Identity-formation example in the
  one-variable Unit context.  Its coherent formation tree recursively preserves
  the Unit type and both variable endpoints; the reflexivity typing branch then
  normalizes its recursive term result onto that exact type result before building
  the Identity fiber.  The exported coherence theorem confirms the resulting
  reflexivity term commutes with the identity substitution.  Together with the
  lambda example, this exercises both cross-directions of the mutual recursion.
  The dependent Sigma example is now connected too.
  `preserveDependentPair` preserves the closed pair
  `⟨unit, refl unit⟩` in `Σ (_ : Unit), Id Unit x x`; its second component is
  recursively normalized onto the canonical instantiated Identity fiber before
  pair introduction.  `preserveDependentPairFirst` then runs the first-projection
  eliminator over the recursively preserved Sigma result.  Both export semantic
  coherence theorems, so canonical Sigma introduction and elimination are now
  exercised end to end rather than only through isolated constructors.
  The remaining dependent eliminators are now exercised as well.
  `preserveDependentPairSecond` constructs the result formation
  `Id Unit (first pair) (first pair)` and runs canonical second projection over
  the preserved Sigma term.  `preserveDependentReflApplication` preserves the
  application `(λ (x : Unit), refl x) unit`, forcing the canonical Pi-application
  branch to instantiate its dependent Identity codomain.  Their coherence
  theorems complete end-to-end coverage of Pi, Sigma, and Identity introduction
  and elimination paths in the preservation fold.
  Closed interpreter result types are now formalized.  A certified closed
  judgment maps to a contextual semantic type together with a term of that type;
  a closed multi-step reduction maps to two terms in one semantic type together
  with their equality.  The dependent Pi/reflexivity and Sigma/pair judgments
  inhabit the first API, and Pi beta plus both Sigma projection reductions
  inhabit the second.  This fixes the dependent result shape and soundness
  obligation for the unconditional certified-judgment interpreter.  The
  provider-relative substitution-preservation recursor is complete; automatic
  construction of its semantic inputs from certification remains pending.
  The evaluator now exposes checked computation equations for every typing
  constructor (variable, unit, pair, projections, lambda, and application),
  and lookup derivations are proof-unique.  These laws provide a stable rewrite
  interface instead of relying on expansion of opaque proof-indexed recursors.
  Full typing-derivation uniqueness requires a stronger theorem that also
  identifies hidden intermediate types in projection/application rules; this
  was initially left unassumed.  It is now proved in two stages: raw typing is
  type-unique for every context and term, including hidden product partners and
  function domains; this type equality then aligns all rule indices and yields
  proof uniqueness for complete typing derivations.  Evaluator results are
  therefore independent of derivation choice, removing the principal
  proof-index ambiguity encountered by semantic substitution.
  Evaluator congruence is now explicit both for equal-typed derivations and
  across an identified type equality.  As a computation-level validation, a
  closed identity function can be renamed into any context, applied to any
  well-typed argument, and its evaluation is proved equal to evaluation of the
  argument itself.  This beta-soundness proof uses lookup proof uniqueness to
  normalize the otherwise opaque binder derivation.
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
  `BisimulationQuotientIncidencePresentation` strengthens a classification
  target with an actual target Incidence and exact boundary-observation law;
  it supplies both the quotient type equivalence and a boundary-logic
  embedding.  The presentation automatically preserves and reflects boundary
  and leaf truth as well as their finite-sequent entailment relations.  The
  simplex-to-shape quotient instantiates this general interface, so every
  translated formula and context has the same boundary/leaf semantics on the
  seven-element source and the three-class quotient presentation.  Moreover,
  any two quotient Incidence presentations of the same source are connected by
  the unique classification equivalence as a boundary-observation embedding;
  boundary and leaf truth, context satisfaction, and finite-sequent semantic
  consequence therefore agree across all such presentation targets.  The
  interface also rules out the known bad case uniformly: because
  `cycleIncidence` has one bisimulation class but a nonempty boundary, no target
  type and no target Incidence can form a boundary-preserving quotient
  presentation for it; subsingleton well-foundedness forces the target boundary
  empty and yields a checked contradiction.  More generally, any source atom
  with a nonempty boundary forces both the presentation target and the actual
  bisimulation quotient to contain two distinct points: the target boundary
  endpoint and its owner cannot coincide by well-foundedness.
  A reusable positive sufficient condition is now formalized too:
  `GradedIncidenceData` constructs an Incidence whenever every boundary edge
  strictly lowers a natural-number grade, deriving the no-self-loop obligation
  rather than assuming it.  `GradedBisimulationQuotientPresentation` combines
  this construction with a complete bisimulation classification and promotes
  it to the full quotient-presentation interface.  The simplex-to-shape model
  is now instantiated through this theorem with grades 0, 1, and 2, replacing
  its former one-off well-foundedness proof.
  At the raw-target level the obstruction is characterized exactly.
  `IncidenceCandidateData` packages every Incidence law except
  well-foundedness; it is realizable by an Incidence with the same boundary,
  type, glue, unit, and guards if and only if its boundary has no self-loop.
  The graded construction factors through this characterization by proving
  that strict grade decrease excludes every self-loop.  Canonical descent of
  raw boundary, glue, type, and guards is characterized below.
  The boundary half is now characterized exactly: mapping each source
  endpoint through the classifier descends to a unique target boundary if and
  only if that mapped boundary is bisimulation-invariant.  The canonical
  quotient lift has a checked beta law and uniqueness theorem.  For the
  simplex classification the invariant condition holds, and this canonical
  boundary is proved equal to `shapeBoundary`.  The corresponding binary
  descent is now characterized in the same exact form: mapped source glue
  descends to a unique target operation if and only if it is invariant under
  bisimilarity in both inputs.  Its canonical construction satisfies beta,
  left-unit, and right-unit laws.  The simplex classification fails this
  condition (two bisimilar vertices produce different mapped glue results
  against the face), formally explaining why `shapeIncidence.glue` must be an
  independently chosen operation rather than descended source glue.
  Source `typeFunc` always descends—bisimilarity preserves types by
  definition—and its canonical lift has beta and uniqueness laws.  Together
  with canonical boundary it automatically satisfies type consistency, sign
  validity, and positive multiplicity.  Finally,
  `CanonicalQuotientIncidenceCoherence` packages boundary/glue invariance,
  absence of descended self-loops, and glue type preservation; from this
  certificate the library constructs a complete quotient Incidence with
  permissive guards and proves exact boundary/glue beta laws.  Transport of a
  non-permissive source guard policy, rather than construction of an Incidence
  itself, was initially a separate refinement.  It is now closed as well:
  source guards descend exactly when their Boolean allow relation is invariant
  under bisimilarity in both inputs.  The descended guard is canonical, unique,
  and satisfies an exact beta law.  Extending the coherence certificate with
  this condition constructs a complete quotient Incidence whose guards agree
  exactly with the source on classified inputs.  Thus the general quotient
  construction conditions are now explicit; the remaining work for a concrete
  nonfaithful incidence is to prove—or refute—those coherence conditions.
  This is now validated by a genuinely nonfaithful positive example, not only
  by interfaces: `natIncidence × trivialIncidence Bool` identifies `(n,false)`
  with `(n,true)` and has quotient classifier `Prod.fst : Nat × Bool → Nat`.
  Its boundary, glue, and guards satisfy all invariance conditions, the
  no-self-loop and glue-type obligations hold, and the guarded coherence
  certificate constructs a canonical quotient Incidence on `Nat`.  The
  descended glue is proved exactly `m+n` and its guard is always true.  Thus
  the construction performs a real collapse while retaining nontrivial Peano
  boundary structure and algebra, unlike faithful quotients (no collapse),
  `cycleIncidence` (boundary obstruction), or simplex-to-shape (glue
  obstruction).

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

For the dependent raw Pi/Sigma/Identity calculus, canonical mutual
substitution preservation now covers every formation and typing constructor
and exposes lawful and strict dispatchers with path agreement.
`IncDepRawRelationalLawfulSubstitutionFiberModel` packages a semantic model,
the exact recursive preservation core (variable replacement and readiness
alignment), and the three strong relational naturality laws
(instantiation, dependent assembly, and generated identity) without first
weakening those laws.  The exact remaining obligation for the concrete
Unit-fiber model is represented by `IncDepRawUnitRelationalCompletion`; an
inhabitant projects directly to lawful and strict preservation.  The target
type and projections are checked, but the completion is not yet inhabited,
so a concrete unconditional preservation theorem is not claimed yet.
In particular, this scoped core deliberately omits the legacy global fiber
rebase field: the library proves that no such provider exists in general, and
the provider-free recursive theorem does not consume it.
The Unit obligation is also exposed as `Stage1` (variable replacement and
readiness alignment), `Stage2` (instantiate relational naturality), and
`Stage3` (dependent relational naturality); supplying generated-identity
naturality to `Stage3.complete` produces the final completion.  This staging
lets each genuine law be proved independently without placeholder axioms.
The alignment contract is now characterized directly: any readiness provider
induces `Subsingleton` instances for both formation and typing readiness at
each fixed derivation.  It must therefore be supplied only where that scoped
uniqueness is justified; it cannot be replaced by blanket proof irrelevance.
The instantiate component is under the same audit: its legacy provider ranges
over arbitrary fold results, while the recursive dispatcher only consumes it
for recursively generated results.  Narrowing that quantifier is the next
provider-inhabitation step.
That narrowing has started at the first concrete consumer: Apply now has
`anchoredTypingFoldResultApplyExactOfAgreement`, which consumes one local
instantiate agreement rather than a globally quantified provider.  The former
Apply API remains as a compatibility wrapper.  Pair and Second now have the
corresponding `...ExactOfAgreement` builders as well, so all three consumers
are localized.  The remaining step is to feed these builders from a provider
quantified only over recursively generated results.
`IncDepRawCanonicalRecursiveInstantiateAgreementProvider` now supplies exactly
that contract: it quantifies only over provenance-carrying domain, codomain,
result, and argument packages, plus their local alignment.  Apply is connected
end-to-end through `recursivelyGeneratedTypingApplyScoped`; a legacy global
relational provider projects to the scoped one for compatibility.  Pair and
Second are now connected by `recursivelyGeneratedTypingPairScoped` and
`recursivelyGeneratedTypingSecondScoped` as well.  Second constructs the
provenance-carrying First result used as its instantiation argument, so all
three dependent typing consumers now avoid arbitrary-fold quantification.
`IncDepRawCanonicalScopedRecursiveFoldInputs` carries this scoped law together
with variable replacement, readiness alignment, and generated agreement.
`recursivelyGeneratedFormationFoldOfScopedInputs` and
`recursivelyGeneratedTypingFoldOfScopedInputs` run the complete mutual
recursion over all thirteen constructors without falling back to the global
instantiate provider in Apply, Pair, or Second.
`scopedAnchoredMutualFoldDispatcher` promotes those recursors to the public
dispatcher level.  The lawful, strict, and path-agreement projections of
`IncDepRawRelationalLawfulSubstitutionFiberModel` now use this scoped route
directly; conversion to the older assembly-lawful bundle remains only as a
compatibility API.
The concrete Unit target now uses
`IncDepRawCanonicalScopedRelationalNaturalityLaws` and
`IncDepRawScopedRelationalLawfulSubstitutionFiberModel` directly.  Its Stage2
obligation is the generated-package instantiate provider, not the legacy law
over arbitrary folds, and `IncDepRawUnitRelationalCompletion.toLawfulModel`
returns the scoped lawful model.  Thus the exact completion target no longer
contains the over-quantified global instantiate premise.
Both the scoped lawful model and `IncDepRawUnitRelationalCompletion` now expose
their path-agreement theorem directly alongside lawful and strict
preservation, so inhabiting the Unit target yields the complete public
preservation API without converting back through the legacy assembly bundle.
Scoped instantiation is now a first-class component,
`IncDepRawCanonicalScopedInstantiateNaturalModel`.  The scoped relational law
bundle has component assembly/projection functions and checked beta laws, and
Unit Stage2 consumes this component directly.  Instantiation, dependent
assembly, and generated identity can therefore be proved independently and
combined without unpacking raw provider records.
The scoped instantiation proof itself has now started.  Splitting on generated
codomain and result provenance yields exactly five outer cases.  Base and Unit
are closed, for every substitution-fiber model, by the sorry-free lemmas
`recursiveInstantiateAgreementBase` and
`recursiveInstantiateAgreementUnit`; both are definitional relational
reflexivity.  Pi, Sigma, and Identity remain and require recursive composition
of their component agreements.
That recursion needs readiness substitution as well as syntactic substitution.
A direct attempt exposed a dependent-index issue: Variable, Apply, Pair, and
Second use propositional rewrites in `HasType.substitute`, so their readiness
is not definitionally indexed by the legacy derivation.  The new
`IncDepRawFormationReadinessSubstitutionResult` and
`IncDepRawTypingReadinessSubstitutionResult` retain the constructed derivation,
its equality to the legacy substitution, and its readiness together.  Base and
Unit formation plus Unit typing constructors were the first inhabitants.  The
formation side is now complete: Pi and Sigma compose the domain result with a
lifted-substitution codomain result, while Identity locally casts both endpoint
typing readiness certificates onto the shared substituted type formation.
All five formation constructors therefore preserve coherent readiness without
assuming derivation equality is definitional.
Typing readiness substitution now covers Unit, Lambda, Refl, and First.  Lambda
composes a lifted body package, while Refl and First derive the exact local
formation cast from the child packages' equalities to their shared canonical
substitution.  Coverage is 4/8; Variable, Apply, Pair, and Second are the
remaining branches whose typing derivations contain explicit substitution
rewrites.
Variable correctly cannot use `.varRule` for an arbitrary replacement term;
`IncDepRawReadinessPreservingSubstitution` records exactly the required
replacement readiness, and the Variable constructor consumes it.  Stable
typing constructor coverage is therefore 5/8.  Direct equation normalization
for Apply, Pair, and Second typechecks incrementally but is deliberately not
accepted: it exceeds the clean-build elaboration budget.  Those three branches
need explicit lightweight transport lemmas before the mutual recursor is tied.
The shared transport layer is now checked.  `IncDepRawWellFormed.castType` and
`IncDepRawHasType.castType` move both derivation kinds along one type equality;
the corresponding coherent-readiness casts transport their certificates in
lockstep.  Reflexive beta laws are proved.  These primitives match the
`Eq.mp` shape used by Apply/Pair/Second substitution without unfolding the
large mutual equation compiler.
Transported Apply/Pair/Second prototypes confirm the cast shape, but their
`typing_eq := rfl` still forces expansion of the legacy mutual recursor during
a clean build and is therefore not accepted as a stable proof.  The remaining
task is an opaque, constructor-specific equation theorem whose checking does
not replay that expansion.
Derivation proof-irrelevance is not a valid shortcut here: dependent lookup
stores a pre-weakening type, and distinct such types can have the same renamed
index.  Consequently the completion path must preserve semantics independently
of the particular typing derivation, rather than postulating that all typing
derivations are equal.  This also fixes the foundation roadmap: semantic
preservation precedes global completeness and broader mathematics imports.

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
