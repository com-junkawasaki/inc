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
  producing these results for every certified judgment remains pending.
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
  Closed interpreter result types are now formalized.  A certified closed
  judgment maps to a contextual semantic type together with a term of that type;
  a closed multi-step reduction maps to two terms in one semantic type together
  with their equality.  The dependent Pi/reflexivity and Sigma/pair judgments
  inhabit the first API, and Pi beta plus both Sigma projection reductions
  inhabit the second.  This fixes the dependent result shape and soundness
  obligation for the general recursive interpreter, which is still pending.
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
