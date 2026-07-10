---
layout: default
title: Formal Verification Results
description: Checked Lean 4 core for Incidence Theory
---

# Formal verification status

The Lean source in `incidence-theory/` is the authoritative record of what is
formalized. Run `./verify.sh` from the repository root to rebuild it and run
the triangle example.

## Checked results

| Area | Checked result |
| --- | --- |
| Boundary data | Finite list representation, sign classification, positive multiplicities |
| Well-founded mode | A decreasing natural-number rank excludes direct boundary cycles |
| Gluing | Unit laws, type preservation, and conditional associativity supplied by `GluingSpec` |
| Bisimulation | Reflexive, symmetric, transitive; observable equality implies bisimilarity; on the finite `leaf`/`root` model, bisimilarity is exactly equality and quotient representatives are injective |
| Linear data | Boundary matrices and Laplacians computed from boundaries; pointwise boundary equality preserves both, every derived `BᵀB` Laplacian is symmetric with nonnegative diagonal entries, append/cons decomposition, exact diagonal increments, and monotonicity under row extension; an explicit boundary-row-balance hypothesis yields zero Laplacian row/column sums |
| Triangle model | Six incidence-matrix entries, three Laplacian entries, its finite `∂² = 0` calculation, checked boundary row-balance and full Laplacian row/column sums, zero vertex-row sums and trace `6` of the vertex Laplacian, two independent eigenvectors of eigenvalue `3` plus the constant kernel vector, and a nontrivial bisimulation quotient in which all three edge representatives agree while an edge class is separated from the empty-boundary vertex class |
| Translation | A functor maps a pushout cocone to a commuting cocone; universal-property preservation is an explicit `PushoutPreserving` condition, pushout apexes are uniquely isomorphic, and their comparison isomorphisms satisfy identity/inverse/associative composition coherence and path-independence across four presentations |
| Terminal model | Concrete witnesses for glue-to-pushout and pushout-preserving identity translation |
| Trivial incidence | Total bisimulation, linear-completeness specification, glue congruence, and `∂² = 0` |
| Finite well-founded incidence | A bundled two-element, nonempty-boundary structure-satisfaction certificate (`root → leaf`) covering the core, gluing, role-erased A2–A10 interfaces, and A16/A17 algebraic layer; decreasing rank, gluing spec, finite `∂² = 0` |
| Finite linear completeness | On the nonempty finite model, equal boundary-matrix/Laplacian observations imply bisimilarity; the exact Laplacian is an idempotent projection with trace `1` and a unique image/kernel direct-sum decomposition (root kernel direction, observed leaf coordinate) |
| Layered algebraic witness | The finite model's role-erasure instantiates legacy A2/A6–A10/A16–A17 interfaces; its matrix and Laplacian are the core computations |
| Internal logic | Propositional formulas over incidence atoms, natural deduction, weakening, substitution, cut, functorial/reflecting proof transport under atom maps, Prop and Kripke semantic map identity/composition/reflection laws, Kripke pullback with exact forcing preservation and equivalence transport, Kripke persistence/soundness, relative empty-context consistency, concrete two-world countermodels showing excluded middle nonderivable/invalid (including the actual `FiniteIncidence.root` atom) while its double-negation is derivable, explicit-enumeration infinite Lindenbaum chains whose limits are closed consistent prime theories extending every consistent finite context, finite-support relative chains over arbitrary prime sources, transitive finite subformula closure/decision, and canonical/ordinary same-universe Kripke completeness; every atom code/decode retraction supplies direct enumeration/completeness and canonical-countermodel instances, with public `Fin n` (`n=0`), `Bool`, `Nat`, and `FiniteIncidence` forms |
| Finite-set reconstruction | A bundled two-atom `SetIncidence` Boolean-fragment model; boundary membership faithfully represents union, intersection, complement, and difference, with Boolean algebra laws |
| Arbitrary finite basis | `BitSet n` has extensionality plus checked Boolean operations, complement laws, distributivity, De Morgan's law, faithful boundary encoding, and boundary-membership preservation over `Fin n` |
| Recursive finite sets | `HFSet` structural incidence model, rank decrease, extensional membership, exact binary-/big-union membership, quotient-level union laws, a finite syntactic powerset presentation with subset soundness/extensional completeness, and Kuratowski ordered pairs with exact finite Cartesian-product membership |
| Extensional recursive sets | Union is well-defined on `HFSet` extensional-equivalence quotient |
| Recursive extensional quotient | Depth-indexed bisimulation equivalence; pairing, singleton/Kuratowski ordered pairs, quotient-level Cartesian product/powerset, and respectful separation descend to the quotient; pair equality is classified, ordered pairs and powerset are injective, product is empty in either empty factor, monotone/distributive, reflects coordinatewise equality/subset under nonempty factors, and connects singleton representatives through `⟨{a},{b}⟩ ∈ P(s)×P(t) ↔ a∈s ∧ b∈t`, `power(∅)={∅}`, powerset reflects inclusion and `⋃ power(s)=s`, pair/ordered-pair/product membership and `x ∈ power(s) ↔ x ⊆ s` have exact iff laws, singleton graphs plus finite-ordinal identity/successor/shift graphs are relational, functional, and injective with exact application and finite-domain totality; their two-/three-stage relational composition has exact application, uniqueness, and associativity-coherence laws, nonempty-domain shift graphs reflect offsets/cancel addition, and respectful predicate filters plus Boolean complement/conjunction/disjunction give quotient-safe relative difference, partition, disjointness, involution, and De Morgan laws; true/false filters are identity/empty, and a quotient-level membership-tree rank proves well-foundedness and the set-theoretic foundation statement |
| Quotient union algebra | Exact pair/binary-/big-union membership; binary union is an idempotent least upper bound, `⋃{s,t}=s∪t`, and big union preserves empty/distributes over binary union |
| Finite set-fragment model | A bundled HF recursive-quotient witness for empty, exact pairing/product, product zero/monotonicity/distribution and singleton-powerset bridge, powerset with `⋃P(s)=s`, respectful separation, exact big union, extensionality, and foundation |
| Natural-number reconstruction | Injective von Neumann naturals in the recursive quotient, with rank `n`, exact membership `m ∈ n ↔ m < n`, internal inclusion/proper inclusion exactly `m ≤ n`/`m < n`, equality/trichotomy, successor `n + 1 = n ∪ {n}`, `⋃(n+1)=n`, and binary union `max(m,n)` with associative/commutative/idempotent laws |
| Recursive union algebra | Recursive quotient union is associative, commutative, and has empty as identity |
| Recursive membership | Membership descends to the recursive quotient; empty has no members, each union summand embeds, and extensionality is proved |

## Deliberately conditional research claims

Generic `∂² = 0`, pushout universality, linear completeness, and preservation
of categorical limits/colimits require additional hypotheses. They are not
claimed as unconditional Lean theorems.

The finite model establishes satisfiability only for the present implemented
finite fragment relative to Lean; it is not a formal ZF or HoTT consistency
model.
