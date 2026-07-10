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
| Bisimulation | Reflexive, symmetric, transitive; observable equality implies bisimilarity |
| Linear data | Boundary matrices and Laplacians computed from boundaries; every derived `BᵀB` Laplacian is symmetric with nonnegative diagonal entries, append/cons decomposition, and diagonal monotonicity under row extension |
| Triangle model | Six incidence-matrix entries, three Laplacian entries, and its finite `∂² = 0` calculation |
| Translation | A functor maps a pushout cocone to a commuting cocone; universal-property preservation is an explicit `PushoutPreserving` condition, and pushout apexes are uniquely isomorphic |
| Terminal model | Concrete witnesses for glue-to-pushout and pushout-preserving identity translation |
| Trivial incidence | Total bisimulation, linear-completeness specification, glue congruence, and `∂² = 0` |
| Finite well-founded incidence | Nonempty `root → leaf` boundary, decreasing rank, gluing spec, finite `∂² = 0` |
| Finite linear completeness | On the nonempty finite model, equal boundary-matrix/Laplacian observations imply bisimilarity |
| Layered algebraic witness | The finite model's role-erasure instantiates legacy A2/A6–A10/A16–A17 interfaces; its matrix and Laplacian are the core computations |
| Internal logic | Propositional formulas over incidence atoms, natural deduction, weakening, substitution, cut, truth-preserving translation, proof transport along atom maps, Kripke pullback with exact forcing preservation, Kripke persistence/soundness, relative empty-context consistency, a two-world proof that excluded middle is underivable while its double-negation is derivable, explicit-enumeration infinite Lindenbaum chains whose limits are closed consistent prime theories extending every consistent finite context, finite-support relative chains over arbitrary prime sources, transitive finite subformula closure/decision, and canonical/ordinary same-universe Kripke completeness from a recurrent formula schedule |
| Finite-set reconstruction | Extensional subsets of two atoms; boundary membership and union laws are proved |
| Arbitrary finite basis | `BitSet n` has extensionality plus checked Boolean operations, complement laws, distributivity, De Morgan's law, faithful boundary encoding, and boundary-membership preservation over `Fin n` |
| Recursive finite sets | `HFSet` structural incidence model, rank decrease, extensional membership, exact binary-/big-union membership, quotient-level union laws, a finite syntactic powerset presentation with subset soundness/extensional completeness, and Kuratowski ordered pairs with exact finite Cartesian-product membership |
| Extensional recursive sets | Union is well-defined on `HFSet` extensional-equivalence quotient |
| Recursive extensional quotient | Depth-indexed bisimulation equivalence; pairing, singleton/Kuratowski ordered pairs, quotient-level powerset, and respectful separation descend to the quotient; pair equality is classified, ordered pairs and powerset are injective, `power(∅)={∅}`, pair/ordered-pair membership and `x ∈ power(s) ↔ x ⊆ s` have exact iff laws, singleton graphs plus finite-ordinal identity/successor/shift graphs are relational, functional, and injective with exact application and finite-domain totality (shift zero/one equal identity/successor, shifts compose by offset addition as internal relations), filters distribute over union/compose by predicate conjunction; true/false filters are identity/empty, and a quotient-level membership-tree rank proves well-foundedness and the set-theoretic foundation statement |
| Quotient union algebra | Exact pair/binary-/big-union membership; binary union is an idempotent least upper bound, `⋃{s,t}=s∪t`, and big union preserves empty/distributes over binary union |
| Finite set-fragment model | A bundled HF recursive-quotient witness for empty, exact pairing, respectful separation, exact big union, extensionality, and foundation |
| Natural-number reconstruction | Injective von Neumann naturals in the recursive quotient, with rank `n`, exact membership `m ∈ n ↔ m < n`, complete classification of ordinal members, internal transitivity, membership trichotomy, and successor `n + 1 = n ∪ {n}` |
| Recursive union algebra | Recursive quotient union is associative, commutative, and has empty as identity |
| Recursive membership | Membership descends to the recursive quotient; empty has no members, each union summand embeds, and extensionality is proved |

## Deliberately conditional research claims

Generic `∂² = 0`, pushout universality, linear completeness, and preservation
of categorical limits/colimits require additional hypotheses. They are not
claimed as unconditional Lean theorems.

The finite model establishes satisfiability only for the present implemented
finite fragment relative to Lean; it is not a formal ZF or HoTT consistency
model.
