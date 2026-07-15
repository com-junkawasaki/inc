# Related work and novelty boundary

## Scope

This is a scoped primary-source audit for the first incidence/resonance paper,
performed on 2026-07-15. It is not a systematic review and does not establish a
priority claim. Its purpose is to separate standard quotient machinery from the
project-specific theorem package before an arXiv submission.

## Comparison

| Area | Established background | Relation to this paper |
| --- | --- | --- |
| Universal algebra | Congruences, quotient algebras, homomorphism theorems, term algebras, and free algebras are standard; see Burris and Sankappanavar, [*A Course in Universal Algebra*](https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html). | Representative independence of an operation or relation, and the resulting unique quotient structure, must not be advertised as new in isolation. The term-algebra core remains supporting algebra. The extension by nonempty incidence-boundary and relational-resonance generators is project-specific, but no novelty claim is made for the general generators-and-relations method. |
| Coalgebra and bisimulation | Behavioural equivalence, bisimulation, quotient/minimization, and kernel-pair/coequalizer reasoning belong to established coalgebraic semantics; see Rutten, [*Universal coalgebra: a theory of systems*](https://doi.org/10.1016/S0304-0208(00)00056-6), and Wißmann, [*Coalgebraic Semantics and Minimization in Sets and Beyond*](https://thorsten-wissmann.de/theses/dissertation-wissmann.pdf). Dorsch, Milius, Schröder, and Wißmann give a generic finite behavioural-quotient algorithm in [CONCUR 2017](https://doi.org/10.4230/LIPIcs.CONCUR.2017.32). | The checked coequalizer is the correct categorical formulation, but a coequalizer of a compatible behavioural quotient and executable partition refinement are not by themselves novelty claims. The paper instead studies when an independently supplied ternary resonance relation is compatible with the particular incidence bisimulation, then classifies failures of that compatibility. |
| Coalgebraic modal logic | Invariance under behavioural equivalence and Hennessy--Milner-style converses are established themes. Bakhtiari and Hansen prove an exact expressiveness result for a parametric coalgebraic bisimulation in [CALCO 2017](https://doi.org/10.4230/LIPIcs.CALCO.2017.4); Bakhtiari, Hansen, and Kurz explicitly review behavioural invariance in their [2019 account](https://digitalcommons.chapman.edu/engineering_articles/69/). | The `ResonanceFormula` result is a deliberately small, tailored observation theorem: exact descent is equivalent to invariance of a propositional language with one ternary atom. It is not a new general Hennessy--Milner theorem. Its value is as an internal necessity witness for this quotient problem. |
| Bisimulation quotients in modal models | Marić constructs bisimulation quotients for inquisitive modal models and proves their connection by surjective bounded morphisms and a quotient-isomorphism characterization in [Logics 2025](https://doi.org/10.3390/logics3030011). | This blocks any broad claim that a modal/bisimulation quotient is new. The current theorem instead asks when a separately supplied ternary relation is exactly representative-independent for an incidence-generated equivalence. |
| Quotients of relational systems | Chajda and Länger study quotient relational systems and strong mappings for one binary relation in [2010](https://eudml.org/doc/116512); Novotný treats strong homomorphisms of relational structures in [1997](https://eudml.org/doc/248043). | Exact coordinatewise invariance is standard relational compatibility. The specialized content is the source of the equivalence from incidence, its interaction with a multi-valued ternary relation, and the resulting finite obstruction invariant. |
| Many-sorted quotients | Sort-indexed congruences, quotient algebras, and homomorphism theorems are standard in many-sorted universal algebra; Salehi states a many-sorted homomorphism theorem in [*Varieties of Many-Sorted Recognizable Sets*](https://saeedsalehi.ir/pdf/papers/PUMA.pdf). For signatures with relation symbols, the standard quotient-model definition requires relations to be representative independent; a concise formulation appears in the [Kyushu many-sorted model-theory notes](https://imi.kyushu-u.ac.jp/~daniel/model-theory/slides/mt3.pdf). | The project’s ternary relation is formally a one-sorted relational symbol. `QuotientResonanceCongruent` is exactly its representative-independence condition, and `CongruencedTernaryResonanceSystem.quotientSystem` is a scoped instance of this standard mechanism. The distinctive content cannot be the mere existence of a relational quotient; it must come from the incidence-derived equivalence, necessity criteria, obstruction structure, and checked examples. |
| Incidence hypergraphs | Grilliette and Rusnak define an incidence hypergraph as sets of vertices, edges, and incidences with two incidence maps, and study the resulting presheaf/topos category in [arXiv:1805.07670](https://arxiv.org/abs/1805.07670). Follow-up work treats injectivity and incidence-matrix/Laplacian structure in [arXiv:1910.02305](https://arxiv.org/abs/1910.02305), box products and exponentials in [arXiv:2007.01842](https://arxiv.org/abs/2007.01842), and functorial repairs of graph constructions in [arXiv:2403.13165](https://arxiv.org/abs/2403.13165). | “Incidence” and categorical treatment of incidence hypergraphs are not new here. The checked `incidenceBoundaryHypergraph` now gives a precise comparison: source cells are edges, endpoint cells are vertices, and concrete endpoint occurrences are incidences. `StructuredIncidenceHom.toCategoricalIncidenceHypergraphHom` preserves the two incidence maps and respects identity and composition. This is deliberately forgetful, not an equivalence or faithful representation: roles, signs, multiplicities, glue, resonance, guards, and types are discarded. |
| Chemical reaction networks and Petri nets | Reaction networks/Petri nets use species and reactions with input/output stoichiometry. Baez and Pollard develop open reaction networks and their rate-equation and black-boxing functors in [*A Compositional Framework for Reaction Networks*](https://arxiv.org/abs/1704.02051). Baez, Genovese, Master, and Shulman compare Petri-net variants and execution semantics in [*Categories of Nets*](https://arxiv.org/abs/2101.04238). | `chemicalReactionIncidence` is a deliberately small structural example: signed reactant/product endpoints encode `A ⇌ B`, and relational resonance adds coarse interacting-reaction modes. Its exact molecule/reaction quotient is checked, but it has no rates, concentrations, firing semantics, mass-action dynamics, thermodynamics, or black-boxing. It demonstrates applicability of the quotient criterion; it does not compete with established reaction-network semantics. |
| Finite obstruction methods | Finite counterexample enumeration and quotienting certificates by symmetry are general mathematical techniques. | The potentially distinctive result is their exact realization for this ternary descent problem: global congruence decomposes into three coordinate conditions, producing a `3 n^4` search; support-minimal certificates are quotiented by resonance-bisimulation automorphisms; and the seven-cell simplex computation yields 12 automorphisms and 32 minimal-obstruction orbits, all checked in Lean. No claim is made that symmetry-reduced obstruction enumeration itself is new. |

## Defensible contribution statement

Subject to a fuller expert literature review, the paper can claim the following
combined contribution:

1. It isolates the compatibility condition between an incidence-derived
   bisimulation and an independent, possibly multi-valued ternary resonance
   relation, proves exact descent, uniqueness, and its coequalizer universal
   property, and exhibits both failure and nontrivial success.
2. It refines failure into coordinatewise finite certificates, proves existence
   of support-minimal obstructions, and supplies an executable classification
   modulo structure-preserving automorphisms, including an exhaustive five-family
   coordinate-and-shape taxonomy and an orbit-constant coordinate normal form
   for all 32 simplex orbits.
3. It connects the abstract criterion to a negative functional selector model,
   a positive relational transport-and-saturation criterion, and a generic
   class-mode representation whose simplex instance has a three-class quotient.
4. It machine-checks this whole theorem spine in one Lean development, including
   the finite counts and the tailored logical necessity converse.
5. It includes a signed reversible reaction-network instance whose molecular
   and reaction cells form the exact behavioral quotient and whose reaction
   interaction is genuinely relational and multi-valued.

The contribution is therefore the incidence/resonance synthesis and its checked
structural and finite consequences, not any one standard quotient lemma.

## Citation chain and definition-level comparison

The citation chain used for positioning is now explicit:

1. Rutten supplies the universal-coalgebra baseline for behavioural
   equivalence. Wißmann develops coalgebraic minimization beyond `Set`, while
   Dorsch--Milius--Schröder--Wißmann give the executable finite quotient
   baseline. These works rule out novelty claims based only on behavioural
   quotienting or minimization.
2. Many-sorted universal algebra supplies sortwise congruences and quotient
   homomorphism theorems. Many-sorted model theory supplies the additional
   representative-independence requirement for relation symbols. These works
   rule out novelty claims based only on descending a compatible ternary
   relation.
3. Grilliette--Rusnak supply the categorical incidence-hypergraph baseline and
   the exact three-sort diagram used for comparison. Their follow-up papers
   establish that products, exponentials, injectivity, incidence matrices, and
   Laplacians already belong to a developed categorical incidence theory.
4. The present paper starts only after those baselines: the equivalence is
   generated by the boundary behavior of a richer single-carrier Incidence,
   resonance is independently supplied, and the main question is when the two
   structures are compatible and how finite incompatibility is classified.
5. Baez--Pollard and the categories-of-nets literature supply the reaction-
   network baseline. The checked reversible model is positioned only as a
   structural incidence/resonance instance; all kinetic and execution-semantic
   claims remain outside scope.

The definitions compare as follows:

| Component | Categorical incidence hypergraph | This development | Checked comparison |
| --- | --- | --- | --- |
| Carriers | Separate `V`, `E`, and incidence set `A` | One cell carrier `I`, endpoint roles `R`, and types `T` | `incidenceBoundaryHypergraph` uses `V = I`, `E = I`, and boundary occurrences for `A`. |
| Incidence maps | `A → V` and `A → E` | An endpoint occurrence records its endpoint cell and the source whose boundary contains it | `vertexOf` selects the endpoint cell; `edgeOf` selects the boundary source. |
| Multiplicity/orientation | Represented only if added as extra structure | Each endpoint has role, sign, and positive multiplicity | Forgotten by the three-sort encoding; identical duplicate list entries are not distinguished as separate incidence points because membership proofs are proof-irrelevant. |
| Morphisms | Three maps commuting with the two incidence maps | `StructuredIncidenceHom` has one cell map preserving unit, glue, boundary membership, and resonance | The same cell map is used on `V` and `E`; mapped endpoint occurrences give the incidence map. Identity and composition are checked. |
| Behavioral quotient | Not part of the bare incidence-hypergraph definition | Generated from boundary behavior by `approxBisim` | No claim that this is a standard hypergraph quotient. |
| Resonance | Not part of the bare three-sort diagram | Independent ternary relation plus optional selector | Forgotten; therefore the encoding cannot establish equivalence of theories or reflect resonance descent. |

Consequently the new Lean construction closes the former definition-comparison
gap, but it also proves why the safe claim is a forgetful boundary encoding,
not a representation equivalence with the established incidence-hypergraph
category.

## Claims excluded without further evidence

- “the first quotient/coequalizer theorem for incidence structures”;
- “the first categorical theory of incidence hypergraphs”;
- “a new general Hennessy--Milner theorem”;
- “a classification of all incidence/resonance structures”;
- novelty of congruence descent, free term algebras, or symmetry reduction by
  themselves;
- priority over all published literature or a formalization-first claim;
- an equivalence or faithful representation of the full structure by ordinary
  incidence hypergraphs or coalgebras (the checked boundary encoding is
  explicitly forgetful).

## Mechanized prior-art audit and remaining literature work

The scoped Lean/mathlib, Isabelle/AFP, Mizar/MML, and Rocq audit is recorded in
[`mechanized-prior-art-audit.md`](mechanized-prior-art-audit.md).  It found
substantial existing mechanizations of quotient coalgebras, bisimulation and
coinduction, coequalizers, and many-sorted quotient algebras.  Those generic
results are therefore explicitly excluded from the novelty claim.  The audit
did not locate the exact incidence/ternary/finite-obstruction conjunction, but
that negative search result is not evidence of priority.

The expanded public Crossref/publisher/arXiv/EuDML discovery pass, exact query
families, candidate dispositions, and false-positive exclusions are recorded in
[`public-database-coverage-log.md`](public-database-coverage-log.md).

Before journal submission:

- extend coverage into subscription databases and cited-reference traversal;
- have a coalgebra/incidence specialist review the novelty statement and the
  precise status of the forgetful boundary encoding.  The ready-to-send request,
  five decision questions, and required response record are in
  [`specialist-review-packet.md`](specialist-review-packet.md).
