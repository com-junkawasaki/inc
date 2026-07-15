# Public database coverage log

Snapshot date: 2026-07-15

Scope: public Crossref metadata plus openly discoverable zbMATH Open, publisher,
arXiv, EuDML, AFP, and Mizar records.  This is a reproducible discovery log, not a
systematic review.  It does not substitute for subscription-database searches,
citation chasing, or specialist judgment.

## Query families

The following exact English query families were used in Crossref and web
discovery, together with reordered terms and singular/plural variants:

1. `incidence structure quotient bisimulation`
2. `ternary relation quotient congruence`
3. `finite obstruction automorphism orbit classification`
4. `coalgebraic quotient coequalizer bisimulation`
5. `relational structures congruence quotient n-ary relations`
6. `strong homomorphism quotient relational structures`
7. `compatibility obstruction quotient relation`
8. `incidence resonance quotient`

The same core strings were restricted to `site:zbmath.org`.  Returned ternary
logic, fuzzy-relation, fixed-point, group-orbit, and classical incidence-geometry
records were screened as terminology collisions; none addressed the target
quotient-compatibility conjunction.  This keyword screen is distinct from the
MSC classification and cited-by traversal still required below.

Crossref requests used `query.bibliographic`, `rows=5`, and selected DOI, title,
author, and publication date.  High result counts and ranking instability mean
the top-five samples are discovery aids only; they are not exhaustive evidence.

## Candidate disposition log

| Candidate | Why inspected | Disposition for this paper |
|---|---|---|
| Staton, [Relating coalgebraic notions of bisimulation](https://doi.org/10.2168/LMCS-7(1:13)2011) | Crossref top result for coalgebraic quotient/bisimulation terminology; compares general coalgebraic bisimulation notions | **Include as background.** It reinforces that general bisimulation theory is prior art; it does not state the incidence-specific ternary compatibility or finite classification. |
| Marić, [Bisimulation Quotient in Inquisitive Modal Logic](https://doi.org/10.3390/logics3030011) | Exact phrase “bisimulation quotient”; proves quotient existence, bounded morphism, and quotient-isomorphism characterization in a modal setting | **Include as close logical analogue.** It blocks broad novelty claims for bisimulation quotients connected to modal logic.  Its model signature and theorem target differ from exact descent of an independently supplied ternary relation. |
| Kurz and Rosický, [Operations and equations for coalgebras](https://doi.org/10.1017/S0960129504004402) | Coalgebraic operations/equations and bisimulation-invariant modal operators | **Include as background.** It blocks novelty claims for coalgebraic equations or modal invariance in general. |
| Chajda and Länger, [Quotients and homomorphisms of relational systems](https://eudml.org/doc/116512) | Direct quotient/strong-homomorphism terminology for relational systems | **Include as relational-quotient comparison.** It treats one binary relation; the current exact three-coordinate iff is an arity-three instance of general relational compatibility, while the incidence-generated relation and finite obstruction family remain the specialized content. |
| Novotný, [Homomorphisms and strong homomorphisms of relational structures](https://eudml.org/doc/248043) | Strong morphism vocabulary for relational structures | **Include for terminology only.** It further prevents presenting strong preservation/reflection as a new morphism notion. |
| Korolkiewicz, [Many Sorted Quotient Algebra](https://fm.mizar.org/1996-5/pdf5-1/msualg_4.pdf) | Many-sorted quotient and congruence | **Include as mechanized algebraic prior art.** Operations rather than the independent incidence/resonance conjunction. |
| Blanchette, Popescu, and Traytel, [Operations on Bounded Natural Functors](https://isa-afp.org/entries/BNF_Operations.html) | Mechanized bisimulation and quotient coalgebra | **Include as mechanized coalgebraic prior art.** It blocks formalization-first claims for quotient coalgebras. |
| Dewan and Dixit, [Congruence and Green's equivalence relation on ternary semigroup](https://doi.org/10.1501/commua1_0000000429) | Crossref top result for ternary congruence | **Exclude from close comparison after inspection of scope.** A ternary *operation*/semigroup congruence is not an arbitrary multi-valued ternary relation, though it is useful terminology evidence. |
| CI-group and finite-group automorphism-orbit papers returned by the orbit query | Exact orbit-count vocabulary | **Exclude as domain-mismatched.** They classify group elements under group automorphisms, not compatibility obstructions under simplex automorphisms. They confirm that orbit classification itself cannot be claimed as a novel method. |
| General CSP, ternary Cayley-structure, topology, and geometric obstruction results | Returned by broad n-ary/obstruction searches | **Exclude as false positives.** Their obstruction or ternary terminology does not concern quotient well-definedness under coordinate replacement. |

## Effect on the novelty boundary

The public-database pass strengthens the conservative formulation:

- exact descent of an n-ary relation through a congruence is standard
  relational-structure compatibility;
- bisimulation quotients, modal invariance, quotient coalgebras, strong
  relational homomorphisms, and automorphism-orbit classifications are known
  independently;
- the defensible candidate is only the assembled incidence-specific theorem
  package and its particular obstruction invariant, not any ingredient or
  method by itself.

No query result establishes priority, and no absence from a result page is
evidence that a theorem has not appeared under different terminology.

## Coverage still external

The following cannot be marked complete by this public pass:

- MathSciNet search and zbMATH MSC classification/cited-by traversal;
- Scopus and Web of Science cited-reference searches;
- searches in languages and terminology not represented above;
- confirmation by a coalgebra/incidence specialist that no closer theorem was
  missed.

Record those searches with database, date, exact query, result count, screened
count, candidates retained, and reviewer identity before changing the journal
gate to passed.
