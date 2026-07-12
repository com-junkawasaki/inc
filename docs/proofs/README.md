# Proof map

Use this index to navigate the checked development by subject rather than by
research chronology.

| Subject | Primary Lean source | Supporting documentation |
|---|---|---|
| Incidence axioms and core | `IncidenceTheory.lean`, `Axioms/` | [status](../status.md) |
| Resonance relation, laws, congruence, and homomorphisms | `Axioms.lean`, `IncidenceTheory.lean`, `GraphModel.lean`, `Peano.lean`, `Product.lean` | [resonance ADR](../adr/2607121930-resonance-as-central-primitive.md) |
| Resonance-preserving translations | `IncidenceTheory.lean` (`ResonantBehavioralTranslation`) | [resonance ADR](../adr/2607121930-resonance-as-central-primitive.md) |
| Resonance on bisimulation quotients | `IncidenceTheory.lean`, `Peano.lean` | [resonance ADR](../adr/2607121930-resonance-as-central-primitive.md) |
| Relational associativity and product preservation | `IncidenceTheory.lean`, `Peano.lean`, `Product.lean` | [resonance ADR](../adr/2607121930-resonance-as-central-primitive.md) |
| Resonance internal-logic atoms and semantic laws | `Logic.lean`, `Coherent.lean` | [resonance ADR](../adr/2607121930-resonance-as-central-primitive.md) |
| Finite resonance-language completeness and countermodels | `GraphModel.lean` | [resonance ADR](../adr/2607121930-resonance-as-central-primitive.md) |
| Finite physical resonance diagram and relative completeness | `GraphModel.lean` (`finiteResonanceDiagram`) | [status](../status.md#checked-foundations) |
| Generic finite physical resonance completeness | `Logic.lean` (`FinitePhysicalResonanceLogic`) | [status](../status.md#checked-foundations) |
| Product closure of normalized resonance completion | `Product.lean`, `CrossInstance.lean` | [status](../status.md#conditional-or-unfinished-layers) |
| Normalized dependent resonance completion | `CrossInstance.lean`, `GraphModel.lean` (`IncDepRawNormalizedResonanceCompletion`) | [status](../status.md#conditional-or-unfinished-layers) |
| Concrete models | `GraphModel.lean`, `Cycle.lean` | [history](../history/post-cycle-41.md) |
| Bisimulation and faithfulness | `IncidenceTheory.lean`, `CrossInstance.lean` | [completion audit](../inc-proof-completion-audit.md) |
| Internal logic | `Logic.lean` | [status](../status.md) |
| Natural numbers and HF sets | `Peano.lean`, `HFSets.lean` | [history](../history/post-cycle-41.md) |
| Pairs and trees | `Pairs.lean`, `Tree.lean` | [history](../history/post-cycle-41.md) |
| Paths and simplices | `PathComplex.lean`, `Simplex.lean` | [history](../history/post-cycle-41.md) |
| Product, sum, quotient | `Product.lean`, `Sum.lean`, `Quotient.lean` | [cycle-41 ADR](../adr/2607100600-inc-theory-maturity-cycle41.md) |
| Dependent calculus | `CrossInstance.lean` | [completion audit](../inc-proof-completion-audit.md) |
| Normalized structural preservation | `CrossInstance.lean` | [status](../status.md#structural-preservation-completion) |

## Reading order

1. Start with the root [README](../../README.md).
2. Read the [authoritative status](../status.md).
3. Use this table to locate the relevant Lean declarations.
4. Consult the [detailed history](../history/post-cycle-41.md) only when the
   development chronology or negative findings are needed.
