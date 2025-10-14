---
title: "Theory of Incidence: A Fourth Foundation Beyond Set, Category, and Type"
authors: "..."
date: "October 14, 2025"
---

### Abstract

Classical mathematical foundations—set theory, category theory, and type theory—provide distinct but compatible paradigms for representing mathematical and computational structure. Yet all share a fundamental limitation: they presuppose a separation between objects and relations. Sets collect elements, categories connect objects, and types classify terms, but none take relation itself as the primitive entity.

We propose the Theory of Incidence as a fourth foundational system in which incidences—relations that may themselves relate to other incidences—are the sole primitive constituents of mathematical structure. Each incidence `i ∈ I` is equipped with a boundary operator `∂: I → MSet(I × R × Σ × N)`, assigning to `i` a finite or guardedly infinite multiset of endpoint incidences, roles, orientations, and multiplicities. Composition of structures is governed by a gluing operator, subject to axioms (A1–A17) ensuring finiteness, type-consistency, compositional closure, and observational equivalence.

Within this framework,
- Sets correspond to zero-ary incidences,
- Categories arise as incidence systems closed under gluing, and
- Types emerge as inductive or coinductive families over incidence configurations.

The theory admits multiple semantic realizations: a set-theoretic model (conservative over ZF), an adhesive-category model (gluing semantics), and a homotopy-type-theoretic model (via coinductive types). A linear-semantic layer—defined through boundary matrices and Laplacians—connects logical inference to spectral computation, linking proof theory with numerical analysis.

The Theory of Incidence thus provides a unifying relational substrate for Set, Cat, and Type: a formalism where relations are first-class citizens, recursion and coinduction are native, and evolving or self-referential structures are expressible without additional meta-level machinery. This approach suggests a direction toward a unified foundation of mathematics and computation based purely on relational composition and equivalence.

### 1. Introduction
Classical foundations separate objects from relations. Incidence Theory unifies them by making relations primitive.

### 2. Formal Definitions
- Incidence set I
- Boundary operator ∂: I → MSet(I × R × Σ × N)

### 3. Axioms (A1–A17)
A1: Finite Endpoints - For all i, ∂(i) is finite.
A2: Type Consistency - Boundary incidences share the same type as the parent.
A3: Sign Rules - Orientations are restricted to -1, 0, +1.
A4: Multiplicities - Each boundary entry has multiplicity ≥1.
A5: Mode Selection - Well-founded or guarded coinductive modes.
A6: Gluing Existence - Gluing operation exists for compatible incidences.
A7: Unit Laws - Unit incidences satisfy left and right identity.
A8: Associativity - Gluing is associative.
A9: Type Preservation - Gluing preserves types.
A10: Guard Preservation - Coinductive guards are maintained under gluing.
A11: Observational Equivalence - Bisimulation based on types and boundaries.
A12: Congruence - Equivalence is preserved under gluing.
A13: Normalization - Structures can be normalized to canonical forms.
A14: Functoriality - Morphisms preserve boundaries.
A15: Colimits - Existence of pushouts and sums.
A16: Boundary Matrix - Defines spectral properties.
A17: Laplacian - Ensures positive semidefiniteness for analysis.

### 4. Relations to Set, Category, and Type Theories
Prove embeddings: Sets as nullary incidences, with membership as gluing. Categories via morphism incidences. Types through inductive definitions.

Proof of set embedding: Define a set S as the collection of nullary incidences where membership is encoded via gluing operations preserving extensionality.

### 5. Semantic Models
Construct ZF model: Interpret incidences as sets with boundary functions.
Adhesive category model: Gluing as pushouts.
HoTT model: Coinductive types for recursive incidences.

Consistency proof: Show that the ZF model interprets all RIF axioms without contradiction, as incidences map to well-founded sets.

Type consistency proof: From A2, boundary incidences share the same type as the parent, ensuring type safety in gluing operations.

Observational equivalence proof: A11 defines ≈ as type and boundary equality, establishing a bisimulation relation.

### 6. Linear Semantics
- Boundary matrices and Laplacians
- Linking logic to spectral methods

### 7. Examples and Applications
- Graph structures
- Self-referential systems
- Applications in computation and medicine

### 8. Conclusion
The Theory of Incidence establishes a relational foundation unifying Set, Cat, and Type.
