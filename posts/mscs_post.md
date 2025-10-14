---
title: "A Theory of Incidence: Unifying Mathematical Structures through Relational Composition"
journal: "Mathematical Structures in Computer Science"
---

### Abstract

The representation of mathematical structures in computer science often requires translating between different formalisms, such as graphs, categories, and rewriting systems. This paper introduces the Theory of Incidence (RIF), a foundational framework designed to unify these representations by positing `incidences`—primitive, recursive relations—as the sole structural entity.

At the core of RIF is a boundary operator `∂` that defines incidences recursively, and a `glue` operator that composes them. This composition is modeled as a pushout in an adhesive category, providing a direct correspondence to Double-Pushout (DPO) graph rewriting and ensuring that structural composition is algebraically well-behaved. We demonstrate that common structures like graphs, hypergraphs, and categories are emergent properties of incidence configurations, derived from zero-ary (objects) and n-ary (morphisms) incidences.

Furthermore, RIF incorporates a canonical linear-algebraic interpretation. Each incidence structure inherently defines a boundary matrix `B` and a corresponding Laplacian `L`. This allows for the direct application of spectral methods for analyzing structural properties like connectivity, community structure, and centrality, thus bridging the gap between symbolic structural representation and numerical analysis. We argue that RIF offers a robust and unified language for specifying, composing, and analyzing the mathematical structures fundamental to computer science.
