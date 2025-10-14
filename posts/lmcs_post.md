---
title: "Incidence Type Theory: A Coinductive Foundation for Relational Structures"
journal: "Logical Methods in Computer Science"
---

### Abstract

While modern type theories, including Homotopy Type Theory (HoTT), provide powerful tools for formalizing mathematics, they often lack native support for representing and reasoning about structures with explicit sharing, dynamic topologies, or non-well-founded behavior. This paper introduces Incidence Type Theory (ITT), a foundational system based on the Theory of Incidence (RIF), which treats relations themselves as the primary building blocks.

In ITT, the universe of structures `I` is modeled as a single, large coinductive type, whose inhabitants are `incidences`. The theory is governed by a boundary operator `∂` and a composition operator `glue`, allowing for the construction of complex relational structures. We present Incidence Logic (IL), a formal proof system for ITT featuring principles of structural induction, guarded coinduction for reasoning about productive, non-well-founded systems, and observational equivalence (`≈`).

We further propose an "Incidence-Univalence" axiom, analogous to HoTT's Univalence, which equates observational equivalence with identity. This provides a powerful principle for reasoning about structural isomorphism. The framework is shown to admit a model within HoTT, establishing its formal consistency. By providing a type-theoretic foundation where relational structures are native, ITT offers a new formal language for specifying and verifying properties of programs and systems with complex, evolving, and potentially infinite state spaces, such as those found in concurrency theory and programming language semantics.
