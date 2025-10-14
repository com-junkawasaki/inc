# Theory of Incidence — Set, Category, Type, and Inc

> A Fourth Foundation for Mathematics and Computation, where relations are the sole primitive entity.

## Overview

This repository hosts the development of the **Theory of Incidence (Inc)**, a proposed fourth foundational framework for mathematics and computation. It stands alongside Set Theory, Category Theory, and Type Theory, offering a new perspective where relations, or "incidences," are the primary building blocks of all structures.

Conventional foundations separate entities from the relationships between them. Inc unifies them by treating every mathematical object—from numbers and sets to functions and categories—as a configuration of incidences. This relational-first approach provides a native language for describing systems with dynamic, recursive, or self-referential structures, which are common in computer science, physics, and biology but are often cumbersome to model in existing frameworks.

## The Vision: Beyond Set, Category, and Type

The goal of Inc is not to replace existing foundations but to provide a unifying substrate that claIncies their connections and addresses their limitations:

1.  **Unifying Objects and Relations**: Inc eliminates the object-relation dualism. An "object" is simply a stable pattern of relations (a zero-ary or fixed-point incidence).
2.  **Native Support for Dynamic Structures**: Through its coinductive mode, Inc can formally model systems that change their own structure over time, such as evolving networks or computational processes.
3.  **Bridging Logic and Geometry**: The theory's axiomatic connection between its relational syntax and linear-algebraic semantics (via Boundary Matrices and Laplacians) creates a direct bridge between formal proof and numerical analysis.

## Core Concepts

The theory is built upon a few simple but powerful ideas:

-   **Incidence (`I`)**: The only primitive type. An incidence is a pure relation that connects other incidences.
-   **Boundary Operator (`∂`)**: A function that defines an incidence by specifying its endpoints. Since endpoints are also incidences, the structure is fully recursive.
-   **Gluing (`glue`)**: The fundamental composition operator. It allows complex structures to be built by "gluing" incidences together along their shared boundaries.
-   **Observational Equivalence (`≈`)**: A form of bisimulation that defines when two incidence structures are considered the same, providing a robust notion of equivalence that respects behavior and structure.

## Project Roadmap

The development of Inc is guided by the process network defined in `story.jsonnet`. The project is divided into four main stages:

1.  **Theoretical Foundation**:
    -   Formalize the core axioms (A1-A17).
    -   Develop **Incidence Logic (IL)**, the formal proof system for Inc.
    -   Establish consistency by constructing models in ZF, Adhesive Categories, and HoTT.
    -   Formalize the translation between Inc and other foundations.

2.  **Reference Implementation**:
    -   Implement the core data structures and operators in a suitable language (e.g., Lean/Agda for formalization, Julia/Python for computation).
    -   Develop the linear-algebraic backend for numerical analysis.
    -   Formalize the theory in a proof assistant to veIncy its properties.

3.  **Academic Publication**:
    -   Publish a foundational paper outlining the theory.
    -   Submit a preprint to arXiv to engage with the community.
    -   Target journals in mathematical logic (`math.LO`), category theory (`math.CT`), and logic in computer science (`cs.LO`).

4.  **Application & Validation**:
    -   Apply Inc to model complex systems in various domains, such as computational processes, mathematical structures (e.g., simplicial homology), and biological networks.

## Getting Started

This project is currently in the foundational stage. The primary document guiding the work is [`story.jsonnet`](./story.jsonnet), which contains the formal project plan as a Merkle DAG.

Further details on the theory and its axiomatization can be found in the project's working documents. (Further links to be added).
