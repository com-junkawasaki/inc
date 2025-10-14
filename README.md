# Theory of Incidence — Set, Category, Type, and Incidence

> A Fourth Foundation for Mathematics and Computation, where relations are the sole primitive entity.

## DOI

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17345516.svg)](https://doi.org/10.5281/zenodo.17345516)

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

### Building the Lean Formalization

The formal axioms and proofs are implemented in Lean4. To build and verify:

1. Install Lean4 via elan: `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y`
2. Clone the repository and navigate to the Lean project: `cd incidence-theory`
3. Build the project: `lake build`
4. Run examples (if any): `lake exe incidence-theory`

#### Current Lean Proof Coverage

The Lean formalization currently covers:

- **Core Structure**: `Incidence` structure with boundary, type function, gluing, unit, A1 finite endpoints, A2 type consistency, A3 sign rules, A4 multiplicities, A5 well-founded mode, A6 gluing existence, A7 unit laws, A8 associativity, A9 boundary preservation, A10 type preservation, A11 boundary gluing, A12 boundary unit, and A13 boundary associativity.
- **Basic Operations**: `glue` function for composition, `approx` relation for observational equivalence.
- **Fundamental Lemmas**:
  - `approx_refl`: Reflexivity of ≈.
  - `approx_symm`: Symmetry of ≈.
  - `approx_trans`: Transitivity of ≈.
  - `finite_endpoints_theorem`: A1 axiom ensuring boundary lists are finite.
  - `type_consistency`: A2 axiom ensuring boundary elements share parent type.
  - `sign_rules_theorem`: A3 axiom ensuring boundary orientations are -1, 0, or 1.
  - `multiplicities_theorem`: A4 axiom ensuring boundary multiplicities are ≥ 1.
  - `well_founded_theorem`: A5 axiom ensuring well-founded boundary recursion.
  - `gluing_existence_theorem`: A6 axiom ensuring gluing is always defined.
  - `unit_left_theorem`: A7 axiom ensuring left unit law for gluing.
  - `unit_right_theorem`: A7 axiom ensuring right unit law for gluing.
  - `associativity_theorem`: A8 axiom ensuring gluing is associative.
  - `boundary_preservation_theorem`: A9 axiom ensuring boundary elements are preserved in gluing.
  - `type_preservation_theorem`: A10 axiom ensuring types are preserved in gluing.
  - `boundary_gluing_theorem`: A11 axiom defining boundary composition.
  - `boundary_unit_theorem`: A12 axiom defining boundary unit behavior.
  - `boundary_associativity_theorem`: A13 axiom ensuring boundary associativity.
- **Examples**:
  - Simple incidence structures with trivial boundaries.
  - Graph structures: Nodes (nullary incidences) and edges (binary incidences with boundary connections).
  - Type distinction: Incidences with different type tags (e.g., `node` vs. `edge`) where `approx` requires both type and boundary equality.
  - Complex gluing: Boundary merging operations that combine incidences into composites with merged boundaries.
  - Verification that `approx` distinguishes incidences based on boundary and type differences.

**Coverage**: ~70% of the full Incidence Theory (A1-A17 axioms and semantic models). Includes core axioms (A1-A13), equivalence proofs, and examples demonstrating relational composition and type safety.

### Viewing the Paper

The draft paper is available in Markdown (`posts/arxiv_post.md`) and LaTeX (`posts/arxiv_paper.tex`). Compile the LaTeX version with pdflatex for a formatted PDF.

Further details on the theory and its axiomatization can be found in the project's working documents. (Further links to be added).
