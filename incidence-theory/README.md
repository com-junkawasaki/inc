# Incidence Theory - Lean 4 Formalization

This directory contains the complete formalization of the Theory of Incidence in Lean 4.

## Quick Build

```bash
lake build          # Build all proofs and definitions
lake exe incidence-theory  # Run the main executable with examples
```

## Project Structure

### Core Modules
- `IncidenceTheory.lean` - Main API with modular axioms integration
- `IncidenceTheory/Axioms.lean` - Complete Incidence structure (A1-A17)
- `IncidenceTheory/GraphModel.lean` - Concrete models and examples
- `Main.lean` - Entry point demonstrating the triangle graph example

### Axiom Modules (Modular Design)
Each axiom is now in its own module for independent development and verification:

**Foundation (A1-A5)**:
- `Axioms/Basic.lean` - Sign, Endpoint, Boundary types
- `Axioms/A1.lean` - Finite Endpoints
- `Axioms/A2.lean` - Type Consistency
- `Axioms/A3.lean` - Sign Rules
- `Axioms/A4.lean` - Multiplicities
- `Axioms/A5.lean` - Well-founded Mode

**Operations (A6-A13)**:
- `Axioms/A6_A8.lean` - Gluing (Existence, Unit, Associativity)
- `Axioms/A9_A13.lean` - Boundary Preservation (Type/Guard/Equivalence/Congruence/Normalization)

**Extensions (A14-A17)**:
- `Axioms/A14_A17.lean` - Advanced features (Functoriality, Colimits, Linear Algebra)

### Legacy Files
- `IncidenceTheory/Basic.lean` - Legacy implementation (being phased out)

## Verification

All axioms A1-A17 are formalized and proven. The CI ensures:
- All proofs check correctly
- Examples run without errors
- Boundary matrices and Laplacians compute properly

## Key Components

- **Incidence Structure**: Core type with boundary, type function, and gluing
- **Bisimulation**: Observational equivalence (≈) with reflexivity/symmetry/transitivity
- **Linear Algebra**: Boundary matrices and Laplacians for spectral analysis
- **Models**: Graph-based concrete implementations

See the main [README](../README.md) for theory details and CI status.