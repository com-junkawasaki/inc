---
layout: default
title: Incidence Proof Completion Audit
description: Scope and checked evidence for the formal incidence core
---

# Incidence proof completion audit

This page distinguishes checked results from stronger claims that need extra
data.  The Lean source in `incidence-theory/` is authoritative.

| Requested item | Checked evidence | Scope |
| --- | --- | --- |
| Consistency model | `finiteIncidenceConsistencyCertificate`, `FiniteIncidenceLayerCertificate` | A concrete nonempty two-object Lean model of the implemented incidence, gluing, normalization, and algebraic layers. |
| Preservation | Formula/Kripke map identity, composition, and reflection; `boundaryRowBalanced_congr`; `PushoutPreservingFamily` | Translation results are conditional precisely on the stated maps, boundary equality, or preservation family. |
| Completeness | `kripke_entails_iff_derives_of_atom_coding` and canonical-countermodel theorems | Intuitionistic propositional fragment over atom types with an explicit code/decode retraction, including `Fin n`, `Bool`, `Nat`, and `FiniteIncidence`. |
| Internal logic | Natural deduction, cut/substitution, Kripke soundness, canonical truth lemma, countermodels | Propositional intuitionistic logic over incidence atoms. |
| Mathematical reconstruction | `HFRecursiveSetFragmentModel`, finite ordinals, products, powersets, relations, and shift graphs | Hereditarily finite, extensional recursive-set fragment; not full ZF or HoTT. |
| Nontrivial sorry-free theorems | Triangle `∂²=0`, balance-to-kernel, spectral family, quotient classification, product/powerset laws | Each theorem is compiled by Lean; the verifier rejects `sorry` and Lean `axiom` declarations. |

## Deliberate boundaries

- Generic `∂²=0`, linear completeness, and colimit preservation are false or
  underdetermined without additional hypotheses.  The core exposes those
  hypotheses explicitly (`BoundaryRowBalanced`, `PushoutPreservingFamily`,
  `BisimulationNormalizationSpec`) instead of asserting unconditional claims.
- A11--A15 are represented by optional specifications, so existing models
  remain source-compatible while clients may require the stronger layers.
- The recursive-set work is a finite fragment.  A formal full-ZF or HoTT
  consistency theorem requires a separately specified ambient theory and is
  outside the present Lean interfaces.

## Verification

From `incidence-theory/`:

```bash
lake build
lake exe incidence-theory
rg -n '\bsorry\b|\baxiom\b' IncidenceTheory -g '*.lean'
git diff --check
```
