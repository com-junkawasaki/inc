import IncidenceTheory
import IncidenceTheory.Logic

/-!
  The coherent layer is the formal home for the strong Inc theorems.
  Bare `Incidence` remains intentionally permissive: it admits chains and
  cycles that refute an unconditional boundary-square law.  A
  `CoherentIncidence` instead packages precisely the extra data required for
  chain-complex, pushout, and complete propositional-logic results.
-/

namespace IncidenceCore

universe u

structure CoherentIncidence (I R T : Type u) [DecidableEq I] where
  chainPushout : ChainComplexPushoutIncidence I R T
  completeLogic : CompletePropositionalInternalLogic I

theorem CoherentIncidence.boundary_composition_zero
    {I R T : Type u} [DecidableEq I] (coherent : CoherentIncidence I R T)
    (idx : List I) (i k : I) (hi : i ∈ idx) (hk : k ∈ idx) :
    boundary_composition coherent.chainPushout.inc idx i k = 0 :=
  coherent.chainPushout.boundary_composition_zero idx i k hi hk

def CoherentIncidence.glue_creates_pushout
    {I R T : Type u} [DecidableEq I] (coherent : CoherentIncidence I R T)
    {i j k : I} (hglue : coherent.chainPushout.inc.glue i j = some k) :
    { pushout : PushoutWitness (coherent.chainPushout.glue_pushout.diagram i j) //
      pushout.apex = k } :=
  coherent.chainPushout.glue_creates_pushout hglue

theorem CoherentIncidence.kripke_complete
    {I R T : Type u} [DecidableEq I] (coherent : CoherentIncidence I R T)
    (context : List (Formula I)) (formula : Formula I) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  coherent.completeLogic.kripke_complete context formula

def mapEndpoint {I R Q : Type u} (classify : I → Q)
    (endpoint : Endpoint I R) : Endpoint Q R :=
  { i := classify endpoint.i,
    role := endpoint.role,
    sign := endpoint.sign,
    mult := endpoint.mult,
    mult_pos := endpoint.mult_pos }

/- A quotient-compatible coherent incidence supplies a target incidence and
   proves that the classifier respects boundary and gluing data.  These are
   the missing hypotheses which a bare quotient lacks; without them the
   `cycleIncidence` counterexample cannot be lifted to an incidence quotient. -/
structure CoherentQuotient {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    (source : CoherentIncidence I R T) where
  target : Incidence Q R T
  classification : BisimulationQuotientClassification (Q := Q) source.chainPushout.inc
  boundary_preserves : ∀ i,
    (source.chainPushout.inc.boundary i).map
      (@mapEndpoint I R Q classification.classify) =
      target.boundary (classification.classify i)
  glue_preserves : ∀ {i j k}, source.chainPushout.inc.glue i j = some k →
    target.glue (classification.classify i) (classification.classify j) =
      some (classification.classify k)

theorem CoherentQuotient.classify_boundary
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (i : I) :
    (source.chainPushout.inc.boundary i).map
      (@mapEndpoint I R Q quotient.classification.classify) =
      quotient.target.boundary (quotient.classification.classify i) :=
  quotient.boundary_preserves i

theorem CoherentQuotient.classify_glue
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {i j k : I} (hglue : source.chainPushout.inc.glue i j = some k) :
    quotient.target.glue (quotient.classification.classify i)
      (quotient.classification.classify j) =
      some (quotient.classification.classify k) :=
  quotient.glue_preserves hglue

theorem CoherentQuotient.quotient_lift_injective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {left right : IncidenceQuotient source.chainPushout.inc}
    (h : quotient.classification.lift left = quotient.classification.lift right) :
    left = right :=
  quotient.classification.lift_injective h

theorem CoherentQuotient.quotient_lift_surjective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (target : Q) :
    ∃ sourceClass : IncidenceQuotient source.chainPushout.inc,
      quotient.classification.lift sourceClass = target :=
  quotient.classification.lift_surjective target

end IncidenceCore
