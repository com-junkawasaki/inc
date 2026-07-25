import IncidenceTheory.DependentTwoSidedCoherentSemanticSubstitution

namespace IncidenceCore

universe u

/-- Interpret a source-side typing judgment by running canonical typing
    preservation along the identity substitution on the retained source tree. -/
noncomputable def IncDepTwoSidedCoherentSemanticSubstitutionInto.sourceIdentityTypingDispatch
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (base : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed targetWellFormed targetResult substitution)
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepRawHasType source term type}
    {formation : IncDepRawWellFormed source type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation) :=
  (model.preservationCanonical hypotheses).typing.dispatch ready base.sourceTree
    (IncDepRawSubstitutionReplacementSemanticResult.identity base.sourceTree)

/-- Exact local evidence needed after source-tree anchoring: syntactic coherent
    readiness for the actual source head, plus a fiber equivalence from the
    identity interpretation of its substituted formation to the formation
    result produced along the semantic tail substitution. -/
structure IncDepSourceHeadReadinessAlignment
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (base : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed targetWellFormed targetResult substitution)
    {type : IncDepRawType}
    (targetFormation : IncDepRawWellFormed target type)
    (targetReady : IncDepRawCoherentFormationDispatchReady targetFormation)
    (headTerm : IncDepRawTerm)
    (headTyping : IncDepRawHasType source headTerm
      (type.substitute substitution.term)) where
  readiness : IncDepRawCoherentTypingDispatchReady headTyping
    (targetFormation.substitute substitution)
  semanticTypeEquivalence : IncTypeInContext.FiberEquiv
    (base.sourceIdentityTypingDispatch model hypotheses readiness
      |>.formationResult.targetFormationResult.semanticType)
    (base.coherent.sourceHeadFormation model hypotheses targetReady
      |>.sourceFormationResult.semanticType)

/-- Aligned readiness gives the formerly assumed source-head semantic typing
    result by transporting the identity-dispatch term into the tail-dispatch
    formation fiber. -/
noncomputable def IncDepSourceHeadReadinessAlignment.typingResult
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    {targetFormation : IncDepRawWellFormed target type}
    {targetReady : IncDepRawCoherentFormationDispatchReady targetFormation}
    {headTerm : IncDepRawTerm}
    {headTyping : IncDepRawHasType source headTerm
      (type.substitute substitution.term)}
    (alignment : IncDepSourceHeadReadinessAlignment model hypotheses base
      targetFormation targetReady headTerm headTyping) :
    IncDepRawTypingSemanticResult headTyping base.coherent.realization.sourceResult
      (base.coherent.sourceHeadFormation model hypotheses targetReady
        |>.sourceFormationResult.semanticType) where
  semanticTerm := alignment.semanticTypeEquivalence.transport
    (base.sourceIdentityTypingDispatch model hypotheses alignment.readiness
      |>.typingResult.targetTermResult.semanticTerm)

/-- Global aligned-readiness coverage includes the source tree that the old
    one-sided interface omitted. -/
def IncDepSourceHeadReadinessAlignmentCoverage
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}) :
    Prop :=
  ∀ {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (base : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution)
    {type : IncDepRawType}
    (targetFormation : IncDepRawWellFormed target type)
    (targetReady : IncDepRawCoherentFormationDispatchReady targetFormation)
    (headTerm : IncDepRawTerm)
    (headTyping : IncDepRawHasType source headTerm
      (type.substitute substitution.term)),
    Nonempty (Sigma fun sourceTree : IncDepRawContextSemanticTree
        base.realization.sourceResult =>
      IncDepSourceHeadReadinessAlignment model hypotheses
        { coherent := base, sourceTree := sourceTree }
        targetFormation targetReady headTerm headTyping)

/-- Readiness plus semantic-type alignment discharges the entire typing-only
    source-head coverage gate. -/
noncomputable def IncDepSourceHeadReadinessAlignmentCoverage.toTypingCoverage
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadReadinessAlignmentCoverage model hypotheses) :
    IncDepSourceHeadTypingSemanticCoverage model hypotheses := by
  intro source target sourceWellFormed targetWellFormed targetResult substitution
    base type targetFormation targetReady headTerm headTyping
  let witness := Classical.choice
    (coverage base targetFormation targetReady headTerm headTyping)
  exact ⟨witness.2.typingResult⟩

structure IncDepSourceHeadReadinessAlignmentTheorem : Prop where
  identityTypingInterpreted : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (base : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed targetWellFormed targetResult substitution)
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepRawHasType source term type}
    {formation : IncDepRawWellFormed source type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation),
    Nonempty (IncDepRawTypingSemanticResult typing
      base.coherent.realization.sourceResult
      (base.sourceIdentityTypingDispatch model hypotheses ready
        |>.formationResult.targetFormationResult.semanticType))
  alignmentDischargesTypingCoverage : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}),
    IncDepSourceHeadReadinessAlignmentCoverage model hypotheses →
      IncDepSourceHeadTypingSemanticCoverage model hypotheses

theorem incDepSourceHeadReadinessAlignmentTheorem :
    IncDepSourceHeadReadinessAlignmentTheorem.{u} where
  identityTypingInterpreted := by
    intro model hypotheses source target sourceWellFormed targetWellFormed
      targetResult substitution base term type typing formation ready
    exact ⟨(base.sourceIdentityTypingDispatch model hypotheses ready
      |>.typingResult.targetTermResult)⟩
  alignmentDischargesTypingCoverage := fun _ _ coverage =>
    coverage.toTypingCoverage

end IncidenceCore
