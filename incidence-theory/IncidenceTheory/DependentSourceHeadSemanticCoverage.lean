import IncidenceTheory.DependentAlignedContextSemantics

namespace IncidenceCore

universe u

/-- The genuinely missing local input for arbitrary source-side pairing.
    Formation semantics is deliberately absent from this hypothesis: the
    canonical preservation dispatcher already synthesizes it from the target
    formation, target tree, and coherent tail realization. -/
def IncDepSourceHeadTypingSemanticCoverage
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}) : Prop :=
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
    let formationDispatch :=
      (model.preservationCanonical hypotheses).formation.dispatch
        targetReady base.targetTree base.realization.replacements
    Nonempty (IncDepRawTypingSemanticResult headTyping
      base.realization.sourceResult
      formationDispatch.formationResult.sourceFormationResult.semanticType)

/-- Formation-fiber semantics for an arbitrary source head is already total
    once its coherent tail realization and target formation readiness exist. -/
noncomputable def IncDepCoherentSemanticSubstitutionInto.sourceHeadFormation
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (base : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution)
    {type : IncDepRawType}
    {targetFormation : IncDepRawWellFormed target type}
    (targetReady : IncDepRawCoherentFormationDispatchReady targetFormation) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation)
      base.realization.substitutionResult :=
  ((model.preservationCanonical hypotheses).formation.dispatch
    targetReady base.targetTree base.realization.replacements).formationResult

/-- The minimal typing-coverage hypothesis completes the already automatic
    formation dispatch into the exact general semantic pairing package. -/
noncomputable def IncDepSourceHeadTypingSemanticCoverage.buildHead
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType}
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
      (type.substitute substitution.term)) :
    IncDepGeneralSemanticPairingHead base.realization type :=
  let formationResult := base.sourceHeadFormation model hypotheses targetReady
  let headResult := Classical.choice
    (coverage base targetFormation targetReady headTerm headTyping)
  { targetFormation := targetFormation
    targetReady := targetReady
    headTerm := headTerm
    headTyping := headTyping
    formationResult := formationResult
    headResult := headResult }

@[simp] theorem IncDepSourceHeadTypingSemanticCoverage.buildHead_term
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType}
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
      (type.substitute substitution.term)) :
    (coverage.buildHead base targetFormation targetReady headTerm headTyping).headTerm =
      headTerm :=
  rfl

/-- Consequently, typing coverage alone closes one coherent recursive
    extension step for the original proof-relevant substitution. -/
noncomputable def IncDepSourceHeadTypingSemanticCoverage.extendCoherently
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution.tail)
    (targetFormation : IncDepRawWellFormed target type)
    (targetReady : IncDepRawCoherentFormationDispatchReady targetFormation) :
    let head := coverage.buildHead tailInput targetFormation targetReady
      (substitution.term 0) substitution.headTyping
    IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult substitution :=
  let head := coverage.buildHead tailInput targetFormation targetReady
    (substitution.term 0) substitution.headTyping
  substitution.coherentSemanticIntoOfTailAndHead tailInput head rfl

structure IncDepSourceHeadSemanticCoverageBoundaryTheorem : Prop where
  formationAutomatic : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (base : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution)
    {type : IncDepRawType}
    {targetFormation : IncDepRawWellFormed target type}
    (targetReady : IncDepRawCoherentFormationDispatchReady targetFormation),
    ∃ result : IncDepRawFormationSubstitutionFiberResult
        (targetFormation := targetFormation)
        base.realization.substitutionResult,
      result = base.sourceHeadFormation model hypotheses targetReady
  typingCoverageBuildsHead : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    (_coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType}
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
    ∃ head : IncDepGeneralSemanticPairingHead base.realization type,
      head.headTerm = headTerm ∧
      HEq head.headTyping headTyping ∧
      HEq head.formationResult
        (base.sourceHeadFormation model hypotheses targetReady)

theorem incDepSourceHeadSemanticCoverageBoundaryTheorem :
    IncDepSourceHeadSemanticCoverageBoundaryTheorem.{u} where
  formationAutomatic := by
    intro model hypotheses source target sourceWellFormed targetWellFormed
      targetResult substitution base type targetFormation targetReady
    exact ⟨base.sourceHeadFormation model hypotheses targetReady, rfl⟩
  typingCoverageBuildsHead := by
    intro model hypotheses coverage source target sourceWellFormed
      targetWellFormed targetResult substitution base type targetFormation
      targetReady headTerm headTyping
    refine ⟨coverage.buildHead base targetFormation targetReady headTerm headTyping,
      rfl, ?_, ?_⟩
    · simp only [IncDepSourceHeadTypingSemanticCoverage.buildHead]
      exact HEq.rfl
    · simp only [IncDepSourceHeadTypingSemanticCoverage.buildHead]
      exact HEq.rfl

end IncidenceCore
