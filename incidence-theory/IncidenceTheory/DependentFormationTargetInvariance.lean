import IncidenceTheory.DependentGlobalTwoSidedSubstitutionCoverage

namespace IncidenceCore

universe u

/-- The exact target-anchoring law for canonical formation preservation.  It
    says that the target formation interpretation depends only on the target
    semantic tree, not on the source, substitution, or replacement witnesses. -/
def IncDepCanonicalFormationTargetInvariance
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}) :
    Prop :=
  ∀ {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source target}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {targetFormation : IncDepRawWellFormed target type}
    (ready : IncDepRawCoherentFormationDispatchReady targetFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    ((model.preservationCanonical hypotheses).formation.dispatch ready
      targetTree replacements |>.formationResult.targetFormationResult) =
    ((model.preservationCanonical hypotheses).formation.dispatch ready
      targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult)

/-- Base formation target semantics is source-independent definitionally. -/
theorem IncDepRawSubstitutionFiberModel.base_targetFormation_invariant
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType} {index : Nat}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source target}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.base
        (context := target) (index := index)) targetTree replacements
      |>.formationResult.targetFormationResult) =
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.base
        (context := target) (index := index)) targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult) :=
  rfl

/-- Unit formation target semantics is source-independent definitionally. -/
theorem IncDepRawSubstitutionFiberModel.unit_targetFormation_invariant
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source target}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.unit (context := target))
      targetTree replacements |>.formationResult.targetFormationResult) =
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.unit (context := target))
      targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult) :=
  rfl

/-- Under the exact invariance law, every arbitrary source-head formation has
    the same target interpretation as canonical identity dispatch on the tail
    target tree.  This is the local equality required by target anchoring. -/
theorem IncDepCoherentSemanticSubstitutionInto.sourceHeadFormation_target_eq
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (invariance : IncDepCanonicalFormationTargetInvariance model hypotheses)
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
    (base.sourceHeadFormation model hypotheses targetReady
      |>.targetFormationResult) =
    ((model.preservationCanonical hypotheses).formation.dispatch targetReady
      base.targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity base.targetTree)
      |>.formationResult.targetFormationResult) :=
  invariance targetReady base.targetTree base.realization.replacements

structure IncDepFormationTargetInvarianceBoundaryTheorem : Prop where
  baseAutomatic : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType} {index : Nat}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source target}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.base
        (context := target) (index := index)) targetTree replacements
      |>.formationResult.targetFormationResult) =
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.base
        (context := target) (index := index)) targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult)
  unitAutomatic : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source target}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.unit (context := target))
      targetTree replacements |>.formationResult.targetFormationResult) =
    ((model.preservationCanonical hypotheses).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.unit (context := target))
      targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult)

theorem incDepFormationTargetInvarianceBoundaryTheorem :
    IncDepFormationTargetInvarianceBoundaryTheorem.{u} where
  baseAutomatic := IncDepRawSubstitutionFiberModel.base_targetFormation_invariant
  unitAutomatic := IncDepRawSubstitutionFiberModel.unit_targetFormation_invariant

end IncidenceCore
