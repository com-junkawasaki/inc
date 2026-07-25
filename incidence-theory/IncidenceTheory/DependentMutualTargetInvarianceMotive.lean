import IncidenceTheory.DependentFormationTargetInvariance

namespace IncidenceCore

universe u

/-- Package the dependent target semantic type and target semantic term emitted
    by a strict typing dispatch so different source-side runs can be compared
    by ordinary equality. -/
def IncDepRawStrictTypingSubstitutionDispatchResult.targetPackage
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {targetFormationReady :
      IncDepRawCoherentFormationDispatchReady targetFormation}
    {targetReady : IncDepRawStrictTypingDispatchReady targetTyping
      targetFormationReady}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult) :
    Sigma fun semanticType : IncTypeInContext targetResult.semanticContext =>
      IncDepRawTypingSemanticResult targetTyping targetResult semanticType :=
  ⟨result.formationResult.targetFormationResult.semanticType,
    result.typingResult.targetTermResult⟩

/-- Formation half of the mutual target-invariance induction, localized at one
    coherent formation-readiness derivation. -/
def IncDepCanonicalFormationTargetInvariantAt
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {target : List IncDepRawType} {type : IncDepRawType}
    {targetFormation : IncDepRawWellFormed target type}
    (ready : IncDepRawCoherentFormationDispatchReady targetFormation) : Prop :=
  ∀ {source : List IncDepRawType}
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
    ((model.preservationCanonical hypotheses).formation.dispatch ready
      targetTree replacements |>.formationResult.targetFormationResult) =
    ((model.preservationCanonical hypotheses).formation.dispatch ready
      targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult)

/-- Typing half of the mutual induction.  It records ordinary equality of the
    target formation result and heterogeneous equality of the dependent target
    semantic term; this avoids imposing equality on irrelevant source fields. -/
def IncDepCanonicalTypingTargetInvariantAt
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    (ready : IncDepRawCoherentTypingDispatchReady targetTyping
      targetFormation) : Prop :=
  ∀ {source : List IncDepRawType}
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
    let first := (model.preservationCanonical hypotheses).typing.dispatch ready
      targetTree replacements
    let second := (model.preservationCanonical hypotheses).typing.dispatch ready
      targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
    first.formationResult.targetFormationResult =
        second.formationResult.targetFormationResult ∧
      HEq first.typingResult.targetTermResult.semanticTerm
        second.typingResult.targetTermResult.semanticTerm

theorem incDepCanonicalFormationTargetInvariance_iff_local
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}) :
    IncDepCanonicalFormationTargetInvariance model hypotheses ↔
      ∀ {target : List IncDepRawType} {type : IncDepRawType}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentFormationDispatchReady targetFormation),
        IncDepCanonicalFormationTargetInvariantAt model hypotheses ready := by
  constructor
  · intro global target type targetFormation ready source sourceWellFormed
      targetWellFormed sourceResult targetResult substitution substitutionResult
      targetTree replacements
    exact global ready targetTree replacements
  · intro localHyp source target type sourceWellFormed targetWellFormed sourceResult
      targetResult substitution substitutionResult targetFormation ready targetTree
      replacements
    exact localHyp ready targetTree replacements

theorem incDepCanonicalFormationTargetInvariantAt_base
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} {index : Nat} :
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.base
        (context := context) (index := index)) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  exact model.base_targetFormation_invariant hypotheses targetTree replacements

theorem incDepCanonicalFormationTargetInvariantAt_unit
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} :
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.unit (context := context)) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  exact model.unit_targetFormation_invariant hypotheses targetTree replacements

theorem incDepCanonicalTypingTargetInvariantAt_unit
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} :
    IncDepCanonicalTypingTargetInvariantAt model hypotheses
      (IncDepRawCoherentTypingDispatchReady.unitRule (context := context)) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  exact ⟨rfl, HEq.rfl⟩

/-- The exact additional law absent from the unconstrained variable provider:
    target-variable interpretation must be source-independent whenever its
    recursively interpreted formation is source-independent. -/
def IncDepCanonicalVariableTargetInvariance
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}) :
    Prop :=
  ∀ {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation},
    IncDepCanonicalFormationTargetInvariantAt model hypotheses typeReady →
      IncDepCanonicalTypingTargetInvariantAt model hypotheses
        (IncDepRawCoherentTypingDispatchReady.varRule (lookup := lookup)
          typeReady)

theorem incDepCanonicalTypingTargetInvariantAt_variable
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    (variableInvariance :
      IncDepCanonicalVariableTargetInvariance model hypotheses)
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    (typeInvariant : IncDepCanonicalFormationTargetInvariantAt model hypotheses
      typeReady) :
    IncDepCanonicalTypingTargetInvariantAt model hypotheses
      (IncDepRawCoherentTypingDispatchReady.varRule (lookup := lookup)
        typeReady) := by
  exact variableInvariance typeInvariant

structure IncDepMutualTargetInvarianceMotiveTheorem : Prop where
  formationGlobalLocal : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}),
    IncDepCanonicalFormationTargetInvariance model hypotheses ↔
      ∀ {target : List IncDepRawType} {type : IncDepRawType}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentFormationDispatchReady targetFormation),
        IncDepCanonicalFormationTargetInvariantAt model hypotheses ready
  baseClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} {index : Nat},
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.base
        (context := context) (index := index))
  unitClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType},
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.unit (context := context))
  typingUnitClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType},
    IncDepCanonicalTypingTargetInvariantAt model hypotheses
      (IncDepRawCoherentTypingDispatchReady.unitRule (context := context))
  variableClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}),
    IncDepCanonicalVariableTargetInvariance model hypotheses →
      ∀ {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
        {lookup : IncDepRawLookup context position type}
        {typeFormation : IncDepRawWellFormed context type}
        {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation},
        IncDepCanonicalFormationTargetInvariantAt model hypotheses typeReady →
          IncDepCanonicalTypingTargetInvariantAt model hypotheses
            (IncDepRawCoherentTypingDispatchReady.varRule (lookup := lookup)
              typeReady)

theorem incDepMutualTargetInvarianceMotiveTheorem :
    IncDepMutualTargetInvarianceMotiveTheorem.{u} where
  formationGlobalLocal := incDepCanonicalFormationTargetInvariance_iff_local
  baseClosed := incDepCanonicalFormationTargetInvariantAt_base
  unitClosed := incDepCanonicalFormationTargetInvariantAt_unit
  typingUnitClosed := incDepCanonicalTypingTargetInvariantAt_unit
  variableClosed := incDepCanonicalTypingTargetInvariantAt_variable

end IncidenceCore
