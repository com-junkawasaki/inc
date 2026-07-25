import IncidenceTheory.DependentScopedTypingTargetInvarianceBase

namespace IncidenceCore

universe u

private theorem incDepProd_heq
    {α β α' β' : Type u} {a : α} {b : β} {a' : α'} {b' : β'}
    (ha : HEq a a') (hb : HEq b b') : HEq (a, b) (a', b') := by
  cases ha
  cases hb
  rfl


theorem incDepScopedCanonicalTyping_formation_eq
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {typing : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (typingReady : IncDepRawCoherentTypingDispatchReady typing typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    let dispatcher := model.scopedCanonicalStrictPreservation inputs
    let typeResult := dispatcher.formation.dispatch typeReady targetTree
      replacements
    let typingResult := dispatcher.typing.dispatch typingReady targetTree
      replacements
    typingResult.formationResult = typeResult.formationResult := by
  have readyEq := inputs.readinessAlignment.alignFormation
    typingReady.formationReady typeReady
  cases readyEq
  exact ((model.scopedAnchoredMutualFoldDispatcher inputs).typing typingReady
    |>.agreement.agree targetTree replacements).result_eq

/-- Transport a target term directly to any propositionally equal semantic
    target formation.  This is the constructor-independent primitive needed by
    Apply/Pair/projection packages, where the comparison formation need not be
    wrapped in a strict dispatch result. -/
def IncDepRawStrictTypingSubstitutionDispatchResult.targetTermCastTo
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
    (typingResult : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult)
    (formationResult : IncDepRawFormationSemanticResult targetFormation
      targetResult)
    (formationEq : typingResult.formationResult.targetFormationResult =
      formationResult) :
    IncTerm formationResult.semanticType :=
  cast (congrArg (fun result => IncTerm result.semanticType) formationEq)
    typingResult.typingResult.targetTermResult.semanticTerm

theorem IncDepRawStrictTypingSubstitutionDispatchResult.targetTermCastTo_heq
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
    (typingResult : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult)
    (formationResult : IncDepRawFormationSemanticResult targetFormation
      targetResult)
    (formationEq : typingResult.formationResult.targetFormationResult =
      formationResult) :
    HEq (typingResult.targetTermCastTo formationResult formationEq)
      typingResult.typingResult.targetTermResult.semanticTerm := by
  exact cast_heq _ _

def IncDepRawStrictTypingSubstitutionDispatchResult.targetTermCast
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
    (typingResult : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult)
    {formationReady : IncDepRawCoherentFormationDispatchReady targetFormation}
    (formationResult : IncDepRawStrictFormationSubstitutionDispatchResult
      formationReady substitutionResult)
    (formationEq : typingResult.formationResult =
      formationResult.formationResult) :
    IncTerm formationResult.formationResult.targetFormationResult.semanticType :=
  typingResult.targetTermCastTo
    formationResult.formationResult.targetFormationResult
    (congrArg
      IncDepRawFormationSubstitutionFiberResult.targetFormationResult
      formationEq)

theorem IncDepRawStrictTypingSubstitutionDispatchResult.targetTermCast_heq
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
    (typingResult : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult)
    {formationReady : IncDepRawCoherentFormationDispatchReady targetFormation}
    (formationResult : IncDepRawStrictFormationSubstitutionDispatchResult
      formationReady substitutionResult)
    (formationEq : typingResult.formationResult =
      formationResult.formationResult) :
    HEq (typingResult.targetTermCast formationResult formationEq)
      typingResult.typingResult.targetTermResult.semanticTerm := by
  exact cast_heq _ _

noncomputable def incDepScopedIdentityExternalTargetPackage
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation)
    (rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    IncDepRawIdentityFormationTargetPackage targetResult typeFormation :=
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let typeResult := dispatcher.formation.dispatch typeReady targetTree
    replacements
  let leftResult := dispatcher.typing.dispatch leftReady targetTree replacements
  let rightResult := dispatcher.typing.dispatch rightReady targetTree replacements
  let leftEq := incDepScopedCanonicalTyping_formation_eq model inputs
    typeReady leftReady targetTree replacements
  let rightEq := incDepScopedCanonicalTyping_formation_eq model inputs
    typeReady rightReady targetTree replacements
  ⟨typeResult.formationResult.targetFormationResult,
    ⟨leftResult.targetTermCast typeResult leftEq,
      rightResult.targetTermCast typeResult rightEq⟩⟩

/-- Exact coherence still required between the Identity branch of the mutual
    formation recursor and the independently evaluated endpoint typing
    recursors.  Formation agreement aligns their carrier fibers, but does not
    by itself identify the transported endpoint choices. -/
def IncDepScopedIdentityRecursivePathCoherence
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) : Prop :=
  ∀ {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation)
    (rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    ((model.scopedCanonicalStrictPreservation inputs).formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.identity typeReady leftReady
        rightReady) targetTree replacements
      |>.formationResult.targetFormationResult) =
      (incDepScopedIdentityExternalTargetPackage model inputs typeReady leftReady
        rightReady targetTree replacements).identity

theorem incDepScopedIdentityExternalTargetPackage_eq
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation}
    {rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation}
    (typeInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady)
    (leftInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) leftReady)
    (rightInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) rightReady)
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed context}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source context}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    incDepScopedIdentityExternalTargetPackage model inputs typeReady leftReady
      rightReady targetTree replacements =
    incDepScopedIdentityExternalTargetPackage model inputs typeReady leftReady
      rightReady targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree) := by
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  let firstType := dispatcher.formation.dispatch typeReady targetTree replacements
  let secondType := dispatcher.formation.dispatch typeReady targetTree
    identityReplacements
  let firstLeft := dispatcher.typing.dispatch leftReady targetTree replacements
  let secondLeft := dispatcher.typing.dispatch leftReady targetTree
    identityReplacements
  let firstRight := dispatcher.typing.dispatch rightReady targetTree replacements
  let secondRight := dispatcher.typing.dispatch rightReady targetTree
    identityReplacements
  have typeEq : firstType.formationResult.targetFormationResult =
      secondType.formationResult.targetFormationResult :=
    typeInvariant targetTree replacements
  have leftRawEq := (leftInvariant targetTree replacements).2
  have rightRawEq := (rightInvariant targetTree replacements).2
  have leftEq : HEq
      (firstLeft.targetTermCast firstType
        (incDepScopedCanonicalTyping_formation_eq model inputs typeReady
          leftReady targetTree replacements))
      (secondLeft.targetTermCast secondType
        (incDepScopedCanonicalTyping_formation_eq model inputs typeReady
          leftReady targetTree identityReplacements)) :=
    (firstLeft.targetTermCast_heq firstType _).trans
      (leftRawEq.trans (secondLeft.targetTermCast_heq secondType _).symm)
  have rightEq : HEq
      (firstRight.targetTermCast firstType
        (incDepScopedCanonicalTyping_formation_eq model inputs typeReady
          rightReady targetTree replacements))
      (secondRight.targetTermCast secondType
        (incDepScopedCanonicalTyping_formation_eq model inputs typeReady
          rightReady targetTree identityReplacements)) :=
    (firstRight.targetTermCast_heq firstType _).trans
      (rightRawEq.trans (secondRight.targetTermCast_heq secondType _).symm)
  apply Sigma.ext
  · exact typeEq
  · exact incDepProd_heq leftEq rightEq

theorem incDepScopedCanonicalFormationTargetInvariantAt_identity
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (pathCoherence : IncDepScopedIdentityRecursivePathCoherence model inputs)
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation}
    {rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation}
    (typeInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady)
    (leftInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) leftReady)
    (rightInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) rightReady) :
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.identity typeReady leftReady
        rightReady) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  rw [pathCoherence typeReady leftReady rightReady targetTree replacements,
    pathCoherence typeReady leftReady rightReady targetTree identityReplacements]
  exact IncDepRawIdentityFormationTargetPackage.identity_congr
    (incDepScopedIdentityExternalTargetPackage_eq model inputs typeInvariant
      leftInvariant rightInvariant targetTree replacements)

structure IncDepScopedIdentityTargetInvarianceTheorem : Prop where
  packageClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation}
    {rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation},
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady →
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) leftReady →
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) rightReady →
    ∀ {source : List IncDepRawType}
      {sourceWellFormed : IncDepRawContext.WellFormed source}
      {targetWellFormed : IncDepRawContext.WellFormed context}
      {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
      {targetResult : IncDepRawContextSemanticResult targetWellFormed}
      {substitution : IncDepRawSubstitution source context}
      {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
        sourceResult targetResult}
      (targetTree : IncDepRawContextSemanticTree targetResult)
      (replacements : IncDepRawSubstitutionReplacementSemanticResult
        substitutionResult),
      incDepScopedIdentityExternalTargetPackage model inputs typeReady leftReady
        rightReady targetTree replacements =
      incDepScopedIdentityExternalTargetPackage model inputs typeReady leftReady
        rightReady targetTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
  identityClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepScopedIdentityRecursivePathCoherence model inputs →
    ∀ {context : List IncDepRawType} {type : IncDepRawType}
      {left right : IncDepRawTerm}
      {typeFormation : IncDepRawWellFormed context type}
      {leftTyping : IncDepRawHasType context left type}
      {rightTyping : IncDepRawHasType context right type}
      {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
      {leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation}
      {rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation},
      IncDepFormationTargetInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs) typeReady →
      IncDepTypingTargetInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs) leftReady →
      IncDepTypingTargetInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs) rightReady →
      IncDepFormationTargetInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs)
        (IncDepRawCoherentFormationDispatchReady.identity typeReady leftReady
          rightReady)

theorem incDepScopedIdentityTargetInvarianceTheorem :
    IncDepScopedIdentityTargetInvarianceTheorem.{u} where
  packageClosed := incDepScopedIdentityExternalTargetPackage_eq
  identityClosed := incDepScopedCanonicalFormationTargetInvariantAt_identity

end IncidenceCore
