import IncidenceTheory.DependentScopedLambdaTargetInvariance

namespace IncidenceCore

universe u

/-- Carrier target and endpoint term needed to construct a reflexivity target. -/
def IncDepRawReflTargetPackage
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed)
    (typeFormation : IncDepRawWellFormed context type) :=
  Sigma fun typeResult : IncDepRawFormationSemanticResult typeFormation
      contextResult =>
    IncTerm typeResult.semanticType

def IncDepRawReflTargetPackage.reflTerm
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {typeFormation : IncDepRawWellFormed context type}
    (package : IncDepRawReflTargetPackage contextResult typeFormation) :
    IncTerm (IncIdentityType package.1.semanticType package.2 package.2) :=
  IncIdentityTerm.refl package.2

def IncDepRawReflTargetPackage.identityType
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {typeFormation : IncDepRawWellFormed context type}
    (package : IncDepRawReflTargetPackage contextResult typeFormation) :
    IncTypeInContext contextResult.semanticContext :=
  IncIdentityType package.1.semanticType package.2 package.2

theorem IncDepRawReflTargetPackage.reflTerm_heq
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {typeFormation : IncDepRawWellFormed context type}
    {first second : IncDepRawReflTargetPackage contextResult typeFormation}
    (packageEq : first = second) :
    HEq first.reflTerm second.reflTerm := by
  cases packageEq
  rfl

noncomputable def incDepScopedReflExternalTargetPackage
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm} {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {termTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (termReady : IncDepRawCoherentTypingDispatchReady termTyping typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    IncDepRawReflTargetPackage targetResult typeFormation :=
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let typeResult := dispatcher.formation.dispatch typeReady targetTree
    replacements
  let termResult := dispatcher.typing.dispatch termReady targetTree replacements
  let formationEq := incDepScopedCanonicalTyping_formation_eq model inputs
    typeReady termReady targetTree replacements
  ⟨typeResult.formationResult.targetFormationResult,
    termResult.targetTermCast typeResult formationEq⟩

theorem incDepScopedReflExternalTargetPackage_eq
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {termTyping : IncDepRawHasType context term type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {termReady : IncDepRawCoherentTypingDispatchReady termTyping typeFormation}
    (typeInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady)
    (termInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) termReady)
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
    incDepScopedReflExternalTargetPackage model inputs typeReady termReady
        targetTree replacements =
      incDepScopedReflExternalTargetPackage model inputs typeReady termReady
        targetTree
          (IncDepRawSubstitutionReplacementSemanticResult.identity
            targetTree) := by
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  let firstType := dispatcher.formation.dispatch typeReady targetTree replacements
  let secondType := dispatcher.formation.dispatch typeReady targetTree
    identityReplacements
  let firstTerm := dispatcher.typing.dispatch termReady targetTree replacements
  let secondTerm := dispatcher.typing.dispatch termReady targetTree
    identityReplacements
  have typeEq : firstType.formationResult.targetFormationResult =
      secondType.formationResult.targetFormationResult :=
    typeInvariant targetTree replacements
  have termEq : HEq
      (firstTerm.targetTermCast firstType
        (incDepScopedCanonicalTyping_formation_eq model inputs typeReady
          termReady targetTree replacements))
      (secondTerm.targetTermCast secondType
        (incDepScopedCanonicalTyping_formation_eq model inputs typeReady
          termReady targetTree identityReplacements)) :=
    (firstTerm.targetTermCast_heq firstType _).trans
      ((termInvariant targetTree replacements).2.trans
        (secondTerm.targetTermCast_heq secondType _).symm)
  exact Sigma.ext typeEq termEq

/-- Exact term-sensitive coherence between the Refl branch of mutual recursion
    and the independently formation-aligned endpoint target. -/
def IncDepScopedReflRecursiveTermCoherence
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) : Prop :=
  ∀ {source target : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm} {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {termTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (termReady : IncDepRawCoherentTypingDispatchReady termTyping typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    HEq
      ((model.scopedCanonicalStrictPreservation inputs).typing.dispatch
        (IncDepRawCoherentTypingDispatchReady.reflRule typeReady termReady)
        targetTree replacements |>.typingResult.targetTermResult.semanticTerm)
      (incDepScopedReflExternalTargetPackage model inputs typeReady termReady
        targetTree replacements).reflTerm

theorem incDepScopedReflRecursiveTermCoherence_of_identity
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (identityCoherence : IncDepScopedIdentityRecursivePathCoherence model inputs) :
    IncDepScopedReflRecursiveTermCoherence model inputs := by
  intro source target type term substitution typeFormation termTyping
    sourceWellFormed targetWellFormed sourceResult targetResult
    substitutionResult typeReady termReady targetTree replacements
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let reflReady := IncDepRawCoherentTypingDispatchReady.reflRule typeReady
    termReady
  let identityReady := IncDepRawCoherentFormationDispatchReady.identity
    typeReady termReady termReady
  let result := dispatcher.typing.dispatch reflReady targetTree replacements
  let package := incDepScopedReflExternalTargetPackage model inputs typeReady
    termReady targetTree replacements
  have typingFormationEq : result.formationResult =
      (dispatcher.formation.dispatch identityReady targetTree replacements
        |>.formationResult) :=
    incDepScopedCanonicalTyping_formation_eq model inputs identityReady
      reflReady targetTree replacements
  have identityFormationEq :
      (dispatcher.formation.dispatch identityReady targetTree replacements
        |>.formationResult.targetFormationResult.semanticType) =
      package.identityType := by
    exact congrArg IncDepRawFormationSemanticResult.semanticType
      (identityCoherence typeReady termReady termReady targetTree replacements)
  have targetTypeEq :
      result.formationResult.targetFormationResult.semanticType =
        package.identityType :=
    (congrArg (fun formationResult =>
      formationResult.targetFormationResult.semanticType)
      typingFormationEq).trans identityFormationEq
  let casted : IncTerm package.identityType :=
    cast (congrArg IncTerm targetTypeEq)
      result.typingResult.targetTermResult.semanticTerm
  have castedEq : casted = package.reflTerm := by
    funext assignment
    exact IncIdentityType.witness_irrel _ _
  exact (cast_heq (congrArg IncTerm targetTypeEq)
      result.typingResult.targetTermResult.semanticTerm).symm.trans
    (heq_of_eq castedEq)

theorem incDepScopedCanonicalTypingTargetTermInvariantAt_refl
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (reflCoherence : IncDepScopedReflRecursiveTermCoherence model inputs)
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {termTyping : IncDepRawHasType context term type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {termReady : IncDepRawCoherentTypingDispatchReady termTyping typeFormation}
    (typeInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady)
    (termInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) termReady) :
    IncDepTypingTargetTermInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.reflRule typeReady termReady) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  have packageEq := incDepScopedReflExternalTargetPackage_eq model inputs
    typeInvariant termInvariant targetTree replacements
  exact (reflCoherence typeReady termReady targetTree replacements).trans
    ((IncDepRawReflTargetPackage.reflTerm_heq packageEq).trans
      (reflCoherence typeReady termReady targetTree identityReplacements).symm)

theorem incDepScopedCanonicalTypingTargetInvariantAt_refl
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (identityCoherence : IncDepScopedIdentityRecursivePathCoherence model inputs)
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {termTyping : IncDepRawHasType context term type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {termReady : IncDepRawCoherentTypingDispatchReady termTyping typeFormation}
    (typeInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady)
    (termInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) termReady) :
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.reflRule typeReady termReady) := by
  have identityInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.identity typeReady termReady
        termReady) :=
    incDepScopedCanonicalFormationTargetInvariantAt_identity model inputs
      identityCoherence typeInvariant termInvariant termInvariant
  have reflTermInvariant : IncDepTypingTargetTermInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.reflRule typeReady termReady) :=
    incDepScopedCanonicalTypingTargetTermInvariantAt_refl model inputs
      (incDepScopedReflRecursiveTermCoherence_of_identity model inputs
        identityCoherence) typeInvariant termInvariant
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  exact ⟨incDepScopedCanonicalTypingFormationTargetInvariantAt model inputs
      (IncDepRawCoherentTypingDispatchReady.reflRule typeReady termReady)
      identityInvariant targetTree replacements,
    reflTermInvariant targetTree replacements⟩

structure IncDepScopedReflTargetInvarianceTheorem : Prop where
  reflClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepScopedIdentityRecursivePathCoherence model inputs →
      ∀ {context : List IncDepRawType} {type : IncDepRawType}
        {term : IncDepRawTerm}
        {typeFormation : IncDepRawWellFormed context type}
        {termTyping : IncDepRawHasType context term type}
        {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
        {termReady : IncDepRawCoherentTypingDispatchReady termTyping
          typeFormation},
        IncDepFormationTargetInvariantForAt
            (model.scopedCanonicalStrictPreservation inputs) typeReady →
          IncDepTypingTargetInvariantForAt
            (model.scopedCanonicalStrictPreservation inputs) termReady →
          IncDepTypingTargetInvariantForAt
            (model.scopedCanonicalStrictPreservation inputs)
            (IncDepRawCoherentTypingDispatchReady.reflRule typeReady termReady)

theorem incDepScopedReflTargetInvarianceTheorem :
    IncDepScopedReflTargetInvarianceTheorem.{u} where
  reflClosed := incDepScopedCanonicalTypingTargetInvariantAt_refl

end IncidenceCore
