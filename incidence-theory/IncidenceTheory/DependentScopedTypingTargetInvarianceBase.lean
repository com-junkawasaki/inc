import IncidenceTheory.DependentScopedPiSigmaTargetInvariance

namespace IncidenceCore

universe u

def IncDepTypingTargetInvariantForAt
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u})
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
    let first := dispatcher.typing.dispatch ready targetTree replacements
    let second := dispatcher.typing.dispatch ready targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
    first.formationResult.targetFormationResult =
        second.formationResult.targetFormationResult ∧
      HEq first.typingResult.targetTermResult.semanticTerm
        second.typingResult.targetTermResult.semanticTerm

/-- The genuinely term-level half of local typing target invariance. -/
def IncDepTypingTargetTermInvariantForAt
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u})
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
    HEq
      (dispatcher.typing.dispatch ready targetTree replacements
        |>.typingResult.targetTermResult.semanticTerm)
      (dispatcher.typing.dispatch ready targetTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
        |>.typingResult.targetTermResult.semanticTerm)

theorem incDepTypingTargetInvarianceFor_iff_local
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}) :
    IncDepTypingTargetInvarianceFor dispatcher ↔
      ∀ {target : List IncDepRawType} {term : IncDepRawTerm}
        {type : IncDepRawType}
        {targetTyping : IncDepRawHasType target term type}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentTypingDispatchReady targetTyping
          targetFormation),
        IncDepTypingTargetInvariantForAt dispatcher ready := by
  constructor
  · intro global target term type targetTyping targetFormation ready source
      sourceWellFormed targetWellFormed sourceResult targetResult substitution
      substitutionResult targetTree replacements
    exact global ready targetTree replacements
  · intro localHyp source target term type sourceWellFormed targetWellFormed
      sourceResult targetResult substitution substitutionResult targetTyping
      targetFormation ready targetTree replacements
    exact localHyp ready targetTree replacements

/-- The formation half of every scoped typing target-invariance goal follows
    uniformly from formation target invariance.  This removes that obligation
    from all six remaining compound typing constructors; their genuinely new
    content is only target-term invariance. -/
theorem incDepScopedCanonicalTypingFormationTargetInvariantAt
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation)
    (formationInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      ready.formationReady) :
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
      ((model.scopedCanonicalStrictPreservation inputs).typing.dispatch ready
          targetTree replacements |>.formationResult.targetFormationResult) =
        ((model.scopedCanonicalStrictPreservation inputs).typing.dispatch ready
          targetTree
          (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
          |>.formationResult.targetFormationResult) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  have firstAgreement :
      (dispatcher.typing.dispatch ready targetTree replacements
        |>.formationResult) =
      (dispatcher.formation.dispatch ready.formationReady targetTree replacements
        |>.formationResult) :=
    ((model.scopedAnchoredMutualFoldDispatcher inputs).typing ready
      |>.agreement.agree targetTree replacements).result_eq
  have secondAgreement :
      (dispatcher.typing.dispatch ready targetTree identityReplacements
        |>.formationResult) =
      (dispatcher.formation.dispatch ready.formationReady targetTree
        identityReplacements |>.formationResult) :=
    ((model.scopedAnchoredMutualFoldDispatcher inputs).typing ready
      |>.agreement.agree targetTree identityReplacements).result_eq
  exact (congrArg IncDepRawFormationSubstitutionFiberResult.targetFormationResult
    firstAgreement).trans ((formationInvariant targetTree replacements).trans
      (congrArg
        IncDepRawFormationSubstitutionFiberResult.targetFormationResult
        secondAgreement).symm)

/-- Conversely, full scoped typing target invariance supplies target invariance
    for the indexed formation, because canonical anchoring identifies both
    typing formation results with the independent formation dispatcher. -/
theorem incDepScopedCanonicalFormationTargetInvariantAt_of_typing
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation)
    (typingInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) ready) :
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      ready.formationReady := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  have firstAgreement :
      (dispatcher.typing.dispatch ready targetTree replacements
        |>.formationResult) =
      (dispatcher.formation.dispatch ready.formationReady targetTree replacements
        |>.formationResult) :=
    ((model.scopedAnchoredMutualFoldDispatcher inputs).typing ready
      |>.agreement.agree targetTree replacements).result_eq
  have secondAgreement :
      (dispatcher.typing.dispatch ready targetTree identityReplacements
        |>.formationResult) =
      (dispatcher.formation.dispatch ready.formationReady targetTree
        identityReplacements |>.formationResult) :=
    ((model.scopedAnchoredMutualFoldDispatcher inputs).typing ready
      |>.agreement.agree targetTree identityReplacements).result_eq
  exact (congrArg IncDepRawFormationSubstitutionFiberResult.targetFormationResult
    firstAgreement).symm.trans (((typingInvariant targetTree replacements).1).trans
      (congrArg
        IncDepRawFormationSubstitutionFiberResult.targetFormationResult
        secondAgreement))

/-- Once the indexed formation is target-invariant, full scoped typing target
    invariance is equivalent to its target-term `HEq` component. -/
theorem incDepScopedCanonicalTypingTargetInvariantAt_iff_term
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation)
    (formationInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      ready.formationReady) :
    IncDepTypingTargetInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs) ready ↔
      IncDepTypingTargetTermInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs) ready := by
  constructor
  · intro invariant source sourceWellFormed targetWellFormed sourceResult
      targetResult substitution substitutionResult targetTree replacements
    exact (invariant targetTree replacements).2
  · intro termInvariant source sourceWellFormed targetWellFormed sourceResult
      targetResult substitution substitutionResult targetTree replacements
    exact ⟨incDepScopedCanonicalTypingFormationTargetInvariantAt model inputs
        ready formationInvariant targetTree replacements,
      termInvariant targetTree replacements⟩

theorem incDepScopedCanonicalTypingTargetInvariantAt_unit
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} :
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.unitRule (context := context)) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  exact ⟨rfl, HEq.rfl⟩

/-- Exact law required of the variable provider by scoped canonical target
    invariance.  The provider intentionally contains arbitrary variable target
    choices, so this source-independence is not derivable from its bare type. -/
def IncDepScopedCanonicalVariableTargetInvariance
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) : Prop :=
  ∀ {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation},
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady →
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.varRule (lookup := lookup)
        typeReady)

theorem incDepScopedCanonicalTypingTargetInvariantAt_variable
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (variableInvariance :
      IncDepScopedCanonicalVariableTargetInvariance model inputs)
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    (typeInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) typeReady) :
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.varRule (lookup := lookup)
        typeReady) :=
  variableInvariance typeInvariant

theorem incDepScopedCanonicalTypingTargetInvariance_iff_local
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) :
    IncDepScopedCanonicalTypingTargetInvariance model inputs ↔
      ∀ {target : List IncDepRawType} {term : IncDepRawTerm}
        {type : IncDepRawType}
        {targetTyping : IncDepRawHasType target term type}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentTypingDispatchReady targetTyping
          targetFormation),
        IncDepTypingTargetInvariantForAt
          (model.scopedCanonicalStrictPreservation inputs) ready := by
  exact incDepTypingTargetInvarianceFor_iff_local _

structure IncDepScopedTypingTargetInvarianceBaseTheorem : Prop where
  globalLocal : ∀
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}),
    IncDepTypingTargetInvarianceFor dispatcher ↔
      ∀ {target : List IncDepRawType} {term : IncDepRawTerm}
        {type : IncDepRawType}
        {targetTyping : IncDepRawHasType target term type}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentTypingDispatchReady targetTyping
          targetFormation),
        IncDepTypingTargetInvariantForAt dispatcher ready
  unitClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType},
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.unitRule (context := context))
  variableClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepScopedCanonicalVariableTargetInvariance model inputs →
    ∀ {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
      {lookup : IncDepRawLookup context position type}
      {typeFormation : IncDepRawWellFormed context type}
      {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation},
      IncDepFormationTargetInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs) typeReady →
      IncDepTypingTargetInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs)
        (IncDepRawCoherentTypingDispatchReady.varRule (lookup := lookup)
          typeReady)

theorem incDepScopedTypingTargetInvarianceBaseTheorem :
    IncDepScopedTypingTargetInvarianceBaseTheorem.{u} where
  globalLocal := incDepTypingTargetInvarianceFor_iff_local
  unitClosed := incDepScopedCanonicalTypingTargetInvariantAt_unit
  variableClosed := incDepScopedCanonicalTypingTargetInvariantAt_variable

end IncidenceCore
