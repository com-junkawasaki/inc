import IncidenceTheory.DependentCanonicalRebase

namespace IncidenceCore

universe u

/-- Target invariance stated against an explicit mutual dispatcher.  This
    removes the obsolete, uninhabited global-rebase hypothesis from the logical
    statement and lets provider-free canonical dispatchers be studied directly. -/
def IncDepFormationTargetInvarianceFor
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}) : Prop :=
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
    (dispatcher.formation.dispatch ready targetTree replacements
      |>.formationResult.targetFormationResult) =
    (dispatcher.formation.dispatch ready targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult)

/-- Typing target invariance for an explicit dispatcher. -/
def IncDepTypingTargetInvarianceFor
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}) : Prop :=
  ∀ {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source target}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    (ready : IncDepRawCoherentTypingDispatchReady targetTyping targetFormation)
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

def IncDepFormationTargetInvariantForAt
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u})
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
    (dispatcher.formation.dispatch ready targetTree replacements
      |>.formationResult.targetFormationResult) =
    (dispatcher.formation.dispatch ready targetTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree)
      |>.formationResult.targetFormationResult)

theorem incDepFormationTargetInvarianceFor_iff_local
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}) :
    IncDepFormationTargetInvarianceFor dispatcher ↔
      ∀ {target : List IncDepRawType} {type : IncDepRawType}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentFormationDispatchReady targetFormation),
        IncDepFormationTargetInvariantForAt dispatcher ready := by
  constructor
  · intro global target type targetFormation ready source sourceWellFormed
      targetWellFormed sourceResult targetResult substitution substitutionResult
      targetTree replacements
    exact global ready targetTree replacements
  · intro localHyp source target type sourceWellFormed targetWellFormed
      sourceResult targetResult substitution substitutionResult targetFormation
      ready targetTree replacements
    exact localHyp ready targetTree replacements

/-- The old formation statement is exactly the explicit-dispatcher statement
    specialized to `preservationCanonical`; no mathematical content is lost by
    migrating clients to the latter interface. -/
theorem incDepCanonicalFormationTargetInvariance_eq_dispatcher
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}) :
    IncDepCanonicalFormationTargetInvariance model hypotheses ↔
      IncDepFormationTargetInvarianceFor
        (model.preservationCanonical hypotheses) := by
  rfl

/-- Non-obsolete target-invariance objective for the existing scoped canonical
    preservation dispatcher. -/
def IncDepScopedCanonicalFormationTargetInvariance
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) : Prop :=
  IncDepFormationTargetInvarianceFor
    (model.scopedCanonicalStrictPreservation inputs)

def IncDepScopedCanonicalTypingTargetInvariance
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) : Prop :=
  IncDepTypingTargetInvarianceFor
    (model.scopedCanonicalStrictPreservation inputs)

theorem incDepScopedCanonicalFormationTargetInvariance_iff_local
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) :
    IncDepScopedCanonicalFormationTargetInvariance model inputs ↔
      ∀ {target : List IncDepRawType} {type : IncDepRawType}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentFormationDispatchReady targetFormation),
        IncDepFormationTargetInvariantForAt
          (model.scopedCanonicalStrictPreservation inputs) ready := by
  exact incDepFormationTargetInvarianceFor_iff_local _

structure IncDepDispatcherTargetInvarianceTheorem : Prop where
  explicitGlobalLocal : ∀
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}),
    IncDepFormationTargetInvarianceFor dispatcher ↔
      ∀ {target : List IncDepRawType} {type : IncDepRawType}
        {targetFormation : IncDepRawWellFormed target type}
        (ready : IncDepRawCoherentFormationDispatchReady targetFormation),
        IncDepFormationTargetInvariantForAt dispatcher ready
  oldInterfaceSpecializes : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}),
    IncDepCanonicalFormationTargetInvariance model hypotheses ↔
      IncDepFormationTargetInvarianceFor
        (model.preservationCanonical hypotheses)

theorem incDepDispatcherTargetInvarianceTheorem :
    IncDepDispatcherTargetInvarianceTheorem.{u} where
  explicitGlobalLocal := incDepFormationTargetInvarianceFor_iff_local
  oldInterfaceSpecializes :=
    incDepCanonicalFormationTargetInvariance_eq_dispatcher

end IncidenceCore
