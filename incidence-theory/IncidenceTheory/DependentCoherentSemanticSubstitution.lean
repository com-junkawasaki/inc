import IncidenceTheory.DependentSemanticSubstitutionInduction

namespace IncidenceCore

universe u

/-- Intrinsic lookup coherence for one component of a semantic substitution.
    It identifies the chosen replacement family with the target lookup family
    reindexed by the semantic assignment map and requires the terms to agree
    after that identification. -/
structure IncDepSemanticLookupCoherence
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    {position : Nat} {type : IncDepRawType}
    (lookup : IncDepRawLookup target position type) where
  fiberEquivalence : IncTypeInContext.FiberEquiv
    (input.replacements.semanticType lookup)
    ((targetTree.interpretLookup lookup).semanticType.reindex
      input.substitutionResult.semanticSubstitution)
  termCoherence : fiberEquivalence.transport
      (input.replacements.typingResult lookup).semanticTerm =
    (targetTree.interpretLookup lookup).semanticTerm.substitute
      input.substitutionResult.semanticSubstitution

/-- Strengthened target-independent realization.  Unlike the basic carrier,
    this interface internalizes lookup-by-lookup coherence rather than relying
    on the provenance of a particular constructor. -/
structure IncDepCoherentSemanticSubstitutionInto
    {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source target) where
  realization : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
    targetWellFormed targetResult substitution
  targetTree : IncDepRawContextSemanticTree targetResult
  lookupCoherence : ∀ {position : Nat} {type : IncDepRawType}
    (lookup : IncDepRawLookup target position type),
    IncDepSemanticLookupCoherence realization targetTree lookup

def IncDepCoherentSemanticSubstitutionInto.semanticSubstitution
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution) :=
  input.realization.substitutionResult.semanticSubstitution

/-- Identity substitutions satisfy intrinsic lookup coherence over every
    coherently interpreted target context. -/
noncomputable def IncDepCoherentSemanticSubstitutionInto.identity
    {context : List IncDepRawType}
    (contextWellFormed : IncDepRawCoherentContext.WellFormed context)
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed.toRaw)
    (contextTree : IncDepRawContextSemanticTree contextResult) :
    IncDepCoherentSemanticSubstitutionInto.{u} contextWellFormed
      contextWellFormed contextResult (IncDepRawSubstitution.identity context) :=
  let realization : IncDepSemanticSubstitutionInto.{u} contextWellFormed
      contextWellFormed contextResult (IncDepRawSubstitution.identity context) :=
    { sourceResult := contextResult
      substitutionResult := IncDepRawSubstitutionSemanticResult.identity contextResult
      replacements :=
        IncDepRawSubstitutionReplacementSemanticResult.identity contextTree }
  { realization := realization
    targetTree := contextTree
    lookupCoherence := by
      intro position type lookup
      exact
        { fiberEquivalence := IncTypeInContext.FiberEquiv.refl _
          termCoherence := rfl } }

@[simp] theorem IncDepCoherentSemanticSubstitutionInto.identity_map
    {context : List IncDepRawType}
    (contextWellFormed : IncDepRawCoherentContext.WellFormed context)
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed.toRaw)
    (contextTree : IncDepRawContextSemanticTree contextResult) :
    (IncDepCoherentSemanticSubstitutionInto.identity contextWellFormed
      contextResult contextTree).semanticSubstitution =
        IncContext.Substitution.identity contextResult.semanticContext :=
  rfl

/-- The completed display projection satisfies the strengthened lookup
    coherence interface, not just its previously stated component equations. -/
noncomputable def IncDepCompletedTyping.coherentProjectionSemanticSubstitution
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    let completedInput := typing.toInput model.fiberModel model.preservation
    IncDepCoherentSemanticSubstitutionInto.{u}
      typing.projectionSourceWellFormed typing.contextWellFormed
      completedInput.contextResult (incDepRawDisplayProjection context type) := by
  let completedInput := typing.toInput model.fiberModel model.preservation
  let realization := (typing.projectionSemanticSubstitution model).toSemanticInto
  exact
    { realization := realization
      targetTree := completedInput.contextTree
      lookupCoherence := by
        intro position lookupType lookup
        exact
          { fiberEquivalence := IncTypeInContext.FiberEquiv.refl _
            termCoherence := rfl } }

@[simp] theorem IncDepCompletedTyping.coherentProjectionSemanticSubstitution_map
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    let completedInput := typing.toInput model.fiberModel model.preservation
    let interpreted := model.interpretTyping typing
    (typing.coherentProjectionSemanticSubstitution model).semanticSubstitution =
      completedInput.contextResult.semanticContext.extendProjection
        interpreted.formationResult.targetFormationResult.semanticType := by
  rfl

structure IncDepCoherentSemanticSubstitutionTheorem : Prop where
  identityCoherent : ∀
    {context : List IncDepRawType}
    (contextWellFormed : IncDepRawCoherentContext.WellFormed context)
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed.toRaw)
    (contextTree : IncDepRawContextSemanticTree contextResult),
    ∃ input : IncDepCoherentSemanticSubstitutionInto.{u} contextWellFormed
      contextWellFormed contextResult (IncDepRawSubstitution.identity context),
      input.targetTree = contextTree
  projectionCoherent : ∀
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    let completedInput := typing.toInput model.fiberModel model.preservation
    ∃ input : IncDepCoherentSemanticSubstitutionInto.{u}
      typing.projectionSourceWellFormed typing.contextWellFormed
      completedInput.contextResult (incDepRawDisplayProjection context type),
      input.targetTree = completedInput.contextTree

theorem incDepCoherentSemanticSubstitutionTheorem :
    IncDepCoherentSemanticSubstitutionTheorem.{u} where
  identityCoherent := fun contextWellFormed contextResult contextTree =>
    ⟨IncDepCoherentSemanticSubstitutionInto.identity contextWellFormed
      contextResult contextTree, rfl⟩
  projectionCoherent := by
    intro model context term type typing
    exact ⟨typing.coherentProjectionSemanticSubstitution model, rfl⟩

end IncidenceCore
