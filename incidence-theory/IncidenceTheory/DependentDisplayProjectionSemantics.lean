import IncidenceTheory.DependentWholeCwFMorphismReadiness

namespace IncidenceCore

universe u

noncomputable def incDepRawDisplayProjection
    (context : List IncDepRawType) (type : IncDepRawType) :
    IncDepRawSubstitution (type :: context) context :=
  let projection := IncDepRawExtensionalSubstitution.projection context type
  { term := projection.term
    preserves := fun lookup => Classical.choice (projection.preserves lookup) }

@[simp] theorem incDepRawDisplayProjection_term
    (context : List IncDepRawType) (type : IncDepRawType) (index : Nat) :
    (incDepRawDisplayProjection context type).term index = .var (index + 1) :=
  rfl

def IncDepCompletedTyping.projectionSourceWellFormed
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepRawCoherentContext.WellFormed (type :: context) :=
  .extend typing.contextWellFormed typing.readiness.formationReady

/-- The display projection of every completed type has a canonical semantic
    realization.  Its source context is the set-valued extension by the
    interpreted type, its semantic map is `Sigma.fst`, and every replacement is
    the corresponding target lookup weakened along that projection. -/
noncomputable def IncDepCompletedTyping.projectionSemanticSubstitution
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepCompletedSemanticSubstitution.{u} typing
      typing.projectionSourceWellFormed
      (incDepRawDisplayProjection context type) :=
  let completedInput := typing.toInput model.fiberModel model.preservation
  let interpreted := model.interpretTyping typing
  let semanticType := interpreted.formationResult.targetFormationResult.semanticType
  let sourceResult := completedInput.contextResult.extend semanticType
  let sourceTree := IncDepRawContextSemanticTree.extend completedInput.contextTree
    interpreted.formationResult.targetFormationResult
  let substitutionResult : IncDepRawSubstitutionSemanticResult
      (incDepRawDisplayProjection context type) sourceResult
      completedInput.contextResult :=
    { semanticSubstitution :=
        completedInput.contextResult.semanticContext.extendProjection semanticType }
  { sourceResult := sourceResult
    targetResult := completedInput.contextResult
    targetTree := completedInput.contextTree
    substitutionResult := substitutionResult
    replacements :=
      { replacement := by
          intro position lookupType lookup
          let lookupResult := completedInput.contextTree.interpretLookup lookup
          exact ⟨lookupResult.semanticType.reindex
              (completedInput.contextResult.semanticContext.extendProjection
                semanticType),
            { semanticTerm := lookupResult.semanticTerm.substitute
                (completedInput.contextResult.semanticContext.extendProjection
                  semanticType) }⟩ } }

@[simp] theorem IncDepCompletedTyping.projectionSemanticSubstitution_map
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    let input := typing.toInput model.fiberModel model.preservation
    let interpreted := model.interpretTyping typing
    (typing.projectionSemanticSubstitution model).substitutionResult.semanticSubstitution =
      input.contextResult.semanticContext.extendProjection
        interpreted.formationResult.targetFormationResult.semanticType := by
  rfl

@[simp] theorem IncDepCompletedTyping.projectionSemanticSubstitution_replacement
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type)
    {position : Nat} {lookupType : IncDepRawType}
    (lookup : IncDepRawLookup context position lookupType) :
    let input := typing.toInput model.fiberModel model.preservation
    let interpreted := model.interpretTyping typing
    ((typing.projectionSemanticSubstitution model).replacements.typingResult
      lookup).semanticTerm =
      (input.contextTree.interpretLookup lookup).semanticTerm.substitute
        (input.contextResult.semanticContext.extendProjection
          interpreted.formationResult.targetFormationResult.semanticType) := by
  rfl

theorem incDepCompletedDisplayProjectionCoverage
    (model : IncDepCompletionModel.{u, u, u}) :
    ∀ {context : List IncDepRawType} {term : IncDepRawTerm}
      {type : IncDepRawType}
      (typing : IncDepCompletedTyping context term type),
      Nonempty (IncDepCompletedSemanticSubstitution.{u} typing
        typing.projectionSourceWellFormed
        (incDepRawDisplayProjection context type)) :=
  fun typing => ⟨typing.projectionSemanticSubstitution model⟩

theorem IncDepCompletedTyping.projectionFinite_exact
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    (typing.projectionSemanticSubstitution model).finiteSubstitution =
      typing.finiteType.projection := by
  apply Quotient.sound
  intro index indexLt
  rfl

structure IncDepCompletedDisplayProjectionSemanticsTheorem : Prop where
  rawComponent : ∀ (context : List IncDepRawType) (type : IncDepRawType)
    (index : Nat),
    (incDepRawDisplayProjection context type).term index = .var (index + 1)
  realized : ∀ (_model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    Nonempty (IncDepCompletedSemanticSubstitution.{u} typing
      typing.projectionSourceWellFormed
      (incDepRawDisplayProjection context type))
  finiteExact : ∀ (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    (typing.projectionSemanticSubstitution model).finiteSubstitution =
      typing.finiteType.projection

theorem incDepCompletedDisplayProjectionSemanticsTheorem :
    IncDepCompletedDisplayProjectionSemanticsTheorem.{u} where
  rawComponent := incDepRawDisplayProjection_term
  realized := incDepCompletedDisplayProjectionCoverage
  finiteExact := IncDepCompletedTyping.projectionFinite_exact

end IncidenceCore
