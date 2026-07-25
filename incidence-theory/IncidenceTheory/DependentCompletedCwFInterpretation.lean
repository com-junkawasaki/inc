import IncidenceTheory.DependentFiniteCwF
import IncidenceTheory.FoundationCompletion

namespace IncidenceCore

universe u

def IncDepCompletedTyping.finiteContext
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepRawFiniteContextObject where
  context := context
  wellFormed := typing.contextWellFormed.toRaw

def IncDepCompletedTyping.finiteType
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepRawFiniteType typing.finiteContext where
  raw := type
  formation := ⟨typing.typeWellFormed⟩

def IncDepCompletedTyping.finiteTotalTerm
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepRawFiniteTypedTerm typing.finiteContext where
  type := type
  term := term
  formation := ⟨typing.typeWellFormed⟩
  typing := ⟨typing.typing⟩

def IncDepCompletedTyping.finiteTerm
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepRawFiniteTerm typing.finiteType where
  val := typing.finiteTotalTerm
  property := rfl

@[simp] theorem IncDepCompletedTyping.finiteContext_raw
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    typing.finiteContext.context = context := rfl

@[simp] theorem IncDepCompletedTyping.finiteType_raw
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    typing.finiteType.raw = type := rfl

@[simp] theorem IncDepCompletedTyping.finiteTerm_raw
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    typing.finiteTerm.val.term = term := rfl

/-- The exact readiness gate for extending the completed interpretation to a
    raw CwF term: the same raw context/type/term must admit a fully coherent
    certificate, not merely formation and typing derivations. -/
def IncDepRawFiniteTerm.SemanticallyCompletable
    {context : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType context}
    (term : IncDepRawFiniteTerm type) : Prop :=
  Nonempty (IncDepCompletedTyping context.context term.val.term type.raw)

theorem IncDepCompletedTyping.finiteTerm_semanticallyCompletable
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    typing.finiteTerm.SemanticallyCompletable :=
  ⟨typing⟩

structure IncDepCompletedCwFInterpretation
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) where
  syntacticContext : IncDepRawFiniteContextObject
  syntacticType : IncDepRawFiniteType syntacticContext
  syntacticTerm : IncDepRawFiniteTerm syntacticType
  semanticContext : IncContext
  semanticType : IncTypeInContext semanticContext
  semanticTerm : IncTerm semanticType

noncomputable def IncDepCompletedTyping.interpretCwF
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepCompletedCwFInterpretation typing :=
  let interpreted := typing.interpret model
  { syntacticContext := typing.finiteContext
    syntacticType := typing.finiteType
    syntacticTerm := typing.finiteTerm
    semanticContext := interpreted.semanticContext
    semanticType := interpreted.semanticType
    semanticTerm := interpreted.semanticTerm }

theorem IncDepCompletedTyping.interpretCwF_identity_coherent
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    let input := typing.toInput model.fiberModel model.preservation
    let result := model.interpretTyping typing
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      result.typingResult.targetTermResult.semanticTerm.substitute
        (IncDepRawSubstitutionSemanticResult.identity
          input.contextResult).semanticSubstitution :=
  model.interpretTyping_sound typing

structure IncDepCompletedCwFComparisonTheorem : Prop where
  conservative_context : ∀ {context : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    typing.finiteContext.context = context
  conservative_type : ∀ {context : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    typing.finiteType.raw = type
  conservative_term : ∀ {context : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    typing.finiteTerm.val.term = term
  completed_lift : ∀ {context : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    typing.finiteTerm.SemanticallyCompletable
  identity_coherent : ∀ (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} (typing : IncDepCompletedTyping context term type),
    let input := typing.toInput model.fiberModel model.preservation
    let result := model.interpretTyping typing
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      result.typingResult.targetTermResult.semanticTerm.substitute
        (IncDepRawSubstitutionSemanticResult.identity
          input.contextResult).semanticSubstitution

theorem incDepCompletedCwFComparisonTheorem :
    IncDepCompletedCwFComparisonTheorem where
  conservative_context := IncDepCompletedTyping.finiteContext_raw
  conservative_type := IncDepCompletedTyping.finiteType_raw
  conservative_term := IncDepCompletedTyping.finiteTerm_raw
  completed_lift := IncDepCompletedTyping.finiteTerm_semanticallyCompletable
  identity_coherent := by
    intro model context term type typing
    exact typing.interpretCwF_identity_coherent model

end IncidenceCore
