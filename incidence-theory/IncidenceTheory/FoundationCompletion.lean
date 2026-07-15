import IncidenceTheory.CrossInstance
import IncidenceTheory.ReferenceFoundationLogic

/-!
  Public completion boundary for the dependent interpretation.

  `IncDepRawHasType` predates the semantic development and intentionally does
  not retain every formation derivation needed by dependent application and
  projection.  The semantically meaningful judgment is therefore the existing
  `IncDepRawFullyCoherentCertifiedTyping`: it contains a raw derivation, a
  recursively certified telescope, the result formation, and coherent
  readiness for every constructor.

  This module gives that judgment a stable completion-facing name and exposes
  one total interpreter plus its coherence theorem.  Clients no longer need to
  know the provider/fold implementation in `CrossInstance.lean`.
-/

namespace IncidenceCore

universe u

abbrev IncDepCompletedTyping := IncDepRawFullyCoherentCertifiedTyping

structure IncDepCompletionModel where
  fiberModel : IncDepRawSubstitutionFiberModel.{u}
  preservation : IncDepRawCanonicalSubstitutionPreservationHypotheses

def IncDepCompletedTyping.erase
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepRawCertifiedTyping context term type :=
  { contextWellFormed := typing.contextWellFormed.toRaw
    typeWellFormed := typing.typeWellFormed
    typing := typing.typing }

noncomputable def IncDepCompletionModel.interpretTyping
    (model : IncDepCompletionModel.{u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :=
  model.fiberModel.interpretFullyCoherentCertified model.preservation typing

theorem IncDepCompletionModel.interpretTyping_sound
    (model : IncDepCompletionModel.{u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    let input := typing.toInput model.fiberModel model.preservation
    let result := model.interpretTyping typing
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      result.typingResult.targetTermResult.semanticTerm.substitute
        (IncDepRawSubstitutionSemanticResult.identity
          input.contextResult).semanticSubstitution := by
  exact model.fiberModel.interpretFullyCoherentCertified_coherent
    model.preservation typing

/- A completed judgment has a genuine semantic context, type, and term. -/
structure IncDepCompletedInterpretation
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
  (typing : IncDepCompletedTyping context term type) where
  semanticContext : IncContext
  semanticType : IncTypeInContext semanticContext
  semanticTerm : IncTerm semanticType

noncomputable def IncDepCompletedTyping.interpret
    (model : IncDepCompletionModel.{u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepCompletedInterpretation typing := by
  let input := typing.toInput model.fiberModel model.preservation
  let result := model.interpretTyping typing
  exact
    { semanticContext := input.contextResult.semanticContext
      semanticType := result.formationResult.targetFormationResult.semanticType
      semanticTerm := result.typingResult.targetTermResult.semanticTerm }

/- The completion judgment is conservative as syntax: it adds evidence but
   does not change the erased term, type, context, or raw typing derivation. -/
theorem IncDepCompletedTyping.erase_typing
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    typing.erase.typing = typing.typing := rfl

theorem IncDepCompletedTyping.erase_formation
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    typing.erase.typeWellFormed = typing.typeWellFormed := rfl

end IncidenceCore
