import IncidenceTheory.DependentCompletedSubstitutionNaturality

namespace IncidenceCore

open CategoryTheory

universe u

/-- The context-extension objects selected by one completed judgment on both
    sides of the syntactic/set-valued comparison. -/
structure IncDepCompletedContextExtensionComparison
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) where
  syntacticBase : IncDepRawFiniteContextObject
  syntacticType : IncDepRawFiniteType syntacticBase
  syntacticExtended : IncDepRawFiniteContextObject
  semanticBase : IncContext
  semanticType : IncTypeInContext semanticBase
  semanticExtended : IncContext

noncomputable def IncDepCompletedTyping.contextExtensionComparison
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepCompletedContextExtensionComparison typing :=
  let interpreted := typing.interpretCwF model
  { syntacticBase := typing.finiteContext
    syntacticType := typing.finiteType
    syntacticExtended := typing.finiteType.extendContext
    semanticBase := interpreted.semanticContext
    semanticType := interpreted.semanticType
    semanticExtended := interpreted.semanticContext.extend interpreted.semanticType }

@[simp] theorem IncDepCompletedTyping.contextExtensionComparison_raw
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    (typing.contextExtensionComparison model).syntacticExtended.context =
      type :: context :=
  rfl

/-- The syntactic comprehension pairing determined by a completed term and a
    semantically realized substitution. -/
noncomputable def IncDepCompletedSemanticSubstitution.syntacticPair
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    input.sourceContext ⟶ typing.finiteType.extendContext :=
  typing.finiteType.pairFiber input.finiteSubstitution
    (typing.finiteTerm.reindex input.finiteSubstitution)

@[simp] theorem IncDepCompletedSemanticSubstitution.syntacticPair_projection
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    input.syntacticPair ≫ typing.finiteType.projection =
      input.finiteSubstitution :=
  IncDepRawFiniteType.pairFiber_projection _ _ _

@[simp] theorem IncDepCompletedSemanticSubstitution.syntacticPair_generic
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    input.syntacticPair.substituteScopedTerm (.var 0)
        typing.finiteType.genericScope =
      term.substitute substitution.term := by
  rw [show term.substitute substitution.term =
      (typing.finiteTerm.reindex input.finiteSubstitution).val.term from
    input.reindex_term_raw.symm]
  exact IncDepRawFiniteType.pairFiber_generic _ _ _

/-- The set-valued pairing corresponding to the same completed term and
    semantic substitution. -/
noncomputable def IncDepCompletedTyping.semanticPairAlong
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution) :
    let result := typing.interpretAlong model sourceWellFormed substitution input
    input.sourceResult.semanticContext.Substitution
      (input.targetResult.semanticContext.extend
        result.formationResult.targetFormationResult.semanticType) :=
  let result := typing.interpretAlong model sourceWellFormed substitution input
  input.substitutionResult.semanticSubstitution.extend
    result.formationResult.targetFormationResult.semanticType
    (result.typingResult.targetTermResult.semanticTerm.substitute
      input.substitutionResult.semanticSubstitution)

@[simp] theorem IncDepCompletedTyping.semanticPairAlong_projection
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution) :
    let result := typing.interpretAlong model sourceWellFormed substitution input
    (input.targetResult.semanticContext.extendProjection
        result.formationResult.targetFormationResult.semanticType).comp
      (typing.semanticPairAlong model sourceWellFormed substitution input) =
      input.substitutionResult.semanticSubstitution := by
  exact IncContext.Substitution.extend_projection _ _ _

@[simp] theorem IncDepCompletedTyping.semanticPairAlong_variable
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution) :
    let result := typing.interpretAlong model sourceWellFormed substitution input
    (input.targetResult.semanticContext.extendVariable
        result.formationResult.targetFormationResult.semanticType).substitute
      (typing.semanticPairAlong model sourceWellFormed substitution input) =
      result.typingResult.targetTermResult.semanticTerm.substitute
        input.substitutionResult.semanticSubstitution := by
  exact IncContext.Substitution.extend_variable _ _ _

/-- The generic component of the semantic pairing is also the transported
    interpretation of the syntactically substituted term. -/
theorem IncDepCompletedTyping.semanticPairAlong_transport
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution) :
    let result := typing.interpretAlong model sourceWellFormed substitution input
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      (input.targetResult.semanticContext.extendVariable
        result.formationResult.targetFormationResult.semanticType).substitute
          (typing.semanticPairAlong model sourceWellFormed substitution input) := by
  let result := typing.interpretAlong model sourceWellFormed substitution input
  exact result.typingResult.semanticTerm_coherence.trans
    (typing.semanticPairAlong_variable model sourceWellFormed substitution input).symm

structure IncDepCompletedComprehensionNaturalityTheorem : Prop where
  extension_raw : ∀ (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} (typing : IncDepCompletedTyping context term type),
    (typing.contextExtensionComparison model).syntacticExtended.context =
      type :: context
  syntactic_projection : ∀ {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution),
    input.syntacticPair ≫ typing.finiteType.projection = input.finiteSubstitution
  syntactic_generic : ∀ {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution),
    input.syntacticPair.substituteScopedTerm (.var 0)
        typing.finiteType.genericScope = term.substitute substitution.term
  semantic_transport : ∀ (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution),
    let result := typing.interpretAlong model sourceWellFormed substitution input
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      (input.targetResult.semanticContext.extendVariable
        result.formationResult.targetFormationResult.semanticType).substitute
          (typing.semanticPairAlong model sourceWellFormed substitution input)

theorem incDepCompletedComprehensionNaturalityTheorem :
    IncDepCompletedComprehensionNaturalityTheorem where
  extension_raw := IncDepCompletedTyping.contextExtensionComparison_raw
  syntactic_projection :=
    IncDepCompletedSemanticSubstitution.syntacticPair_projection
  syntactic_generic := IncDepCompletedSemanticSubstitution.syntacticPair_generic
  semantic_transport := IncDepCompletedTyping.semanticPairAlong_transport

end IncidenceCore
