import IncidenceTheory.DependentCompletedCwFInterpretation

namespace IncidenceCore

open CategoryTheory

universe u

/-- All semantic data needed to interpret one raw substitution into the
    context of a completed typing judgment.  Keeping this data explicit makes
    the remaining global-completion obligation visible rather than hiding it
    behind a choice principle. -/
structure IncDepCompletedSemanticSubstitution
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target) where
  sourceResult : IncDepRawContextSemanticResult sourceWellFormed.toRaw
  targetResult : IncDepRawContextSemanticResult typing.contextWellFormed.toRaw
  targetTree : IncDepRawContextSemanticTree targetResult
  substitutionResult : IncDepRawSubstitutionSemanticResult substitution
    sourceResult targetResult
  replacements : IncDepRawSubstitutionReplacementSemanticResult
    substitutionResult

def IncDepCompletedSemanticSubstitution.sourceContext
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (_ : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    IncDepRawFiniteContextObject where
  context := source
  wellFormed := sourceWellFormed.toRaw

noncomputable def IncDepCompletedSemanticSubstitution.finiteSubstitution
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    input.sourceContext ⟶ typing.finiteContext :=
  Quotient.mk _ substitution.toExtensional

/-- The syntactic side of a completed semantic substitution is exactly raw
    substitution of the original term; the quotient-CwF map introduces no
    change of syntax. -/
@[simp] theorem IncDepCompletedSemanticSubstitution.reindex_term_raw
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    (typing.finiteTerm.reindex input.finiteSubstitution).val.term =
      term.substitute substitution.term :=
  rfl

/-- Interpret a completed judgment along an arbitrary semantically realized
    substitution, using the general mutual substitution dispatcher. -/
noncomputable def IncDepCompletedTyping.interpretAlong
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :=
  (model.fiberModel.preservationCanonical model.preservation).typing.dispatch
    typing.readiness input.targetTree input.replacements

/-- Arbitrary-substitution naturality for the completed fragment.  The
    transported interpretation of the substituted raw term is precisely the
    substitution of the original semantic term. -/
theorem IncDepCompletedTyping.interpretAlong_coherent
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    let result := typing.interpretAlong model sourceWellFormed substitution input
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      result.typingResult.targetTermResult.semanticTerm.substitute
        input.substitutionResult.semanticSubstitution := by
  exact (typing.interpretAlong model sourceWellFormed substitution input)
    |>.typingResult.semanticTerm_coherence

/-- The precise global gate left before the naturality theorem applies to
    every substitution into every completed judgment. -/
def IncDepCompletedSubstitutionSemanticCoverage : Prop :=
  ∀ {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target),
    Nonempty (IncDepCompletedSemanticSubstitution.{u} typing sourceWellFormed substitution)

structure IncDepCompletedSubstitutionNaturalityTheorem : Prop where
  syntactic_exact : ∀ {source target term type}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u} typing sourceWellFormed substitution),
    (typing.finiteTerm.reindex input.finiteSubstitution).val.term =
      term.substitute substitution.term
  semantic_natural : ∀ (model : IncDepCompletionModel.{u, u, u})
    {source target term type}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target)
    (input : IncDepCompletedSemanticSubstitution.{u} typing sourceWellFormed substitution),
    let result := typing.interpretAlong model sourceWellFormed substitution input
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      result.typingResult.targetTermResult.semanticTerm.substitute
        input.substitutionResult.semanticSubstitution

theorem incDepCompletedSubstitutionNaturalityTheorem :
    IncDepCompletedSubstitutionNaturalityTheorem where
  syntactic_exact := IncDepCompletedSemanticSubstitution.reindex_term_raw
  semantic_natural := IncDepCompletedTyping.interpretAlong_coherent

end IncidenceCore
