import IncidenceTheory.DependentCompletedComprehensionNaturality

namespace IncidenceCore

universe u

/-- Identity substitutions require no external semantic-realization witness:
    the coherent telescope synthesizer already supplies their context tree and
    every variable is interpreted by lookup. -/
noncomputable def IncDepCompletedTyping.identitySemanticSubstitution
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    IncDepCompletedSemanticSubstitution.{u} typing typing.contextWellFormed
      (IncDepRawSubstitution.identity context) :=
  let completedInput := typing.toInput model.fiberModel model.preservation
  { sourceResult := completedInput.contextResult
    targetResult := completedInput.contextResult
    targetTree := completedInput.contextTree
    substitutionResult :=
      IncDepRawSubstitutionSemanticResult.identity completedInput.contextResult
    replacements := IncDepRawSubstitutionReplacementSemanticResult.identity
      completedInput.contextTree }

@[simp] theorem IncDepCompletedTyping.identitySemanticSubstitution_map
    (model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    (typing.identitySemanticSubstitution model).substitutionResult.semanticSubstitution =
      IncContext.Substitution.identity
        (typing.identitySemanticSubstitution model).sourceResult.semanticContext :=
  rfl

theorem incDepCompletedIdentitySubstitutionCoverage
    (model : IncDepCompletionModel.{u, u, u}) :
    ∀ {context : List IncDepRawType} {term : IncDepRawTerm}
      {type : IncDepRawType}
      (typing : IncDepCompletedTyping context term type),
      Nonempty (IncDepCompletedSemanticSubstitution.{u} typing
        typing.contextWellFormed (IncDepRawSubstitution.identity context)) :=
  fun typing => ⟨typing.identitySemanticSubstitution model⟩

/-- Exact, model-independent gates for promoting the checked local comparison
    theorems to a total CwF morphism.  The first field completes every term of
    the finite syntactic CwF; the second realizes every raw substitution into
    every such completed judgment. -/
structure IncDepWholeCwFMorphismReadiness : Prop where
  judgmentCoverage : ∀
    {context : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType context}
    (term : IncDepRawFiniteTerm type),
    term.SemanticallyCompletable
  substitutionCoverage : IncDepCompletedSubstitutionSemanticCoverage.{u}

def IncDepWholeCwFMorphismReadiness.ofGates
    (judgments : ∀
      {context : IncDepRawFiniteContextObject}
      {type : IncDepRawFiniteType context}
      (term : IncDepRawFiniteTerm type), term.SemanticallyCompletable)
    (substitutions : IncDepCompletedSubstitutionSemanticCoverage.{u}) :
    IncDepWholeCwFMorphismReadiness.{u} where
  judgmentCoverage := judgments
  substitutionCoverage := substitutions

theorem incDepWholeCwFMorphismReadiness_iff :
    Nonempty IncDepWholeCwFMorphismReadiness.{u} ↔
      (∀ {context : IncDepRawFiniteContextObject}
        {type : IncDepRawFiniteType context}
        (term : IncDepRawFiniteTerm type), term.SemanticallyCompletable) ∧
      IncDepCompletedSubstitutionSemanticCoverage.{u} := by
  constructor
  · rintro ⟨readiness⟩
    exact ⟨readiness.judgmentCoverage, readiness.substitutionCoverage⟩
  · rintro ⟨judgments, substitutions⟩
    exact ⟨.ofGates judgments substitutions⟩

/-- The currently checked local CwF-morphism laws together with the exact two
    global coverage gates.  This prevents either coverage obligation from being
    hidden when the local theorems are cited. -/
structure IncDepWholeCwFMorphismBoundaryTheorem : Prop where
  localJudgmentComparison : IncDepCompletedCwFComparisonTheorem
  localSubstitutionNaturality : IncDepCompletedSubstitutionNaturalityTheorem
  localComprehensionNaturality : IncDepCompletedComprehensionNaturalityTheorem
  identitySubstitutionsRealized : ∀
    (_model : IncDepCompletionModel.{u, u, u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type),
    Nonempty (IncDepCompletedSemanticSubstitution.{u} typing
      typing.contextWellFormed (IncDepRawSubstitution.identity context))
  totalityBoundary : Nonempty IncDepWholeCwFMorphismReadiness.{u} ↔
      (∀ {context : IncDepRawFiniteContextObject}
        {type : IncDepRawFiniteType context}
        (term : IncDepRawFiniteTerm type), term.SemanticallyCompletable) ∧
      IncDepCompletedSubstitutionSemanticCoverage.{u}

theorem incDepWholeCwFMorphismBoundaryTheorem :
    IncDepWholeCwFMorphismBoundaryTheorem.{u} where
  localJudgmentComparison := incDepCompletedCwFComparisonTheorem
  localSubstitutionNaturality := incDepCompletedSubstitutionNaturalityTheorem
  localComprehensionNaturality := incDepCompletedComprehensionNaturalityTheorem
  identitySubstitutionsRealized := incDepCompletedIdentitySubstitutionCoverage
  totalityBoundary := incDepWholeCwFMorphismReadiness_iff

end IncidenceCore
