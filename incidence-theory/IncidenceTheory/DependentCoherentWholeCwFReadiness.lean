import IncidenceTheory.DependentCoherentSemanticSubstitutionClosure

namespace IncidenceCore

universe u

/-- Global substitution coverage anchored to the canonical semantic context and
    tree synthesized by a fixed completion model, with intrinsic lookup
    coherence for every component. -/
def IncDepCompletedCoherentSubstitutionCoverage
    (model : IncDepCompletionModel.{u, u, u}) : Prop :=
  ∀ {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typing : IncDepCompletedTyping target term type)
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (substitution : IncDepRawSubstitution source target),
    let completedInput := typing.toInput model.fiberModel model.preservation
    Nonempty (IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      typing.contextWellFormed completedInput.contextResult substitution)

/-- Forget intrinsic lookup coherence while retaining the exact canonical
    target context and target semantic tree. -/
noncomputable def IncDepCoherentSemanticSubstitutionInto.toCompleted
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input :
      let completedInput := typing.toInput model.fiberModel model.preservation
      IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
        typing.contextWellFormed completedInput.contextResult substitution) :
    IncDepCompletedSemanticSubstitution.{u} typing sourceWellFormed substitution :=
  { sourceResult := input.realization.sourceResult
    targetResult := (typing.toInput model.fiberModel model.preservation).contextResult
    targetTree := input.targetTree
    substitutionResult := input.realization.substitutionResult
    replacements := input.realization.replacements }

@[simp] theorem IncDepCoherentSemanticSubstitutionInto.toCompleted_map
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input :
      let completedInput := typing.toInput model.fiberModel model.preservation
      IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
        typing.contextWellFormed completedInput.contextResult substitution) :
    (input.toCompleted model).substitutionResult.semanticSubstitution =
      input.semanticSubstitution :=
  rfl

theorem IncDepCompletedCoherentSubstitutionCoverage.toBasic
    (model : IncDepCompletionModel.{u, u, u})
    (coverage : IncDepCompletedCoherentSubstitutionCoverage model) :
    IncDepCompletedSubstitutionSemanticCoverage.{u} := by
  intro source target term type typing sourceWellFormed substitution
  rcases coverage typing sourceWellFormed substitution with ⟨input⟩
  exact ⟨input.toCompleted model⟩

/-- Strengthened whole-CwF readiness.  The judgment gate is unchanged, while
    substitution coverage is now canonical-model-anchored and intrinsically
    lookup coherent. -/
structure IncDepCoherentWholeCwFMorphismReadiness
    (model : IncDepCompletionModel.{u, u, u}) : Prop where
  judgmentCoverage : ∀
    {context : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType context}
    (term : IncDepRawFiniteTerm type),
    term.SemanticallyCompletable
  coherentSubstitutionCoverage :
    IncDepCompletedCoherentSubstitutionCoverage model

def IncDepCoherentWholeCwFMorphismReadiness.ofGates
    (model : IncDepCompletionModel.{u, u, u})
    (judgments : ∀
      {context : IncDepRawFiniteContextObject}
      {type : IncDepRawFiniteType context}
      (term : IncDepRawFiniteTerm type), term.SemanticallyCompletable)
    (substitutions : IncDepCompletedCoherentSubstitutionCoverage model) :
    IncDepCoherentWholeCwFMorphismReadiness model where
  judgmentCoverage := judgments
  coherentSubstitutionCoverage := substitutions

theorem incDepCoherentWholeCwFMorphismReadiness_iff
    (model : IncDepCompletionModel.{u, u, u}) :
    Nonempty (IncDepCoherentWholeCwFMorphismReadiness model) ↔
      (∀ {context : IncDepRawFiniteContextObject}
        {type : IncDepRawFiniteType context}
        (term : IncDepRawFiniteTerm type), term.SemanticallyCompletable) ∧
      IncDepCompletedCoherentSubstitutionCoverage model := by
  constructor
  · rintro ⟨readiness⟩
    exact ⟨readiness.judgmentCoverage,
      readiness.coherentSubstitutionCoverage⟩
  · rintro ⟨judgments, substitutions⟩
    exact ⟨IncDepCoherentWholeCwFMorphismReadiness.ofGates model
      judgments substitutions⟩

/-- Strengthened readiness implies the previous exact two-gate readiness, so
    existing local CwF comparison theorems remain available without weakening
    the new public coverage standard. -/
noncomputable def IncDepCoherentWholeCwFMorphismReadiness.toBasic
    (model : IncDepCompletionModel.{u, u, u})
    (readiness : IncDepCoherentWholeCwFMorphismReadiness model) :
    IncDepWholeCwFMorphismReadiness.{u} where
  judgmentCoverage := readiness.judgmentCoverage
  substitutionCoverage :=
    IncDepCompletedCoherentSubstitutionCoverage.toBasic model
      readiness.coherentSubstitutionCoverage

structure IncDepCoherentWholeCwFMorphismBoundaryTheorem : Prop where
  basicLocalBoundary : IncDepWholeCwFMorphismBoundaryTheorem.{u}
  coherentIdentityAndProjection : IncDepCoherentSemanticSubstitutionTheorem.{u}
  coherentClosure : IncDepCoherentSemanticSubstitutionClosureTheorem.{u}
  strengthenedBoundary : ∀ (model : IncDepCompletionModel.{u, u, u}),
    Nonempty (IncDepCoherentWholeCwFMorphismReadiness model) ↔
      (∀ {context : IncDepRawFiniteContextObject}
        {type : IncDepRawFiniteType context}
        (term : IncDepRawFiniteTerm type), term.SemanticallyCompletable) ∧
      IncDepCompletedCoherentSubstitutionCoverage model
  forgetfulSound : ∀ (model : IncDepCompletionModel.{u, u, u}),
    IncDepCoherentWholeCwFMorphismReadiness model →
      Nonempty IncDepWholeCwFMorphismReadiness.{u}

theorem incDepCoherentWholeCwFMorphismBoundaryTheorem :
    IncDepCoherentWholeCwFMorphismBoundaryTheorem.{u} where
  basicLocalBoundary := incDepWholeCwFMorphismBoundaryTheorem
  coherentIdentityAndProjection := incDepCoherentSemanticSubstitutionTheorem
  coherentClosure := incDepCoherentSemanticSubstitutionClosureTheorem
  strengthenedBoundary := incDepCoherentWholeCwFMorphismReadiness_iff
  forgetfulSound := fun model readiness => ⟨readiness.toBasic model⟩

end IncidenceCore
