import IncidenceTheory.DependentJudgmentRepresentation

namespace IncidenceCore

/-- A proof-theoretic model of the dependent raw judgments.  It deliberately
    asks only for closure under the raw inference rules; no extensional or
    set-valued interpretation is hidden in this interface. -/
structure IncDepJudgmentModel where
  formation : List IncDepRawType → IncDepRawType → Prop
  typing : List IncDepRawType → IncDepRawTerm → IncDepRawType → Prop
  base : ∀ {context index}, formation context (.base index)
  unitFormation : ∀ {context}, formation context .unit
  pi : ∀ {context domain codomain}, formation context domain →
    formation (domain :: context) codomain → formation context (.pi domain codomain)
  sigma : ∀ {context domain codomain}, formation context domain →
    formation (domain :: context) codomain → formation context (.sigma domain codomain)
  identity : ∀ {context type left right}, formation context type →
    typing context left type → typing context right type →
    formation context (.identity type left right)
  varRule : ∀ {context index type}, IncDepRawLookup context index type →
    typing context (.var index) type
  unitRule : ∀ {context}, typing context .unit .unit
  lambdaRule : ∀ {context domain codomain body}, formation context domain →
    typing (domain :: context) body codomain →
    typing context (.lambda domain body) (.pi domain codomain)
  applyRule : ∀ {context domain codomain function argument},
    typing context function (.pi domain codomain) → typing context argument domain →
    typing context (.apply function argument) (codomain.instantiate argument)
  pairRule : ∀ {context domain codomain first second},
    typing context first domain → typing context second (codomain.instantiate first) →
    typing context (.pair first second) (.sigma domain codomain)
  firstRule : ∀ {context domain codomain pair},
    typing context pair (.sigma domain codomain) → typing context (.first pair) domain
  secondRule : ∀ {context domain codomain pair},
    typing context pair (.sigma domain codomain) →
    typing context (.second pair) (codomain.instantiate (.first pair))
  reflRule : ∀ {context type term}, typing context term type →
    typing context (.refl term) (.identity type term term)

mutual
  noncomputable def IncDepRawWellFormed.sound
      (model : IncDepJudgmentModel) {context type}
      (derivation : IncDepRawWellFormed context type) :
      model.formation context type := by
    cases derivation with
    | base => exact model.base
    | unit => exact model.unitFormation
    | pi domain codomain =>
        exact model.pi (domain.sound model) (codomain.sound model)
    | sigma domain codomain =>
        exact model.sigma (domain.sound model) (codomain.sound model)
    | identity formation left right =>
        exact model.identity (formation.sound model) (left.sound model) (right.sound model)

  noncomputable def IncDepRawHasType.sound
      (model : IncDepJudgmentModel) {context term type}
      (derivation : IncDepRawHasType context term type) :
      model.typing context term type := by
    cases derivation with
    | varRule lookup => exact model.varRule lookup
    | unitRule => exact model.unitRule
    | lambdaRule formation body =>
        exact model.lambdaRule (formation.sound model) (body.sound model)
    | applyRule function argument =>
        exact model.applyRule (function.sound model) (argument.sound model)
    | pairRule first second =>
        exact model.pairRule (first.sound model) (second.sound model)
    | firstRule pair => exact model.firstRule (pair.sound model)
    | secondRule pair => exact model.secondRule (pair.sound model)
    | reflRule term => exact model.reflRule (term.sound model)
end

/-- The term model: its valid judgments are exactly the derivable judgments. -/
def syntacticIncDepJudgmentModel : IncDepJudgmentModel where
  formation context type := Nonempty (IncDepRawWellFormed context type)
  typing context term type := Nonempty (IncDepRawHasType context term type)
  base := ⟨.base⟩
  unitFormation := ⟨.unit⟩
  pi := fun ⟨domain⟩ ⟨codomain⟩ => ⟨.pi domain codomain⟩
  sigma := fun ⟨domain⟩ ⟨codomain⟩ => ⟨.sigma domain codomain⟩
  identity := fun ⟨formation⟩ ⟨left⟩ ⟨right⟩ =>
    ⟨.identity formation left right⟩
  varRule lookup := ⟨.varRule lookup⟩
  unitRule := ⟨.unitRule⟩
  lambdaRule := fun ⟨formation⟩ ⟨body⟩ => ⟨.lambdaRule formation body⟩
  applyRule := fun ⟨function⟩ ⟨argument⟩ => ⟨.applyRule function argument⟩
  pairRule := fun ⟨first⟩ ⟨second⟩ => ⟨.pairRule first second⟩
  firstRule := fun ⟨pair⟩ => ⟨.firstRule pair⟩
  secondRule := fun ⟨pair⟩ => ⟨.secondRule pair⟩
  reflRule := fun ⟨term⟩ => ⟨.reflRule term⟩

theorem dependentJudgmentSoundness (model : IncDepJudgmentModel) :
    (∀ {context type}, Nonempty (IncDepRawWellFormed context type) →
      model.formation context type) ∧
    (∀ {context term type}, Nonempty (IncDepRawHasType context term type) →
      model.typing context term type) := by
  constructor
  · rintro context type ⟨derivation⟩
    exact derivation.sound model
  · rintro context term type ⟨derivation⟩
    exact derivation.sound model

theorem syntacticIncDepJudgmentModel_exact :
    (∀ context type, syntacticIncDepJudgmentModel.formation context type ↔
      Nonempty (IncDepRawWellFormed context type)) ∧
    (∀ context term type, syntacticIncDepJudgmentModel.typing context term type ↔
      Nonempty (IncDepRawHasType context term type)) := by
  exact ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

/-- Initiality at the level of judgment predicates: the term model is
    contained in every model closed under the inference rules. -/
theorem syntacticIncDepJudgmentModel_least (model : IncDepJudgmentModel) :
    (∀ {context type}, syntacticIncDepJudgmentModel.formation context type →
      model.formation context type) ∧
    (∀ {context term type}, syntacticIncDepJudgmentModel.typing context term type →
      model.typing context term type) :=
  dependentJudgmentSoundness model

theorem syntacticFormation_rename
    {source target type} (renameMap : IncDepRawRenaming source target) :
    syntacticIncDepJudgmentModel.formation source type →
      syntacticIncDepJudgmentModel.formation target (type.rename renameMap.index) := by
  rintro ⟨derivation⟩
  exact ⟨derivation.rename renameMap⟩

theorem syntacticTyping_rename
    {source target term type} (renameMap : IncDepRawRenaming source target) :
    syntacticIncDepJudgmentModel.typing source term type →
      syntacticIncDepJudgmentModel.typing target (term.rename renameMap.index)
        (type.rename renameMap.index) := by
  rintro ⟨derivation⟩
  exact ⟨derivation.rename renameMap⟩

theorem syntacticFormation_substitute
    {source target type} (substitution : IncDepRawSubstitution source target) :
    syntacticIncDepJudgmentModel.formation target type →
      syntacticIncDepJudgmentModel.formation source
        (type.substitute substitution.term) := by
  rintro ⟨derivation⟩
  exact ⟨derivation.substitute substitution⟩

theorem syntacticTyping_substitute
    {source target term type} (substitution : IncDepRawSubstitution source target) :
    syntacticIncDepJudgmentModel.typing target term type →
      syntacticIncDepJudgmentModel.typing source
        (term.substitute substitution.term) (type.substitute substitution.term) := by
  rintro ⟨derivation⟩
  exact ⟨derivation.substitute substitution⟩

structure DependentJudgmentSoundnessCompletenessTheorem : Prop where
  sound : ∀ model : IncDepJudgmentModel,
    (∀ {context type}, Nonempty (IncDepRawWellFormed context type) →
      model.formation context type) ∧
    (∀ {context term type}, Nonempty (IncDepRawHasType context term type) →
      model.typing context term type)
  complete :
    (∀ context type, syntacticIncDepJudgmentModel.formation context type ↔
      Nonempty (IncDepRawWellFormed context type)) ∧
    (∀ context term type, syntacticIncDepJudgmentModel.typing context term type ↔
      Nonempty (IncDepRawHasType context term type))
  least : ∀ model : IncDepJudgmentModel,
    (∀ {context type}, syntacticIncDepJudgmentModel.formation context type →
      model.formation context type) ∧
    (∀ {context term type}, syntacticIncDepJudgmentModel.typing context term type →
      model.typing context term type)

theorem dependentJudgmentSoundnessCompletenessTheorem :
    DependentJudgmentSoundnessCompletenessTheorem where
  sound := dependentJudgmentSoundness
  complete := syntacticIncDepJudgmentModel_exact
  least := syntacticIncDepJudgmentModel_least

end IncidenceCore
