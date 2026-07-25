import IncidenceTheory.CrossInstance
import IncidenceTheory.RelationalCategoryComparison

namespace IncidenceCore

inductive IncDepJudgmentNode where
  | type : IncDepRawType → IncDepJudgmentNode
  | term : IncDepRawTerm → IncDepJudgmentNode
  deriving DecidableEq, Repr

def dependentJudgmentRelation (context : List IncDepRawType) :
    IncDepJudgmentNode → IncDepJudgmentNode → IncDepJudgmentNode → Prop
  | .type type₁, .type type₂, .type output =>
      type₁ = type₂ ∧ type₂ = output ∧
        Nonempty (IncDepRawWellFormed context type₁)
  | .term term, .type type, .type output =>
      type = output ∧ Nonempty (IncDepRawHasType context term type)
  | _, _, _ => False

def dependentJudgmentSystem (context : List IncDepRawType) :
    TernaryResonanceSystem where
  Carrier := IncDepJudgmentNode
  resonance := dependentJudgmentRelation context

theorem dependentJudgmentRelation_formation_iff
    (context : List IncDepRawType) (type : IncDepRawType) :
    (dependentJudgmentSystem context).resonance
        (.type type) (.type type) (.type type) ↔
      Nonempty (IncDepRawWellFormed context type) := by
  simp [dependentJudgmentSystem, dependentJudgmentRelation]

theorem dependentJudgmentRelation_typing_iff
    (context : List IncDepRawType) (term : IncDepRawTerm)
    (type : IncDepRawType) :
    (dependentJudgmentSystem context).resonance
        (.term term) (.type type) (.type type) ↔
      Nonempty (IncDepRawHasType context term type) := by
  simp [dependentJudgmentSystem, dependentJudgmentRelation]

def IncDepRawRenaming.mapJudgmentNode
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) :
    IncDepJudgmentNode → IncDepJudgmentNode
  | .type type => .type (type.rename renameMap.index)
  | .term term => .term (term.rename renameMap.index)

noncomputable def dependentJudgmentRenamingHom
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) :
    dependentJudgmentSystem source ⟶ dependentJudgmentSystem target where
  toFun := renameMap.mapJudgmentNode
  preserves := by
    intro first second output resonant
    rcases first with type₁ | term <;>
      rcases second with type₂ | term₂ <;>
      rcases output with outputType | outputTerm <;>
      simp only [dependentJudgmentSystem, dependentJudgmentRelation] at resonant ⊢
    · rcases resonant with ⟨rfl, rfl, ⟨formation⟩⟩
      exact ⟨rfl, rfl, ⟨formation.rename renameMap⟩⟩
    · rcases resonant with ⟨rfl, ⟨typing⟩⟩
      exact ⟨rfl, ⟨typing.rename renameMap⟩⟩

def IncDepRawRenaming.comp
    {first second third : List IncDepRawType}
    (later : IncDepRawRenaming second third)
    (earlier : IncDepRawRenaming first second) :
    IncDepRawRenaming first third where
  index := later.index ∘ earlier.index
  preserves := by
    intro position type lookup
    have mapped := later.preserves (earlier.preserves lookup)
    rw [IncDepRawType.rename_comp] at mapped
    exact mapped

@[simp] theorem dependentJudgmentRenamingHom_identity
    (context : List IncDepRawType) :
    dependentJudgmentRenamingHom (IncDepRawRenaming.identity context) =
      TernaryResonanceHom.id (dependentJudgmentSystem context) := by
  apply TernaryResonanceHom.ext
  funext node
  rcases node with type | term
  · simp [dependentJudgmentRenamingHom,
      IncDepRawRenaming.mapJudgmentNode, IncDepRawRenaming.identity,
      IncDepRawType.rename_identity, TernaryResonanceHom.id]
  · simp [dependentJudgmentRenamingHom,
      IncDepRawRenaming.mapJudgmentNode, IncDepRawRenaming.identity,
      IncDepRawTerm.rename_identity, TernaryResonanceHom.id]

@[simp] theorem dependentJudgmentRenamingHom_comp
    {first second third : List IncDepRawType}
    (earlier : IncDepRawRenaming first second)
    (later : IncDepRawRenaming second third) :
    dependentJudgmentRenamingHom (later.comp earlier) =
      (dependentJudgmentRenamingHom later).comp
        (dependentJudgmentRenamingHom earlier) := by
  apply TernaryResonanceHom.ext
  funext node
  rcases node with type | term
  · simp [dependentJudgmentRenamingHom,
      IncDepRawRenaming.mapJudgmentNode, IncDepRawRenaming.comp,
      TernaryResonanceHom.comp, IncDepRawType.rename_comp]
  · simp [dependentJudgmentRenamingHom,
      IncDepRawRenaming.mapJudgmentNode, IncDepRawRenaming.comp,
      TernaryResonanceHom.comp, IncDepRawTerm.rename_comp]

noncomputable def dependentJudgmentIncidence
    (context : List IncDepRawType) :=
  ternaryInteractionIncidence (dependentJudgmentSystem context)

theorem dependentJudgmentIncidence_formation_iff
    (context : List IncDepRawType) (type : IncDepRawType) :
    (dependentJudgmentIncidence context).resonance
        (some (.type type)) (some (.type type)) (some (.type type)) ↔
      Nonempty (IncDepRawWellFormed context type) := by
  unfold dependentJudgmentIncidence
  rw [ternaryInteractionIncidence_resonance_some_iff]
  exact dependentJudgmentRelation_formation_iff context type

theorem dependentJudgmentIncidence_typing_iff
    (context : List IncDepRawType) (term : IncDepRawTerm)
    (type : IncDepRawType) :
    (dependentJudgmentIncidence context).resonance
        (some (.term term)) (some (.type type)) (some (.type type)) ↔
      Nonempty (IncDepRawHasType context term type) := by
  unfold dependentJudgmentIncidence
  rw [ternaryInteractionIncidence_resonance_some_iff]
  exact dependentJudgmentRelation_typing_iff context term type

theorem dependentJudgmentRepresentation_recoverable
    (context : List IncDepRawType) :
    Nonempty (dependentJudgmentSystem context ≅
      nonunitResonanceSystem
        (ternaryInteractionObject (dependentJudgmentSystem context))) :=
  ⟨ternaryInteractionRepresentationIso (dependentJudgmentSystem context)⟩

structure DependentJudgmentRepresentationTheorem
    (context : List IncDepRawType) : Prop where
  formation_exact : ∀ type : IncDepRawType,
    (dependentJudgmentIncidence context).resonance
        (some (.type type)) (some (.type type)) (some (.type type)) ↔
      Nonempty (IncDepRawWellFormed context type)
  typing_exact : ∀ term : IncDepRawTerm, ∀ type : IncDepRawType,
    (dependentJudgmentIncidence context).resonance
        (some (.term term)) (some (.type type)) (some (.type type)) ↔
      Nonempty (IncDepRawHasType context term type)
  recoverable : Nonempty (dependentJudgmentSystem context ≅
    nonunitResonanceSystem
      (ternaryInteractionObject (dependentJudgmentSystem context)))

theorem dependentJudgmentRepresentationTheorem
    (context : List IncDepRawType) :
    DependentJudgmentRepresentationTheorem context where
  formation_exact := dependentJudgmentIncidence_formation_iff context
  typing_exact := dependentJudgmentIncidence_typing_iff context
  recoverable := dependentJudgmentRepresentation_recoverable context

end IncidenceCore
