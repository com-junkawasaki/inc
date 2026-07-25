import IncidenceTheory.DependentScopedSyntax

namespace IncidenceCore

open CategoryTheory

theorem IncDepRawLookup.exists_of_lt
    {context : List IncDepRawType} {position : Nat}
    (positionLt : position < context.length) :
    ∃ type, Nonempty (IncDepRawLookup context position type) := by
  induction context generalizing position with
  | nil => simp at positionLt
  | cons head tail ih =>
      cases position with
      | zero => exact ⟨head.rename Nat.succ, ⟨.here⟩⟩
      | succ position =>
          have tailLt : position < tail.length := by simpa using positionLt
          rcases ih tailLt with ⟨type, ⟨lookup⟩⟩
          exact ⟨type.rename Nat.succ, ⟨.there lookup⟩⟩

def IncDepRawExtensionalSubstitution.FiniteEquivalent
    {source target : List IncDepRawType}
    (first second : IncDepRawExtensionalSubstitution source target) : Prop :=
  ∀ index, index < target.length → first.term index = second.term index

theorem IncDepRawExtensionalSubstitution.finiteEquivalent_refl
    {source target} (substitution : IncDepRawExtensionalSubstitution source target) :
    substitution.FiniteEquivalent substitution := fun _ _ => rfl

theorem IncDepRawExtensionalSubstitution.finiteEquivalent_symm
    {source target} {first second : IncDepRawExtensionalSubstitution source target}
    (equivalent : first.FiniteEquivalent second) : second.FiniteEquivalent first :=
  fun index indexLt => (equivalent index indexLt).symm

theorem IncDepRawExtensionalSubstitution.finiteEquivalent_trans
    {source target}
    {first second third : IncDepRawExtensionalSubstitution source target}
    (firstSecond : first.FiniteEquivalent second)
    (secondThird : second.FiniteEquivalent third) :
    first.FiniteEquivalent third :=
  fun index indexLt => (firstSecond index indexLt).trans (secondThird index indexLt)

def incDepRawFiniteSubstitutionSetoid (source target : List IncDepRawType) :
    Setoid (IncDepRawExtensionalSubstitution source target) where
  r := IncDepRawExtensionalSubstitution.FiniteEquivalent
  iseqv := ⟨IncDepRawExtensionalSubstitution.finiteEquivalent_refl,
    IncDepRawExtensionalSubstitution.finiteEquivalent_symm,
    IncDepRawExtensionalSubstitution.finiteEquivalent_trans⟩

abbrev IncDepRawFiniteSubstitution (source target : List IncDepRawType) :=
  Quotient (incDepRawFiniteSubstitutionSetoid source target)

theorem IncDepRawExtensionalSubstitution.comp_finiteEquivalent
    {first second third : List IncDepRawType}
    {before₁ before₂ : IncDepRawExtensionalSubstitution first second}
    {after₁ after₂ : IncDepRawExtensionalSubstitution second third}
    (beforeEq : before₁.FiniteEquivalent before₂)
    (afterEq : after₁.FiniteEquivalent after₂) :
    (before₁.comp after₁).FiniteEquivalent (before₂.comp after₂) := by
  intro index indexLt
  have afterComponent := afterEq index indexLt
  rw [show (before₁.comp after₁).term index =
      (after₁.term index).substitute before₁.term from rfl]
  rw [show (before₂.comp after₂).term index =
      (after₂.term index).substitute before₂.term from rfl]
  rw [afterComponent]
  rcases IncDepRawLookup.exists_of_lt indexLt with ⟨type, ⟨lookup⟩⟩
  rcases after₂.preserves lookup with ⟨typing⟩
  exact typing.substitute_term_eq_of_context_agreement beforeEq

noncomputable def IncDepRawFiniteSubstitution.identity
    (context : List IncDepRawType) : IncDepRawFiniteSubstitution context context :=
  Quotient.mk _ (IncDepRawExtensionalSubstitution.identity context)

noncomputable def IncDepRawFiniteSubstitution.comp
    {first second third : List IncDepRawType}
    (before : IncDepRawFiniteSubstitution first second)
    (after : IncDepRawFiniteSubstitution second third) :
    IncDepRawFiniteSubstitution first third :=
  Quotient.liftOn₂ before after
    (fun before after => Quotient.mk _ (before.comp after))
    (by
      intro before₁ after₁ before₂ after₂ beforeEq afterEq
      exact Quotient.sound
        (IncDepRawExtensionalSubstitution.comp_finiteEquivalent beforeEq afterEq))

@[simp] theorem IncDepRawFiniteSubstitution.identity_comp
    {source target} (substitution : IncDepRawFiniteSubstitution source target) :
    (IncDepRawFiniteSubstitution.identity source).comp substitution = substitution := by
  induction substitution using Quotient.inductionOn with
  | _ substitution =>
      exact congrArg (Quotient.mk _)
        (IncDepRawExtensionalSubstitution.identity_comp substitution)

@[simp] theorem IncDepRawFiniteSubstitution.comp_identity
    {source target} (substitution : IncDepRawFiniteSubstitution source target) :
    substitution.comp (IncDepRawFiniteSubstitution.identity target) = substitution := by
  induction substitution using Quotient.inductionOn with
  | _ substitution =>
      exact congrArg (Quotient.mk _)
        (IncDepRawExtensionalSubstitution.comp_identity substitution)

@[simp] theorem IncDepRawFiniteSubstitution.comp_assoc
    {first second third fourth}
    (firstMap : IncDepRawFiniteSubstitution first second)
    (secondMap : IncDepRawFiniteSubstitution second third)
    (thirdMap : IncDepRawFiniteSubstitution third fourth) :
    (firstMap.comp secondMap).comp thirdMap =
      firstMap.comp (secondMap.comp thirdMap) := by
  induction firstMap using Quotient.inductionOn with
  | _ firstMap =>
    induction secondMap using Quotient.inductionOn with
    | _ secondMap =>
      induction thirdMap using Quotient.inductionOn with
      | _ thirdMap =>
        exact congrArg (Quotient.mk _)
          (IncDepRawExtensionalSubstitution.comp_assoc firstMap secondMap thirdMap)

/-- The corrected context category: morphisms identify substitutions that
    agree on every variable actually present in the finite target context. -/
structure IncDepRawFiniteContextObject where
  context : List IncDepRawType
  wellFormed : IncDepRawContext.WellFormed context

noncomputable instance : Category IncDepRawFiniteContextObject where
  Hom source target := IncDepRawFiniteSubstitution source.context target.context
  id object := IncDepRawFiniteSubstitution.identity object.context
  comp before after := before.comp after
  id_comp := IncDepRawFiniteSubstitution.identity_comp
  comp_id := IncDepRawFiniteSubstitution.comp_identity
  assoc := IncDepRawFiniteSubstitution.comp_assoc

def incDepRawFiniteEmptyContext : IncDepRawFiniteContextObject where
  context := []
  wellFormed := .empty

def incDepRawEmptyTargetSubstitution (source : List IncDepRawType) :
    IncDepRawExtensionalSubstitution source [] where
  term _ := .unit
  preserves := by
    intro position type lookup
    cases lookup

noncomputable def incDepRawFiniteEmptyMap
    (source : IncDepRawFiniteContextObject) :
    source ⟶ incDepRawFiniteEmptyContext :=
  Quotient.mk _ (incDepRawEmptyTargetSubstitution source.context)

theorem incDepRawFiniteEmptyMap_unique
    (source : IncDepRawFiniteContextObject)
    (map : source ⟶ incDepRawFiniteEmptyContext) :
    map = incDepRawFiniteEmptyMap source := by
  induction map using Quotient.inductionOn with
  | _ representative =>
      apply Quotient.sound
      intro index indexLt
      change index < ([] : List IncDepRawType).length at indexLt
      simp at indexLt

theorem incDepRawFiniteEmpty_terminal
    (source : IncDepRawFiniteContextObject) :
    ∃! map : source ⟶ incDepRawFiniteEmptyContext, map = map := by
  exact ⟨incDepRawFiniteEmptyMap source, rfl,
    fun map _ => incDepRawFiniteEmptyMap_unique source map⟩

structure IncDepRawFiniteContextCategoryTheorem : Prop where
  composition_well_defined : ∀ {first second third}
    {before₁ before₂ : IncDepRawExtensionalSubstitution first second}
    {after₁ after₂ : IncDepRawExtensionalSubstitution second third},
    before₁.FiniteEquivalent before₂ → after₁.FiniteEquivalent after₂ →
      (before₁.comp after₁).FiniteEquivalent (before₂.comp after₂)
  terminal : ∀ source : IncDepRawFiniteContextObject,
    ∃! map : source ⟶ incDepRawFiniteEmptyContext, map = map

theorem incDepRawFiniteContextCategoryTheorem :
    IncDepRawFiniteContextCategoryTheorem where
  composition_well_defined :=
    IncDepRawExtensionalSubstitution.comp_finiteEquivalent
  terminal := incDepRawFiniteEmpty_terminal

end IncidenceCore
