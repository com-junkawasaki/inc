import IncidenceTheory.CrossInstance
import Mathlib.CategoryTheory.Category.Basic

namespace IncidenceCore

/-- Well-formed raw contexts, retaining their formation certificate. -/
structure IncDepRawContextObject where
  context : List IncDepRawType
  wellFormed : IncDepRawContext.WellFormed context

/-- Extensional substitutions forget the particular derivation objects in
    `IncDepRawSubstitution` while retaining, propositionally, that every lookup
    is sent to a well-typed term.  This proof erasure is what makes strict
    categorical identity and associativity possible. -/
structure IncDepRawExtensionalSubstitution
    (source target : List IncDepRawType) where
  term : Nat → IncDepRawTerm
  preserves : ∀ {position type}, IncDepRawLookup target position type →
    Nonempty (IncDepRawHasType source (term position) (type.substitute term))

@[ext] theorem IncDepRawExtensionalSubstitution.ext
    {source target} {first second : IncDepRawExtensionalSubstitution source target}
    (term_eq : first.term = second.term) : first = second := by
  cases first with
  | mk firstTerm firstPreserves =>
    cases second with
    | mk secondTerm secondPreserves =>
      cases term_eq
      congr

def IncDepRawSubstitution.toExtensional
    {source target} (substitution : IncDepRawSubstitution source target) :
    IncDepRawExtensionalSubstitution source target where
  term := substitution.term
  preserves lookup := ⟨substitution.preserves lookup⟩

noncomputable def IncDepRawExtensionalSubstitution.identity (context : List IncDepRawType) :
    IncDepRawExtensionalSubstitution context context :=
  (IncDepRawSubstitution.identity context).toExtensional

noncomputable def IncDepRawExtensionalSubstitution.comp
    {first second third : List IncDepRawType}
    (before : IncDepRawExtensionalSubstitution first second)
    (after : IncDepRawExtensionalSubstitution second third) :
    IncDepRawExtensionalSubstitution first third where
  term index := (after.term index).substitute before.term
  preserves := by
    intro position type lookup
    rcases after.preserves lookup with ⟨typing⟩
    rcases before with ⟨beforeTerm, beforePreserves⟩
    let rawBefore : IncDepRawSubstitution first second :=
      { term := beforeTerm
        preserves := fun lookup => Classical.choice (beforePreserves lookup) }
    have substituted := typing.substitute rawBefore
    rw [IncDepRawType.substitute_comp] at substituted
    exact ⟨substituted⟩

@[simp] theorem IncDepRawExtensionalSubstitution.identity_comp
    {source target} (substitution : IncDepRawExtensionalSubstitution source target) :
    (IncDepRawExtensionalSubstitution.identity source).comp substitution =
      substitution := by
  ext
  exact IncDepRawTerm.substitute_identity _

@[simp] theorem IncDepRawExtensionalSubstitution.comp_identity
    {source target} (substitution : IncDepRawExtensionalSubstitution source target) :
    substitution.comp (IncDepRawExtensionalSubstitution.identity target) =
      substitution := by
  ext
  rfl

@[simp] theorem IncDepRawExtensionalSubstitution.comp_assoc
    {first second third fourth}
    (firstMap : IncDepRawExtensionalSubstitution first second)
    (secondMap : IncDepRawExtensionalSubstitution second third)
    (thirdMap : IncDepRawExtensionalSubstitution third fourth) :
    (firstMap.comp secondMap).comp thirdMap =
      firstMap.comp (secondMap.comp thirdMap) := by
  ext
  exact (IncDepRawTerm.substitute_comp
    (thirdMap.term _) secondMap.term firstMap.term).symm

noncomputable instance : CategoryTheory.Category IncDepRawContextObject where
  Hom source target :=
    IncDepRawExtensionalSubstitution source.context target.context
  id object := IncDepRawExtensionalSubstitution.identity object.context
  comp before after := before.comp after
  id_comp := IncDepRawExtensionalSubstitution.identity_comp
  comp_id := IncDepRawExtensionalSubstitution.comp_identity
  assoc := IncDepRawExtensionalSubstitution.comp_assoc

/-- Reindex a raw type along an extensional substitution. -/
def IncDepRawExtensionalSubstitution.reindexType
    {source target} (substitution : IncDepRawExtensionalSubstitution source target)
    (type : IncDepRawType) : IncDepRawType :=
  type.substitute substitution.term

@[simp] theorem IncDepRawExtensionalSubstitution.reindexType_identity
    (context) (type : IncDepRawType) :
    (IncDepRawExtensionalSubstitution.identity context).reindexType type = type :=
  IncDepRawType.substitute_identity type

theorem IncDepRawExtensionalSubstitution.reindexType_comp
    {first second third}
    (firstMap : IncDepRawExtensionalSubstitution first second)
    (secondMap : IncDepRawExtensionalSubstitution second third)
    (type : IncDepRawType) :
    (firstMap.comp secondMap).reindexType type =
      firstMap.reindexType (secondMap.reindexType type) := by
  exact (IncDepRawType.substitute_comp type secondMap.term firstMap.term).symm

def IncDepRawContextObject.extend
    (context : IncDepRawContextObject)
    {type : IncDepRawType}
    (formation : IncDepRawWellFormed context.context type) :
    IncDepRawContextObject where
  context := type :: context.context
  wellFormed := .extend context.wellFormed formation

/-- The display map from a context extension to its base context. -/
noncomputable def IncDepRawExtensionalSubstitution.projection
    (context : List IncDepRawType) (type : IncDepRawType) :
    IncDepRawExtensionalSubstitution (type :: context) context where
  term index := .var (index + 1)
  preserves := by
    intro position lookupType lookup
    have typing : IncDepRawHasType (type :: context) (.var (position + 1))
        (lookupType.rename Nat.succ) :=
      .varRule (.there lookup)
    have typeEq : lookupType.substitute (fun index => .var (index + 1)) =
        lookupType.rename Nat.succ := by
      have mapEq : (fun index => IncDepRawTerm.var (index + 1)) =
          IncDepRawTerm.var ∘ Nat.succ := by
        funext index
        rfl
      rw [mapEq]
      rw [← IncDepRawType.rename_substitute lookupType Nat.succ IncDepRawTerm.var,
        IncDepRawType.substitute_identity]
    rw [typeEq]
    exact ⟨typing⟩

/-- The generic variable of a context extension. -/
def incDepRawContextGenericVariable
    (context : List IncDepRawType) (type : IncDepRawType) :
    IncDepRawHasType (type :: context) (.var 0) (type.rename Nat.succ) :=
  .varRule .here

/-- Pair a substitution into the base context with a term of the reindexed
    display type.  This is the comprehension pairing operation. -/
noncomputable def IncDepRawExtensionalSubstitution.extendPair
    {source target : List IncDepRawType}
    (substitution : IncDepRawExtensionalSubstitution source target)
    (type : IncDepRawType) (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source term
      (type.substitute substitution.term))) :
    IncDepRawExtensionalSubstitution source (type :: target) where
  term index := match index with
    | 0 => term
    | next + 1 => substitution.term next
  preserves := by
    intro position lookupType lookup
    cases lookup with
    | here =>
        have typeEq :
            (type.rename Nat.succ).substitute (fun index => match index with
              | 0 => term
              | next + 1 => substitution.term next) =
              type.substitute substitution.term := by
          rw [IncDepRawType.rename_substitute]
          congr 1
        rw [typeEq]
        exact typing
    | there previous =>
        rcases substitution.preserves previous with ⟨previousTyping⟩
        simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
          (show Nonempty _ from ⟨previousTyping⟩)

@[simp] theorem IncDepRawExtensionalSubstitution.extendPair_projection
    {source target} (substitution : IncDepRawExtensionalSubstitution source target)
    (type : IncDepRawType) (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source term
      (type.substitute substitution.term))) :
    (substitution.extendPair type term typing).comp
        (IncDepRawExtensionalSubstitution.projection target type) = substitution := by
  ext
  rfl

@[simp] theorem IncDepRawExtensionalSubstitution.extendPair_generic
    {source target} (substitution : IncDepRawExtensionalSubstitution source target)
    (type : IncDepRawType) (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source term
      (type.substitute substitution.term))) :
    (IncDepRawTerm.var 0).substitute
      (substitution.extendPair type term typing).term = term := by
  rfl

/-- The comprehension pairing is the unique substitution with the prescribed
    projection and generic component. -/
theorem IncDepRawExtensionalSubstitution.extendPair_unique
    {source target} (substitution : IncDepRawExtensionalSubstitution source target)
    (type : IncDepRawType) (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source term
      (type.substitute substitution.term)))
    (candidate : IncDepRawExtensionalSubstitution source (type :: target))
    (projection_eq : candidate.comp
      (IncDepRawExtensionalSubstitution.projection target type) = substitution)
    (generic_eq : candidate.term 0 = term) :
    candidate = substitution.extendPair type term typing := by
  ext position
  cases position with
  | zero => exact generic_eq
  | succ position =>
      have componentEq := congrArg
        (fun map : IncDepRawExtensionalSubstitution source target => map.term position)
        projection_eq
      exact componentEq

structure IncDepRawContextualCategoryTheorem : Prop where
  identity_left : ∀ {source target}
    (substitution : IncDepRawExtensionalSubstitution source target),
    (IncDepRawExtensionalSubstitution.identity source).comp substitution = substitution
  identity_right : ∀ {source target}
    (substitution : IncDepRawExtensionalSubstitution source target),
    substitution.comp (IncDepRawExtensionalSubstitution.identity target) = substitution
  associative : ∀ {first second third fourth}
    (firstMap : IncDepRawExtensionalSubstitution first second)
    (secondMap : IncDepRawExtensionalSubstitution second third)
    (thirdMap : IncDepRawExtensionalSubstitution third fourth),
    (firstMap.comp secondMap).comp thirdMap = firstMap.comp (secondMap.comp thirdMap)
  reindex_identity : ∀ context type,
    (IncDepRawExtensionalSubstitution.identity context).reindexType type = type
  reindex_composition : ∀ {first second third}
    (firstMap : IncDepRawExtensionalSubstitution first second)
    (secondMap : IncDepRawExtensionalSubstitution second third) type,
    (firstMap.comp secondMap).reindexType type =
      firstMap.reindexType (secondMap.reindexType type)
  display_and_generic : ∀ context type,
    Nonempty (IncDepRawExtensionalSubstitution (type :: context) context) ∧
      Nonempty (IncDepRawHasType (type :: context) (.var 0) (type.rename Nat.succ))
  comprehension : ∀ {source target}
    (substitution : IncDepRawExtensionalSubstitution source target)
    (type : IncDepRawType) (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source term
      (type.substitute substitution.term))),
    let paired := substitution.extendPair type term typing
    paired.comp (IncDepRawExtensionalSubstitution.projection target type) = substitution ∧
      (IncDepRawTerm.var 0).substitute paired.term = term ∧
      ∀ candidate : IncDepRawExtensionalSubstitution source (type :: target),
        candidate.comp (IncDepRawExtensionalSubstitution.projection target type) =
            substitution → candidate.term 0 = term → candidate = paired

theorem incDepRawContextualCategoryTheorem :
    IncDepRawContextualCategoryTheorem where
  identity_left := IncDepRawExtensionalSubstitution.identity_comp
  identity_right := IncDepRawExtensionalSubstitution.comp_identity
  associative := IncDepRawExtensionalSubstitution.comp_assoc
  reindex_identity := IncDepRawExtensionalSubstitution.reindexType_identity
  reindex_composition := IncDepRawExtensionalSubstitution.reindexType_comp
  display_and_generic := fun context type =>
    ⟨⟨IncDepRawExtensionalSubstitution.projection context type⟩,
      ⟨incDepRawContextGenericVariable context type⟩⟩
  comprehension := by
    intro source target substitution type term typing
    exact ⟨substitution.extendPair_projection type term typing,
      substitution.extendPair_generic type term typing,
      fun candidate projectionEq genericEq =>
        substitution.extendPair_unique type term typing candidate projectionEq genericEq⟩

end IncidenceCore
