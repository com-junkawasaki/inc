import IncidenceTheory.DependentContextualCategory

namespace IncidenceCore

open CategoryTheory

noncomputable def IncDepRawExtensionalSubstitution.toRaw
    {source target} (substitution : IncDepRawExtensionalSubstitution source target) :
    IncDepRawSubstitution source target where
  term := substitution.term
  preserves lookup := Classical.choice (substitution.preserves lookup)

/-- A well-formed raw type over a well-formed context, with formation evidence
    propositionally truncated so equality depends only on the raw type. -/
structure IncDepRawExtensionalType (context : IncDepRawContextObject) where
  raw : IncDepRawType
  formation : Nonempty (IncDepRawWellFormed context.context raw)

@[ext] theorem IncDepRawExtensionalType.ext
    {context} {first second : IncDepRawExtensionalType context}
    (raw_eq : first.raw = second.raw) : first = second := by
  cases first
  cases second
  cases raw_eq
  congr

noncomputable def IncDepRawExtensionalType.reindex
    {source target : IncDepRawContextObject}
    (type : IncDepRawExtensionalType target) (substitution : source ⟶ target) :
    IncDepRawExtensionalType source where
  raw := type.raw.substitute substitution.term
  formation := by
    rcases type.formation with ⟨formation⟩
    exact ⟨formation.substitute substitution.toRaw⟩

@[simp] theorem IncDepRawExtensionalType.reindex_identity
    {context : IncDepRawContextObject}
    (type : IncDepRawExtensionalType context) :
    type.reindex (𝟙 context) = type := by
  ext
  exact IncDepRawType.substitute_identity type.raw

theorem IncDepRawExtensionalType.reindex_comp
    {first second third : IncDepRawContextObject}
    (type : IncDepRawExtensionalType third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third) :
    type.reindex (firstMap ≫ secondMap) =
      (type.reindex secondMap).reindex firstMap := by
  ext
  exact (IncDepRawType.substitute_comp
    type.raw secondMap.term firstMap.term).symm

/-- The total space of typed terms over a context.  Keeping the type in the
    bundle avoids transports when stating strict substitution laws. -/
structure IncDepRawExtensionalTypedTerm (context : IncDepRawContextObject) where
  type : IncDepRawType
  term : IncDepRawTerm
  formation : Nonempty (IncDepRawWellFormed context.context type)
  typing : Nonempty (IncDepRawHasType context.context term type)

@[ext] theorem IncDepRawExtensionalTypedTerm.ext
    {context} {first second : IncDepRawExtensionalTypedTerm context}
    (type_eq : first.type = second.type) (term_eq : first.term = second.term) :
    first = second := by
  cases first
  cases second
  cases type_eq
  cases term_eq
  congr

def IncDepRawExtensionalTypedTerm.typeObject
    {context} (term : IncDepRawExtensionalTypedTerm context) :
    IncDepRawExtensionalType context where
  raw := term.type
  formation := term.formation

noncomputable def IncDepRawExtensionalTypedTerm.reindex
    {source target : IncDepRawContextObject}
    (typedTerm : IncDepRawExtensionalTypedTerm target)
    (substitution : source ⟶ target) :
    IncDepRawExtensionalTypedTerm source where
  type := typedTerm.type.substitute substitution.term
  term := typedTerm.term.substitute substitution.term
  formation := by
    rcases typedTerm.formation with ⟨formation⟩
    exact ⟨formation.substitute substitution.toRaw⟩
  typing := by
    rcases typedTerm.typing with ⟨typing⟩
    exact ⟨typing.substitute substitution.toRaw⟩

@[simp] theorem IncDepRawExtensionalTypedTerm.reindex_identity
    {context : IncDepRawContextObject}
    (typedTerm : IncDepRawExtensionalTypedTerm context) :
    typedTerm.reindex (𝟙 context) = typedTerm := by
  ext
  · exact IncDepRawType.substitute_identity typedTerm.type
  · exact IncDepRawTerm.substitute_identity typedTerm.term

theorem IncDepRawExtensionalTypedTerm.reindex_comp
    {first second third : IncDepRawContextObject}
    (typedTerm : IncDepRawExtensionalTypedTerm third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third) :
    typedTerm.reindex (firstMap ≫ secondMap) =
      (typedTerm.reindex secondMap).reindex firstMap := by
  ext
  · exact (IncDepRawType.substitute_comp
      typedTerm.type secondMap.term firstMap.term).symm
  · exact (IncDepRawTerm.substitute_comp
      typedTerm.term secondMap.term firstMap.term).symm

theorem IncDepRawExtensionalTypedTerm.typeObject_reindex
    {source target : IncDepRawContextObject}
    (typedTerm : IncDepRawExtensionalTypedTerm target)
    (substitution : source ⟶ target) :
    (typedTerm.reindex substitution).typeObject =
      typedTerm.typeObject.reindex substitution := by
  rfl

/-- A second endomorphism of the empty raw context.  Its unconstrained values
    expose why Nat-indexed substitutions are not yet a genuine CwF base: the
    empty context is not terminal under equality of all Nat components. -/
def incDepRawEmptyJunkSubstitution :
    IncDepRawExtensionalSubstitution [] [] where
  term _ := .unit
  preserves := by
    intro position type lookup
    cases lookup

theorem incDepRawEmpty_identity_ne_junk :
    IncDepRawExtensionalSubstitution.identity [] ≠
      incDepRawEmptyJunkSubstitution := by
  intro equal
  have component := congrArg
    (fun substitution : IncDepRawExtensionalSubstitution [] [] =>
      substitution.term 0) equal
  simp [IncDepRawExtensionalSubstitution.identity,
    IncDepRawSubstitution.toExtensional,
    IncDepRawSubstitution.identity,
    incDepRawEmptyJunkSubstitution] at component

structure IncDepRawTypeTermPresheafTheorem : Prop where
  type_identity : ∀ {context : IncDepRawContextObject}
    (type : IncDepRawExtensionalType context), type.reindex (𝟙 context) = type
  type_composition : ∀ {first second third : IncDepRawContextObject}
    (type : IncDepRawExtensionalType third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third),
    type.reindex (firstMap ≫ secondMap) =
      (type.reindex secondMap).reindex firstMap
  term_identity : ∀ {context : IncDepRawContextObject}
    (term : IncDepRawExtensionalTypedTerm context), term.reindex (𝟙 context) = term
  term_composition : ∀ {first second third : IncDepRawContextObject}
    (term : IncDepRawExtensionalTypedTerm third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third),
    term.reindex (firstMap ≫ secondMap) =
      (term.reindex secondMap).reindex firstMap
  typing_fiber_natural : ∀ {source target : IncDepRawContextObject}
    (term : IncDepRawExtensionalTypedTerm target) (substitution : source ⟶ target),
    (term.reindex substitution).typeObject = term.typeObject.reindex substitution
  terminal_residual : IncDepRawExtensionalSubstitution.identity [] ≠
    incDepRawEmptyJunkSubstitution

theorem incDepRawTypeTermPresheafTheorem :
    IncDepRawTypeTermPresheafTheorem where
  type_identity := IncDepRawExtensionalType.reindex_identity
  type_composition := IncDepRawExtensionalType.reindex_comp
  term_identity := IncDepRawExtensionalTypedTerm.reindex_identity
  term_composition := IncDepRawExtensionalTypedTerm.reindex_comp
  typing_fiber_natural := IncDepRawExtensionalTypedTerm.typeObject_reindex
  terminal_residual := incDepRawEmpty_identity_ne_junk

end IncidenceCore
