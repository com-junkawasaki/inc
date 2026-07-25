import IncidenceTheory.DependentExtensionalContextCategory

namespace IncidenceCore

open CategoryTheory

def IncDepRawFiniteContextObject.toExtensional
    (context : IncDepRawFiniteContextObject) : IncDepRawContextObject where
  context := context.context
  wellFormed := context.wellFormed

abbrev IncDepRawFiniteType (context : IncDepRawFiniteContextObject) :=
  IncDepRawExtensionalType context.toExtensional

abbrev IncDepRawFiniteTypedTerm (context : IncDepRawFiniteContextObject) :=
  IncDepRawExtensionalTypedTerm context.toExtensional

noncomputable def IncDepRawFiniteType.reindexFinite
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target) :
    IncDepRawFiniteType source :=
  Quotient.liftOn substitution
    (fun representative => type.reindex representative)
    (by
      intro first second equivalent
      apply IncDepRawExtensionalType.ext
      rcases type.formation with ⟨formation⟩
      exact formation.substitute_eq_of_context_agreement equivalent)

@[simp] theorem IncDepRawFiniteType.reindexFinite_identity
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) :
    type.reindexFinite (𝟙 context) = type := by
  exact IncDepRawExtensionalType.reindex_identity type

theorem IncDepRawFiniteType.reindexFinite_comp
    {first second third : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third) :
    type.reindexFinite (firstMap ≫ secondMap) =
      (type.reindexFinite secondMap).reindexFinite firstMap := by
  induction firstMap using Quotient.inductionOn with
  | _ firstRepresentative =>
    induction secondMap using Quotient.inductionOn with
    | _ secondRepresentative =>
      apply IncDepRawExtensionalType.ext
      exact (IncDepRawType.substitute_comp type.raw
        secondRepresentative.term firstRepresentative.term).symm

noncomputable def IncDepRawFiniteTypedTerm.reindexFinite
    {source target : IncDepRawFiniteContextObject}
    (typedTerm : IncDepRawFiniteTypedTerm target)
    (substitution : source ⟶ target) :
    IncDepRawFiniteTypedTerm source :=
  Quotient.liftOn substitution
    (fun representative => typedTerm.reindex representative)
    (by
      intro first second equivalent
      apply IncDepRawExtensionalTypedTerm.ext
      · rcases typedTerm.formation with ⟨formation⟩
        exact formation.substitute_eq_of_context_agreement equivalent
      · rcases typedTerm.typing with ⟨typing⟩
        exact typing.substitute_term_eq_of_context_agreement equivalent)

@[simp] theorem IncDepRawFiniteTypedTerm.reindexFinite_identity
    {context : IncDepRawFiniteContextObject}
    (typedTerm : IncDepRawFiniteTypedTerm context) :
    typedTerm.reindexFinite (𝟙 context) = typedTerm := by
  exact IncDepRawExtensionalTypedTerm.reindex_identity typedTerm

theorem IncDepRawFiniteTypedTerm.reindexFinite_comp
    {first second third : IncDepRawFiniteContextObject}
    (typedTerm : IncDepRawFiniteTypedTerm third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third) :
    typedTerm.reindexFinite (firstMap ≫ secondMap) =
      (typedTerm.reindexFinite secondMap).reindexFinite firstMap := by
  induction firstMap using Quotient.inductionOn with
  | _ firstRepresentative =>
    induction secondMap using Quotient.inductionOn with
    | _ secondRepresentative =>
      apply IncDepRawExtensionalTypedTerm.ext
      · exact (IncDepRawType.substitute_comp typedTerm.type
          secondRepresentative.term firstRepresentative.term).symm
      · exact (IncDepRawTerm.substitute_comp typedTerm.term
          secondRepresentative.term firstRepresentative.term).symm

def IncDepRawFiniteTypedTerm.finiteTypeObject
    {context : IncDepRawFiniteContextObject}
    (typedTerm : IncDepRawFiniteTypedTerm context) :
    IncDepRawFiniteType context :=
  typedTerm.typeObject

theorem IncDepRawFiniteTypedTerm.finiteTypeObject_reindexFinite
    {source target : IncDepRawFiniteContextObject}
    (typedTerm : IncDepRawFiniteTypedTerm target)
    (substitution : source ⟶ target) :
    (typedTerm.reindexFinite substitution).finiteTypeObject =
      typedTerm.finiteTypeObject.reindexFinite substitution := by
  induction substitution using Quotient.inductionOn with
  | _ representative =>
      rfl

structure IncDepRawFinitePresheafTheorem : Prop where
  type_well_defined : ∀ {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target)
    {first second : IncDepRawExtensionalSubstitution source.context target.context},
    first.FiniteEquivalent second → type.reindexFinite (Quotient.mk _ first) =
      type.reindexFinite (Quotient.mk _ second)
  type_identity : ∀ {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context), type.reindexFinite (𝟙 context) = type
  type_composition : ∀ {first second third : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third),
    type.reindexFinite (firstMap ≫ secondMap) =
      (type.reindexFinite secondMap).reindexFinite firstMap
  term_identity : ∀ {context : IncDepRawFiniteContextObject}
    (term : IncDepRawFiniteTypedTerm context), term.reindexFinite (𝟙 context) = term
  term_composition : ∀ {first second third : IncDepRawFiniteContextObject}
    (term : IncDepRawFiniteTypedTerm third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third),
    term.reindexFinite (firstMap ≫ secondMap) =
      (term.reindexFinite secondMap).reindexFinite firstMap
  typing_natural : ∀ {source target : IncDepRawFiniteContextObject}
    (term : IncDepRawFiniteTypedTerm target) (substitution : source ⟶ target),
    (term.reindexFinite substitution).finiteTypeObject =
      term.finiteTypeObject.reindexFinite substitution

theorem incDepRawFinitePresheafTheorem : IncDepRawFinitePresheafTheorem where
  type_well_defined := by
    intro source target type first second equivalent
    apply IncDepRawExtensionalType.ext
    rcases type.formation with ⟨formation⟩
    exact formation.substitute_eq_of_context_agreement equivalent
  type_identity := IncDepRawFiniteType.reindexFinite_identity
  type_composition := IncDepRawFiniteType.reindexFinite_comp
  term_identity := IncDepRawFiniteTypedTerm.reindexFinite_identity
  term_composition := IncDepRawFiniteTypedTerm.reindexFinite_comp
  typing_natural := IncDepRawFiniteTypedTerm.finiteTypeObject_reindexFinite

end IncidenceCore
