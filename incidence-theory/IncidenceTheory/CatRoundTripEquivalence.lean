import IncidenceTheory.RecognizedRoundTripNaturalIso

namespace IncidenceCore

open CategoryTheory

universe u

abbrev CategoryRecognizedObject (C : Cat.{u, u}) :=
  RelationalCategoryObject (categoryCompositionSystem C)

noncomputable instance categoryRecognizedObjectCategory (C : Cat.{u, u}) :
    Category.{u} (CategoryRecognizedObject C) :=
  (categoryCompositionSystem_relationalCategoryAxioms C).toCategory

def categoryRoundTripObject (C : Cat.{u, u}) (object : C) :
    CategoryRecognizedObject C :=
  ⟨categoryIdentityArrow object, categoryIdentityArrow_pure object⟩

def categoryRoundTripMap (C : Cat.{u, u}) {X Y : C} (arrow : X ⟶ Y) :
    categoryRoundTripObject C X ⟶ categoryRoundTripObject C Y :=
  ⟨SmallCategoryArrow.ofHom arrow,
    (by simpa [TernarySourceIdentity, TernaryPureIdentity,
        CategoryCompositionPureSourceIdentity,
        CategoryCompositionPureIdentity] using
      (categoryCompositionPureSourceIdentity_iff
        (SmallCategoryArrow.ofHom arrow)
        (categoryIdentityArrow X)).mpr rfl),
    (by simpa [TernaryTargetIdentity, TernaryPureIdentity,
        CategoryCompositionPureTargetIdentity,
        CategoryCompositionPureIdentity] using
      (categoryCompositionPureTargetIdentity_iff
        (SmallCategoryArrow.ofHom arrow)
        (categoryIdentityArrow Y)).mpr rfl)⟩

noncomputable def categoryRoundTripFunctor (C : Cat.{u, u}) :
    C ⥤ CategoryRecognizedObject C := by
  exact
    { obj := categoryRoundTripObject C
      map := categoryRoundTripMap C
      map_id := by
        intro X
        apply Subtype.ext
        rfl
      map_comp := by
        intro X Y Z first second
        apply Subtype.ext
        apply categoryCompositionRelation_functional
        · exact categoryCompositionRelation_ofHom_iff first second
            (SmallCategoryArrow.ofHom (first ≫ second)) |>.mpr rfl
        · exact (categoryCompositionSystem_relationalCategoryAxioms C).composite_resonant
            (categoryRoundTripMap C first) (categoryRoundTripMap C second) }

theorem categoryRoundTripFunctor_obj
    (C : Cat.{u, u}) (object : C) :
    (categoryRoundTripFunctor C).obj object =
      ⟨categoryIdentityArrow object, categoryIdentityArrow_pure object⟩ := rfl

theorem categoryRoundTripFunctor_map_val
    (C : Cat.{u, u}) {X Y : C} (arrow : X ⟶ Y) :
    ((categoryRoundTripFunctor C).map arrow).val =
      SmallCategoryArrow.ofHom arrow := rfl

instance categoryRoundTripFunctor_faithful (C : Cat.{u, u}) :
    (categoryRoundTripFunctor C).Faithful where
  map_injective := by
    intro X Y first second equal
    have valueEqual := congrArg Subtype.val equal
    injection valueEqual

instance categoryRoundTripFunctor_full (C : Cat.{u, u}) :
    (categoryRoundTripFunctor C).Full where
  map_surjective := by
    intro X Y arrow
    have sourceProperty : CategoryCompositionPureSourceIdentity arrow.val
        (categoryIdentityArrow X) := by
      simpa [TernarySourceIdentity, TernaryPureIdentity,
        CategoryCompositionPureSourceIdentity,
        CategoryCompositionPureIdentity] using arrow.property.1
    have targetProperty : CategoryCompositionPureTargetIdentity arrow.val
        (categoryIdentityArrow Y) := by
      simpa [TernaryTargetIdentity, TernaryPureIdentity,
        CategoryCompositionPureTargetIdentity,
        CategoryCompositionPureIdentity] using arrow.property.2
    have sourceIdentity :=
      (categoryCompositionPureSourceIdentity_iff arrow.val
        (categoryIdentityArrow X)).mp sourceProperty
    have targetIdentity :=
      (categoryCompositionPureTargetIdentity_iff arrow.val
        (categoryIdentityArrow Y)).mp targetProperty
    have sourceEq : arrow.val.source = X :=
      (categoryIdentityArrow_injective sourceIdentity).symm
    have targetEq : arrow.val.target = Y :=
      (categoryIdentityArrow_injective targetIdentity).symm
    let fiber : CategoryArrowFiber C X Y :=
      ⟨arrow.val, sourceEq, targetEq⟩
    refine ⟨(categoryHomFiberEquiv C X Y).symm fiber, ?_⟩
    apply Subtype.ext
    have mapped := congrArg Subtype.val
      ((categoryHomFiberEquiv C X Y).apply_symm_apply fiber)
    exact mapped

instance categoryRoundTripFunctor_essSurj (C : Cat.{u, u}) :
    (categoryRoundTripFunctor C).EssSurj :=
  Functor.essSurj_of_surj (by
    intro identity
    refine ⟨identity.val.source, ?_⟩
    apply Subtype.ext
    exact (categoryCompositionPureIdentity_iff identity.val).mp
      identity.property |>.symm)

instance categoryRoundTripFunctor_isEquivalence (C : Cat.{u, u}) :
    (categoryRoundTripFunctor C).IsEquivalence where

noncomputable def categoryRoundTripEquivalence (C : Cat.{u, u}) :
    C ≌ CategoryRecognizedObject C :=
  (categoryRoundTripFunctor C).asEquivalence

structure CatRoundTripEquivalenceTheorem : Prop where
  canonical_functor : ∀ C : Cat.{u, u}, Nonempty
    (C ⥤ CategoryRecognizedObject C)
  faithful : ∀ C : Cat.{u, u},
    (categoryRoundTripFunctor C).Faithful
  full : ∀ C : Cat.{u, u},
    (categoryRoundTripFunctor C).Full
  essentially_surjective : ∀ C : Cat.{u, u},
    (categoryRoundTripFunctor C).EssSurj
  category_equivalence : ∀ C : Cat.{u, u}, Nonempty
    (C ≌ CategoryRecognizedObject C)

theorem catRoundTripEquivalenceTheorem :
    CatRoundTripEquivalenceTheorem.{u} where
  canonical_functor := fun C => ⟨categoryRoundTripFunctor C⟩
  faithful := fun C => categoryRoundTripFunctor_faithful C
  full := fun C => categoryRoundTripFunctor_full C
  essentially_surjective := fun C => categoryRoundTripFunctor_essSurj C
  category_equivalence := fun C => ⟨categoryRoundTripEquivalence C⟩

end IncidenceCore
