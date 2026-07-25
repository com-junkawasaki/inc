import IncidenceTheory.CatRoundTripNaturality

namespace IncidenceCore

open CategoryTheory

universe u

/-! This structure records exactly the comparison level currently proved.
The recognized-system round trip is a natural isomorphism in an ordinary
category.  On the `Cat` side the components are equivalences of categories,
and the chosen forward equivalence functors are natural.  Since equivalence of
categories is weaker than isomorphism in the ordinary 1-category `Cat`, these
fields deliberately do not masquerade as a `CategoryTheory.Equivalence`
between the two model categories. -/
structure RelationalCategoryComparisonData where
  reconstruction : RecognizedTernaryCategory.{u} ⥤ Cat.{u, u}
  recognition : Cat.{u, u} ⥤ RecognizedTernaryCategory.{u}
  recognized_roundTrip :
    𝟭 (RecognizedTernaryCategory.{u}) ≅ reconstruction ⋙ recognition
  category_roundTrip : ∀ C : Cat.{u, u},
    C ≌ RelationalCategoryObject (categoryCompositionSystem C)
  category_roundTrip_functor : ∀ C : Cat.{u, u},
    C ⥤ RelationalCategoryObject (categoryCompositionSystem C)
  category_roundTrip_functor_exact : ∀ C : Cat.{u, u},
    (category_roundTrip C).functor = category_roundTrip_functor C
  category_naturality : ∀ {C D : Cat.{u, u}} (functor : C ⟶ D),
    category_roundTrip_functor C ⋙ categoryRoundTripMappedFunctor functor =
      functor ⋙ category_roundTrip_functor D

noncomputable def relationalCategoryComparisonData :
    RelationalCategoryComparisonData.{u} where
  reconstruction := relationalCategoryReconstructionFunctor
  recognition := categoryRecognitionFunctor
  recognized_roundTrip := recognizedRoundTripNatIso
  category_roundTrip := categoryRoundTripEquivalence
  category_roundTrip_functor := categoryRoundTripFunctor
  category_roundTrip_functor_exact := fun _ => rfl
  category_naturality := categoryRoundTripFunctor_natural

theorem relationalCategoryComparison_recognized_component
    (object : RecognizedTernaryCategory.{u}) :
    (relationalCategoryComparisonData.recognized_roundTrip.hom.app object).toFun =
      object.axioms.encodeArrow := rfl

theorem relationalCategoryComparison_recognized_inverse_component
    (object : RecognizedTernaryCategory.{u}) :
    (relationalCategoryComparisonData.recognized_roundTrip.inv.app object).toFun =
      object.axioms.decodeArrow := rfl

theorem relationalCategoryComparison_category_full
    (C : Cat.{u, u}) :
    (relationalCategoryComparisonData.category_roundTrip_functor C).Full :=
  categoryRoundTripFunctor_full C

theorem relationalCategoryComparison_category_faithful
    (C : Cat.{u, u}) :
    (relationalCategoryComparisonData.category_roundTrip_functor C).Faithful :=
  categoryRoundTripFunctor_faithful C

theorem relationalCategoryComparison_category_essSurj
    (C : Cat.{u, u}) :
    (relationalCategoryComparisonData.category_roundTrip_functor C).EssSurj :=
  categoryRoundTripFunctor_essSurj C

structure RelationalCategoryComparisonTheorem : Prop where
  comparison_data : Nonempty RelationalCategoryComparisonData.{u}
  recognized_natural_iso : Nonempty
    (𝟭 (RecognizedTernaryCategory.{u}) ≅
      relationalCategoryReconstructionFunctor ⋙ categoryRecognitionFunctor)
  cat_objectwise_equivalence : ∀ C : Cat.{u, u}, Nonempty
    (C ≌ RelationalCategoryObject (categoryCompositionSystem C))
  cat_functor_naturality : ∀ {C D : Cat.{u, u}} (functor : C ⟶ D),
    categoryRoundTripFunctor C ⋙ categoryRoundTripMappedFunctor functor =
      functor ⋙ categoryRoundTripFunctor D
  cat_components_full_faithful_essSurj : ∀ C : Cat.{u, u},
    (categoryRoundTripFunctor C).Full ∧
      (categoryRoundTripFunctor C).Faithful ∧
      (categoryRoundTripFunctor C).EssSurj

theorem relationalCategoryComparisonTheorem :
    RelationalCategoryComparisonTheorem.{u} where
  comparison_data := ⟨relationalCategoryComparisonData⟩
  recognized_natural_iso := ⟨recognizedRoundTripNatIso⟩
  cat_objectwise_equivalence := fun C => ⟨categoryRoundTripEquivalence C⟩
  cat_functor_naturality := categoryRoundTripFunctor_natural
  cat_components_full_faithful_essSurj := fun C =>
    ⟨categoryRoundTripFunctor_full C,
      categoryRoundTripFunctor_faithful C,
      categoryRoundTripFunctor_essSurj C⟩

end IncidenceCore
