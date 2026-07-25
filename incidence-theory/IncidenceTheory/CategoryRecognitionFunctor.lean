import IncidenceTheory.CategoryReconstructionFunctor

namespace IncidenceCore

open CategoryTheory

universe u

def recognizedCategoryOfCat (C : Cat.{u, u}) :
    RecognizedTernaryCategory.{u} where
  system := categoryCompositionSystem C
  axioms := categoryCompositionSystem_relationalCategoryAxioms C

def categoryFunctorRecognizedHom
    {C D : Cat.{u, u}} (functor : C ⟶ D) :
    RecognizedTernaryHom (recognizedCategoryOfCat C)
      (recognizedCategoryOfCat D) where
  toFun := SmallCategoryArrow.map functor
  preserves := (categoryCompositionMap functor).preserves
  maps_pure := by
    intro identity pure
    have identityEqual :=
      (categoryCompositionPureIdentity_iff identity).mp pure
    apply (categoryCompositionPureIdentity_iff _).mpr
    rw [identityEqual]
    simp [SmallCategoryArrow.map, categoryIdentityArrow,
      SmallCategoryArrow.ofHom]

@[simp] theorem categoryFunctorRecognizedHom_id
    (C : Cat.{u, u}) :
    categoryFunctorRecognizedHom (𝟭 C) =
      RecognizedTernaryHom.id (recognizedCategoryOfCat C) := by
  apply RecognizedTernaryHom.ext
  funext arrow
  rcases arrow with ⟨source, target, hom⟩
  simp [categoryFunctorRecognizedHom, SmallCategoryArrow.map,
    RecognizedTernaryHom.id]

@[simp] theorem categoryFunctorRecognizedHom_comp
    {C D E : Cat.{u, u}} (first : C ⟶ D) (second : D ⟶ E) :
    categoryFunctorRecognizedHom (first ≫ second) =
      RecognizedTernaryHom.comp
        (categoryFunctorRecognizedHom second)
        (categoryFunctorRecognizedHom first) := by
  apply RecognizedTernaryHom.ext
  funext arrow
  rcases arrow with ⟨source, target, hom⟩
  simp [categoryFunctorRecognizedHom, SmallCategoryArrow.map,
    RecognizedTernaryHom.comp]

noncomputable def categoryRecognitionFunctor :
    Cat.{u, u} ⥤ RecognizedTernaryCategory.{u} where
  obj := recognizedCategoryOfCat
  map := categoryFunctorRecognizedHom
  map_id := categoryFunctorRecognizedHom_id
  map_comp := categoryFunctorRecognizedHom_comp

@[simp] theorem categoryRecognitionFunctor_obj
    (C : Cat.{u, u}) :
    categoryRecognitionFunctor.obj C = recognizedCategoryOfCat C := rfl

@[simp] theorem categoryRecognitionFunctor_map
    {C D : Cat.{u, u}} (functor : C ⟶ D) :
    categoryRecognitionFunctor.map functor =
      categoryFunctorRecognizedHom functor := rfl

structure CategoryRecognitionFunctorTheorem : Prop where
  packaged_functor : Nonempty
    (Cat.{u, u} ⥤ RecognizedTernaryCategory.{u})
  object_exact : ∀ C : Cat.{u, u},
    categoryRecognitionFunctor.obj C = recognizedCategoryOfCat C
  map_exact : ∀ {C D : Cat.{u, u}} (functor : C ⟶ D),
    categoryRecognitionFunctor.map functor =
      categoryFunctorRecognizedHom functor

theorem categoryRecognitionFunctorTheorem :
    CategoryRecognitionFunctorTheorem.{u} where
  packaged_functor := ⟨categoryRecognitionFunctor⟩
  object_exact := categoryRecognitionFunctor_obj
  map_exact := categoryRecognitionFunctor_map

end IncidenceCore
