import IncidenceTheory.CatRoundTripEquivalence

namespace IncidenceCore

open CategoryTheory

universe u

noncomputable def categoryRoundTripMappedFunctor
    {C D : Cat.{u, u}} (functor : C ⟶ D) :
    CategoryRecognizedObject C ⥤ CategoryRecognizedObject D :=
  (categoryFunctorRecognizedHom functor).reconstructFunctor

theorem categoryRoundTripObject_natural
    {C D : Cat.{u, u}} (functor : C ⟶ D) (object : C) :
    (categoryRoundTripMappedFunctor functor).obj
        ((categoryRoundTripFunctor C).obj object) =
      (categoryRoundTripFunctor D).obj (functor.obj object) := by
  apply Subtype.ext
  simp [categoryRoundTripFunctor, categoryRoundTripObject,
    categoryRoundTripMappedFunctor, categoryFunctorRecognizedHom,
    RecognizedTernaryHom.reconstructFunctor,
    RecognizedTernaryHom.mapObject, SmallCategoryArrow.map,
    categoryIdentityArrow, SmallCategoryArrow.ofHom]

theorem categoryRoundTripFunctor_natural
    {C D : Cat.{u, u}} (functor : C ⟶ D) :
    categoryRoundTripFunctor C ⋙ categoryRoundTripMappedFunctor functor =
      functor ⋙ categoryRoundTripFunctor D := by
  apply CategoryTheory.Functor.hext
    (categoryRoundTripObject_natural functor)
  intro X Y arrow
  apply (Subtype.heq_iff_coe_eq (fun candidate => by
    simp only [Functor.comp_obj]
    rw [categoryRoundTripObject_natural functor X,
      categoryRoundTripObject_natural functor Y])).mpr
  rfl

theorem categoryRoundTripFunctor_natural_obj
    {C D : Cat.{u, u}} (functor : C ⟶ D) (object : C) :
    (categoryRoundTripMappedFunctor functor).obj
        ((categoryRoundTripFunctor C).obj object) =
      (categoryRoundTripFunctor D).obj (functor.obj object) := by
  exact categoryRoundTripObject_natural functor object

theorem categoryRoundTripFunctor_natural_map
    {C D : Cat.{u, u}} (functor : C ⟶ D)
    {X Y : C} (arrow : X ⟶ Y) :
    HEq ((categoryRoundTripMappedFunctor functor).map
        ((categoryRoundTripFunctor C).map arrow))
      ((categoryRoundTripFunctor D).map (functor.map arrow)) := by
  apply (Subtype.heq_iff_coe_eq (fun candidate => by
    rw [categoryRoundTripObject_natural functor X,
      categoryRoundTripObject_natural functor Y])).mpr
  rfl

structure CatRoundTripNaturalityTheorem : Prop where
  mapped_functor : ∀ {C D : Cat.{u, u}} (_functor : C ⟶ D), Nonempty
    (CategoryRecognizedObject C ⥤ CategoryRecognizedObject D)
  natural_square : ∀ {C D : Cat.{u, u}} (functor : C ⟶ D),
    categoryRoundTripFunctor C ⋙ categoryRoundTripMappedFunctor functor =
      functor ⋙ categoryRoundTripFunctor D
  object_exact : ∀ {C D : Cat.{u, u}} (functor : C ⟶ D) (object : C),
    (categoryRoundTripMappedFunctor functor).obj
        ((categoryRoundTripFunctor C).obj object) =
      (categoryRoundTripFunctor D).obj (functor.obj object)
  map_exact : ∀ {C D : Cat.{u, u}} (functor : C ⟶ D)
      {X Y : C} (arrow : X ⟶ Y),
    HEq ((categoryRoundTripMappedFunctor functor).map
        ((categoryRoundTripFunctor C).map arrow))
      ((categoryRoundTripFunctor D).map (functor.map arrow))

theorem catRoundTripNaturalityTheorem :
    CatRoundTripNaturalityTheorem.{u} where
  mapped_functor := fun functor => ⟨categoryRoundTripMappedFunctor functor⟩
  natural_square := categoryRoundTripFunctor_natural
  object_exact := categoryRoundTripFunctor_natural_obj
  map_exact := categoryRoundTripFunctor_natural_map

end IncidenceCore
