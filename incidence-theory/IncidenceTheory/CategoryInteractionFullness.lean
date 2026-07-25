import IncidenceTheory.IntrinsicCategoryRecovery

namespace IncidenceCore

open CategoryTheory

universe u

/-! The unrestricted ternary-resonance homomorphisms between category
composition systems need not be induced by functors: preservation of a
partial multiplication alone does not force preservation of endpoints or
identities.  `FunctorialCategoryCompositionHom` gives a non-circular
description of the exact essential image.  Its laws mention only an object
map, maps on the original hom types, the ordinary identity/composition laws,
and agreement with the supplied resonance homomorphism on every arrow. -/
structure FunctorialCategoryCompositionHom
    (C D : Type u) [Category.{u} C] [Category.{u} D] where
  objectMap : C → D
  homMap : ∀ {X Y : C}, (X ⟶ Y) → (objectMap X ⟶ objectMap Y)
  map_id : ∀ X : C, homMap (𝟙 X) = 𝟙 (objectMap X)
  map_comp : ∀ {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z),
    homMap (first ≫ second) = homMap first ≫ homMap second

def FunctorialCategoryCompositionHom.toFunctor
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (hom : FunctorialCategoryCompositionHom C D) : C ⥤ D where
  obj := hom.objectMap
  map := hom.homMap
  map_id := hom.map_id
  map_comp := hom.map_comp

def functorialCategoryCompositionHom
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (functor : C ⥤ D) : FunctorialCategoryCompositionHom C D where
  objectMap := functor.obj
  homMap := functor.map
  map_id := functor.map_id
  map_comp := functor.map_comp

def FunctorialCategoryCompositionHom.resonanceHom
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (hom : FunctorialCategoryCompositionHom C D) :
    categoryCompositionSystem C ⟶ categoryCompositionSystem D :=
  categoryCompositionMap hom.toFunctor

@[simp] theorem functorialCategoryCompositionHom_toFunctor
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (functor : C ⥤ D) :
    (functorialCategoryCompositionHom functor).toFunctor = functor := by
  rfl

theorem FunctorialCategoryCompositionHom.resonanceHom_eq
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (hom : FunctorialCategoryCompositionHom C D) :
    hom.resonanceHom = categoryCompositionMap hom.toFunctor := rfl

theorem categoryCompositionMap_essentialImage_iff
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (resonanceHom : categoryCompositionSystem C ⟶ categoryCompositionSystem D) :
    (∃ functor : C ⥤ D, categoryCompositionMap functor = resonanceHom) ↔
      ∃ hom : FunctorialCategoryCompositionHom C D,
        hom.resonanceHom = resonanceHom := by
  constructor
  · rintro ⟨functor, rfl⟩
    exact ⟨functorialCategoryCompositionHom functor, rfl⟩
  · rintro ⟨hom, rfl⟩
    exact ⟨hom.toFunctor, hom.resonanceHom_eq.symm⟩

theorem categoryCompositionMap_full_on_functorial_homs
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (hom : FunctorialCategoryCompositionHom C D) :
    ∃ functor : C ⥤ D, categoryCompositionMap functor = hom.resonanceHom :=
  ⟨hom.toFunctor, hom.resonanceHom_eq.symm⟩

theorem categoryCompositionMap_faithful
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {first second : C ⥤ D}
    (equal : categoryCompositionMap first = categoryCompositionMap second) :
    first = second := by
  apply CategoryTheory.Functor.hext (fun object => by
    have pointEqual := congrArg
      (fun hom => hom.toFun (categoryIdentityArrow object)) equal
    simpa [categoryCompositionMap, SmallCategoryArrow.map,
      categoryIdentityArrow] using
        congrArg SmallCategoryArrow.source pointEqual) (fun X Y arrow => by
    have pointEqual := congrArg
      (fun hom => hom.toFun (SmallCategoryArrow.ofHom arrow)) equal
    simp only [categoryCompositionMap, SmallCategoryArrow.map,
      SmallCategoryArrow.ofHom] at pointEqual
    injection pointEqual)

theorem categoryCompositionMap_full_and_faithful_on_functorial_homs
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (hom : FunctorialCategoryCompositionHom C D) :
    ∃! functor : C ⥤ D,
      categoryCompositionMap functor = hom.resonanceHom := by
  refine ⟨hom.toFunctor, hom.resonanceHom_eq.symm, ?_⟩
  intro other otherEqual
  exact categoryCompositionMap_faithful
    (otherEqual.trans hom.resonanceHom_eq)

structure CategoryInteractionFullnessTheorem
    (C D : Type u) [Category.{u} C] [Category.{u} D] : Prop where
  full : ∀ hom : FunctorialCategoryCompositionHom C D,
    ∃ functor : C ⥤ D, categoryCompositionMap functor = hom.resonanceHom
  faithful : ∀ first second : C ⥤ D,
    categoryCompositionMap first = categoryCompositionMap second → first = second
  exact_essential_image : ∀
      resonanceHom : categoryCompositionSystem C ⟶ categoryCompositionSystem D,
    (∃ functor : C ⥤ D, categoryCompositionMap functor = resonanceHom) ↔
      ∃ hom : FunctorialCategoryCompositionHom C D,
        hom.resonanceHom = resonanceHom

theorem categoryInteractionFullnessTheorem
    (C D : Type u) [Category.{u} C] [Category.{u} D] :
    CategoryInteractionFullnessTheorem C D where
  full := categoryCompositionMap_full_on_functorial_homs
  faithful := by
    intro first second equal
    exact categoryCompositionMap_faithful equal
  exact_essential_image := categoryCompositionMap_essentialImage_iff

end IncidenceCore
