import IncidenceTheory.RelationalCategoryFunctoriality
import Mathlib.CategoryTheory.Category.Cat

namespace IncidenceCore

open CategoryTheory

universe u

noncomputable def recognizedReconstructedCat
    (object : RecognizedTernaryCategory.{u}) : Cat.{u, u} :=
  @Cat.of (RelationalCategoryObject object.system) object.axioms.toCategory

noncomputable def relationalCategoryReconstructionFunctor :
    RecognizedTernaryCategory.{u} ⥤ Cat.{u, u} where
  obj := recognizedReconstructedCat
  map := fun hom => hom.reconstructFunctor
  map_id := reconstructFunctor_id
  map_comp := reconstructFunctor_comp

@[simp] theorem relationalCategoryReconstructionFunctor_obj
    (object : RecognizedTernaryCategory.{u}) :
    relationalCategoryReconstructionFunctor.obj object =
      recognizedReconstructedCat object := rfl

@[simp] theorem relationalCategoryReconstructionFunctor_map
    {source target : RecognizedTernaryCategory.{u}}
    (hom : source ⟶ target) :
    relationalCategoryReconstructionFunctor.map hom =
      hom.reconstructFunctor := rfl

theorem relationalCategoryReconstructionFunctor_map_obj
    {source target : RecognizedTernaryCategory.{u}}
    (hom : source ⟶ target)
    (object : RelationalCategoryObject source.system) :
    (relationalCategoryReconstructionFunctor.map hom).obj object =
      hom.mapObject object := rfl

theorem relationalCategoryReconstructionFunctor_map_hom
    {source target : RecognizedTernaryCategory.{u}}
    (hom : source ⟶ target)
    {X Y : RelationalCategoryObject source.system}
    (arrow : RelationalCategoryHom source.system X Y) :
    (relationalCategoryReconstructionFunctor.map hom).map arrow =
      hom.mapHom arrow := rfl

structure CategoryReconstructionFunctorTheorem : Prop where
  packaged_functor : Nonempty
    (RecognizedTernaryCategory.{u} ⥤ Cat.{u, u})
  object_exact : ∀ object : RecognizedTernaryCategory.{u},
    relationalCategoryReconstructionFunctor.obj object =
      recognizedReconstructedCat object
  map_exact : ∀ {source target : RecognizedTernaryCategory.{u}}
      (hom : source ⟶ target),
    relationalCategoryReconstructionFunctor.map hom =
      hom.reconstructFunctor
  encoding_natural : ∀
      {source target : RecognizedTernaryCategory.{u}}
      (hom : source ⟶ target) (arrow : source.system.Carrier),
    target.axioms.encodeArrow (hom.toFun arrow) =
      hom.mapRecognizedArrow (source.axioms.encodeArrow arrow)

theorem categoryReconstructionFunctorTheorem :
    CategoryReconstructionFunctorTheorem.{u} where
  packaged_functor := ⟨relationalCategoryReconstructionFunctor⟩
  object_exact := relationalCategoryReconstructionFunctor_obj
  map_exact := relationalCategoryReconstructionFunctor_map
  encoding_natural := RecognizedTernaryHom.encodeArrow_natural

end IncidenceCore
