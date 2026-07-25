import IncidenceTheory.CategoryInteractionRepresentation

namespace IncidenceCore

open CategoryTheory

universe u

def categoryIdentityArrow
    {C : Type u} [Category.{u} C] (object : C) : SmallCategoryArrow C :=
  SmallCategoryArrow.ofHom (𝟙 object)

theorem categoryIdentityArrow_injective
    {C : Type u} [Category.{u} C] :
    Function.Injective (categoryIdentityArrow (C := C)) := by
  intro first second equal
  exact congrArg SmallCategoryArrow.source equal

def CategoryIdentityImage (C : Type u) [Category.{u} C] :=
  { arrow : SmallCategoryArrow C //
    ∃ object : C, categoryIdentityArrow object = arrow }

noncomputable def categoryObjectRecoveryEquiv
    (C : Type u) [Category.{u} C] : C ≃ CategoryIdentityImage C where
  toFun object := ⟨categoryIdentityArrow object, object, rfl⟩
  invFun arrow := Classical.choose arrow.property
  left_inv object := by
    apply categoryIdentityArrow_injective (C := C)
    exact Classical.choose_spec
      (show ∃ source : C,
        categoryIdentityArrow source = categoryIdentityArrow object from
        ⟨object, rfl⟩)
  right_inv arrow := by
    apply Subtype.ext
    exact Classical.choose_spec arrow.property

def CategoryArrowFiber (C : Type u) [Category.{u} C] (X Y : C) :=
  { arrow : SmallCategoryArrow C // arrow.source = X ∧ arrow.target = Y }

def categoryHomFiberEquiv
    (C : Type u) [Category.{u} C] (X Y : C) :
    (X ⟶ Y) ≃ CategoryArrowFiber C X Y where
  toFun hom := ⟨SmallCategoryArrow.ofHom hom, rfl, rfl⟩
  invFun arrow := by
    rcases arrow with ⟨⟨source, target, hom⟩, sourceEq, targetEq⟩
    cases sourceEq
    cases targetEq
    exact hom
  left_inv hom := rfl
  right_inv arrow := by
    rcases arrow with ⟨⟨source, target, hom⟩, sourceEq, targetEq⟩
    cases sourceEq
    cases targetEq
    rfl

@[simp] theorem categoryHomFiberEquiv_apply
    {C : Type u} [Category.{u} C] {X Y : C} (hom : X ⟶ Y) :
    (categoryHomFiberEquiv C X Y hom).val = SmallCategoryArrow.ofHom hom :=
  rfl

theorem categoryHomFiberEquiv_composition_iff
    {C : Type u} [Category.{u} C] {X Y Z : C}
    (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : CategoryArrowFiber C X Z) :
    categoryCompositionRelation
        (categoryHomFiberEquiv C X Y first).val
        (categoryHomFiberEquiv C Y Z second).val output.val ↔
      (categoryHomFiberEquiv C X Z).symm output = first ≫ second := by
  rw [categoryHomFiberEquiv_apply, categoryHomFiberEquiv_apply,
    categoryCompositionRelation_ofHom_iff]
  constructor
  · intro equal
    apply (categoryHomFiberEquiv C X Z).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact equal
  · intro equal
    have mapped := congrArg (categoryHomFiberEquiv C X Z) equal
    rw [Equiv.apply_symm_apply] at mapped
    exact congrArg Subtype.val mapped

theorem categoryInteractionIncidence_recovers_composition
    {C : Type u} [Category.{u} C] {X Y Z : C}
    (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : CategoryArrowFiber C X Z) :
    (categoryInteractionIncidence C).resonance
        (some (categoryHomFiberEquiv C X Y first).val)
        (some (categoryHomFiberEquiv C Y Z second).val)
        (some output.val) ↔
      (categoryHomFiberEquiv C X Z).symm output = first ≫ second := by
  unfold categoryInteractionIncidence
  rw [ternaryInteractionIncidence_resonance_some_iff]
  exact categoryHomFiberEquiv_composition_iff first second output

structure InternalCategoryRecoveryTheorem
    (C : Type u) [Category.{u} C] : Prop where
  objects : Nonempty (C ≃ CategoryIdentityImage C)
  homs : ∀ X Y : C, Nonempty ((X ⟶ Y) ≃ CategoryArrowFiber C X Y)
  composition : ∀ {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : CategoryArrowFiber C X Z),
    (categoryInteractionIncidence C).resonance
        (some (categoryHomFiberEquiv C X Y first).val)
        (some (categoryHomFiberEquiv C Y Z second).val)
        (some output.val) ↔
      (categoryHomFiberEquiv C X Z).symm output = first ≫ second

theorem internalCategoryRecoveryTheorem
    (C : Type u) [Category.{u} C] : InternalCategoryRecoveryTheorem C where
  objects := ⟨categoryObjectRecoveryEquiv C⟩
  homs := fun X Y => ⟨categoryHomFiberEquiv C X Y⟩
  composition := categoryInteractionIncidence_recovers_composition

end IncidenceCore
