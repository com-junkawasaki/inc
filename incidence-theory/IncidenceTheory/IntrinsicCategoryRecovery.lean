import IncidenceTheory.InternalCategoryRecovery

namespace IncidenceCore

open CategoryTheory

universe u

/-! This predicate uses only endpoint projections and the ternary composition
relation.  No preselected set of identity arrows occurs in its definition. -/
def CategoryCompositionIntrinsicIdentity
    {C : Type u} [Category.{u} C] (identity : SmallCategoryArrow C) : Prop :=
  identity.source = identity.target ∧
  (∀ arrow : SmallCategoryArrow C,
    identity.target = arrow.source →
      categoryCompositionRelation identity arrow arrow) ∧
  (∀ arrow : SmallCategoryArrow C,
    arrow.target = identity.source →
      categoryCompositionRelation arrow identity arrow)

theorem categoryIdentityArrow_intrinsic
    {C : Type u} [Category.{u} C] (object : C) :
    CategoryCompositionIntrinsicIdentity (categoryIdentityArrow object) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro arrow compatible
    rcases arrow with ⟨source, target, hom⟩
    cases compatible
    exact (categoryCompositionRelation_ofHom_iff (𝟙 object) hom
      (SmallCategoryArrow.ofHom hom)).mpr (by simp [SmallCategoryArrow.ofHom])
  · intro arrow compatible
    rcases arrow with ⟨source, target, hom⟩
    cases compatible
    exact (categoryCompositionRelation_ofHom_iff hom (𝟙 object)
      (SmallCategoryArrow.ofHom hom)).mpr (by simp [SmallCategoryArrow.ofHom])

theorem categoryCompositionIntrinsicIdentity_eq_identity
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C)
    (intrinsic : CategoryCompositionIntrinsicIdentity arrow) :
    arrow = categoryIdentityArrow arrow.source := by
  rcases arrow with ⟨source, target, hom⟩
  rcases intrinsic with ⟨loop, leftIdentity, rightIdentity⟩
  cases loop
  have resonant := leftIdentity (categoryIdentityArrow source) rfl
  have outputEq := (categoryCompositionRelation_ofHom_iff hom (𝟙 source)
    (categoryIdentityArrow source)).mp resonant
  have homEq : hom = 𝟙 source := by
    have componentEq : 𝟙 source = hom ≫ 𝟙 source := by
      injection outputEq
    simpa using componentEq.symm
  cases homEq
  rfl

theorem categoryCompositionIntrinsicIdentity_iff
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryCompositionIntrinsicIdentity arrow ↔
      arrow = categoryIdentityArrow arrow.source := by
  constructor
  · exact categoryCompositionIntrinsicIdentity_eq_identity arrow
  · intro equal
    have intrinsic := categoryIdentityArrow_intrinsic arrow.source
    rw [← equal] at intrinsic
    exact intrinsic

def CategoryIntrinsicIdentityImage (C : Type u) [Category.{u} C] :=
  { arrow : SmallCategoryArrow C // CategoryCompositionIntrinsicIdentity arrow }

def intrinsicCategoryObjectRecoveryEquiv
    (C : Type u) [Category.{u} C] : C ≃ CategoryIntrinsicIdentityImage C where
  toFun object := ⟨categoryIdentityArrow object,
    categoryIdentityArrow_intrinsic object⟩
  invFun identity := identity.val.source
  left_inv object := rfl
  right_inv identity := by
    apply Subtype.ext
    exact (categoryCompositionIntrinsicIdentity_iff identity.val).mp
      identity.property |>.symm

theorem intrinsicIdentityImage_eq_knownIdentityImage
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryCompositionIntrinsicIdentity arrow ↔
      ∃ object : C, categoryIdentityArrow object = arrow := by
  constructor
  · intro intrinsic
    exact ⟨arrow.source,
      (categoryCompositionIntrinsicIdentity_iff arrow).mp intrinsic |>.symm⟩
  · rintro ⟨object, rfl⟩
    exact categoryIdentityArrow_intrinsic object

structure IntrinsicInternalCategoryRecoveryTheorem
    (C : Type u) [Category.{u} C] : Prop where
  intrinsic_objects : Nonempty (C ≃ CategoryIntrinsicIdentityImage C)
  identity_exact : ∀ arrow : SmallCategoryArrow C,
    CategoryCompositionIntrinsicIdentity arrow ↔
      arrow = categoryIdentityArrow arrow.source
  homs : ∀ X Y : C, Nonempty ((X ⟶ Y) ≃ CategoryArrowFiber C X Y)
  composition : ∀ {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : CategoryArrowFiber C X Z),
    (categoryInteractionIncidence C).resonance
        (some (categoryHomFiberEquiv C X Y first).val)
        (some (categoryHomFiberEquiv C Y Z second).val)
        (some output.val) ↔
      (categoryHomFiberEquiv C X Z).symm output = first ≫ second

theorem intrinsicInternalCategoryRecoveryTheorem
    (C : Type u) [Category.{u} C] :
    IntrinsicInternalCategoryRecoveryTheorem C where
  intrinsic_objects := ⟨intrinsicCategoryObjectRecoveryEquiv C⟩
  identity_exact := categoryCompositionIntrinsicIdentity_iff
  homs := fun X Y => ⟨categoryHomFiberEquiv C X Y⟩
  composition := categoryInteractionIncidence_recovers_composition

end IncidenceCore
