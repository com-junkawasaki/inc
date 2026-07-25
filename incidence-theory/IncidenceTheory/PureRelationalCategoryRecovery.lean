import IncidenceTheory.CategoryInteractionFullness

namespace IncidenceCore

open CategoryTheory

universe u

/-! Unlike `CategoryCompositionIntrinsicIdentity`, the following predicate
does not mention endpoint projections.  It says solely that every defined
left or right composite with the candidate is unchanged. -/
def CategoryCompositionPureIdentity
    {C : Type u} [Category.{u} C] (identity : SmallCategoryArrow C) : Prop :=
  (∀ arrow output : SmallCategoryArrow C,
    categoryCompositionRelation identity arrow output → output = arrow) ∧
  (∀ arrow output : SmallCategoryArrow C,
    categoryCompositionRelation arrow identity output → output = arrow)

theorem categoryIdentityArrow_pure
    {C : Type u} [Category.{u} C] (object : C) :
    CategoryCompositionPureIdentity (categoryIdentityArrow object) := by
  constructor
  · intro arrow output resonant
    rcases resonant with ⟨compatible, rfl⟩
    rcases arrow with ⟨source, target, hom⟩
    cases compatible
    simp [SmallCategoryArrow.compose, SmallCategoryArrow.ofHom,
      categoryIdentityArrow]
  · intro arrow output resonant
    rcases resonant with ⟨compatible, rfl⟩
    rcases arrow with ⟨source, target, hom⟩
    cases compatible
    simp [SmallCategoryArrow.compose, SmallCategoryArrow.ofHom,
      categoryIdentityArrow]

theorem categoryCompositionPureIdentity_eq_identity
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C)
    (pure : CategoryCompositionPureIdentity arrow) :
    arrow = categoryIdentityArrow arrow.source := by
  rcases arrow with ⟨source, target, hom⟩
  have resonant : categoryCompositionRelation
      (SmallCategoryArrow.ofHom hom) (categoryIdentityArrow target)
      (SmallCategoryArrow.ofHom hom) :=
    (categoryCompositionRelation_ofHom_iff hom (𝟙 target)
      (SmallCategoryArrow.ofHom hom)).mpr (by simp [SmallCategoryArrow.ofHom])
  have equal := pure.1 _ _ resonant
  cases equal
  rfl

theorem categoryCompositionPureIdentity_iff
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryCompositionPureIdentity arrow ↔
      arrow = categoryIdentityArrow arrow.source := by
  constructor
  · exact categoryCompositionPureIdentity_eq_identity arrow
  · intro equal
    rw [equal]
    exact categoryIdentityArrow_pure arrow.source

theorem categoryCompositionPureIdentity_iff_intrinsic
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryCompositionPureIdentity arrow ↔
      CategoryCompositionIntrinsicIdentity arrow := by
  rw [categoryCompositionPureIdentity_iff,
    categoryCompositionIntrinsicIdentity_iff]

def CategoryPureIdentityImage (C : Type u) [Category.{u} C] :=
  { arrow : SmallCategoryArrow C // CategoryCompositionPureIdentity arrow }

def pureCategoryObjectRecoveryEquiv
    (C : Type u) [Category.{u} C] : C ≃ CategoryPureIdentityImage C where
  toFun object := ⟨categoryIdentityArrow object,
    categoryIdentityArrow_pure object⟩
  invFun identity := identity.val.source
  left_inv object := rfl
  right_inv identity := by
    apply Subtype.ext
    exact (categoryCompositionPureIdentity_iff identity.val).mp
      identity.property |>.symm

/-! Source and target identities are now specified solely by pure identity and
one resonance fact. -/
def CategoryCompositionPureSourceIdentity
    {C : Type u} [Category.{u} C]
    (arrow identity : SmallCategoryArrow C) : Prop :=
  CategoryCompositionPureIdentity identity ∧
    categoryCompositionRelation identity arrow arrow

def CategoryCompositionPureTargetIdentity
    {C : Type u} [Category.{u} C]
    (arrow identity : SmallCategoryArrow C) : Prop :=
  CategoryCompositionPureIdentity identity ∧
    categoryCompositionRelation arrow identity arrow

theorem categoryCompositionPureSourceIdentity_iff
    {C : Type u} [Category.{u} C]
    (arrow identity : SmallCategoryArrow C) :
    CategoryCompositionPureSourceIdentity arrow identity ↔
      identity = categoryIdentityArrow arrow.source := by
  constructor
  · rintro ⟨pure, resonant⟩
    have identityEqual :=
      (categoryCompositionPureIdentity_iff identity).mp pure
    rw [identityEqual] at resonant
    rcases resonant with ⟨compatible, outputEqual⟩
    have sourceEqual : identity.source = arrow.source := by
      simpa [categoryIdentityArrow] using compatible
    rw [identityEqual, sourceEqual]
  · rintro rfl
    exact ⟨categoryIdentityArrow_pure arrow.source,
      (categoryIdentityArrow_intrinsic arrow.source).2.1 arrow rfl⟩

theorem categoryCompositionPureTargetIdentity_iff
    {C : Type u} [Category.{u} C]
    (arrow identity : SmallCategoryArrow C) :
    CategoryCompositionPureTargetIdentity arrow identity ↔
      identity = categoryIdentityArrow arrow.target := by
  constructor
  · rintro ⟨pure, resonant⟩
    have identityEqual :=
      (categoryCompositionPureIdentity_iff identity).mp pure
    rw [identityEqual] at resonant
    rcases resonant with ⟨compatible, outputEqual⟩
    have targetEqual : identity.source = arrow.target := by
      simpa [categoryIdentityArrow] using compatible.symm
    rw [identityEqual, targetEqual]
  · rintro rfl
    exact ⟨categoryIdentityArrow_pure arrow.target,
      (categoryIdentityArrow_intrinsic arrow.target).2.2 arrow rfl⟩

theorem categoryCompositionPureSourceIdentity_existsUnique
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    ∃! identity, CategoryCompositionPureSourceIdentity arrow identity := by
  refine ⟨categoryIdentityArrow arrow.source,
    (categoryCompositionPureSourceIdentity_iff arrow _).mpr rfl, ?_⟩
  intro identity property
  exact (categoryCompositionPureSourceIdentity_iff arrow identity).mp property

theorem categoryCompositionPureTargetIdentity_existsUnique
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    ∃! identity, CategoryCompositionPureTargetIdentity arrow identity := by
  refine ⟨categoryIdentityArrow arrow.target,
    (categoryCompositionPureTargetIdentity_iff arrow _).mpr rfl, ?_⟩
  intro identity property
  exact (categoryCompositionPureTargetIdentity_iff arrow identity).mp property

def pureRelationalSourceIdentity
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryPureIdentityImage C :=
  ⟨categoryIdentityArrow arrow.source,
    categoryIdentityArrow_pure arrow.source⟩

def pureRelationalTargetIdentity
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryPureIdentityImage C :=
  ⟨categoryIdentityArrow arrow.target,
    categoryIdentityArrow_pure arrow.target⟩

theorem pureRelationalSourceIdentity_spec
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryCompositionPureSourceIdentity arrow
      (pureRelationalSourceIdentity arrow).val :=
  (categoryCompositionPureSourceIdentity_iff arrow _).mpr rfl

theorem pureRelationalTargetIdentity_spec
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    CategoryCompositionPureTargetIdentity arrow
      (pureRelationalTargetIdentity arrow).val :=
  (categoryCompositionPureTargetIdentity_iff arrow _).mpr rfl

def pureRelationalRecoveredSource
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) : C :=
  (pureCategoryObjectRecoveryEquiv C).symm
    (pureRelationalSourceIdentity arrow)

def pureRelationalRecoveredTarget
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) : C :=
  (pureCategoryObjectRecoveryEquiv C).symm
    (pureRelationalTargetIdentity arrow)

@[simp] theorem pureRelationalRecoveredSource_eq
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    pureRelationalRecoveredSource arrow = arrow.source := rfl

@[simp] theorem pureRelationalRecoveredTarget_eq
    {C : Type u} [Category.{u} C] (arrow : SmallCategoryArrow C) :
    pureRelationalRecoveredTarget arrow = arrow.target := rfl

def PureRelationalArrowFiber
    (C : Type u) [Category.{u} C] (X Y : C) :=
  { arrow : SmallCategoryArrow C //
    CategoryCompositionPureSourceIdentity arrow (categoryIdentityArrow X) ∧
    CategoryCompositionPureTargetIdentity arrow (categoryIdentityArrow Y) }

def pureRelationalArrowFiberEquiv
    (C : Type u) [Category.{u} C] (X Y : C) :
    PureRelationalArrowFiber C X Y ≃ CategoryArrowFiber C X Y where
  toFun arrow := by
    have sourceIdentity :=
      (categoryCompositionPureSourceIdentity_iff arrow.val
        (categoryIdentityArrow X)).mp arrow.property.1
    have targetIdentity :=
      (categoryCompositionPureTargetIdentity_iff arrow.val
        (categoryIdentityArrow Y)).mp arrow.property.2
    have sourceEq : arrow.val.source = X :=
      (congrArg SmallCategoryArrow.source sourceIdentity).symm
    have targetEq : arrow.val.target = Y :=
      (congrArg SmallCategoryArrow.target targetIdentity).symm
    exact ⟨arrow.val, sourceEq, targetEq⟩
  invFun arrow :=
    ⟨arrow.val,
      (categoryCompositionPureSourceIdentity_iff _ _).mpr
        (congrArg categoryIdentityArrow arrow.property.1.symm),
      (categoryCompositionPureTargetIdentity_iff _ _).mpr
        (congrArg categoryIdentityArrow arrow.property.2.symm)⟩
  left_inv arrow := by
    apply Subtype.ext
    rfl
  right_inv arrow := by
    apply Subtype.ext
    rfl

def pureRelationalHomFiberEquiv
    (C : Type u) [Category.{u} C] (X Y : C) :
    (X ⟶ Y) ≃ PureRelationalArrowFiber C X Y :=
  (categoryHomFiberEquiv C X Y).trans
    (pureRelationalArrowFiberEquiv C X Y).symm

@[simp] theorem pureRelationalHomFiberEquiv_apply
    {C : Type u} [Category.{u} C] {X Y : C} (hom : X ⟶ Y) :
    (pureRelationalHomFiberEquiv C X Y hom).val =
      SmallCategoryArrow.ofHom hom := by
  rfl

theorem pureRelationalHomFiberEquiv_composition_iff
    {C : Type u} [Category.{u} C] {X Y Z : C}
    (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : PureRelationalArrowFiber C X Z) :
    categoryCompositionRelation
        (pureRelationalHomFiberEquiv C X Y first).val
        (pureRelationalHomFiberEquiv C Y Z second).val output.val ↔
      (pureRelationalHomFiberEquiv C X Z).symm output = first ≫ second := by
  rw [pureRelationalHomFiberEquiv_apply,
    pureRelationalHomFiberEquiv_apply,
    categoryCompositionRelation_ofHom_iff]
  constructor
  · intro equal
    apply (pureRelationalHomFiberEquiv C X Z).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact equal
  · intro equal
    have mapped := congrArg (pureRelationalHomFiberEquiv C X Z) equal
    rw [Equiv.apply_symm_apply] at mapped
    exact congrArg Subtype.val mapped

structure PureRelationalCategoryRecoveryTheorem
    (C : Type u) [Category.{u} C] : Prop where
  pure_identity_exact : ∀ arrow : SmallCategoryArrow C,
    CategoryCompositionPureIdentity arrow ↔
      arrow = categoryIdentityArrow arrow.source
  objects : Nonempty (C ≃ CategoryPureIdentityImage C)
  source_identity : ∀ arrow : SmallCategoryArrow C,
    ∃! identity, CategoryCompositionPureSourceIdentity arrow identity
  target_identity : ∀ arrow : SmallCategoryArrow C,
    ∃! identity, CategoryCompositionPureTargetIdentity arrow identity
  homs : ∀ X Y : C,
    Nonempty ((X ⟶ Y) ≃ PureRelationalArrowFiber C X Y)
  composition : ∀ {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : PureRelationalArrowFiber C X Z),
    categoryCompositionRelation
        (pureRelationalHomFiberEquiv C X Y first).val
        (pureRelationalHomFiberEquiv C Y Z second).val output.val ↔
      (pureRelationalHomFiberEquiv C X Z).symm output = first ≫ second
  source_recovered : ∀ arrow : SmallCategoryArrow C,
    pureRelationalRecoveredSource arrow = arrow.source
  target_recovered : ∀ arrow : SmallCategoryArrow C,
    pureRelationalRecoveredTarget arrow = arrow.target

theorem pureRelationalCategoryRecoveryTheorem
    (C : Type u) [Category.{u} C] :
    PureRelationalCategoryRecoveryTheorem C where
  pure_identity_exact := categoryCompositionPureIdentity_iff
  objects := ⟨pureCategoryObjectRecoveryEquiv C⟩
  source_identity := categoryCompositionPureSourceIdentity_existsUnique
  target_identity := categoryCompositionPureTargetIdentity_existsUnique
  homs := fun X Y => ⟨pureRelationalHomFiberEquiv C X Y⟩
  composition := pureRelationalHomFiberEquiv_composition_iff
  source_recovered := pureRelationalRecoveredSource_eq
  target_recovered := pureRelationalRecoveredTarget_eq

end IncidenceCore
