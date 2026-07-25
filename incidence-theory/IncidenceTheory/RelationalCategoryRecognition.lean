import IncidenceTheory.PureRelationalCategoryRecovery

namespace IncidenceCore

open CategoryTheory

universe u


def TernaryPureIdentity (system : TernaryResonanceSystem.{u})
    (identity : system.Carrier) : Prop :=
  (∀ arrow output, system.resonance identity arrow output → output = arrow) ∧
  (∀ arrow output, system.resonance arrow identity output → output = arrow)

def TernarySourceIdentity (system : TernaryResonanceSystem.{u})
    (arrow identity : system.Carrier) : Prop :=
  TernaryPureIdentity system identity ∧
    system.resonance identity arrow arrow

def TernaryTargetIdentity (system : TernaryResonanceSystem.{u})
    (arrow identity : system.Carrier) : Prop :=
  TernaryPureIdentity system identity ∧
    system.resonance arrow identity arrow

structure RelationalCategoryAxioms (system : TernaryResonanceSystem.{u}) : Prop where
  functional : ∀ {first second output₁ output₂},
    system.resonance first second output₁ →
    system.resonance first second output₂ → output₁ = output₂
  identity_self : ∀ {identity}, TernaryPureIdentity system identity →
    system.resonance identity identity identity
  source_exists_unique : ∀ arrow,
    ∃! identity, TernarySourceIdentity system arrow identity
  target_exists_unique : ∀ arrow,
    ∃! identity, TernaryTargetIdentity system arrow identity
  composable : ∀ {first second identity},
    TernaryTargetIdentity system first identity →
    TernarySourceIdentity system second identity →
    ∃ output, system.resonance first second output
  resonance_composable : ∀ {first second output},
    system.resonance first second output →
    ∃ identity, TernaryTargetIdentity system first identity ∧
      TernarySourceIdentity system second identity
  source_stable : ∀ {first second output identity},
    system.resonance first second output →
    TernarySourceIdentity system first identity →
    TernarySourceIdentity system output identity
  target_stable : ∀ {first second output identity},
    system.resonance first second output →
    TernaryTargetIdentity system second identity →
    TernaryTargetIdentity system output identity
  associative : ∀ first second third output,
    (∃ middle, system.resonance first second middle ∧
      system.resonance middle third output) ↔
    (∃ middle, system.resonance second third middle ∧
      system.resonance first middle output)

theorem categoryCompositionSystem_relationalCategoryAxioms
    (C : Type u) [Category.{u} C] :
    RelationalCategoryAxioms (categoryCompositionSystem C) where
  functional := categoryCompositionRelation_functional
  identity_self := by
    intro identity pure
    have categoricalPure : CategoryCompositionPureIdentity identity := pure
    have equal :=
      (categoryCompositionPureIdentity_iff identity).mp categoricalPure
    rw [equal]
    exact (categoryIdentityArrow_intrinsic identity.source).2.1
      (categoryIdentityArrow identity.source) rfl
  source_exists_unique := by
    intro arrow
    simpa [TernarySourceIdentity, TernaryPureIdentity,
      CategoryCompositionPureSourceIdentity,
      CategoryCompositionPureIdentity] using
      categoryCompositionPureSourceIdentity_existsUnique arrow
  target_exists_unique := by
    intro arrow
    simpa [TernaryTargetIdentity, TernaryPureIdentity,
      CategoryCompositionPureTargetIdentity,
      CategoryCompositionPureIdentity] using
      categoryCompositionPureTargetIdentity_existsUnique arrow
  composable := by
    intro first second identity firstTarget secondSource
    have targetEqual :=
      (categoryCompositionPureTargetIdentity_iff first identity).mp firstTarget
    have sourceEqual :=
      (categoryCompositionPureSourceIdentity_iff second identity).mp secondSource
    have compatible : first.target = second.source := by
      apply categoryIdentityArrow_injective (C := C)
      exact targetEqual.symm.trans sourceEqual
    exact ⟨first.compose second compatible, compatible, rfl⟩
  resonance_composable := by
    intro first second output resonant
    rcases resonant with ⟨compatible, outputEqual⟩
    refine ⟨categoryIdentityArrow first.target,
      (categoryCompositionPureTargetIdentity_iff _ _).mpr rfl, ?_⟩
    apply (categoryCompositionPureSourceIdentity_iff _ _).mpr
    exact congrArg categoryIdentityArrow compatible
  source_stable := by
    intro first second output identity resonant firstSource
    have identityEqual :=
      (categoryCompositionPureSourceIdentity_iff first identity).mp firstSource
    rcases resonant with ⟨compatible, rfl⟩
    apply (categoryCompositionPureSourceIdentity_iff _ _).mpr
    simpa [SmallCategoryArrow.compose] using identityEqual
  target_stable := by
    intro first second output identity resonant secondTarget
    have identityEqual :=
      (categoryCompositionPureTargetIdentity_iff second identity).mp secondTarget
    rcases resonant with ⟨compatible, rfl⟩
    apply (categoryCompositionPureTargetIdentity_iff _ _).mpr
    simpa [SmallCategoryArrow.compose] using identityEqual
  associative := categoryComposition_associative C

def RelationalCategoryObject (system : TernaryResonanceSystem.{u}) :=
  { identity : system.Carrier // TernaryPureIdentity system identity }

def RelationalCategoryHom (system : TernaryResonanceSystem.{u})
    (source target : RelationalCategoryObject system) :=
  { arrow : system.Carrier //
    TernarySourceIdentity system arrow source.val ∧
    TernaryTargetIdentity system arrow target.val }

noncomputable def RelationalCategoryAxioms.sourceIdentity
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    system.Carrier :=
  Classical.choose (axioms.source_exists_unique arrow)

theorem RelationalCategoryAxioms.sourceIdentity_spec
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    TernarySourceIdentity system arrow (axioms.sourceIdentity arrow) :=
  Classical.choose_spec (axioms.source_exists_unique arrow) |>.1

theorem RelationalCategoryAxioms.sourceIdentity_eq
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) {arrow identity : system.Carrier}
    (property : TernarySourceIdentity system arrow identity) :
    axioms.sourceIdentity arrow = identity :=
  (Classical.choose_spec (axioms.source_exists_unique arrow) |>.2 identity property).symm

noncomputable def RelationalCategoryAxioms.targetIdentity
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    system.Carrier :=
  Classical.choose (axioms.target_exists_unique arrow)

theorem RelationalCategoryAxioms.targetIdentity_spec
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    TernaryTargetIdentity system arrow (axioms.targetIdentity arrow) :=
  Classical.choose_spec (axioms.target_exists_unique arrow) |>.1

theorem RelationalCategoryAxioms.targetIdentity_eq
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) {arrow identity : system.Carrier}
    (property : TernaryTargetIdentity system arrow identity) :
    axioms.targetIdentity arrow = identity :=
  (Classical.choose_spec (axioms.target_exists_unique arrow) |>.2 identity property).symm

noncomputable def RelationalCategoryAxioms.sourceObject
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    RelationalCategoryObject system :=
  ⟨axioms.sourceIdentity arrow, (axioms.sourceIdentity_spec arrow).1⟩

noncomputable def RelationalCategoryAxioms.targetObject
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    RelationalCategoryObject system :=
  ⟨axioms.targetIdentity arrow, (axioms.targetIdentity_spec arrow).1⟩

noncomputable def RelationalCategoryAxioms.typedArrow
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    RelationalCategoryHom system (axioms.sourceObject arrow)
      (axioms.targetObject arrow) :=
  ⟨arrow, axioms.sourceIdentity_spec arrow, axioms.targetIdentity_spec arrow⟩

@[simp] theorem RelationalCategoryAxioms.typedArrow_val
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    (axioms.typedArrow arrow).val = arrow := rfl

theorem RelationalCategoryAxioms.carrier_covered_by_typed_homs
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    ∃ (X Y : RelationalCategoryObject system)
        (typed : RelationalCategoryHom system X Y), typed.val = arrow :=
  ⟨axioms.sourceObject arrow, axioms.targetObject arrow,
    axioms.typedArrow arrow, rfl⟩

noncomputable def RelationalCategoryAxioms.composite
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    {X Y Z : RelationalCategoryObject system}
    (first : RelationalCategoryHom system X Y)
    (second : RelationalCategoryHom system Y Z) :
    RelationalCategoryHom system X Z := by
  have existence := axioms.composable first.property.2 second.property.1
  let output := Classical.choose existence
  have resonant : system.resonance first.val second.val output :=
    Classical.choose_spec existence
  exact ⟨output, axioms.source_stable resonant first.property.1,
    axioms.target_stable resonant second.property.2⟩

theorem RelationalCategoryAxioms.composite_resonant
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    {X Y Z : RelationalCategoryObject system}
    (first : RelationalCategoryHom system X Y)
    (second : RelationalCategoryHom system Y Z) :
    system.resonance first.val second.val
      (axioms.composite first second).val := by
  unfold RelationalCategoryAxioms.composite
  exact Classical.choose_spec
    (axioms.composable first.property.2 second.property.1)

def RelationalCategoryAxioms.identityHom
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (object : RelationalCategoryObject system) :
    RelationalCategoryHom system object object :=
  ⟨object.val,
    ⟨object.property, axioms.identity_self object.property⟩,
    ⟨object.property, axioms.identity_self object.property⟩⟩

noncomputable def RelationalCategoryAxioms.toCategory
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) :
    Category.{u} (RelationalCategoryObject system) where
  Hom := RelationalCategoryHom system
  id := axioms.identityHom
  comp := axioms.composite
  id_comp := by
    intro X Y arrow
    apply Subtype.ext
    exact (X.property.1 arrow.val
      (axioms.composite (axioms.identityHom X) arrow).val
      (axioms.composite_resonant (axioms.identityHom X) arrow))
  comp_id := by
    intro X Y arrow
    apply Subtype.ext
    exact Y.property.2 arrow.val
      (axioms.composite arrow (axioms.identityHom Y)).val
      (axioms.composite_resonant arrow (axioms.identityHom Y))
  assoc := by
    intro W X Y Z first second third
    apply Subtype.ext
    have leftFirst := axioms.composite_resonant first second
    have leftSecond := axioms.composite_resonant
      (axioms.composite first second) third
    have rightFirst := axioms.composite_resonant second third
    have rightSecond := axioms.composite_resonant first
      (axioms.composite second third)
    rcases (axioms.associative first.val second.val third.val
      (axioms.composite (axioms.composite first second) third).val).mp
        ⟨(axioms.composite first second).val, leftFirst, leftSecond⟩ with
      ⟨middle, middleResonant, outputResonant⟩
    have middleEqual := axioms.functional middleResonant rightFirst
    subst middleEqual
    exact axioms.functional outputResonant rightSecond

theorem RelationalCategoryAxioms.resonance_comp_iff
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    {X Y Z : RelationalCategoryObject system}
    (first : RelationalCategoryHom system X Y)
    (second : RelationalCategoryHom system Y Z)
    (output : RelationalCategoryHom system X Z) :
    system.resonance first.val second.val output.val ↔
      output = axioms.composite first second := by
  constructor
  · intro resonant
    apply Subtype.ext
    exact axioms.functional resonant
      (axioms.composite_resonant first second)
  · rintro rfl
    exact axioms.composite_resonant first second

structure RelationalCategoryRecognitionTheorem
    (system : TernaryResonanceSystem.{u})
    (axioms : RelationalCategoryAxioms system) : Prop where
  category_exists : Nonempty (Category.{u} (RelationalCategoryObject system))
  carrier_coverage : ∀ arrow : system.Carrier,
    ∃ (X Y : RelationalCategoryObject system)
        (typed : RelationalCategoryHom system X Y), typed.val = arrow
  composition_exact : ∀ {X Y Z : RelationalCategoryObject system}
    (first : RelationalCategoryHom system X Y)
    (second : RelationalCategoryHom system Y Z)
    (output : RelationalCategoryHom system X Z),
    system.resonance first.val second.val output.val ↔
      output = axioms.composite first second

theorem relationalCategoryRecognitionTheorem
    (system : TernaryResonanceSystem.{u})
    (axioms : RelationalCategoryAxioms system) :
    RelationalCategoryRecognitionTheorem system axioms where
  category_exists := ⟨axioms.toCategory⟩
  carrier_coverage := axioms.carrier_covered_by_typed_homs
  composition_exact := axioms.resonance_comp_iff

end IncidenceCore
