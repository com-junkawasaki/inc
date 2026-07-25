import IncidenceTheory.RelationalCategoryRecognition

namespace IncidenceCore

open CategoryTheory

universe u

abbrev RecognizedCategoryArrow
    (system : TernaryResonanceSystem.{u})
    (axioms : RelationalCategoryAxioms system) :=
  @SmallCategoryArrow (RelationalCategoryObject system) axioms.toCategory

theorem recognizedCategoryArrow_ext
    {system : TernaryResonanceSystem.{u}}
    {axioms : RelationalCategoryAxioms system}
    {first second : RecognizedCategoryArrow system axioms}
    (sourceEqual : (@SmallCategoryArrow.source _ axioms.toCategory first) =
      @SmallCategoryArrow.source _ axioms.toCategory second)
    (targetEqual : (@SmallCategoryArrow.target _ axioms.toCategory first) =
      @SmallCategoryArrow.target _ axioms.toCategory second)
    (homEqual : HEq (@SmallCategoryArrow.hom _ axioms.toCategory first)
      (@SmallCategoryArrow.hom _ axioms.toCategory second)) : first = second := by
  rcases first with ⟨firstSource, firstTarget, firstHom⟩
  rcases second with ⟨secondSource, secondTarget, secondHom⟩
  cases sourceEqual
  cases targetEqual
  cases eq_of_heq homEqual
  rfl

noncomputable def RelationalCategoryAxioms.encodeArrow
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    RecognizedCategoryArrow system axioms :=
  @SmallCategoryArrow.mk (RelationalCategoryObject system) axioms.toCategory
    (axioms.sourceObject arrow) (axioms.targetObject arrow)
    (axioms.typedArrow arrow)

def RelationalCategoryAxioms.decodeArrow
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (arrow : RecognizedCategoryArrow system axioms) : system.Carrier := by
  letI := axioms.toCategory
  exact arrow.hom.val

@[simp] theorem RelationalCategoryAxioms.decode_encodeArrow
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) (arrow : system.Carrier) :
    axioms.decodeArrow (axioms.encodeArrow arrow) = arrow := rfl

theorem RelationalCategoryAxioms.encode_decodeArrow
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (arrow : RecognizedCategoryArrow system axioms) :
    axioms.encodeArrow (axioms.decodeArrow arrow) = arrow := by
  rcases arrow with ⟨source, target, hom⟩
  have sourceValueEqual : axioms.sourceIdentity hom.val = source.val :=
    axioms.sourceIdentity_eq hom.property.1
  have targetValueEqual : axioms.targetIdentity hom.val = target.val :=
    axioms.targetIdentity_eq hom.property.2
  have sourceEqual : source = axioms.sourceObject hom.val := by
    apply Subtype.ext
    exact sourceValueEqual.symm
  have targetEqual : target = axioms.targetObject hom.val := by
    apply Subtype.ext
    exact targetValueEqual.symm
  apply recognizedCategoryArrow_ext sourceEqual.symm targetEqual.symm
  apply (Subtype.heq_iff_coe_eq (fun candidate => by
    simp only [RelationalCategoryAxioms.encodeArrow,
      RelationalCategoryAxioms.decodeArrow]
    rw [← sourceEqual, ← targetEqual])).mpr
  rfl

noncomputable def RelationalCategoryAxioms.arrowEquiv
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) :
    system.Carrier ≃ RecognizedCategoryArrow system axioms where
  toFun := axioms.encodeArrow
  invFun := axioms.decodeArrow
  left_inv := axioms.decode_encodeArrow
  right_inv := axioms.encode_decodeArrow

def recognizedCategoryCompositionRelation
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (first second output : RecognizedCategoryArrow system axioms) : Prop :=
  @categoryCompositionRelation (RelationalCategoryObject system)
    axioms.toCategory first second output

def recognizedArrowSource
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (arrow : RecognizedCategoryArrow system axioms) :=
  @SmallCategoryArrow.source _ axioms.toCategory arrow

def recognizedArrowTarget
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (arrow : RecognizedCategoryArrow system axioms) :=
  @SmallCategoryArrow.target _ axioms.toCategory arrow

def recognizedArrowHom
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (arrow : RecognizedCategoryArrow system axioms) :
    RelationalCategoryHom system (recognizedArrowSource axioms arrow)
      (recognizedArrowTarget axioms arrow) :=
  @SmallCategoryArrow.hom _ axioms.toCategory arrow

noncomputable def recognizedArrowCompose
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (first second : RecognizedCategoryArrow system axioms)
    (compatible : recognizedArrowTarget axioms first =
      recognizedArrowSource axioms second) :
    RecognizedCategoryArrow system axioms :=
  @SmallCategoryArrow.compose _ axioms.toCategory first second compatible

theorem recognizedEqToHom_val
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    {X Y : RelationalCategoryObject system} (equal : X = Y) :
    (@eqToHom (RelationalCategoryObject system) axioms.toCategory X Y equal :
      RelationalCategoryHom system X Y).val = X.val := by
  cases equal
  rfl

theorem RelationalCategoryAxioms.recognizedCompose_resonant
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (first second : RecognizedCategoryArrow system axioms)
    (compatible : recognizedArrowTarget axioms first =
      recognizedArrowSource axioms second) :
    system.resonance (recognizedArrowHom axioms first).val
      (recognizedArrowHom axioms second).val
      (recognizedArrowHom axioms
        (recognizedArrowCompose axioms first second compatible)).val := by
  let bridge : RelationalCategoryHom system
      (recognizedArrowTarget axioms first)
      (recognizedArrowSource axioms second) :=
    @eqToHom (RelationalCategoryObject system) axioms.toCategory
      (recognizedArrowTarget axioms first)
      (recognizedArrowSource axioms second) compatible
  have bridgeValue : bridge.val = (recognizedArrowTarget axioms first).val :=
    recognizedEqToHom_val axioms compatible
  have bridgeSecond := axioms.composite_resonant bridge
    (recognizedArrowHom axioms second)
  have bridgeSecondEqual :
      (axioms.composite bridge (recognizedArrowHom axioms second)).val =
        (recognizedArrowHom axioms second).val := by
    apply (recognizedArrowSource axioms second).property.1
      (recognizedArrowHom axioms second).val
      (axioms.composite bridge (recognizedArrowHom axioms second)).val
    simpa [bridge, bridgeValue, compatible] using bridgeSecond
  have finalResonant := axioms.composite_resonant
    (recognizedArrowHom axioms first)
    (axioms.composite bridge (recognizedArrowHom axioms second))
  rw [bridgeSecondEqual] at finalResonant
  dsimp [bridge] at finalResonant
  have composeValue :
      (recognizedArrowHom axioms
        (recognizedArrowCompose axioms first second compatible)).val =
      (axioms.composite (recognizedArrowHom axioms first)
        (axioms.composite
          (@eqToHom (RelationalCategoryObject system) axioms.toCategory
            (recognizedArrowTarget axioms first)
            (recognizedArrowSource axioms second) compatible)
          (recognizedArrowHom axioms second))).val := by
    rfl
  rw [composeValue]
  exact finalResonant

theorem RelationalCategoryAxioms.encodeArrow_resonance_iff
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    (first second output : system.Carrier) :
    system.resonance first second output ↔
      recognizedCategoryCompositionRelation axioms
        (axioms.encodeArrow first) (axioms.encodeArrow second)
        (axioms.encodeArrow output) := by
  constructor
  · intro resonant
    rcases axioms.resonance_composable resonant with
      ⟨middleIdentity, firstTarget, secondSource⟩
    have compatible : axioms.targetObject first = axioms.sourceObject second := by
      apply Subtype.ext
      exact (axioms.targetIdentity_eq firstTarget).trans
        (axioms.sourceIdentity_eq secondSource).symm
    have outputSourceEqual :
        axioms.sourceObject output = axioms.sourceObject first := by
      apply Subtype.ext
      exact axioms.sourceIdentity_eq
        (axioms.source_stable resonant (axioms.sourceIdentity_spec first))
    have outputTargetEqual :
        axioms.targetObject output = axioms.targetObject second := by
      apply Subtype.ext
      exact axioms.targetIdentity_eq
        (axioms.target_stable resonant (axioms.targetIdentity_spec second))
    refine ⟨compatible, ?_⟩
    apply recognizedCategoryArrow_ext
    · exact outputSourceEqual
    · exact outputTargetEqual
    · apply (Subtype.heq_iff_coe_eq (fun candidate => by
        simp only [RelationalCategoryAxioms.encodeArrow,
          SmallCategoryArrow.compose]
        rw [outputSourceEqual, outputTargetEqual])).mpr
      exact axioms.functional resonant
        (axioms.recognizedCompose_resonant
          (axioms.encodeArrow first) (axioms.encodeArrow second) compatible)
  · rintro ⟨compatible, outputEqual⟩
    have compositeResonant := axioms.recognizedCompose_resonant
      (axioms.encodeArrow first) (axioms.encodeArrow second) compatible
    have decodedEqual := congrArg axioms.decodeArrow outputEqual
    rw [axioms.decode_encodeArrow] at decodedEqual
    have decodedEqual' : output =
        axioms.decodeArrow
          (recognizedArrowCompose axioms (axioms.encodeArrow first)
            (axioms.encodeArrow second) compatible) := by
      simpa [recognizedArrowCompose] using decodedEqual
    change system.resonance first second
      (axioms.decodeArrow
        (recognizedArrowCompose axioms (axioms.encodeArrow first)
          (axioms.encodeArrow second) compatible)) at compositeResonant
    rw [← decodedEqual'] at compositeResonant
    exact compositeResonant

def recognizedCategoryCompositionSystem
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) : TernaryResonanceSystem.{u} where
  Carrier := RecognizedCategoryArrow system axioms
  resonance := recognizedCategoryCompositionRelation axioms

noncomputable def RelationalCategoryAxioms.roundTripHom
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) :
    system ⟶ recognizedCategoryCompositionSystem axioms where
  toFun := axioms.encodeArrow
  preserves := by
    intro first second output resonant
    exact (axioms.encodeArrow_resonance_iff first second output).mp resonant

noncomputable def RelationalCategoryAxioms.roundTripInverseHom
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) :
    recognizedCategoryCompositionSystem axioms ⟶ system where
  toFun := axioms.decodeArrow
  preserves := by
    intro first second output resonant
    rw [← axioms.encode_decodeArrow first,
      ← axioms.encode_decodeArrow second,
      ← axioms.encode_decodeArrow output] at resonant
    exact (axioms.encodeArrow_resonance_iff _ _ _).mpr resonant

noncomputable def RelationalCategoryAxioms.roundTripIso
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system) :
    system ≅ recognizedCategoryCompositionSystem axioms where
  hom := axioms.roundTripHom
  inv := axioms.roundTripInverseHom
  hom_inv_id := by
    apply TernaryResonanceHom.ext
    funext arrow
    exact axioms.decode_encodeArrow arrow
  inv_hom_id := by
    apply TernaryResonanceHom.ext
    funext arrow
    exact axioms.encode_decodeArrow arrow

structure RelationalCategoryRoundTripTheorem
    (system : TernaryResonanceSystem.{u})
    (axioms : RelationalCategoryAxioms system) : Prop where
  carrier_equivalence : Nonempty
    (system.Carrier ≃ RecognizedCategoryArrow system axioms)
  relation_exact : ∀ first second output : system.Carrier,
    system.resonance first second output ↔
      recognizedCategoryCompositionRelation axioms
        (axioms.encodeArrow first) (axioms.encodeArrow second)
        (axioms.encodeArrow output)
  system_isomorphism : Nonempty
    (system ≅ recognizedCategoryCompositionSystem axioms)

theorem relationalCategoryRoundTripTheorem
    (system : TernaryResonanceSystem.{u})
    (axioms : RelationalCategoryAxioms system) :
    RelationalCategoryRoundTripTheorem system axioms where
  carrier_equivalence := ⟨axioms.arrowEquiv⟩
  relation_exact := axioms.encodeArrow_resonance_iff
  system_isomorphism := ⟨axioms.roundTripIso⟩

end IncidenceCore
