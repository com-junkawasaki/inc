import IncidenceTheory.CategoryRecognitionFunctor

namespace IncidenceCore

open CategoryTheory

universe u

noncomputable def recognizedRoundTripFunctor :
    RecognizedTernaryCategory.{u} ⥤ RecognizedTernaryCategory.{u} :=
  relationalCategoryReconstructionFunctor ⋙ categoryRecognitionFunctor

theorem RelationalCategoryAxioms.encodeArrow_mapsPure
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    {identity : system.Carrier} (pure : TernaryPureIdentity system identity) :
    TernaryPureIdentity (recognizedCategoryCompositionSystem axioms)
      (axioms.encodeArrow identity) := by
  constructor
  · intro arrow output resonant
    rw [← axioms.encode_decodeArrow arrow,
      ← axioms.encode_decodeArrow output] at resonant
    have sourceResonant :=
      (axioms.encodeArrow_resonance_iff identity
        (axioms.decodeArrow arrow) (axioms.decodeArrow output)).mpr resonant
    exact (axioms.encode_decodeArrow output).symm.trans
      ((congrArg axioms.encodeArrow
        (pure.1 _ _ sourceResonant)).trans
          (axioms.encode_decodeArrow arrow))
  · intro arrow output resonant
    rw [← axioms.encode_decodeArrow arrow,
      ← axioms.encode_decodeArrow output] at resonant
    have sourceResonant :=
      (axioms.encodeArrow_resonance_iff
        (axioms.decodeArrow arrow) identity
        (axioms.decodeArrow output)).mpr resonant
    exact (axioms.encode_decodeArrow output).symm.trans
      ((congrArg axioms.encodeArrow
        (pure.2 _ _ sourceResonant)).trans
          (axioms.encode_decodeArrow arrow))

theorem RelationalCategoryAxioms.decodeArrow_mapsPure
    {system : TernaryResonanceSystem.{u}}
    (axioms : RelationalCategoryAxioms system)
    {identity : (recognizedCategoryCompositionSystem axioms).Carrier}
    (pure : TernaryPureIdentity
      (recognizedCategoryCompositionSystem axioms) identity) :
    TernaryPureIdentity system (axioms.decodeArrow identity) := by
  constructor
  · intro arrow output resonant
    have encodedResonant :=
      (axioms.encodeArrow_resonance_iff (axioms.decodeArrow identity)
        arrow output).mp resonant
    rw [axioms.encode_decodeArrow] at encodedResonant
    have equal := pure.1 _ _ encodedResonant
    exact congrArg axioms.decodeArrow equal
  · intro arrow output resonant
    have encodedResonant :=
      (axioms.encodeArrow_resonance_iff arrow
        (axioms.decodeArrow identity) output).mp resonant
    rw [axioms.encode_decodeArrow] at encodedResonant
    have equal := pure.2 _ _ encodedResonant
    exact congrArg axioms.decodeArrow equal

noncomputable def recognizedRoundTripHom
    (object : RecognizedTernaryCategory.{u}) :
    object ⟶ recognizedRoundTripFunctor.obj object where
  toFun := object.axioms.encodeArrow
  preserves := by
    intro first second output resonant
    exact (object.axioms.encodeArrow_resonance_iff first second output).mp
      resonant
  maps_pure := object.axioms.encodeArrow_mapsPure

noncomputable def recognizedRoundTripInv
    (object : RecognizedTernaryCategory.{u}) :
    recognizedRoundTripFunctor.obj object ⟶ object where
  toFun := object.axioms.decodeArrow
  preserves := by
    intro first second output resonant
    rw [← object.axioms.encode_decodeArrow first,
      ← object.axioms.encode_decodeArrow second,
      ← object.axioms.encode_decodeArrow output] at resonant
    exact (object.axioms.encodeArrow_resonance_iff _ _ _).mpr resonant
  maps_pure := object.axioms.decodeArrow_mapsPure

noncomputable def recognizedRoundTripIso
    (object : RecognizedTernaryCategory.{u}) :
    object ≅ recognizedRoundTripFunctor.obj object where
  hom := recognizedRoundTripHom object
  inv := recognizedRoundTripInv object
  hom_inv_id := by
    apply RecognizedTernaryHom.ext
    funext arrow
    exact object.axioms.decode_encodeArrow arrow
  inv_hom_id := by
    apply RecognizedTernaryHom.ext
    funext arrow
    exact object.axioms.encode_decodeArrow arrow

noncomputable def recognizedRoundTripNatIso :
    𝟭 (RecognizedTernaryCategory.{u}) ≅ recognizedRoundTripFunctor :=
  NatIso.ofComponents recognizedRoundTripIso (by
    intro source target hom
    apply RecognizedTernaryHom.ext
    funext arrow
    exact hom.encodeArrow_natural arrow)

structure RecognizedRoundTripNaturalIsoTheorem : Prop where
  component_iso : ∀ object : RecognizedTernaryCategory.{u},
    Nonempty (object ≅ recognizedRoundTripFunctor.obj object)
  natural_iso : Nonempty
    (𝟭 (RecognizedTernaryCategory.{u}) ≅ recognizedRoundTripFunctor)
  component_hom_exact : ∀ object : RecognizedTernaryCategory.{u},
    (recognizedRoundTripNatIso.hom.app object).toFun =
      object.axioms.encodeArrow
  component_inv_exact : ∀ object : RecognizedTernaryCategory.{u},
    (recognizedRoundTripNatIso.inv.app object).toFun =
      object.axioms.decodeArrow

theorem recognizedRoundTripNaturalIsoTheorem :
    RecognizedRoundTripNaturalIsoTheorem.{u} where
  component_iso := fun object => ⟨recognizedRoundTripIso object⟩
  natural_iso := ⟨recognizedRoundTripNatIso⟩
  component_hom_exact := fun _ => rfl
  component_inv_exact := fun _ => rfl

end IncidenceCore
