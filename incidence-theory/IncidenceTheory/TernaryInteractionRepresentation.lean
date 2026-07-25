import IncidenceTheory.GlobalResonanceSaturation

namespace IncidenceCore

open CategoryTheory

universe u

abbrev InteractionSort : Type u := ULift.{u} Unit

noncomputable instance interactionCarrierDecidableEq
    (system : TernaryResonanceSystem.{u}) :
    DecidableEq (Option system.Carrier) := Classical.decEq _

/-! Every small ternary relational system has a canonical Incidence
representation.  `none` is a freely adjoined interaction unit; the original
carrier occupies the `some` sector.  Boundaries and cell types are deliberately
trivial, so the construction isolates exactly the expressive contribution of
the primitive resonance relation. -/

def freeUnitInteractionResonance (system : TernaryResonanceSystem.{u}) :
    Option system.Carrier → Option system.Carrier →
      Option system.Carrier → Prop
  | none, right, output => output = right
  | some left, none, output => output = some left
  | some left, some right, some output =>
      system.resonance left right output
  | some _, some _, none => False

def freeUnitInteractionGlue (system : TernaryResonanceSystem.{u}) :
    Option system.Carrier → Option system.Carrier →
      Option (Option system.Carrier)
  | none, right => some right
  | some left, none => some (some left)
  | some _, some _ => none

noncomputable def ternaryInteractionIncidence
    (system : TernaryResonanceSystem.{u}) :
    @Incidence (Option system.Carrier) InteractionSort InteractionSort
      (interactionCarrierDecidableEq system) where
  boundary := fun _ => []
  typeFunc := fun _ => ⟨()⟩
  glue := freeUnitInteractionGlue system
  resonance := freeUnitInteractionResonance system
  selected_resonates := by
    intro left right output selected
    cases left <;> cases right <;>
      simp [freeUnitInteractionGlue, freeUnitInteractionResonance] at selected ⊢ <;>
      symm <;> assumption
  unit := none
  guards := { allow := fun _ _ => true }
  type_consistent := by simp
  sign_rules := by simp
  multiplicities := by simp
  well_founded := by simp
  unit_left := by intro value; rfl
  unit_right := by intro value; cases value <;> rfl
  type_preserve := by simp

noncomputable def ternaryInteractionObject
    (system : TernaryResonanceSystem.{u}) :
    GlobalResonanceObject InteractionSort where
  Carrier := Option system.Carrier
  CellType := InteractionSort
  carrierDecidableEq := interactionCarrierDecidableEq system
  incidence := ternaryInteractionIncidence system

@[simp] theorem ternaryInteractionIncidence_resonance_some_iff
    (system : TernaryResonanceSystem.{u})
    (left right output : system.Carrier) :
    (ternaryInteractionIncidence system).resonance
        (some left) (some right) (some output) ↔
      system.resonance left right output := by
  rfl

theorem ternaryInteractionIncidence_approxBisim_total
    (system : TernaryResonanceSystem.{u})
    (first second : Option system.Carrier) :
    approxBisim (ternaryInteractionIncidence system) first second := by
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro left right _
  refine ⟨rfl, ?_⟩
  simp [boundaryMatched, ternaryInteractionIncidence]

noncomputable def ternaryInteractionMap
    {source target : TernaryResonanceSystem.{u}}
    (hom : source ⟶ target) :
    ternaryInteractionObject source ⟶ ternaryInteractionObject target where
  structured := {
    toFun := Option.map hom.toFun
    map_unit := rfl
    map_glue := by
      intro left right output selected
      cases left <;> cases right <;> cases output <;>
        simp [ternaryInteractionObject, ternaryInteractionIncidence,
          freeUnitInteractionGlue] at selected ⊢
      all_goals simp_all
    map_boundary := by
      intro value endpoint member
      simp [ternaryInteractionObject, ternaryInteractionIncidence] at member
    map_resonance := by
      intro left right output resonant
      cases left <;> cases right <;> cases output <;>
        simp [ternaryInteractionObject, ternaryInteractionIncidence,
          freeUnitInteractionResonance] at resonant ⊢
      all_goals first | exact hom.preserves resonant | simp_all }
  map_bisimulation := fun _ =>
    by
      change approxBisim (ternaryInteractionIncidence target) _ _
      exact ternaryInteractionIncidence_approxBisim_total target _ _

noncomputable def ternaryInteractionRepresentationFunctor :
    TernaryResonanceSystem.{u} ⥤ GlobalResonanceObject InteractionSort where
  obj := ternaryInteractionObject
  map := ternaryInteractionMap
  map_id := by
    intro system
    apply GlobalResonanceHom.ext
    funext value
    change Option.map (fun item => item) value = value
    cases value <;>
      rfl
  map_comp := by
    intro source middle target before after
    apply GlobalResonanceHom.ext
    funext value
    change Option.map (after.toFun ∘ before.toFun) value =
      Option.map after.toFun (Option.map before.toFun value)
    cases value <;>
      rfl

theorem ternaryInteractionRepresentationFunctor_faithful
    {source target : TernaryResonanceSystem.{u}} :
    Function.Injective
      (fun hom : (source ⟶ target) =>
        ternaryInteractionRepresentationFunctor.map hom) := by
  intro first second equal
  apply TernaryResonanceHom.ext
  funext value
  have mapped := congrFun
    (congrArg (fun hom : ternaryInteractionObject source ⟶
        ternaryInteractionObject target => hom.structured.toFun) equal)
    (some value)
  simp [ternaryInteractionRepresentationFunctor, ternaryInteractionMap] at mapped
  exact Option.some.inj mapped

instance ternaryInteractionRepresentationFunctorFaithful :
    Functor.Faithful ternaryInteractionRepresentationFunctor where
  map_injective := by
    intro source target first second equal
    exact ternaryInteractionRepresentationFunctor_faithful equal

def nonunitResonanceSystem {Role : Type u}
    (object : GlobalResonanceObject Role) :
    TernaryResonanceSystem where
  Carrier := { value : object.Carrier // value ≠ object.incidence.unit }
  resonance := fun left right output =>
    object.incidence.resonance left.val right.val output.val

def ternaryInteractionEncode (system : TernaryResonanceSystem.{u}) :
    system ⟶ nonunitResonanceSystem (ternaryInteractionObject system) where
  toFun := fun value => ⟨some value, by simp [ternaryInteractionObject,
    ternaryInteractionIncidence]⟩
  preserves := by
    intro left right output resonant
    change freeUnitInteractionResonance system
      (some left) (some right) (some output)
    exact resonant

def ternaryInteractionDecodeCarrier
    (system : TernaryResonanceSystem.{u})
    (value : (nonunitResonanceSystem
      (ternaryInteractionObject system)).Carrier) : system.Carrier := by
  cases selected : value.val with
  | none =>
      exfalso
      apply value.property
      simpa [ternaryInteractionObject, ternaryInteractionIncidence] using selected
  | some result => exact result

def ternaryInteractionDecode (system : TernaryResonanceSystem.{u}) :
    nonunitResonanceSystem (ternaryInteractionObject system) ⟶ system where
  toFun := ternaryInteractionDecodeCarrier system
  preserves := by
    intro left right output resonant
    rcases left with ⟨left, leftNonunit⟩
    rcases right with ⟨right, rightNonunit⟩
    rcases output with ⟨output, outputNonunit⟩
    cases left with
    | none =>
      apply (leftNonunit ?_).elim
      simp [ternaryInteractionObject, ternaryInteractionIncidence]
    | some left =>
      cases right with
      | none =>
        apply (rightNonunit ?_).elim
        simp [ternaryInteractionObject, ternaryInteractionIncidence]
      | some right =>
        cases output with
        | none =>
          apply (outputNonunit ?_).elim
          simp [ternaryInteractionObject, ternaryInteractionIncidence]
        | some output =>
          change system.resonance left right output
          exact resonant

def ternaryInteractionRepresentationIso
    (system : TernaryResonanceSystem.{u}) :
    system ≅ nonunitResonanceSystem (ternaryInteractionObject system) where
  hom := ternaryInteractionEncode system
  inv := ternaryInteractionDecode system
  hom_inv_id := by
    apply TernaryResonanceHom.ext
    funext value
    rfl
  inv_hom_id := by
    apply TernaryResonanceHom.ext
    funext value
    rcases value with ⟨value, nonunit⟩
    cases value with
    | none =>
      apply (nonunit ?_).elim
      simp [ternaryInteractionObject, ternaryInteractionIncidence]
    | some value => rfl

/- The representation theorem combines exact relation reflection on the data
sector, categorical faithfulness on maps, and recovery up to isomorphism. -/
structure TernaryInteractionRepresentationTheorem
    (system : TernaryResonanceSystem.{u}) : Prop where
  exact_on_data : ∀ left right output,
    (ternaryInteractionIncidence system).resonance
        (some left) (some right) (some output) ↔
      system.resonance left right output
  recoverable : Nonempty
    (system ≅ nonunitResonanceSystem (ternaryInteractionObject system))

theorem ternaryInteractionRepresentationTheorem
    (system : TernaryResonanceSystem.{u}) :
    TernaryInteractionRepresentationTheorem system where
  exact_on_data := ternaryInteractionIncidence_resonance_some_iff system
  recoverable := ⟨ternaryInteractionRepresentationIso system⟩

end IncidenceCore
