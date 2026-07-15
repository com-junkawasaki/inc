import Mathlib.SetTheory.ZFC.Basic
import IncidenceTheory.ReferenceFoundationInfinity

/-! A concrete model of the actual-infinity reference theory in Mathlib's
extensional quotient model `ZFSet`. -/

namespace IncidenceCore.ReferenceFoundation

open scoped Classical

noncomputable def zfStructure : Structure where
  Carrier := ZFSet
  membership := fun left right => left ∈ right
  constant := fun _ => ∅
  empty := ∅
  pair := fun left right => {left, right}
  union := ZFSet.sUnion
  powerset := ZFSet.powerset

theorem zf_extensionality_valid (valuation : Nat → ZFSet) :
    extensionality.Realize zfStructure valuation := by
  simp only [extensionality, Formula.Realize, Formula.iff, Term.evaluate,
    extend]
  intro left right sameMembers
  apply ZFSet.ext
  intro value
  exact ⟨(sameMembers value).1, (sameMembers value).2⟩

theorem zf_empty_valid (valuation : Nat → ZFSet) :
    emptySet.Realize zfStructure valuation := by
  simp only [emptySet, Formula.Realize, Formula.neg, Term.evaluate, extend]
  intro value member
  exact ZFSet.notMem_empty value member

theorem zf_pairing_valid (valuation : Nat → ZFSet) :
    pairing.Realize zfStructure valuation := by
  simp only [pairing, Formula.Realize, Formula.iff, Term.evaluate, extend]
  intro left right value
  exact ⟨ZFSet.mem_pair.mp, ZFSet.mem_pair.mpr⟩

theorem zf_union_valid (valuation : Nat → ZFSet) :
    unionSet.Realize zfStructure valuation := by
  simp only [unionSet, Formula.Realize, Formula.iff, Term.evaluate, extend]
  intro source value
  constructor
  · intro member
    rcases ZFSet.mem_sUnion.mp member with ⟨middle, middleSource, valueMiddle⟩
    exact ⟨middle, valueMiddle, middleSource⟩
  · rintro ⟨middle, valueMiddle, middleSource⟩
    exact ZFSet.mem_sUnion.mpr ⟨middle, middleSource, valueMiddle⟩

theorem zf_power_valid (valuation : Nat → ZFSet) :
    powerSet.Realize zfStructure valuation := by
  simp only [powerSet, Formula.Realize, Formula.iff, Term.evaluate, extend]
  intro source value
  exact ⟨fun member => ZFSet.subset_def.mp (ZFSet.mem_powerset.mp member),
    fun subset => ZFSet.mem_powerset.mpr (ZFSet.subset_def.mpr subset)⟩

theorem zf_separation_valid (body : Formula) (valuation : Nat → ZFSet) :
    (separationInstance body).Realize zfStructure valuation := by
  simp only [separationInstance, Formula.Realize, Formula.iff,
    Term.evaluate, extend]
  intro source
  let predicate : ZFSet → Prop := fun value =>
    body.Realize zfStructure (extend value (extend source valuation))
  refine ⟨ZFSet.sep predicate source, ?_⟩
  intro value
  have renamedBody :
      (body.rename (fun | 0 => 0 | n + 1 => n + 2)).Realize zfStructure
          (extend value (extend (ZFSet.sep predicate source)
            (extend source valuation))) ↔ predicate value := by
    rw [Formula.realize_rename]
    have mapsEqual :
        (extend value (extend (ZFSet.sep predicate source)
            (extend source valuation)) ∘
          (fun | 0 => 0 | n + 1 => n + 2)) =
        extend value (extend source valuation) := by
      funext index
      cases index <;> rfl
    rw [mapsEqual]
  constructor
  · intro member
    have separated := ZFSet.mem_sep.mp member
    exact ⟨separated.1, renamedBody.mpr separated.2⟩
  · rintro ⟨member, bodyValid⟩
    exact ZFSet.mem_sep.mpr ⟨member, renamedBody.mp bodyValid⟩

theorem zf_successor_eq_insert (value : ZFSet) :
    (Term.successor (.var 0)).evaluate zfStructure
      (extend value fun _ => (∅ : ZFSet)) =
      insert value value := by
  change ZFSet.sUnion {value, {value, value}} = insert value value
  apply ZFSet.ext
  intro member
  constructor
  · intro inUnion
    rcases ZFSet.mem_sUnion.mp inUnion with ⟨middle, middleOuter, memberMiddle⟩
    rcases ZFSet.mem_pair.mp middleOuter with rfl | rfl
    · exact ZFSet.mem_insert_iff.mpr (Or.inr memberMiddle)
    · have equal : member = value :=
        (ZFSet.mem_pair.mp memberMiddle).elim id id
      exact ZFSet.mem_insert_iff.mpr (Or.inl equal)
  · intro inInsert
    rcases ZFSet.mem_insert_iff.mp inInsert with memberEqual | memberValue
    · exact ZFSet.mem_sUnion.mpr
        ⟨{value, value}, ZFSet.mem_pair.mpr (Or.inr rfl),
          ZFSet.mem_pair.mpr (Or.inl memberEqual)⟩
    · exact ZFSet.mem_sUnion.mpr
        ⟨value, ZFSet.mem_pair.mpr (Or.inl rfl), memberValue⟩

theorem zf_actualInfinity_valid (valuation : Nat → ZFSet) :
    actualInfinity.Realize zfStructure valuation := by
  simp only [actualInfinity, Formula.Realize, Term.evaluate, extend]
  refine ⟨ZFSet.omega, ZFSet.omega_zero, ?_⟩
  intro value member
  change ZFSet.sUnion {value, {value, value}} ∈ ZFSet.omega
  rw [show ZFSet.sUnion {value, {value, value}} =
      (insert value value : ZFSet) by
    exact zf_successor_eq_insert value]
  exact ZFSet.omega_succ member

noncomputable def zfActualInfinityModel : Model actualInfinitySchema where
  toStructure := zfStructure
  axiom_valid := by
    intro formula valid valuation
    cases valid with
    | extensionality => exact zf_extensionality_valid valuation
    | emptySet => exact zf_empty_valid valuation
    | pairing => exact zf_pairing_valid valuation
    | unionSet => exact zf_union_valid valuation
    | powerSet => exact zf_power_valid valuation
    | boundedSeparation bounded scopedBody constFree substitutionClosed =>
        exact zf_separation_valid _ valuation
    | infinity => exact zf_actualInfinity_valid valuation

theorem zfActualInfinityFoundation_sound {formula : Sentence}
    (proof : Derives actualInfinitySchema [] formula) :
    zfActualInfinityModel.Valid formula :=
  theory_proof_valid_in_model zfActualInfinityModel proof

theorem zfActualInfinityFoundation_consistent :
    Theory.Consistent { infinity := actualInfinitySchema } := by
  intro contradiction
  have valid : zfActualInfinityModel.{0}.Valid .bot :=
    zfActualInfinityFoundation_sound contradiction
  exact valid (fun _ => (∅ : ZFSet))

end IncidenceCore.ReferenceFoundation
