import IncidenceTheory.HFSets
import IncidenceTheory.ReferenceFoundationLogic

/-!
  A concrete hereditary-finite model of the reference foundation.

  The infinity hook is intentionally interpreted by `top`; consequently this
  is a model of the finite fragment, not a claim that a hereditary-finite set
  is inductive/infinite.  The distinction is exposed in the model name and in
  the completion claim matrix.
-/

namespace IncidenceCore.ReferenceFoundation

open IncidenceCore

noncomputable def hfSetSeparate
    (predicate : HFRecursiveSet → Prop) [DecidablePred predicate] : HFSet → HFSet
  | .empty => .empty
  | .insert head tail =>
      if predicate (Quotient.mk hfRecursiveSetoid head) then
        .insert head (hfSetSeparate predicate tail)
      else
        hfSetSeparate predicate tail

theorem hfRecursiveMemberRaw_separate_iff
    (predicate : HFRecursiveSet → Prop) [DecidablePred predicate]
    (x source : HFSet) :
    HFRecursiveMemberRaw x (hfSetSeparate predicate source) ↔
      HFRecursiveMemberRaw x source ∧
        predicate (Quotient.mk hfRecursiveSetoid x) := by
  induction source with
  | empty =>
      simp only [hfSetSeparate]
      constructor
      · intro h
        rcases h 0 with ⟨member, memberEmpty, _⟩
        exact False.elim (hf_not_member_empty memberEmpty)
      · rintro ⟨h, _⟩
        rcases h 0 with ⟨member, memberEmpty, _⟩
        exact False.elim (hf_not_member_empty memberEmpty)
  | insert head tail headIH tailIH =>
      by_cases keep : predicate (Quotient.mk hfRecursiveSetoid head)
      · rw [hfSetSeparate, if_pos keep,
          hfRecursiveMemberRaw_insert_iff, tailIH,
          hfRecursiveMemberRaw_insert_iff]
        constructor
        · rintro (equalHead | ⟨memberTail, predicateX⟩)
          · refine ⟨Or.inl equalHead, ?_⟩
            have quotientEq :
                (Quotient.mk hfRecursiveSetoid x : HFRecursiveSet) =
                  Quotient.mk hfRecursiveSetoid head := Quotient.sound equalHead
            simpa only [quotientEq] using keep
          · exact ⟨Or.inr memberTail, predicateX⟩
        · rintro ⟨equalHead | memberTail, predicateX⟩
          · exact Or.inl equalHead
          · exact Or.inr ⟨memberTail, predicateX⟩
      · rw [hfSetSeparate, if_neg keep, tailIH,
          hfRecursiveMemberRaw_insert_iff]
        constructor
        · rintro ⟨memberTail, predicateX⟩
          exact ⟨Or.inr memberTail, predicateX⟩
        · rintro ⟨equalHead | memberTail, predicateX⟩
          · have quotientEq :
                (Quotient.mk hfRecursiveSetoid x : HFRecursiveSet) =
                  Quotient.mk hfRecursiveSetoid head := Quotient.sound equalHead
            exact False.elim (keep (by simpa only [quotientEq] using predicateX))
          · exact ⟨memberTail, predicateX⟩

noncomputable def hfRecursiveSeparate
    (predicate : HFRecursiveSet → Prop) (source : HFRecursiveSet) : HFRecursiveSet := by
  classical
  exact Quotient.liftOn source
    (fun raw =>
      Quotient.mk hfRecursiveSetoid (hfSetSeparate predicate raw))
    (by
      intro left right equal
      apply Quotient.sound
      apply hfRecursive_extensionality
      intro x
      rw [hfRecursiveMemberRaw_separate_iff,
        hfRecursiveMemberRaw_separate_iff]
      have sourceEq :
          (Quotient.mk hfRecursiveSetoid left : HFRecursiveSet) =
            Quotient.mk hfRecursiveSetoid right := Quotient.sound equal
      constructor
      · rintro ⟨member, holds⟩
        exact ⟨(show HFRecursiveMember
          (Quotient.mk hfRecursiveSetoid x)
          (Quotient.mk hfRecursiveSetoid right) from by
            rw [← sourceEq]
            exact member), holds⟩
      · rintro ⟨member, holds⟩
        exact ⟨(show HFRecursiveMember
          (Quotient.mk hfRecursiveSetoid x)
          (Quotient.mk hfRecursiveSetoid left) from by
            rw [sourceEq]
            exact member), holds⟩)

theorem hfRecursiveMember_separate_iff
    (predicate : HFRecursiveSet → Prop) (x source : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveSeparate predicate source) ↔
      HFRecursiveMember x source ∧ predicate x := by
  classical
  refine Quotient.inductionOn source ?_
  intro raw
  refine Quotient.inductionOn x ?_
  intro x
  exact hfRecursiveMemberRaw_separate_iff predicate x raw

def finiteInfinitySchema : InfinitySchema where
  statement := .top
  closed := fun _ => rfl
  const_free := by trivial
  substitution_closed := fun _ => rfl

def hfRecursiveStructure : Structure where
  Carrier := HFRecursiveSet
  membership := HFRecursiveMember
  constant := fun _ => hfRecursiveEmpty
  empty := hfRecursiveEmpty
  pair := hfRecursivePair
  union := hfRecursiveBigUnion
  powerset := hfRecursivePower

theorem hfRecursive_extensionality_valid
    (valuation : Nat → HFRecursiveSet) :
    extensionality.Realize hfRecursiveStructure valuation := by
  simp only [extensionality, Formula.Realize, Formula.iff, Term.evaluate, extend]
  intro left right sameMembers
  apply hfRecursiveSet_extensionality
  intro value
  exact ⟨(sameMembers value).1, (sameMembers value).2⟩

theorem hfRecursive_empty_valid
    (valuation : Nat → HFRecursiveSet) :
    emptySet.Realize hfRecursiveStructure valuation := by
  intro value member
  exact hfRecursiveMember_empty value member

theorem hfRecursive_pairing_valid
    (valuation : Nat → HFRecursiveSet) :
    pairing.Realize hfRecursiveStructure valuation := by
  simp only [pairing, Formula.Realize, Formula.iff, Term.evaluate, extend]
  intro left right value
  exact ⟨(hfRecursiveMember_pair_iff value left right).mp,
    (hfRecursiveMember_pair_iff value left right).mpr⟩

theorem hfRecursive_union_valid
    (valuation : Nat → HFRecursiveSet) :
    unionSet.Realize hfRecursiveStructure valuation := by
  simp only [unionSet, Formula.Realize, Formula.iff, Term.evaluate, extend]
  intro source value
  constructor
  · intro member
    rcases (hfRecursiveMember_bigUnion_iff value source).mp member with
      ⟨middle, middleSource, valueMiddle⟩
    exact ⟨middle, valueMiddle, middleSource⟩
  · rintro ⟨middle, valueMiddle, middleSource⟩
    exact (hfRecursiveMember_bigUnion_iff value source).mpr
      ⟨middle, middleSource, valueMiddle⟩

theorem hfRecursive_power_valid
    (valuation : Nat → HFRecursiveSet) :
    powerSet.Realize hfRecursiveStructure valuation := by
  simp only [powerSet, Formula.Realize, Formula.iff, Term.evaluate, extend]
  intro source subset
  exact ⟨(hfRecursiveMember_power_iff_subset subset source).mp,
    (hfRecursiveMember_power_iff_subset subset source).mpr⟩

theorem hfRecursive_separation_valid (body : Formula)
    (valuation : Nat → HFRecursiveSet) :
    (separationInstance body).Realize hfRecursiveStructure valuation := by
  simp only [separationInstance, Formula.Realize, Formula.iff,
    Term.evaluate, extend]
  intro source
  let predicate : HFRecursiveSet → Prop := fun value =>
    body.Realize hfRecursiveStructure (extend value (extend source valuation))
  refine ⟨hfRecursiveSeparate predicate source, ?_⟩
  intro value
  have renamedBody :
      (body.rename (fun | 0 => 0 | n + 1 => n + 2)).Realize
          hfRecursiveStructure
          (extend value (extend (hfRecursiveSeparate predicate source)
            (extend source valuation))) ↔ predicate value := by
    rw [Formula.realize_rename]
    have mapsEqual :
        (extend value (extend (hfRecursiveSeparate predicate source)
            (extend source valuation)) ∘
          (fun | 0 => 0 | n + 1 => n + 2)) =
        extend value (extend source valuation) := by
      funext index
      cases index <;> rfl
    rw [mapsEqual]
  constructor
  · intro member
    have separated :=
      (hfRecursiveMember_separate_iff predicate value source).mp member
    exact ⟨separated.1, renamedBody.mpr separated.2⟩
  · rintro ⟨member, bodyValid⟩
    exact (hfRecursiveMember_separate_iff predicate value source).mpr
      ⟨member, renamedBody.mp bodyValid⟩

def hfRecursiveModel : Model finiteInfinitySchema where
  toStructure := hfRecursiveStructure
  axiom_valid := by
    intro formula valid valuation
    cases valid with
    | extensionality => exact hfRecursive_extensionality_valid valuation
    | emptySet => exact hfRecursive_empty_valid valuation
    | pairing => exact hfRecursive_pairing_valid valuation
    | unionSet => exact hfRecursive_union_valid valuation
    | powerSet => exact hfRecursive_power_valid valuation
    | boundedSeparation bounded scopedBody constFree substitutionClosed =>
        exact hfRecursive_separation_valid _ valuation
    | infinity =>
        simp [finiteInfinitySchema, Formula.top, Formula.Realize]

theorem hfReferenceFoundation_sound {formula : Sentence}
    (proof : Derives finiteInfinitySchema [] formula) :
    hfRecursiveModel.Valid formula :=
  theory_proof_valid_in_model hfRecursiveModel proof

theorem hfReferenceFoundation_consistent :
    Theory.Consistent { infinity := finiteInfinitySchema } := by
  intro contradiction
  have valid := hfReferenceFoundation_sound contradiction
  exact valid (fun _ => hfRecursiveEmpty)

end IncidenceCore.ReferenceFoundation
