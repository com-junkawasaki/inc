import IncidenceTheory.DependentGeneralSemanticPairing

namespace IncidenceCore

open CategoryTheory

/-- Remove the newest target component of a raw substitution. -/
noncomputable def IncDepRawSubstitution.tail
    {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)) :
    IncDepRawSubstitution source target where
  term index := substitution.term (index + 1)
  preserves := by
    intro position lookupType lookup
    simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
      substitution.preserves (IncDepRawLookup.there lookup)

@[simp] theorem IncDepRawSubstitution.tail_term
    {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)) (index : Nat) :
    substitution.tail.term index = substitution.term (index + 1) :=
  rfl

/-- The newest component of every substitution into a context extension has
    exactly the display type reindexed along its tail substitution. -/
noncomputable def IncDepRawSubstitution.headTyping
    {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)) :
    IncDepRawHasType source (substitution.term 0)
      (type.substitute substitution.tail.term) := by
  simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
    substitution.preserves (IncDepRawLookup.here (context := target) (type := type))

/-- Proof-relevant comprehension pairing for an arbitrary raw substitution and
    arbitrary well-typed source-side head. -/
noncomputable def IncDepRawSubstitution.extendPair
    {source target : List IncDepRawType}
    (substitution : IncDepRawSubstitution source target)
    (type : IncDepRawType) (head : IncDepRawTerm)
    (headTyping : IncDepRawHasType source head
      (type.substitute substitution.term)) :
    IncDepRawSubstitution source (type :: target) where
  term index := match index with
    | 0 => head
    | next + 1 => substitution.term next
  preserves := by
    intro position lookupType lookup
    cases lookup with
    | here =>
        simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
          headTyping
    | there previous =>
        simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
          substitution.preserves previous

@[simp] theorem IncDepRawSubstitution.extendPair_zero
    {source target : List IncDepRawType}
    (substitution : IncDepRawSubstitution source target)
    (type : IncDepRawType) (head : IncDepRawTerm)
    (headTyping : IncDepRawHasType source head
      (type.substitute substitution.term)) :
    (substitution.extendPair type head headTyping).term 0 = head :=
  rfl

@[simp] theorem IncDepRawSubstitution.extendPair_succ
    {source target : List IncDepRawType}
    (substitution : IncDepRawSubstitution source target)
    (type : IncDepRawType) (head : IncDepRawTerm)
    (headTyping : IncDepRawHasType source head
      (type.substitute substitution.term)) (index : Nat) :
    (substitution.extendPair type head headTyping).term (index + 1) =
      substitution.term index :=
  rfl

/-- Every raw substitution into a context extension has exactly the same term
    components as the pairing of its tail with its newest component.  Since raw
    substitutions retain proof-relevant typing derivations, the canonical
    equality statement is made after proof erasure. -/
theorem IncDepRawSubstitution.tail_extendPair_head_term
    {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)) :
    (substitution.tail.extendPair type (substitution.term 0)
      substitution.headTyping).term = substitution.term := by
  funext index
  cases index with
  | zero => rfl
  | succ index => rfl

theorem IncDepRawSubstitution.tail_extendPair_head_extensional
    {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)) :
    (substitution.tail.extendPair type (substitution.term 0)
      substitution.headTyping).toExtensional = substitution.toExtensional := by
  apply IncDepRawExtensionalSubstitution.ext
  exact substitution.tail_extendPair_head_term

noncomputable def IncDepRawSubstitution.tailFinite
    {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)) :
    IncDepRawFiniteSubstitution source target :=
  Quotient.mk _ substitution.tail.toExtensional

noncomputable def IncDepRawSubstitution.targetFiniteType
    {source target : List IncDepRawType} {type : IncDepRawType}
    (_substitution : IncDepRawSubstitution source (type :: target))
    (targetWellFormed : IncDepRawContext.WellFormed target)
    (typeWellFormed : IncDepRawWellFormed target type) :
    IncDepRawFiniteType
      ({ context := target, wellFormed := targetWellFormed } :
        IncDepRawFiniteContextObject) where
  raw := type
  formation := ⟨typeWellFormed⟩

/-- The exact raw decomposition descends to the expected comprehension pairing
    in the finite quotient CwF. -/
theorem IncDepRawSubstitution.finite_eq_pair_tail_head
    {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target))
    (sourceWellFormed : IncDepRawContext.WellFormed source)
    (targetWellFormed : IncDepRawContext.WellFormed target)
    (typeWellFormed : IncDepRawWellFormed target type) :
    (Quotient.mk _ substitution.toExtensional :
      IncDepRawFiniteSubstitution source (type :: target)) =
      (substitution.targetFiniteType targetWellFormed typeWellFormed).pair
        (show
          ({ context := source, wellFormed := sourceWellFormed } :
              IncDepRawFiniteContextObject) ⟶
            ({ context := target, wellFormed := targetWellFormed } :
              IncDepRawFiniteContextObject) from substitution.tailFinite)
        (substitution.term 0) ⟨substitution.headTyping⟩ := by
  apply Quotient.sound
  intro index indexLt
  cases index with
  | zero => rfl
  | succ index =>
      have outEquivalent := Quotient.exact
        (Quotient.out_eq substitution.tailFinite)
      have baseLt : index < target.length := by
        change index + 1 < (type :: target).length at indexLt
        simpa using indexLt
      exact (outEquivalent index baseLt).symm

structure IncDepRawSubstitutionDecompositionTheorem : Prop where
  componentExact : ∀ {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)),
    (substitution.tail.extendPair type (substitution.term 0)
      substitution.headTyping).term = substitution.term
  proofErasedExact : ∀ {source target : List IncDepRawType}
    {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target)),
    (substitution.tail.extendPair type (substitution.term 0)
      substitution.headTyping).toExtensional = substitution.toExtensional
  finiteExact : ∀ {source target : List IncDepRawType} {type : IncDepRawType}
    (substitution : IncDepRawSubstitution source (type :: target))
    (sourceWellFormed : IncDepRawContext.WellFormed source)
    (targetWellFormed : IncDepRawContext.WellFormed target)
    (typeWellFormed : IncDepRawWellFormed target type),
    (Quotient.mk _ substitution.toExtensional :
      IncDepRawFiniteSubstitution source (type :: target)) =
      (substitution.targetFiniteType targetWellFormed typeWellFormed).pair
        (show
          ({ context := source, wellFormed := sourceWellFormed } :
              IncDepRawFiniteContextObject) ⟶
            ({ context := target, wellFormed := targetWellFormed } :
              IncDepRawFiniteContextObject) from substitution.tailFinite)
        (substitution.term 0) ⟨substitution.headTyping⟩

theorem incDepRawSubstitutionDecompositionTheorem :
    IncDepRawSubstitutionDecompositionTheorem where
  componentExact := IncDepRawSubstitution.tail_extendPair_head_term
  proofErasedExact := IncDepRawSubstitution.tail_extendPair_head_extensional
  finiteExact := IncDepRawSubstitution.finite_eq_pair_tail_head

end IncidenceCore
