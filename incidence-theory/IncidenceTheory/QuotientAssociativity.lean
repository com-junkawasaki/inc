import IncidenceTheory.AssociativeSaturation

namespace IncidenceCore

universe u

def QuotientResonanceAssociative
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop :=
  ∀ left right third output : IncidenceQuotient inc,
    (∃ middle,
      quotientResonance inc left right middle ∧
      quotientResonance inc middle third output) ↔
    (∃ middle,
      quotientResonance inc right third middle ∧
      quotientResonance inc left middle output)

theorem saturation_resonance_iff_quotientResonance
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (left right output : I) :
    (bisimulationResonanceSaturation inc).resonance left right output ↔
      quotientResonance inc
        (Quotient.mk (approxBisimSetoid inc) left)
        (Quotient.mk (approxBisimSetoid inc) right)
        (Quotient.mk (approxBisimSetoid inc) output) :=
  Iff.rfl

def saturationAssociativeResonanceSpecOfQuotient
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (quotientAssociative : QuotientResonanceAssociative inc) :
    AssociativeResonanceSpec (bisimulationResonanceSaturation inc) where
  reassociate := by
    intro left right third output
    constructor
    · rintro ⟨middle, first, second⟩
      have quotientChain := (quotientAssociative
        (Quotient.mk (approxBisimSetoid inc) left)
        (Quotient.mk (approxBisimSetoid inc) right)
        (Quotient.mk (approxBisimSetoid inc) third)
        (Quotient.mk (approxBisimSetoid inc) output)).mp
        ⟨Quotient.mk (approxBisimSetoid inc) middle, first, second⟩
      rcases quotientChain with ⟨quotientMiddle, firstQ, secondQ⟩
      rcases quotient_mk_surjective inc quotientMiddle with
        ⟨representative, representativeEq⟩
      refine ⟨representative, ?_, ?_⟩
      · change quotientResonance inc
          (Quotient.mk (approxBisimSetoid inc) right)
          (Quotient.mk (approxBisimSetoid inc) third)
          (Quotient.mk (approxBisimSetoid inc) representative)
        rw [representativeEq]
        exact firstQ
      · change quotientResonance inc
          (Quotient.mk (approxBisimSetoid inc) left)
          (Quotient.mk (approxBisimSetoid inc) representative)
          (Quotient.mk (approxBisimSetoid inc) output)
        rw [representativeEq]
        exact secondQ
    · rintro ⟨middle, first, second⟩
      have quotientChain := (quotientAssociative
        (Quotient.mk (approxBisimSetoid inc) left)
        (Quotient.mk (approxBisimSetoid inc) right)
        (Quotient.mk (approxBisimSetoid inc) third)
        (Quotient.mk (approxBisimSetoid inc) output)).mpr
        ⟨Quotient.mk (approxBisimSetoid inc) middle, first, second⟩
      rcases quotientChain with ⟨quotientMiddle, firstQ, secondQ⟩
      rcases quotient_mk_surjective inc quotientMiddle with
        ⟨representative, representativeEq⟩
      refine ⟨representative, ?_, ?_⟩
      · change quotientResonance inc
          (Quotient.mk (approxBisimSetoid inc) left)
          (Quotient.mk (approxBisimSetoid inc) right)
          (Quotient.mk (approxBisimSetoid inc) representative)
        rw [representativeEq]
        exact firstQ
      · change quotientResonance inc
          (Quotient.mk (approxBisimSetoid inc) representative)
          (Quotient.mk (approxBisimSetoid inc) third)
          (Quotient.mk (approxBisimSetoid inc) output)
        rw [representativeEq]
        exact secondQ

theorem quotientResonanceAssociativeOfSaturation
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (saturatedAssociative :
      AssociativeResonanceSpec (bisimulationResonanceSaturation inc)) :
    QuotientResonanceAssociative inc := by
  intro left right third output
  induction left using Quotient.ind with
  | _ left =>
    induction right using Quotient.ind with
    | _ right =>
      induction third using Quotient.ind with
      | _ third =>
        induction output using Quotient.ind with
        | _ output =>
          constructor
          · rintro ⟨middle, first, second⟩
            induction middle using Quotient.ind with
            | _ middle =>
              rcases saturatedAssociative.reassociate.mp
                ⟨middle, first, second⟩ with
                ⟨newMiddle, newFirst, newSecond⟩
              exact ⟨Quotient.mk (approxBisimSetoid inc) newMiddle,
                newFirst, newSecond⟩
          · rintro ⟨middle, first, second⟩
            induction middle using Quotient.ind with
            | _ middle =>
              rcases saturatedAssociative.reassociate.mpr
                ⟨middle, first, second⟩ with
                ⟨newMiddle, newFirst, newSecond⟩
              exact ⟨Quotient.mk (approxBisimSetoid inc) newMiddle,
                newFirst, newSecond⟩

theorem saturation_associative_iff_quotientResonanceAssociative
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    Nonempty (AssociativeResonanceSpec
        (bisimulationResonanceSaturation inc)) ↔
      QuotientResonanceAssociative inc := by
  constructor
  · rintro ⟨associative⟩
    exact quotientResonanceAssociativeOfSaturation associative
  · intro associative
    exact ⟨saturationAssociativeResonanceSpecOfQuotient associative⟩

theorem quotientResonanceAssociative_of_transport
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (associative : AssociativeResonanceSpec inc)
    (transport : BisimulationResonanceSpec inc) :
    QuotientResonanceAssociative inc :=
  quotientResonanceAssociativeOfSaturation
    (saturationAssociativeResonanceSpec associative transport)

structure IncDepRawQuotientAssociativeCompletion
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  structural : IncDepRawNormalizedBasicPreservation
  resonance : ResonanceSpec inc
  quotientAssociative : QuotientResonanceAssociative inc

noncomputable def IncDepRawQuotientAssociativeCompletion.saturate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawQuotientAssociativeCompletion inc) :
    IncDepRawNormalizedResonanceCompletion
      (bisimulationResonanceSaturation inc) where
  structural := completion.structural
  resonance := saturationResonanceSpec completion.resonance
  associative := saturationAssociativeResonanceSpecOfQuotient
    completion.quotientAssociative
  quotientCongruent := quotientResonanceCongruent_of_exact_descent
    (bisimulationResonanceSaturation_exactDescent inc)

noncomputable def boolTrivialQuotientAssociativeCompletion :
    IncDepRawQuotientAssociativeCompletion boolTrivialIncidence where
  structural := incDepRawNormalizedBasicPreservation
  resonance := boolTrivialResonanceSpec
  quotientAssociative := quotientResonanceAssociative_of_transport
    boolTrivialAssociativeResonanceSpec
    boolTrivialBisimulationResonanceSpec

end IncidenceCore
