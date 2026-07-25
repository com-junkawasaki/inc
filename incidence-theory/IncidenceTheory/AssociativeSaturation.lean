import IncidenceTheory.DependentSaturation

namespace IncidenceCore

universe u

def saturationResonanceSpec
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (spec : ResonanceSpec inc) :
    ResonanceSpec (bisimulationResonanceSaturation inc) where
  symmetric := by
    intro left right output saturated
    rcases saturated with
      ⟨sourceLeft, sourceRight, sourceOutput,
        leftEq, rightEq, outputEq, resonant⟩
    exact ⟨sourceRight, sourceLeft, sourceOutput,
      rightEq, leftEq, outputEq, spec.symmetric resonant⟩
  unit_left := fun value =>
    resonance_implies_bisimulationResonanceSaturation (spec.unit_left value)
  unit_right := fun value =>
    resonance_implies_bisimulationResonanceSaturation (spec.unit_right value)
  type_compatible := by
    intro left right output saturated
    rcases saturated with
      ⟨sourceLeft, sourceRight, sourceOutput,
        leftEq, rightEq, outputEq, resonant⟩
    have sourceTypes := spec.type_compatible resonant
    have leftType : inc.typeFunc sourceLeft = inc.typeFunc left :=
      approxBisim_typeFunc_eq (Quotient.exact leftEq)
    have rightType : inc.typeFunc sourceRight = inc.typeFunc right :=
      approxBisim_typeFunc_eq (Quotient.exact rightEq)
    have outputType : inc.typeFunc sourceOutput = inc.typeFunc output :=
      approxBisim_typeFunc_eq (Quotient.exact outputEq)
    exact ⟨leftType.symm.trans (sourceTypes.1.trans rightType),
      outputType.symm.trans (sourceTypes.2.trans leftType)⟩

def saturationAssociativeResonanceSpec
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (associative : AssociativeResonanceSpec inc)
    (transport : BisimulationResonanceSpec inc) :
    AssociativeResonanceSpec (bisimulationResonanceSaturation inc) where
  reassociate := by
    intro left right third output
    constructor
    · rintro ⟨middle, firstSaturated, secondSaturated⟩
      rcases firstSaturated with
        ⟨sourceLeft, sourceRight, firstMiddle,
          leftEq, rightEq, firstMiddleEq, firstResonant⟩
      rcases secondSaturated with
        ⟨secondMiddle, sourceThird, sourceOutput,
          secondMiddleEq, thirdEq, outputEq, secondResonant⟩
      have middlesRelated : approxBisim inc firstMiddle secondMiddle :=
        Quotient.exact (firstMiddleEq.trans secondMiddleEq.symm)
      rcases (transport.respects middlesRelated
        (approxBisim_refl inc sourceThird)).2 secondResonant with
        ⟨alignedOutput, alignedSecond, outputsRelated⟩
      rcases associative.reassociate.mp
        ⟨firstMiddle, firstResonant, alignedSecond⟩ with
        ⟨sourceRightThird, rightThirdResonant, finalResonant⟩
      refine ⟨sourceRightThird, ?_, ?_⟩
      · exact ⟨sourceRight, sourceThird, sourceRightThird,
          rightEq, thirdEq, rfl, rightThirdResonant⟩
      · exact ⟨sourceLeft, sourceRightThird, alignedOutput,
          leftEq, rfl, Quotient.sound outputsRelated |>.trans outputEq,
          finalResonant⟩
    · rintro ⟨middle, firstSaturated, secondSaturated⟩
      rcases firstSaturated with
        ⟨sourceRight, sourceThird, firstMiddle,
          rightEq, thirdEq, firstMiddleEq, firstResonant⟩
      rcases secondSaturated with
        ⟨sourceLeft, secondMiddle, sourceOutput,
          leftEq, secondMiddleEq, outputEq, secondResonant⟩
      have middlesRelated : approxBisim inc firstMiddle secondMiddle :=
        Quotient.exact (firstMiddleEq.trans secondMiddleEq.symm)
      rcases (transport.respects (approxBisim_refl inc sourceLeft)
        (approxBisim_symm middlesRelated)).1 secondResonant with
        ⟨alignedOutput, alignedSecond, outputsRelated⟩
      rcases associative.reassociate.mpr
        ⟨firstMiddle, firstResonant, alignedSecond⟩ with
        ⟨sourceLeftRight, leftRightResonant, finalResonant⟩
      refine ⟨sourceLeftRight, ?_, ?_⟩
      · exact ⟨sourceLeft, sourceRight, sourceLeftRight,
          leftEq, rightEq, rfl, leftRightResonant⟩
      · exact ⟨sourceLeftRight, sourceThird, alignedOutput,
          rfl, thirdEq,
          (Quotient.sound (approxBisim_symm outputsRelated)).trans outputEq,
          finalResonant⟩

structure IncDepRawSaturatableResonanceCompletion
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  structural : IncDepRawNormalizedBasicPreservation
  resonance : ResonanceSpec inc
  associative : AssociativeResonanceSpec inc
  transport : BisimulationResonanceSpec inc

noncomputable def IncDepRawSaturatableResonanceCompletion.saturate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawSaturatableResonanceCompletion inc) :
    IncDepRawNormalizedResonanceCompletion
      (bisimulationResonanceSaturation inc) where
  structural := completion.structural
  resonance := saturationResonanceSpec completion.resonance
  associative := saturationAssociativeResonanceSpec
    completion.associative completion.transport
  quotientCongruent := quotientResonanceCongruent_of_exact_descent
    (bisimulationResonanceSaturation_exactDescent inc)

abbrev boolTrivialIncidence : Incidence Bool GraphRole GraphType :=
  trivialIncidence

def boolTrivialResonanceSpec : ResonanceSpec boolTrivialIncidence where
  symmetric := by
    intro left right output resonant
    cases left <;> cases right <;> cases output <;>
      simp [boolTrivialIncidence, trivialIncidence] at resonant ⊢
  unit_left := by intro value; cases value <;> simp [boolTrivialIncidence,
    trivialIncidence]
  unit_right := by intro value; cases value <;> simp [boolTrivialIncidence,
    trivialIncidence]
  type_compatible := by simp [boolTrivialIncidence, trivialIncidence]

def boolTrivialAssociativeResonanceSpec :
    AssociativeResonanceSpec boolTrivialIncidence where
  reassociate := by
    intro left right third output
    cases left <;> cases right <;> cases third <;> cases output <;>
      simp [boolTrivialIncidence, trivialIncidence]

def boolTrivialBisimulationResonanceSpec :
    BisimulationResonanceSpec boolTrivialIncidence where
  respects := by
    intro left₁ left₂ right₁ right₂ leftRelated rightRelated
    constructor
    · intro output resonant
      cases left₁ <;> cases left₂ <;> cases right₁ <;> cases right₂ <;>
        cases output <;>
        simp [boolTrivialIncidence, trivialIncidence] at resonant ⊢ <;>
        try exact trivial_approxBisim_total _ _
    · intro output resonant
      cases left₁ <;> cases left₂ <;> cases right₁ <;> cases right₂ <;>
        cases output <;>
        simp [boolTrivialIncidence, trivialIncidence] at resonant ⊢ <;>
        try exact trivial_approxBisim_total _ _

theorem boolTrivialResonance_not_quotientCongruent :
    ¬ QuotientResonanceCongruent boolTrivialIncidence := by
  intro congruent
  have exactOutputs := congruent
    (approxBisim_refl boolTrivialIncidence true)
    (approxBisim_refl boolTrivialIncidence true)
    (trivial_approxBisim_total true false)
  simp [boolTrivialIncidence, trivialIncidence] at exactOutputs

noncomputable def boolTrivialSaturatableResonanceCompletion :
    IncDepRawSaturatableResonanceCompletion boolTrivialIncidence where
  structural := incDepRawNormalizedBasicPreservation
  resonance := boolTrivialResonanceSpec
  associative := boolTrivialAssociativeResonanceSpec
  transport := boolTrivialBisimulationResonanceSpec

noncomputable def boolTrivialSaturatedNormalizedCompletion :
    IncDepRawNormalizedResonanceCompletion
      (bisimulationResonanceSaturation boolTrivialIncidence) :=
  boolTrivialSaturatableResonanceCompletion.saturate

theorem boolTrivial_saturation_strict_and_associative :
    (bisimulationResonanceSaturation boolTrivialIncidence).resonance
        true true false ∧
      ¬ boolTrivialIncidence.resonance true true false ∧
      Nonempty (AssociativeResonanceSpec
        (bisimulationResonanceSaturation boolTrivialIncidence)) := by
  refine ⟨?_, ?_, ⟨boolTrivialSaturatedNormalizedCompletion.associative⟩⟩
  · change quotientResonance boolTrivialIncidence
      (Quotient.mk (approxBisimSetoid boolTrivialIncidence) true)
      (Quotient.mk (approxBisimSetoid boolTrivialIncidence) true)
      (Quotient.mk (approxBisimSetoid boolTrivialIncidence) false)
    exact ⟨true, true, true, rfl, rfl,
      Quotient.sound (trivial_approxBisim_total true false), by
        simp [boolTrivialIncidence, trivialIncidence]⟩
  · simp [boolTrivialIncidence, trivialIncidence]

end IncidenceCore
