import IncidenceTheory.FoundationCompletion
import IncidenceTheory.SaturationLogic

namespace IncidenceCore

universe u

theorem IncDepRawNormalizedResonanceCompletion.saturation_resonance_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawNormalizedResonanceCompletion inc)
    (left right output : I) :
    (bisimulationResonanceSaturation inc).resonance left right output ↔
      inc.resonance left right output :=
  (bisimulationResonanceSaturation_eq_self_iff inc).mpr
    completion.quotientCongruent left right output

noncomputable def IncDepRawNormalizedResonanceCompletion.saturate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawNormalizedResonanceCompletion inc) :
    IncDepRawNormalizedResonanceCompletion
      (bisimulationResonanceSaturation inc) where
  structural := completion.structural
  resonance := {
    symmetric := by
      intro left right output resonant
      apply (completion.saturation_resonance_iff right left output).mpr
      exact completion.resonance.symmetric
        ((completion.saturation_resonance_iff left right output).mp resonant)
    unit_left := by
      intro value
      exact resonance_implies_bisimulationResonanceSaturation
        (completion.resonance.unit_left value)
    unit_right := by
      intro value
      exact resonance_implies_bisimulationResonanceSaturation
        (completion.resonance.unit_right value)
    type_compatible := by
      intro left right output resonant
      exact completion.resonance.type_compatible
        ((completion.saturation_resonance_iff left right output).mp resonant) }
  associative := {
    reassociate := by
      intro left right third output
      simp_rw [completion.saturation_resonance_iff]
      exact completion.associative.reassociate }
  quotientCongruent := quotientResonanceCongruent_of_exact_descent
    (bisimulationResonanceSaturation_exactDescent inc)

@[simp] theorem IncDepRawNormalizedResonanceCompletion.saturate_structural
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawNormalizedResonanceCompletion inc) :
    completion.saturate.structural = completion.structural := rfl

theorem IncDepRawNormalizedResonanceCompletion.saturate_renameFormation
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawNormalizedResonanceCompletion inc)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {formation : IncDepRawWellFormed source type}
    (ready : IncDepRawFormationDispatchReady formation)
    (renameMap : IncDepRawRenaming source target) :
    completion.saturate.structural.renameFormation ready renameMap =
      completion.structural.renameFormation ready renameMap := rfl

theorem IncDepRawNormalizedResonanceCompletion.saturate_renameTyping
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawNormalizedResonanceCompletion inc)
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType source term type}
    (ready : IncDepRawTypingDispatchReady typing)
    (renameMap : IncDepRawRenaming source target) :
    completion.saturate.structural.renameTyping ready renameMap =
      completion.structural.renameTyping ready renameMap := rfl

theorem IncDepRawNormalizedResonanceCompletion.saturate_substituteFormation
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawNormalizedResonanceCompletion inc)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {formation : IncDepRawWellFormed target type}
    (ready : IncDepRawFormationDispatchReady formation)
    (substitution : IncDepRawNormalizedReadinessPreservingSubstitution
      source target) :
    completion.saturate.structural.substituteFormation ready substitution =
      completion.structural.substituteFormation ready substitution := rfl

theorem IncDepRawNormalizedResonanceCompletion.saturate_substituteTyping
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepRawNormalizedResonanceCompletion inc)
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType target term type}
    (ready : IncDepRawTypingDispatchReady typing)
    (substitution : IncDepRawNormalizedReadinessPreservingSubstitution
      source target) :
    completion.saturate.structural.substituteTyping ready substitution =
      completion.structural.substituteTyping ready substitution := rfl

structure IncDepSaturationCompletion
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  normalized : IncDepRawNormalizedResonanceCompletion inc
  semantics : IncDepCompletionModel.{u}

noncomputable def IncDepSaturationCompletion.saturate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepSaturationCompletion inc) :
    IncDepSaturationCompletion (bisimulationResonanceSaturation inc) where
  normalized := completion.normalized.saturate
  semantics := completion.semantics

noncomputable def IncDepSaturationCompletion.interpretTyping
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepSaturationCompletion inc)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :=
  completion.semantics.interpretTyping typing

theorem IncDepSaturationCompletion.saturate_interpretTyping
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepSaturationCompletion inc)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    completion.saturate.interpretTyping typing =
      completion.interpretTyping typing := rfl

theorem IncDepSaturationCompletion.interpretTyping_sound
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepSaturationCompletion inc)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    let input := typing.toInput completion.semantics.fiberModel
      completion.semantics.preservation
    let result := completion.interpretTyping typing
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      result.typingResult.targetTermResult.semanticTerm.substitute
        (IncDepRawSubstitutionSemanticResult.identity
          input.contextResult).semanticSubstitution :=
  completion.semantics.interpretTyping_sound typing

theorem IncDepSaturationCompletion.saturate_interpretTyping_sound
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (completion : IncDepSaturationCompletion inc)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    let input := typing.toInput completion.saturate.semantics.fiberModel
      completion.saturate.semantics.preservation
    let result := completion.saturate.interpretTyping typing
    result.formationResult.semanticFiberEquivalence.transport
        result.typingResult.sourceTermResult.semanticTerm =
      result.typingResult.targetTermResult.semanticTerm.substitute
        (IncDepRawSubstitutionSemanticResult.identity
          input.contextResult).semanticSubstitution :=
  completion.saturate.interpretTyping_sound typing

noncomputable def natIncDepSaturationCompletion
    (semantics : IncDepCompletionModel.{0}) :
    IncDepSaturationCompletion natIncidence where
  normalized := natIncDepRawNormalizedResonanceCompletion
  semantics := semantics

theorem natDependentCompletion_saturation_resonance_iff
    (left right output : Nat) :
    (bisimulationResonanceSaturation natIncidence).resonance
        left right output ↔
      natIncidence.resonance left right output :=
  natIncDepRawNormalizedResonanceCompletion.saturation_resonance_iff
    left right output

theorem natIncDepSaturationCompletion_resonance_fixed
    (_semantics : IncDepCompletionModel.{0}) (left right output : Nat) :
    (bisimulationResonanceSaturation natIncidence).resonance
        left right output ↔ natIncidence.resonance left right output :=
  natDependentCompletion_saturation_resonance_iff left right output

theorem natIncDepSaturationCompletion_interpretTyping_fixed
    (semantics : IncDepCompletionModel.{0})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (typing : IncDepCompletedTyping context term type) :
    (natIncDepSaturationCompletion semantics).saturate.interpretTyping typing =
      (natIncDepSaturationCompletion semantics).interpretTyping typing := rfl

end IncidenceCore
