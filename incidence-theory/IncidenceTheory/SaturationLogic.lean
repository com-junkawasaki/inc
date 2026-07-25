import IncidenceTheory.CarrierSurjectiveSaturation

namespace IncidenceCore

universe u

def ResonanceFormula.Positive : ResonanceFormula → Prop
  | .truth | .falsity | .atom _ _ _ => True
  | .and first second | .or first second => first.Positive ∧ second.Positive
  | .implication _ _ => False

theorem ResonanceFormula.realize_mono_of_positive
    {I : Type u} {source target : I → I → I → Prop}
    (included : ∀ {left right output}, source left right output →
      target left right output)
    {formula : ResonanceFormula} (positive : formula.Positive)
    (valuation : ResonanceVariable → I) :
    formula.Realize source valuation → formula.Realize target valuation := by
  induction formula with
  | truth => intro; trivial
  | falsity => intro impossible; exact impossible
  | atom firstVar secondVar resultVar => exact included
  | and first second firstIH secondIH =>
      rintro ⟨firstTrue, secondTrue⟩
      exact ⟨firstIH positive.1 firstTrue, secondIH positive.2 secondTrue⟩
  | or first second firstIH secondIH =>
      intro disjunction
      exact disjunction.elim
        (fun firstTrue => Or.inl (firstIH positive.1 firstTrue))
        (fun secondTrue => Or.inr (secondIH positive.2 secondTrue))
  | implication first second firstIH secondIH => contradiction

theorem ResonanceFormula.realize_saturation_of_positive
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {formula : ResonanceFormula} (positive : formula.Positive)
    (valuation : ResonanceVariable → I) :
    formula.Realize inc.resonance valuation →
      formula.Realize (bisimulationResonanceSaturation inc).resonance
        valuation :=
  formula.realize_mono_of_positive
    (fun resonant => resonance_implies_bisimulationResonanceSaturation resonant)
    positive valuation

theorem ResonanceFormula.realize_congr_of_relation_iff
    {I : Type u} {first second : I → I → I → Prop}
    (same : ∀ left right output,
      first left right output ↔ second left right output)
    (formula : ResonanceFormula) (valuation : ResonanceVariable → I) :
    formula.Realize first valuation ↔ formula.Realize second valuation := by
  induction formula with
  | truth => exact Iff.rfl
  | falsity => exact Iff.rfl
  | atom firstVar secondVar resultVar => exact same _ _ _
  | and firstFormula secondFormula firstIH secondIH =>
      exact and_congr firstIH secondIH
  | or firstFormula secondFormula firstIH secondIH =>
      exact or_congr firstIH secondIH
  | implication firstFormula secondFormula firstIH secondIH =>
      exact imp_congr firstIH secondIH

theorem ResonanceFormula.realize_saturation_iff_of_congruent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (congruent : QuotientResonanceCongruent inc)
    (formula : ResonanceFormula) (valuation : ResonanceVariable → I) :
    formula.Realize (bisimulationResonanceSaturation inc).resonance valuation ↔
      formula.Realize inc.resonance valuation := by
  apply formula.realize_congr_of_relation_iff
  exact (bisimulationResonanceSaturation_eq_self_iff inc).mpr congruent

def resonanceFormulaValuation (left right output : I) : ResonanceVariable → I
  | .left => left
  | .right => right
  | .output => output

theorem all_formula_saturation_conservative_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (∀ formula : ResonanceFormula, ∀ valuation : ResonanceVariable → I,
      formula.Realize (bisimulationResonanceSaturation inc).resonance valuation ↔
        formula.Realize inc.resonance valuation) ↔
      QuotientResonanceCongruent inc := by
  constructor
  · intro conservative
    apply (bisimulationResonanceSaturation_eq_self_iff inc).mp
    intro left right output
    simpa [resonanceObservationFormula, ResonanceFormula.Realize,
      resonanceFormulaValuation] using
      conservative resonanceObservationFormula
        (resonanceFormulaValuation left right output)
  · intro congruent formula valuation
    exact formula.realize_saturation_iff_of_congruent congruent valuation

theorem all_formula_bisimulationInvariant_iff_saturation_conservative
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (∀ formula : ResonanceFormula, formula.BisimulationInvariant inc) ↔
      ∀ formula : ResonanceFormula, ∀ valuation : ResonanceVariable → I,
        formula.Realize (bisimulationResonanceSaturation inc).resonance valuation ↔
          formula.Realize inc.resonance valuation := by
  rw [← quotientResonanceCongruent_iff_all_formula_invariant,
    all_formula_saturation_conservative_iff]

theorem saturation_all_formula_bisimulationInvariant
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : ResonanceFormula) :
    formula.BisimulationInvariant (bisimulationResonanceSaturation inc) :=
  formula.bisimulationInvariant_of_congruent
    (quotientResonanceCongruent_of_exact_descent
      (bisimulationResonanceSaturation_exactDescent inc))

theorem simplex_saturation_logic_strict :
    let valuation := resonanceFormulaValuation
      SimplexId.v1 SimplexId.face SimplexId.face
    resonanceObservationFormula.Realize
        (bisimulationResonanceSaturation simplexIncidence).resonance valuation ∧
      ¬ resonanceObservationFormula.Realize simplexIncidence.resonance valuation := by
  simpa [resonanceObservationFormula, ResonanceFormula.Realize,
    resonanceFormulaValuation] using simplex_bisimulationResonanceSaturation_strict

theorem ResonanceFormula.toIncProof_saturation_of_positive
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (encode : I → HFSet)
    (referenceTruth : ReferenceFoundation.Formula → Prop)
    (sourceTruth saturatedTruth : HFSet → HFSet → HFSet → Prop)
    (sourceAgrees : ∀ left right output,
      sourceTruth (encode left) (encode right) (encode output) ↔
        inc.resonance left right output)
    (saturatedAgrees : ∀ left right output,
      saturatedTruth (encode left) (encode right) (encode output) ↔
        (bisimulationResonanceSaturation inc).resonance left right output)
    {formula : ResonanceFormula} (positive : formula.Positive)
    (valuation : ResonanceVariable → I) :
    (formula.toIncProof encode valuation).RealizeWith
        referenceTruth sourceTruth →
      (formula.toIncProof encode valuation).RealizeWith
        referenceTruth saturatedTruth := by
  rw [formula.toIncProof_realize_iff encode referenceTruth sourceTruth
    sourceAgrees valuation,
    formula.toIncProof_realize_iff encode referenceTruth saturatedTruth
      saturatedAgrees valuation]
  exact formula.realize_saturation_of_positive positive valuation

theorem all_translatedIncProof_saturation_conservative_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (encode : I → HFSet)
    (referenceTruth : ReferenceFoundation.Formula → Prop)
    (sourceTruth saturatedTruth : HFSet → HFSet → HFSet → Prop)
    (sourceAgrees : ∀ left right output,
      sourceTruth (encode left) (encode right) (encode output) ↔
        inc.resonance left right output)
    (saturatedAgrees : ∀ left right output,
      saturatedTruth (encode left) (encode right) (encode output) ↔
        (bisimulationResonanceSaturation inc).resonance left right output) :
    (∀ formula : ResonanceFormula, ∀ valuation : ResonanceVariable → I,
      (formula.toIncProof encode valuation).RealizeWith
          referenceTruth saturatedTruth ↔
        (formula.toIncProof encode valuation).RealizeWith
          referenceTruth sourceTruth) ↔
      QuotientResonanceCongruent inc := by
  rw [← all_formula_saturation_conservative_iff inc]
  constructor <;> intro conservative formula valuation
  · rw [← formula.toIncProof_realize_iff encode referenceTruth saturatedTruth
        saturatedAgrees valuation,
      ← formula.toIncProof_realize_iff encode referenceTruth sourceTruth
        sourceAgrees valuation]
    exact conservative formula valuation
  · rw [formula.toIncProof_realize_iff encode referenceTruth saturatedTruth
        saturatedAgrees valuation,
      formula.toIncProof_realize_iff encode referenceTruth sourceTruth
        sourceAgrees valuation]
    exact conservative formula valuation

end IncidenceCore
