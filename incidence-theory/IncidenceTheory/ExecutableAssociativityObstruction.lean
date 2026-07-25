import IncidenceTheory.AssociativityObstruction

namespace IncidenceCore

universe u

structure ExecutableSaturationPresentation
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  bisimCheck : I → I → Bool
  resonanceCheck : I → I → I → Bool
  bisimCheck_eq_true : ∀ first second,
    bisimCheck first second = true ↔ approxBisim inc first second
  resonanceCheck_eq_true : ∀ left right output,
    resonanceCheck left right output = true ↔
      inc.resonance left right output

theorem saturation_resonance_iff_representatives
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (left right output : I) :
    (bisimulationResonanceSaturation inc).resonance left right output ↔
      ∃ sourceLeft sourceRight sourceOutput,
        approxBisim inc sourceLeft left ∧
        approxBisim inc sourceRight right ∧
        approxBisim inc sourceOutput output ∧
        inc.resonance sourceLeft sourceRight sourceOutput := by
  constructor
  · rintro ⟨sourceLeft, sourceRight, sourceOutput,
      leftEq, rightEq, outputEq, resonant⟩
    exact ⟨sourceLeft, sourceRight, sourceOutput,
      Quotient.exact leftEq, Quotient.exact rightEq,
      Quotient.exact outputEq, resonant⟩
  · rintro ⟨sourceLeft, sourceRight, sourceOutput,
      leftRelated, rightRelated, outputRelated, resonant⟩
    exact ⟨sourceLeft, sourceRight, sourceOutput,
      Quotient.sound leftRelated, Quotient.sound rightRelated,
      Quotient.sound outputRelated, resonant⟩

def ExecutableSaturationPresentation.saturationCheck
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (left right output : I) : Bool :=
  decide (∃ sourceLeft sourceRight sourceOutput,
    presentation.bisimCheck sourceLeft left = true ∧
    presentation.bisimCheck sourceRight right = true ∧
    presentation.bisimCheck sourceOutput output = true ∧
    presentation.resonanceCheck sourceLeft sourceRight sourceOutput = true)

theorem ExecutableSaturationPresentation.saturationCheck_eq_true
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (left right output : I) :
    presentation.saturationCheck left right output = true ↔
      (bisimulationResonanceSaturation inc).resonance left right output := by
  rw [saturation_resonance_iff_representatives]
  simp only [ExecutableSaturationPresentation.saturationCheck,
    decide_eq_true_eq,
    presentation.bisimCheck_eq_true, presentation.resonanceCheck_eq_true]

def ExecutableSaturationPresentation.leftChainCheck
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (left right third output : I) : Bool :=
  decide (∃ middle,
    presentation.saturationCheck left right middle = true ∧
      presentation.saturationCheck middle third output = true)

def ExecutableSaturationPresentation.rightChainCheck
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (left right third output : I) : Bool :=
  decide (∃ middle,
    presentation.saturationCheck right third middle = true ∧
      presentation.saturationCheck left middle output = true)

theorem ExecutableSaturationPresentation.leftChainCheck_eq_true
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (left right third output : I) :
    presentation.leftChainCheck left right third output = true ↔
      saturationLeftAssociated inc left right third output := by
  simp only [ExecutableSaturationPresentation.leftChainCheck,
    decide_eq_true_eq,
    saturationLeftAssociated, presentation.saturationCheck_eq_true]

theorem ExecutableSaturationPresentation.rightChainCheck_eq_true
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (left right third output : I) :
    presentation.rightChainCheck left right third output = true ↔
      saturationRightAssociated inc left right third output := by
  simp only [ExecutableSaturationPresentation.rightChainCheck,
    decide_eq_true_eq,
    saturationRightAssociated, presentation.saturationCheck_eq_true]

def ExecutableSaturationPresentation.obstructionCheck
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (candidate : SaturationAssociativityCandidate I) : Bool :=
  match candidate.direction with
  | .leftToRight =>
      presentation.leftChainCheck candidate.left candidate.right
          candidate.third candidate.output &&
        !presentation.rightChainCheck candidate.left candidate.right
          candidate.third candidate.output
  | .rightToLeft =>
      presentation.rightChainCheck candidate.left candidate.right
          candidate.third candidate.output &&
        !presentation.leftChainCheck candidate.left candidate.right
          candidate.third candidate.output

theorem ExecutableSaturationPresentation.obstructionCheck_eq_true
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (candidate : SaturationAssociativityCandidate I) :
    presentation.obstructionCheck candidate = true ↔
      candidate.IsObstruction inc := by
  cases candidate with
  | mk direction left right third output =>
    cases direction <;>
      simp [ExecutableSaturationPresentation.obstructionCheck,
        SaturationAssociativityCandidate.IsObstruction,
        Bool.eq_false_iff,
        presentation.leftChainCheck_eq_true,
        presentation.rightChainCheck_eq_true]

def ExecutableSaturationPresentation.obstructionTable
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc) :
    Finset (SaturationAssociativityCandidate I) :=
  Finset.univ.filter fun candidate => presentation.obstructionCheck candidate

theorem ExecutableSaturationPresentation.mem_obstructionTable_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc)
    (candidate : SaturationAssociativityCandidate I) :
    candidate ∈ presentation.obstructionTable ↔
      candidate.IsObstruction inc := by
  simp [ExecutableSaturationPresentation.obstructionTable,
    presentation.obstructionCheck_eq_true]

theorem ExecutableSaturationPresentation.obstructionTable_empty_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    {inc : Incidence I R T}
    (presentation : ExecutableSaturationPresentation inc) :
    presentation.obstructionTable = ∅ ↔
      QuotientResonanceAssociative inc := by
  rw [← no_saturationAssociativityObstruction_iff_quotientAssociative]
  constructor
  · intro empty ⟨candidate, obstruction⟩
    have member : candidate ∈ presentation.obstructionTable :=
      (presentation.mem_obstructionTable_iff candidate).mpr obstruction
    rw [empty] at member
    simp at member
  · intro noObstruction
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate member
    exact noObstruction ⟨candidate,
      (presentation.mem_obstructionTable_iff candidate).mp member⟩

def boolTrivialExecutableSaturationPresentation :
    ExecutableSaturationPresentation boolTrivialIncidence where
  bisimCheck := fun _ _ => true
  resonanceCheck := fun left right output =>
    decide (boolTrivialIncidence.glue left right = some output)
  bisimCheck_eq_true := by
    intro first second
    exact ⟨fun _ => trivial_approxBisim_total first second, fun _ => rfl⟩
  resonanceCheck_eq_true := by
    intro left right output
    simp [boolTrivialIncidence, trivialIncidence]

theorem boolTrivial_executable_obstructionTable_empty :
    boolTrivialExecutableSaturationPresentation.obstructionTable = ∅ := by
  native_decide

theorem boolTrivial_executable_associativity_verified :
    QuotientResonanceAssociative boolTrivialIncidence :=
  (boolTrivialExecutableSaturationPresentation.obstructionTable_empty_iff).mp
    boolTrivial_executable_obstructionTable_empty

end IncidenceCore
