import IncidenceTheory.QuotientAssociativity
import Mathlib.Tactic.DeriveFintype

namespace IncidenceCore

universe u

inductive AssociativityDirection where
  | leftToRight
  | rightToLeft
deriving DecidableEq, Fintype, Repr

structure SaturationAssociativityCandidate (I : Type u) where
  direction : AssociativityDirection
  left : I
  right : I
  third : I
  output : I
deriving DecidableEq, Fintype, Repr

def saturationLeftAssociated
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (left right third output : I) : Prop :=
  ∃ middle,
    (bisimulationResonanceSaturation inc).resonance left right middle ∧
    (bisimulationResonanceSaturation inc).resonance middle third output

def saturationRightAssociated
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (left right third output : I) : Prop :=
  ∃ middle,
    (bisimulationResonanceSaturation inc).resonance right third middle ∧
    (bisimulationResonanceSaturation inc).resonance left middle output

def SaturationAssociativityCandidate.IsObstruction
    {I R T : Type u} [DecidableEq I]
    (candidate : SaturationAssociativityCandidate I)
    (inc : Incidence I R T) : Prop :=
  match candidate.direction with
  | .leftToRight =>
      saturationLeftAssociated inc candidate.left candidate.right
          candidate.third candidate.output ∧
        ¬ saturationRightAssociated inc candidate.left candidate.right
          candidate.third candidate.output
  | .rightToLeft =>
      saturationRightAssociated inc candidate.left candidate.right
          candidate.third candidate.output ∧
        ¬ saturationLeftAssociated inc candidate.left candidate.right
          candidate.third candidate.output

theorem no_saturationAssociativityObstruction_iff_associative
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (¬ ∃ candidate : SaturationAssociativityCandidate I,
        candidate.IsObstruction inc) ↔
      Nonempty (AssociativeResonanceSpec
        (bisimulationResonanceSaturation inc)) := by
  classical
  constructor
  · intro noObstruction
    refine ⟨{ reassociate := ?_ }⟩
    intro left right third output
    constructor
    · intro leftChain
      by_contra noRightChain
      exact noObstruction ⟨{
        direction := .leftToRight
        left := left
        right := right
        third := third
        output := output }, leftChain, noRightChain⟩
    · intro rightChain
      by_contra noLeftChain
      exact noObstruction ⟨{
        direction := .rightToLeft
        left := left
        right := right
        third := third
        output := output }, rightChain, noLeftChain⟩
  · rintro ⟨associative⟩ ⟨candidate, obstruction⟩
    rcases candidate with ⟨direction, left, right, third, output⟩
    cases direction with
    | leftToRight =>
        exact obstruction.2 (associative.reassociate.mp obstruction.1)
    | rightToLeft =>
        exact obstruction.2 (associative.reassociate.mpr obstruction.1)

theorem no_saturationAssociativityObstruction_iff_quotientAssociative
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (¬ ∃ candidate : SaturationAssociativityCandidate I,
        candidate.IsObstruction inc) ↔
      QuotientResonanceAssociative inc := by
  rw [no_saturationAssociativityObstruction_iff_associative,
    saturation_associative_iff_quotientResonanceAssociative]

noncomputable def finiteSaturationAssociativityObstructions
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    Finset (SaturationAssociativityCandidate I) := by
  classical
  exact Finset.univ.filter (fun candidate => candidate.IsObstruction inc)

theorem mem_finiteSaturationAssociativityObstructions_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    (candidate : SaturationAssociativityCandidate I) :
    candidate ∈ finiteSaturationAssociativityObstructions inc ↔
      candidate.IsObstruction inc := by
  classical
  simp [finiteSaturationAssociativityObstructions]

theorem finiteSaturationAssociativityObstructions_empty_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    finiteSaturationAssociativityObstructions inc = ∅ ↔
      QuotientResonanceAssociative inc := by
  rw [← no_saturationAssociativityObstruction_iff_quotientAssociative]
  constructor
  · intro empty ⟨candidate, obstruction⟩
    have member : candidate ∈ finiteSaturationAssociativityObstructions inc :=
      (mem_finiteSaturationAssociativityObstructions_iff inc candidate).mpr
        obstruction
    rw [empty] at member
    simp at member
  · intro noObstruction
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate member
    exact noObstruction ⟨candidate,
      (mem_finiteSaturationAssociativityObstructions_iff inc candidate).mp
        member⟩

theorem finite_saturation_not_associative_iff_obstruction_exists
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    ¬ QuotientResonanceAssociative inc ↔
      (finiteSaturationAssociativityObstructions inc).Nonempty := by
  constructor
  · intro notAssociative
    rw [Finset.nonempty_iff_ne_empty]
    intro empty
    exact notAssociative
      ((finiteSaturationAssociativityObstructions_empty_iff inc).mp empty)
  · intro nonempty associative
    have empty :=
      (finiteSaturationAssociativityObstructions_empty_iff inc).mpr associative
    rw [empty] at nonempty
    exact Finset.not_nonempty_empty nonempty

theorem boolTrivial_finiteSaturationAssociativityObstructions_empty :
    finiteSaturationAssociativityObstructions boolTrivialIncidence = ∅ :=
  (finiteSaturationAssociativityObstructions_empty_iff
    boolTrivialIncidence).mpr
      boolTrivialQuotientAssociativeCompletion.quotientAssociative

end IncidenceCore
