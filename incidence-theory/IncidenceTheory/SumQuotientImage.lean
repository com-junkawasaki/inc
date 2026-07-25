import IncidenceTheory.IncidenceResearch

/-!
  The reachable image of the canonical sum-quotient classifier.

  `SumQuotient.lean` proves unique factorization, and
  `IncidenceResearch.lean` lifts that factorization to resonance morphisms.
  Here the codomain is restricted to observations that actually occur. Under
  `SumQuotientControlSpec`, the resulting factorization is bijective and then
  upgraded to an isomorphism of ternary resonance systems.
-/

namespace IncidenceCore

universe u

open CategoryTheory

/-- Under control, the canonical classifier has exactly bisimilarity as its
kernel. The reverse implication uses only the classifier shape; control is
needed for the forward invariance implication. -/
theorem sumQuotientClassifier_eq_iff_approxBisim
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) {x y : I1 ⊕ I2} :
    sumQuotientClassifier inc1 inc2 x =
        sumQuotientClassifier inc1 inc2 y ↔
      approxBisim (incidenceSum inc1 inc2) x y := by
  constructor
  · intro equal
    rcases x with a | a <;> rcases y with b | b
    · simp only [sumQuotientClassifier] at equal
      have pairEqual := Sum.inl.inj equal
      exact incidenceSum_lift_left inc1 inc2
        (Quotient.exact (congrArg Prod.fst pairEqual))
    · simp only [sumQuotientClassifier] at equal
      exact Sum.noConfusion equal
    · simp only [sumQuotientClassifier] at equal
      exact Sum.noConfusion equal
    · simp only [sumQuotientClassifier] at equal
      have ab := Sum.inr.inj equal
      subst b
      exact approxBisim_refl _ _
  · intro related
    exact (sumQuotientControl_iff_classifier_invariant inc1 inc2).mp
      ⟨control⟩ related

/-- Only canonical observations that are represented by an actual sum value. -/
def SumQuotientClassifierImage
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :=
  { observed : (Quotient (approxBisimSetoid inc1) × Bool) ⊕ I2 //
    ∃ value, sumQuotientClassifier inc1 inc2 value = observed }

/-- The direct-image resonance restricted to reachable classifier values. -/
def sumQuotientClassifierImageResonanceSystem
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    TernaryResonanceSystem where
  Carrier := SumQuotientClassifierImage inc1 inc2
  resonance := fun left right output =>
    ∃ leftRep rightRep outputRep,
      (⟨sumQuotientClassifier inc1 inc2 leftRep, ⟨leftRep, rfl⟩⟩ :
          SumQuotientClassifierImage inc1 inc2) = left ∧
      (⟨sumQuotientClassifier inc1 inc2 rightRep, ⟨rightRep, rfl⟩⟩ :
          SumQuotientClassifierImage inc1 inc2) = right ∧
      (⟨sumQuotientClassifier inc1 inc2 outputRep, ⟨outputRep, rfl⟩⟩ :
          SumQuotientClassifierImage inc1 inc2) = output ∧
      (incidenceSum inc1 inc2).resonance leftRep rightRep outputRep

def sumQuotientClassifierImageHom
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    TernaryResonanceHom (incidenceSum inc1 inc2).resonanceSystem
      (sumQuotientClassifierImageResonanceSystem inc1 inc2) where
  toFun := fun value =>
    ⟨sumQuotientClassifier inc1 inc2 value, ⟨value, rfl⟩⟩
  preserves := by
    intro left right output resonant
    exact ⟨left, right, output, rfl, rfl, rfl, resonant⟩

/-- The direct-image relation is the least resonance on the reachable image
for which the classifier preserves source resonance. -/
theorem sumQuotientClassifierImageResonance_least
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (candidate : SumQuotientClassifierImage inc1 inc2 →
      SumQuotientClassifierImage inc1 inc2 →
      SumQuotientClassifierImage inc1 inc2 → Prop)
    (preserves : ∀ {left right output},
      (incidenceSum inc1 inc2).resonance left right output →
        candidate
          ⟨sumQuotientClassifier inc1 inc2 left, ⟨left, rfl⟩⟩
          ⟨sumQuotientClassifier inc1 inc2 right, ⟨right, rfl⟩⟩
          ⟨sumQuotientClassifier inc1 inc2 output, ⟨output, rfl⟩⟩) :
    ∀ {left right output},
      (sumQuotientClassifierImageResonanceSystem inc1 inc2).resonance
          left right output →
        candidate left right output := by
  rintro left right output
    ⟨leftRep, rightRep, outputRep, rfl, rfl, rfl, resonant⟩
  exact preserves resonant

theorem sumQuotientClassifierImageHom_invariant
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) :
    BisimulationInvariantResonanceHom (incidenceSum inc1 inc2)
      (sumQuotientClassifierImageResonanceSystem inc1 inc2)
      (sumQuotientClassifierImageHom inc1 inc2) := by
  intro first second related
  apply Subtype.ext
  exact (sumQuotientClassifier_eq_iff_approxBisim inc1 inc2 control).mpr
    related

def sumBisimulationQuotientToClassifierImage
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) :
    TernaryResonanceHom
      (bisimulationQuotientResonanceSystem (incidenceSum inc1 inc2))
      (sumQuotientClassifierImageResonanceSystem inc1 inc2) :=
  bisimulationQuotientResonanceLift
    (sumQuotientClassifierImageHom inc1 inc2)
    (sumQuotientClassifierImageHom_invariant inc1 inc2 control)

theorem sumBisimulationQuotientToClassifierImage_bijective
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) :
    Function.Bijective
      (sumBisimulationQuotientToClassifierImage inc1 inc2 control).toFun := by
  constructor
  · intro first second equal
    induction first using Quotient.ind with
    | _ firstRep =>
      induction second using Quotient.ind with
      | _ secondRep =>
        apply Quotient.sound
        apply (sumQuotientClassifier_eq_iff_approxBisim
          inc1 inc2 control).mp
        exact congrArg Subtype.val equal
  · intro observed
    rcases observed.property with ⟨value, realizes⟩
    refine ⟨Quotient.mk
      (approxBisimSetoid (incidenceSum inc1 inc2)) value, ?_⟩
    apply Subtype.ext
    exact realizes

noncomputable def sumBisimulationQuotientEquivClassifierImage
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) :
    IncidenceQuotient (incidenceSum inc1 inc2) ≃
      SumQuotientClassifierImage inc1 inc2 :=
  Equiv.ofBijective
    (sumBisimulationQuotientToClassifierImage inc1 inc2 control).toFun
    (sumBisimulationQuotientToClassifierImage_bijective inc1 inc2 control)

noncomputable def classifierImageToSumBisimulationQuotient
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) :
    TernaryResonanceHom
      (sumQuotientClassifierImageResonanceSystem inc1 inc2)
      (bisimulationQuotientResonanceSystem (incidenceSum inc1 inc2)) where
  toFun := (sumBisimulationQuotientEquivClassifierImage
    inc1 inc2 control).symm
  preserves := by
    rintro left right output
      ⟨leftRep, rightRep, outputRep, rfl, rfl, rfl, resonant⟩
    let equivalence :=
      sumBisimulationQuotientEquivClassifierImage inc1 inc2 control
    change quotientResonance (incidenceSum inc1 inc2)
      (equivalence.symm (equivalence
        (Quotient.mk
          (approxBisimSetoid (incidenceSum inc1 inc2)) leftRep)))
      (equivalence.symm (equivalence
        (Quotient.mk
          (approxBisimSetoid (incidenceSum inc1 inc2)) rightRep)))
      (equivalence.symm (equivalence
        (Quotient.mk
          (approxBisimSetoid (incidenceSum inc1 inc2)) outputRep)))
    rw [equivalence.symm_apply_apply, equivalence.symm_apply_apply,
      equivalence.symm_apply_apply]
    exact quotientResonance_of_resonance resonant

/-- The quotient and the reachable classifier image are isomorphic as ternary
resonance systems, not only equivalent as carrier types. -/
noncomputable def sumBisimulationQuotientIsoClassifierImage
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) :
    bisimulationQuotientResonanceSystem (incidenceSum inc1 inc2) ≅
      sumQuotientClassifierImageResonanceSystem inc1 inc2 where
  hom := sumBisimulationQuotientToClassifierImage inc1 inc2 control
  inv := classifierImageToSumBisimulationQuotient inc1 inc2 control
  hom_inv_id := by
    apply TernaryResonanceHom.ext
    funext quotient
    exact (sumBisimulationQuotientEquivClassifierImage
      inc1 inc2 control).symm_apply_apply quotient
  inv_hom_id := by
    apply TernaryResonanceHom.ext
    funext observed
    exact (sumBisimulationQuotientEquivClassifierImage
      inc1 inc2 control).apply_symm_apply observed

/-- The isomorphism gives exact resonance preservation and reflection. -/
theorem sumBisimulationQuotientIsoClassifierImage_resonance_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2)
    (left right output :
      (bisimulationQuotientResonanceSystem
        (incidenceSum inc1 inc2)).Carrier) :
    (bisimulationQuotientResonanceSystem
        (incidenceSum inc1 inc2)).resonance left right output ↔
      (sumQuotientClassifierImageResonanceSystem inc1 inc2).resonance
        ((sumBisimulationQuotientIsoClassifierImage
          inc1 inc2 control).hom.toFun left)
        ((sumBisimulationQuotientIsoClassifierImage
          inc1 inc2 control).hom.toFun right)
        ((sumBisimulationQuotientIsoClassifierImage
          inc1 inc2 control).hom.toFun output) := by
  let iso := sumBisimulationQuotientIsoClassifierImage inc1 inc2 control
  constructor
  · exact iso.hom.preserves
  · intro resonant
    have reflected := iso.inv.preserves resonant
    have functionEqual :
        (iso.hom ≫ iso.inv).toFun =
          (TernaryResonanceHom.id
            (bisimulationQuotientResonanceSystem
              (incidenceSum inc1 inc2))).toFun :=
      congrArg TernaryResonanceHom.toFun iso.hom_inv_id
    change (bisimulationQuotientResonanceSystem
      (incidenceSum inc1 inc2)).resonance
        (iso.inv.toFun (iso.hom.toFun left))
        (iso.inv.toFun (iso.hom.toFun right))
        (iso.inv.toFun (iso.hom.toFun output)) at reflected
    have leftEqual : iso.inv.toFun (iso.hom.toFun left) = left :=
      congrFun functionEqual left
    have rightEqual : iso.inv.toFun (iso.hom.toFun right) = right :=
      congrFun functionEqual right
    have outputEqual : iso.inv.toFun (iso.hom.toFun output) = output :=
      congrFun functionEqual output
    rw [leftEqual, rightEqual, outputEqual] at reflected
    exact reflected

def natCycleSumQuotientControl :
    SumQuotientControlSpec natIncidence cycleIncidenceFixed :=
  sumQuotientControlOfFaithfulNoSharedLeaves
    natIncidence cycleIncidenceFixed natIncidence_approxBisim_iff
    cycleIncidenceFixed_approxBisim_iff
    (fun value => by
      cases value <;> simp [cycleIncidenceFixed, cycleBoundaryFixed])

/-- Concrete resonance-system isomorphism for the Nat/fixed-cycle sum. -/
noncomputable def natCycleSumBisimulationQuotientIsoClassifierImage :
    bisimulationQuotientResonanceSystem
        (incidenceSum natIncidence cycleIncidenceFixed) ≅
      sumQuotientClassifierImageResonanceSystem
        natIncidence cycleIncidenceFixed :=
  sumBisimulationQuotientIsoClassifierImage natIncidence cycleIncidenceFixed
    natCycleSumQuotientControl

end IncidenceCore
