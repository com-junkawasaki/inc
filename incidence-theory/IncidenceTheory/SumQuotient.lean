import IncidenceTheory.Quotient
import IncidenceTheory.Sum

/-!
  Universal quotient semantics for the disjoint incidence sum.

  `incidenceSum` deliberately erases the factors' type maps and uses the left
  unit as its global unit. Consequently its quotient needs to remember three
  pieces of observable information: the left bisimulation class, whether a
  left representative is the unit, and the exact right representative.
-/

universe u

namespace IncidenceCore

/-- The canonical observable carried by a sum representative. -/
def sumQuotientClassifier
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (_inc2 : Incidence I2 R2 T2) :
    I1 ⊕ I2 → (Quotient (approxBisimSetoid inc1) × Bool) ⊕ I2
  | .inl a => .inl (Quotient.mk (approxBisimSetoid inc1) a,
      decide (a = inc1.unit))
  | .inr b => .inr b

/-- Representative control is exactly invariance of the canonical classifier
under sum bisimulation. -/
theorem sumQuotientControl_iff_classifier_invariant
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    Nonempty (SumQuotientControlSpec inc1 inc2) ↔
      BisimulationInvariantMap (incidenceSum inc1 inc2)
        (sumQuotientClassifier inc1 inc2) := by
  constructor
  · rintro ⟨control⟩ x y h
    have classified := control.classify h
    rcases x with a | a <;> rcases y with b | b
    · simp only at classified
      simp only [sumQuotientClassifier]
      congr 1
      apply Prod.ext (Quotient.sound classified.1)
      by_cases ha : a = inc1.unit
      · simp [ha, classified.2.mp ha]
      · have hb : b ≠ inc1.unit := fun hb => ha (classified.2.mpr hb)
        simp [ha, hb]
    · exact False.elim classified
    · exact False.elim classified
    · exact congrArg Sum.inr classified
  · intro invariant
    refine ⟨⟨?_⟩⟩
    intro x y h
    have observed := invariant h
    rcases x with a | a <;> rcases y with b | b
    · simp only [sumQuotientClassifier] at observed
      have pairEq := Sum.inl.inj observed
      refine ⟨Quotient.exact (congrArg Prod.fst pairEq), ?_⟩
      have unitBitEq := congrArg Prod.snd pairEq
      constructor
      · intro ha
        by_cases hb : b = inc1.unit
        · exact hb
        · simp [ha, hb] at unitBitEq
      · intro hb
        by_cases ha : a = inc1.unit
        · exact ha
        · simp [ha, hb] at unitBitEq
    · simp only [sumQuotientClassifier] at observed
      exact Sum.noConfusion observed
    · simp only [sumQuotientClassifier] at observed
      exact Sum.noConfusion observed
    · simp only [sumQuotientClassifier] at observed
      exact Sum.inr.inj observed

/-- Existence and uniqueness of a factorization of the canonical classifier
through the sum's bisimulation quotient. -/
def SumQuotientClassifierFactorsUniquely
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) : Prop :=
  ∃ lift : Quotient (approxBisimSetoid (incidenceSum inc1 inc2)) →
      (Quotient (approxBisimSetoid inc1) × Bool) ⊕ I2,
    (∀ x, lift (Quotient.mk (approxBisimSetoid (incidenceSum inc1 inc2)) x) =
      sumQuotientClassifier inc1 inc2 x) ∧
    ∀ candidate : Quotient (approxBisimSetoid (incidenceSum inc1 inc2)) →
        (Quotient (approxBisimSetoid inc1) × Bool) ⊕ I2,
      (∀ x, candidate
        (Quotient.mk (approxBisimSetoid (incidenceSum inc1 inc2)) x) =
          sumQuotientClassifier inc1 inc2 x) →
      candidate = lift

/-- Universal characterization: local representative laws hold iff the
canonical observable factors uniquely through the bisimulation quotient. -/
theorem sumQuotientControl_iff_classifier_factorsUniquely
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    Nonempty (SumQuotientControlSpec inc1 inc2) ↔
      SumQuotientClassifierFactorsUniquely inc1 inc2 := by
  rw [sumQuotientControl_iff_classifier_invariant]
  constructor
  · intro invariant
    exact bisimulationQuotient_universal_property
      (incidenceSum inc1 inc2) (sumQuotientClassifier inc1 inc2) invariant
  · rintro ⟨lift, factors, _unique⟩
    exact (factors_through_bisimulationQuotient_iff_invariant
      (incidenceSum inc1 inc2) (sumQuotientClassifier inc1 inc2)).mp
      ⟨lift, factors⟩

/-- Under type reflection and left quotient congruence, sum resonance descends
precisely when the canonical observable has the unique factorization above. -/
theorem incidenceSum_quotientResonanceCongruent_iff_classifier_factorsUniquely
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (first : ResonanceSpec inc1)
    (firstQuotient : QuotientResonanceCongruent inc1)
    (typeReflecting : SumLeftTypeReflecting inc1 inc2) :
    QuotientResonanceCongruent (incidenceSum inc1 inc2) ↔
      SumQuotientClassifierFactorsUniquely inc1 inc2 := by
  rw [incidenceSum_quotientResonanceCongruent_iff_control_of_typeReflecting
    inc1 inc2 first firstQuotient typeReflecting]
  exact sumQuotientControl_iff_classifier_factorsUniquely inc1 inc2

/-- For `GraphType`, type reflection is automatic. -/
theorem incidenceSum_quotientResonanceCongruent_iff_classifier_factorsUniquely_graphType
    {I1 R1 I2 R2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 GraphType) (inc2 : Incidence I2 R2 GraphType)
    (first : ResonanceSpec inc1)
    (firstQuotient : QuotientResonanceCongruent inc1) :
    QuotientResonanceCongruent (incidenceSum inc1 inc2) ↔
      SumQuotientClassifierFactorsUniquely inc1 inc2 :=
  incidenceSum_quotientResonanceCongruent_iff_classifier_factorsUniquely
    inc1 inc2 first firstQuotient
    (incidenceSum_leftTypeReflecting_graphType inc1 inc2)

/-- Concrete non-vacuous witness of the universal factorization theorem. -/
theorem natCycleSumQuotientClassifierFactorsUniquely :
    SumQuotientClassifierFactorsUniquely natIncidence cycleIncidenceFixed :=
  (incidenceSum_quotientResonanceCongruent_iff_classifier_factorsUniquely_graphType
    natIncidence cycleIncidenceFixed natResonanceSpec.toResonanceSpec
    natQuotientResonanceCongruent).mp
    natCycleSum_quotientResonanceCongruent

end IncidenceCore
