import IncidenceTheory.Integers

namespace IncidenceCore

/-- A fraction representative with a strictly positive denominator. -/
structure RationalRepresentative where
  numerator : Int
  denominator : Int
  denominator_pos : 0 < denominator

def RationalRepresentative.Equivalent
    (left right : RationalRepresentative) : Prop :=
  left.numerator * right.denominator =
    right.numerator * left.denominator

theorem rationalEquivalent_refl (value : RationalRepresentative) :
    value.Equivalent value := rfl

theorem rationalEquivalent_symm {left right : RationalRepresentative}
    (equivalent : left.Equivalent right) : right.Equivalent left :=
  equivalent.symm

theorem rationalEquivalent_trans {first second third : RationalRepresentative}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt second.denominator_pos)
  calc
    (first.numerator * third.denominator) * second.denominator =
        (first.numerator * second.denominator) * third.denominator := by
          ac_rfl
    _ = (second.numerator * first.denominator) * third.denominator := by
          rw [firstSecond]
    _ = (second.numerator * third.denominator) * first.denominator := by
          ac_rfl
    _ = (third.numerator * second.denominator) * first.denominator := by
          rw [secondThird]
    _ = (third.numerator * first.denominator) * second.denominator := by
          ac_rfl

def rationalRepresentativeSetoid : Setoid RationalRepresentative where
  r := RationalRepresentative.Equivalent
  iseqv := ⟨rationalEquivalent_refl, rationalEquivalent_symm,
    rationalEquivalent_trans⟩

/-- Rational numbers reconstructed as the quotient of positive-denominator
integer fractions by cross-multiplication. -/
abbrev IncRational := Quotient rationalRepresentativeSetoid

def rationalRepresentative (numerator denominator : Int)
    (positive : 0 < denominator) : RationalRepresentative :=
  ⟨numerator, denominator, positive⟩

def rationalOfInteger (value : Int) : IncRational :=
  Quotient.mk rationalRepresentativeSetoid
    (rationalRepresentative value 1 (by omega))

theorem rationalOfInteger_injective {left right : Int}
    (equal : rationalOfInteger left = rationalOfInteger right) : left = right := by
  have exactRelation := Quotient.exact equal
  change left * 1 = right * 1 at exactRelation
  simpa using exactRelation

theorem rational_half_eq_two_fourths :
    Quotient.mk rationalRepresentativeSetoid
        (rationalRepresentative 1 2 (by omega)) =
      Quotient.mk rationalRepresentativeSetoid
        (rationalRepresentative 2 4 (by omega)) := by
  apply Quotient.sound
  change (1 : Int) * 4 = 2 * 2
  decide

theorem rational_zero_ne_one :
    rationalOfInteger 0 ≠ rationalOfInteger 1 := by
  intro equal
  have := rationalOfInteger_injective equal
  omega

def RationalRepresentative.add
    (left right : RationalRepresentative) : RationalRepresentative :=
  { numerator := left.numerator * right.denominator +
      right.numerator * left.denominator
    denominator := left.denominator * right.denominator
    denominator_pos := Int.mul_pos left.denominator_pos right.denominator_pos }

def RationalRepresentative.mul
    (left right : RationalRepresentative) : RationalRepresentative :=
  { numerator := left.numerator * right.numerator
    denominator := left.denominator * right.denominator
    denominator_pos := Int.mul_pos left.denominator_pos right.denominator_pos }

def RationalRepresentative.neg
    (value : RationalRepresentative) : RationalRepresentative :=
  { numerator := -value.numerator
    denominator := value.denominator
    denominator_pos := value.denominator_pos }

theorem rationalNeg_respects {left right : RationalRepresentative}
    (equivalent : left.Equivalent right) :
    left.neg.Equivalent right.neg := by
  change (-left.numerator) * right.denominator =
    (-right.numerator) * left.denominator
  rw [Int.neg_mul, Int.neg_mul]
  exact congrArg Neg.neg equivalent

theorem rationalMul_respects
    {left left' right right' : RationalRepresentative}
    (leftEq : left.Equivalent left') (rightEq : right.Equivalent right') :
    (left.mul right).Equivalent (left'.mul right') := by
  calc
    (left.numerator * right.numerator) *
        (left'.denominator * right'.denominator) =
      (left.numerator * left'.denominator) *
        (right.numerator * right'.denominator) := by ac_rfl
    _ = (left'.numerator * left.denominator) *
        (right.numerator * right'.denominator) := by rw [leftEq]
    _ = (left'.numerator * left.denominator) *
        (right'.numerator * right.denominator) := by rw [rightEq]
    _ = (left'.numerator * right'.numerator) *
        (left.denominator * right.denominator) := by ac_rfl

theorem rationalAdd_respects
    {left left' right right' : RationalRepresentative}
    (leftEq : left.Equivalent left') (rightEq : right.Equivalent right') :
    (left.add right).Equivalent (left'.add right') := by
  have firstTerm :
      (left.numerator * right.denominator) *
          (left'.denominator * right'.denominator) =
        (left'.numerator * right'.denominator) *
          (left.denominator * right.denominator) := by
    calc
      _ = (left.numerator * left'.denominator) *
          (right.denominator * right'.denominator) := by ac_rfl
      _ = (left'.numerator * left.denominator) *
          (right.denominator * right'.denominator) := by rw [leftEq]
      _ = _ := by ac_rfl
  have secondTerm :
      (right.numerator * left.denominator) *
          (left'.denominator * right'.denominator) =
        (right'.numerator * left'.denominator) *
          (left.denominator * right.denominator) := by
    calc
      _ = (right.numerator * right'.denominator) *
          (left.denominator * left'.denominator) := by ac_rfl
      _ = (right'.numerator * right.denominator) *
          (left.denominator * left'.denominator) := by rw [rightEq]
      _ = _ := by ac_rfl
  simp only [RationalRepresentative.add, RationalRepresentative.Equivalent,
    Int.add_mul]
  rw [firstTerm, secondTerm]

def rationalAdd : IncRational → IncRational → IncRational :=
  Quotient.lift₂
    (fun left right => Quotient.mk rationalRepresentativeSetoid (left.add right))
    (by
      intro left right left' right' leftEq rightEq
      exact Quotient.sound (rationalAdd_respects leftEq rightEq))

def rationalMul : IncRational → IncRational → IncRational :=
  Quotient.lift₂
    (fun left right => Quotient.mk rationalRepresentativeSetoid (left.mul right))
    (by
      intro left right left' right' leftEq rightEq
      exact Quotient.sound (rationalMul_respects leftEq rightEq))

def rationalNeg : IncRational → IncRational :=
  Quotient.lift
    (fun value => Quotient.mk rationalRepresentativeSetoid value.neg)
    (fun _ _ equivalent => Quotient.sound (rationalNeg_respects equivalent))

def rationalAddResonance (left right mode : IncRational) : Prop :=
  rationalAdd left right = mode

def rationalMulResonance (left right mode : IncRational) : Prop :=
  rationalMul left right = mode

theorem rational_half_add_half :
    rationalAdd
      (Quotient.mk rationalRepresentativeSetoid
        (rationalRepresentative 1 2 (by omega)))
      (Quotient.mk rationalRepresentativeSetoid
        (rationalRepresentative 1 2 (by omega))) =
      rationalOfInteger 1 := by
  apply Quotient.sound
  change (4 : Int) * 1 = 1 * 4
  decide

theorem rational_half_mul_half :
    rationalMul
      (Quotient.mk rationalRepresentativeSetoid
        (rationalRepresentative 1 2 (by omega)))
      (Quotient.mk rationalRepresentativeSetoid
        (rationalRepresentative 1 2 (by omega))) =
      Quotient.mk rationalRepresentativeSetoid
        (rationalRepresentative 1 4 (by omega)) := by
  rfl

theorem rationalAdd_comm (left right : IncRational) :
    rationalAdd left right = rationalAdd right left := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep
  apply Quotient.sound
  change
    (leftRep.numerator * rightRep.denominator +
        rightRep.numerator * leftRep.denominator) *
        (rightRep.denominator * leftRep.denominator) =
      (rightRep.numerator * leftRep.denominator +
        leftRep.numerator * rightRep.denominator) *
        (leftRep.denominator * rightRep.denominator)
  rw [Int.add_comm, Int.mul_comm rightRep.denominator leftRep.denominator]

theorem rationalAdd_zero_left (value : IncRational) :
    rationalAdd (rationalOfInteger 0) value = value := by
  refine Quotient.inductionOn value ?_
  intro representative
  apply Quotient.sound
  change
    (0 * representative.denominator + representative.numerator * 1) *
        representative.denominator =
      representative.numerator * (1 * representative.denominator)
  simp

theorem rationalAdd_zero_right (value : IncRational) :
    rationalAdd value (rationalOfInteger 0) = value := by
  rw [rationalAdd_comm, rationalAdd_zero_left]

theorem rationalAdd_neg (value : IncRational) :
    rationalAdd value (rationalNeg value) = rationalOfInteger 0 := by
  refine Quotient.inductionOn value ?_
  intro representative
  apply Quotient.sound
  change
    (representative.numerator * representative.denominator +
        -representative.numerator * representative.denominator) * 1 =
      0 * (representative.denominator * representative.denominator)
  rw [← Int.add_mul]
  have cancel : representative.numerator + -representative.numerator = 0 :=
    by omega
  rw [cancel]
  simp

theorem rationalAdd_assoc (first second third : IncRational) :
    rationalAdd (rationalAdd first second) third =
      rationalAdd first (rationalAdd second third) := by
  refine Quotient.inductionOn₂ first second ?_
  intro firstRep secondRep
  refine Quotient.inductionOn third ?_
  intro thirdRep
  apply Quotient.sound
  simp only [RationalRepresentative.add, Int.add_mul]
  ac_rfl

theorem rationalMul_comm (left right : IncRational) :
    rationalMul left right = rationalMul right left := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep
  apply Quotient.sound
  simp only [RationalRepresentative.mul]
  ac_rfl

theorem rationalMul_one_left (value : IncRational) :
    rationalMul (rationalOfInteger 1) value = value := by
  refine Quotient.inductionOn value ?_
  intro representative
  apply Quotient.sound
  change
    (1 * representative.numerator) * representative.denominator =
      representative.numerator * (1 * representative.denominator)
  simp

theorem rationalMul_one_right (value : IncRational) :
    rationalMul value (rationalOfInteger 1) = value := by
  rw [rationalMul_comm, rationalMul_one_left]

theorem rationalMul_assoc (first second third : IncRational) :
    rationalMul (rationalMul first second) third =
      rationalMul first (rationalMul second third) := by
  refine Quotient.inductionOn₂ first second ?_
  intro firstRep secondRep
  refine Quotient.inductionOn third ?_
  intro thirdRep
  apply Quotient.sound
  simp only [RationalRepresentative.mul]
  ac_rfl

theorem rationalMul_add (first second third : IncRational) :
    rationalMul first (rationalAdd second third) =
      rationalAdd (rationalMul first second) (rationalMul first third) := by
  refine Quotient.inductionOn₂ first second ?_
  intro firstRep secondRep
  refine Quotient.inductionOn third ?_
  intro thirdRep
  apply Quotient.sound
  simp only [RationalRepresentative.add, RationalRepresentative.mul]
  change _ = _
  simp only [Int.mul_add, Int.add_mul]
  ac_rfl

inductive RationalRole where
  | fraction
deriving DecidableEq, Repr

noncomputable instance : DecidableEq IncRational :=
  Classical.typeDecidableEq IncRational

noncomputable def rationalIncidence :
    Incidence IncRational RationalRole GraphType where
  boundary := fun _ => []
  typeFunc := fun _ => GraphType.unit
  glue := fun left right => some (rationalAdd left right)
  unit := rationalOfInteger 0
  guards := Guards.permissive IncRational
  type_consistent := fun _ _ member => by simp at member
  sign_rules := by intro _ _ member; simp at member
  multiplicities := by intro _ _ member; simp at member
  well_founded := by simp
  unit_left := fun i => congrArg some (rationalAdd_zero_left i)
  unit_right := fun i => congrArg some (rationalAdd_zero_right i)
  type_preserve := by intro i j k allowed selected; rfl

noncomputable def rationalResonanceSpec :
    FunctionalResonanceSpec rationalIncidence where
  symmetric := by
    intro i j k resonant
    simpa [rationalIncidence, rationalAdd_comm] using resonant
  unit_left := by intro i; simp [rationalIncidence, rationalAdd_zero_left]
  unit_right := by intro i; simp [rationalIncidence, rationalAdd_zero_right]
  type_compatible := by intro i j k resonant; exact ⟨rfl, rfl⟩
  selected_complete := by intro i j k resonant; exact resonant

noncomputable def rationalAssociativeResonanceSpec :
    AssociativeResonanceSpec rationalIncidence where
  reassociate := by
    intro i j k out
    constructor
    · rintro ⟨ij, hij, hout⟩
      have hijEq : rationalAdd i j = ij := by
        simpa [rationalIncidence] using hij
      subst ij
      refine ⟨rationalAdd j k, ?_, ?_⟩
      · simp [rationalIncidence]
      · simpa [rationalIncidence, rationalAdd_assoc] using hout
    · rintro ⟨jk, hjk, hout⟩
      have hjkEq : rationalAdd j k = jk := by
        simpa [rationalIncidence] using hjk
      subst jk
      refine ⟨rationalAdd i j, ?_, ?_⟩
      · simp [rationalIncidence]
      · simpa [rationalIncidence, rationalAdd_assoc] using hout

noncomputable def rationalDistributiveResonanceSpec :
    DistributiveResonanceSpec rationalIncidence where
  one := rationalOfInteger 1
  multiply := rationalMulResonance
  symmetric := by
    intro i j k multiplied
    simpa [rationalMulResonance, rationalMul_comm] using multiplied
  unit_left := by intro i; exact rationalMul_one_left i
  unit_right := by intro i; exact rationalMul_one_right i
  associative := by
    intro i j k out
    constructor
    · rintro ⟨ij, hij, hout⟩
      subst ij
      refine ⟨rationalMul j k, rfl, ?_⟩
      simpa [rationalMulResonance, rationalMul_assoc] using hout
    · rintro ⟨jk, hjk, hout⟩
      subst jk
      refine ⟨rationalMul i j, rfl, ?_⟩
      simpa [rationalMulResonance, rationalMul_assoc] using hout
  distributes := by
    intro i j k out
    constructor
    · rintro ⟨jk, hjk, hout⟩
      have hjkEq : rationalAdd j k = jk := by
        simpa [rationalIncidence] using hjk
      subst jk
      refine ⟨rationalMul i j, rationalMul i k, rfl, rfl, ?_⟩
      simpa [rationalIncidence, rationalMulResonance, rationalMul_add] using hout
    · rintro ⟨ij, ik, hij, hik, hout⟩
      subst ij
      subst ik
      refine ⟨rationalAdd j k, ?_, ?_⟩
      · simp [rationalIncidence]
      · simpa [rationalIncidence, rationalMulResonance, rationalMul_add] using hout

theorem rationalIncidence_half_resonance :
    let half := Quotient.mk rationalRepresentativeSetoid
      (rationalRepresentative 1 2 (by omega))
    rationalIncidence.resonance half half (rationalOfInteger 1) := by
  simpa [rationalIncidence] using rational_half_add_half

/-- The first rational incidence presentation deliberately has no boundary
observations.  Consequently its algebraic carrier is correct, but its
bisimulation quotient collapses every rational to one class. -/
theorem rationalIncidence_all_bisimilar (left right : IncRational) :
    approxBisim rationalIncidence left right := by
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro i j _
  refine ⟨rfl, ?_, ?_⟩ <;> simp [rationalIncidence]

theorem rationalIncidence_not_bisimulationFaithful :
    ¬ CompletenessTheory.BisimulationFaithful rationalIncidence := by
  intro faithful
  exact rational_zero_ne_one
    (faithful (rationalIncidence_all_bisimilar
      (rationalOfInteger 0) (rationalOfInteger 1)))

end IncidenceCore
