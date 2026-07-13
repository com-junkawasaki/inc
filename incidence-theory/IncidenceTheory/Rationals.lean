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

theorem rationalAdd_neg_left (value : IncRational) :
    rationalAdd (rationalNeg value) value = rationalOfInteger 0 := by
  rw [rationalAdd_comm]
  exact rationalAdd_neg value

theorem rationalAdd_sub_cancel (left right : IncRational) :
    rationalAdd (rationalAdd left (rationalNeg right)) right = left := by
  rw [rationalAdd_assoc, rationalAdd_neg_left, rationalAdd_zero_right]

theorem rationalAdd_add_neg_cancel (left right : IncRational) :
    rationalAdd (rationalAdd left right) (rationalNeg right) = left := by
  rw [rationalAdd_assoc, rationalAdd_neg, rationalAdd_zero_right]

theorem rationalNeg_neg (value : IncRational) :
    rationalNeg (rationalNeg value) = value := by
  refine Quotient.inductionOn value ?_
  intro representative
  apply Quotient.sound
  show RationalRepresentative.Equivalent representative.neg.neg representative
  simp [RationalRepresentative.Equivalent, RationalRepresentative.neg]

theorem rationalNeg_zero :
    rationalNeg (rationalOfInteger 0) = rationalOfInteger 0 := by
  apply Quotient.sound
  show RationalRepresentative.Equivalent
    (rationalRepresentative 0 1 (by omega)).neg
    (rationalRepresentative 0 1 (by omega))
  simp [RationalRepresentative.Equivalent, RationalRepresentative.neg,
    rationalRepresentative]

theorem rationalNeg_add (left right : IncRational) :
    rationalNeg (rationalAdd left right) =
      rationalAdd (rationalNeg left) (rationalNeg right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep
  apply Quotient.sound
  simp only [RationalRepresentative.add, RationalRepresentative.neg]
  change
    (-(leftRep.numerator * rightRep.denominator +
      rightRep.numerator * leftRep.denominator)) *
        (leftRep.denominator * rightRep.denominator) =
      ((-leftRep.numerator) * rightRep.denominator +
        (-rightRep.numerator) * leftRep.denominator) *
          (leftRep.denominator * rightRep.denominator)
  rw [Int.neg_add, Int.neg_mul, Int.neg_mul]

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

theorem rational_nonzero_has_mul_inverse {value : IncRational}
    (nonzero : value ≠ rationalOfInteger 0) :
    ∃ inverse, rationalMulResonance value inverse (rationalOfInteger 1) := by
  refine Quotient.inductionOn value ?_ nonzero
  intro representative representativeNonzero
  have numeratorNonzero : representative.numerator ≠ 0 := by
    intro numeratorZero
    apply representativeNonzero
    apply Quotient.sound
    change representative.numerator * 1 = 0 * representative.denominator
    simp [numeratorZero]
  by_cases positive : 0 < representative.numerator
  · let inverseRepresentative : RationalRepresentative :=
      rationalRepresentative representative.denominator
        representative.numerator positive
    refine ⟨Quotient.mk rationalRepresentativeSetoid inverseRepresentative, ?_⟩
    apply Quotient.sound
    change
      (representative.numerator * representative.denominator) * 1 =
        1 * (representative.denominator * representative.numerator)
    ac_rfl
  · have negative : representative.numerator < 0 := by omega
    have inverseDenominatorPositive : 0 < -representative.numerator := by omega
    let inverseRepresentative : RationalRepresentative :=
      rationalRepresentative (-representative.denominator)
        (-representative.numerator) inverseDenominatorPositive
    refine ⟨Quotient.mk rationalRepresentativeSetoid inverseRepresentative, ?_⟩
    apply Quotient.sound
    change
      (representative.numerator * -representative.denominator) * 1 =
        1 * (representative.denominator * -representative.numerator)
    simp only [Int.mul_one, Int.one_mul, Int.mul_neg]
    congr 1
    ac_rfl

theorem rationalMul_cancel_left {factor left right : IncRational}
    (factorNonzero : factor ≠ rationalOfInteger 0)
    (equal : rationalMul factor left = rationalMul factor right) :
    left = right := by
  obtain ⟨inverse, inverseLaw⟩ :=
    rational_nonzero_has_mul_inverse factorNonzero
  have inverseLaw' : rationalMul inverse factor = rationalOfInteger 1 := by
    simpa [rationalMulResonance, rationalMul_comm] using inverseLaw
  calc
    left = rationalMul (rationalOfInteger 1) left :=
      (rationalMul_one_left left).symm
    _ = rationalMul (rationalMul inverse factor) left := by rw [inverseLaw']
    _ = rationalMul inverse (rationalMul factor left) :=
      rationalMul_assoc inverse factor left
    _ = rationalMul inverse (rationalMul factor right) := by rw [equal]
    _ = rationalMul (rationalMul inverse factor) right :=
      (rationalMul_assoc inverse factor right).symm
    _ = rationalMul (rationalOfInteger 1) right := by rw [inverseLaw']
    _ = right := rationalMul_one_left right

theorem rationalMul_cancel_right {factor left right : IncRational}
    (factorNonzero : factor ≠ rationalOfInteger 0)
    (equal : rationalMul left factor = rationalMul right factor) :
    left = right := by
  apply rationalMul_cancel_left factorNonzero
  simpa [rationalMul_comm] using equal

def RationalRepresentative.LE
    (left right : RationalRepresentative) : Prop :=
  left.numerator * right.denominator ≤
    right.numerator * left.denominator

theorem rationalLE_respects
    {left left' right right' : RationalRepresentative}
    (leftEq : left.Equivalent left') (rightEq : right.Equivalent right') :
    left.LE right ↔ left'.LE right' := by
  have forward : ∀ {a a' b b' : RationalRepresentative},
      a.Equivalent a' → b.Equivalent b' → a.LE b → a'.LE b' := by
    intro a a' b b' aEq bEq ordered
    have scaled := Int.mul_le_mul_of_nonneg_right ordered
      (Int.le_of_lt (Int.mul_pos a'.denominator_pos b'.denominator_pos))
    apply Int.le_of_mul_le_mul_right _
      (Int.mul_pos a.denominator_pos b.denominator_pos)
    calc
      (a'.numerator * b'.denominator) *
          (a.denominator * b.denominator) =
        (a'.numerator * a.denominator) *
          (b.denominator * b'.denominator) := by ac_rfl
      _ = (a.numerator * a'.denominator) *
          (b.denominator * b'.denominator) := by rw [aEq]
      _ = (a.numerator * b.denominator) *
          (a'.denominator * b'.denominator) := by ac_rfl
      _ ≤ (b.numerator * a.denominator) *
          (a'.denominator * b'.denominator) := scaled
      _ = (b.numerator * b'.denominator) *
          (a.denominator * a'.denominator) := by ac_rfl
      _ = (b'.numerator * b.denominator) *
          (a.denominator * a'.denominator) := by rw [bEq]
      _ = (b'.numerator * a'.denominator) *
          (a.denominator * b.denominator) := by ac_rfl
  exact ⟨forward leftEq rightEq,
    forward (rationalEquivalent_symm leftEq)
      (rationalEquivalent_symm rightEq)⟩

def rationalLE : IncRational → IncRational → Prop :=
  Quotient.lift₂ RationalRepresentative.LE (by
    intro left right left' right' leftEq rightEq
    exact propext (rationalLE_respects leftEq rightEq))

theorem rationalLE_refl (value : IncRational) : rationalLE value value := by
  refine Quotient.inductionOn value ?_
  intro representative
  exact Int.le_refl _

theorem rationalLE_antisymm {left right : IncRational}
    (leftRight : rationalLE left right) (rightLeft : rationalLE right left) :
    left = right := by
  refine Quotient.inductionOn₂ left right ?_ leftRight rightLeft
  intro leftRep rightRep ordered reverse
  apply Quotient.sound
  exact Int.le_antisymm ordered reverse

theorem rationalLE_trans {first second third : IncRational}
    (firstSecond : rationalLE first second)
    (secondThird : rationalLE second third) : rationalLE first third := by
  revert firstSecond secondThird
  refine Quotient.inductionOn₃ first second third ?_
  intro firstRep secondRep thirdRep firstSecond secondThird
  apply Int.le_of_mul_le_mul_right _ secondRep.denominator_pos
  calc
    (firstRep.numerator * thirdRep.denominator) * secondRep.denominator =
        (firstRep.numerator * secondRep.denominator) *
          thirdRep.denominator := by ac_rfl
    _ ≤ (secondRep.numerator * firstRep.denominator) *
          thirdRep.denominator :=
      Int.mul_le_mul_of_nonneg_right firstSecond
        (Int.le_of_lt thirdRep.denominator_pos)
    _ = (secondRep.numerator * thirdRep.denominator) *
          firstRep.denominator := by ac_rfl
    _ ≤ (thirdRep.numerator * secondRep.denominator) *
          firstRep.denominator :=
      Int.mul_le_mul_of_nonneg_right secondThird
        (Int.le_of_lt firstRep.denominator_pos)
    _ = (thirdRep.numerator * firstRep.denominator) *
          secondRep.denominator := by ac_rfl

theorem rationalLE_total (left right : IncRational) :
    rationalLE left right ∨ rationalLE right left := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep
  exact Int.le_total _ _

theorem rationalOfInteger_le_iff (left right : Int) :
    rationalLE (rationalOfInteger left) (rationalOfInteger right) ↔
      left ≤ right := by
  change left * 1 ≤ right * 1 ↔ left ≤ right
  simp

theorem rationalLE_add_left (offset : IncRational) {left right : IncRational}
    (ordered : rationalLE left right) :
    rationalLE (rationalAdd offset left) (rationalAdd offset right) := by
  revert ordered
  refine Quotient.inductionOn₃ offset left right ?_
  intro offsetRep leftRep rightRep ordered
  have scaled := Int.mul_le_mul_of_nonneg_right ordered
    (Int.le_of_lt (Int.mul_pos offsetRep.denominator_pos
      offsetRep.denominator_pos))
  change
    (offsetRep.numerator * leftRep.denominator +
        leftRep.numerator * offsetRep.denominator) *
          (offsetRep.denominator * rightRep.denominator) ≤
      (offsetRep.numerator * rightRep.denominator +
        rightRep.numerator * offsetRep.denominator) *
          (offsetRep.denominator * leftRep.denominator)
  calc
    _ = offsetRep.numerator * leftRep.denominator *
          (offsetRep.denominator * rightRep.denominator) +
        (leftRep.numerator * rightRep.denominator) *
          (offsetRep.denominator * offsetRep.denominator) := by
            rw [Int.add_mul]
            congr 1 <;> ac_rfl
    _ ≤ offsetRep.numerator * leftRep.denominator *
          (offsetRep.denominator * rightRep.denominator) +
        (rightRep.numerator * leftRep.denominator) *
          (offsetRep.denominator * offsetRep.denominator) :=
      Int.add_le_add_left scaled _
    _ = (offsetRep.numerator * rightRep.denominator +
          rightRep.numerator * offsetRep.denominator) *
          (offsetRep.denominator * leftRep.denominator) := by
            rw [Int.add_mul]
            congr 1 <;> ac_rfl

theorem rationalLE_add_right (offset : IncRational) {left right : IncRational}
    (ordered : rationalLE left right) :
    rationalLE (rationalAdd left offset) (rationalAdd right offset) := by
  simpa [rationalAdd_comm] using rationalLE_add_left offset ordered

theorem rationalMul_nonnegative {left right : IncRational}
    (leftNonnegative : rationalLE (rationalOfInteger 0) left)
    (rightNonnegative : rationalLE (rationalOfInteger 0) right) :
    rationalLE (rationalOfInteger 0) (rationalMul left right) := by
  revert leftNonnegative rightNonnegative
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep leftNonnegative rightNonnegative
  change 0 * leftRep.denominator ≤ leftRep.numerator * 1 at leftNonnegative
  change 0 * rightRep.denominator ≤ rightRep.numerator * 1 at rightNonnegative
  have leftNumerator : 0 ≤ leftRep.numerator := by
    simpa using leftNonnegative
  have rightNumerator : 0 ≤ rightRep.numerator := by
    simpa using rightNonnegative
  change 0 * (leftRep.denominator * rightRep.denominator) ≤
    (leftRep.numerator * rightRep.numerator) * 1
  simpa using Int.mul_nonneg leftNumerator rightNumerator

def rationalLT (left right : IncRational) : Prop :=
  rationalLE left right ∧ left ≠ right

theorem rationalLE_neg_reverse {left right : IncRational}
    (ordered : rationalLE left right) :
    rationalLE (rationalNeg right) (rationalNeg left) := by
  revert ordered
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep ordered
  change (-rightRep.numerator) * leftRep.denominator ≤
    (-leftRep.numerator) * rightRep.denominator
  rw [Int.neg_mul, Int.neg_mul]
  exact Int.neg_le_neg ordered

theorem rationalLT_neg_reverse {left right : IncRational}
    (strict : rationalLT left right) :
    rationalLT (rationalNeg right) (rationalNeg left) := by
  refine ⟨rationalLE_neg_reverse strict.1, ?_⟩
  intro equal
  apply strict.2
  have := congrArg rationalNeg equal
  simpa [rationalNeg_neg] using this.symm

theorem rational_mk_lt_iff (left right : RationalRepresentative) :
    rationalLT
        (Quotient.mk rationalRepresentativeSetoid left)
        (Quotient.mk rationalRepresentativeSetoid right) ↔
      left.numerator * right.denominator <
        right.numerator * left.denominator := by
  constructor
  · rintro ⟨ordered, distinct⟩
    have crossDistinct :
        left.numerator * right.denominator ≠
          right.numerator * left.denominator := by
      intro equal
      exact distinct (Quotient.sound equal)
    exact Int.lt_iff_le_and_ne.mpr ⟨ordered, crossDistinct⟩
  · intro strict
    refine ⟨Int.le_of_lt strict, ?_⟩
    intro equal
    exact (Int.ne_of_lt strict) (Quotient.exact equal)

theorem rationalLT_irrefl (value : IncRational) : ¬ rationalLT value value := by
  intro strict
  exact strict.2 rfl

theorem rationalLT_trans {first second third : IncRational}
    (firstSecond : rationalLT first second)
    (secondThird : rationalLT second third) : rationalLT first third := by
  refine ⟨rationalLE_trans firstSecond.1 secondThird.1, ?_⟩
  intro firstThird
  subst third
  have secondFirst : rationalLE second first := secondThird.1
  exact firstSecond.2 (rationalLE_antisymm firstSecond.1 secondFirst)

theorem rationalLT_of_lt_of_le {first second third : IncRational}
    (firstSecond : rationalLT first second)
    (secondThird : rationalLE second third) : rationalLT first third := by
  refine ⟨rationalLE_trans firstSecond.1 secondThird, ?_⟩
  intro firstThird
  subst third
  exact firstSecond.2 (rationalLE_antisymm firstSecond.1 secondThird)

theorem rationalLT_of_le_of_lt {first second third : IncRational}
    (firstSecond : rationalLE first second)
    (secondThird : rationalLT second third) : rationalLT first third := by
  refine ⟨rationalLE_trans firstSecond secondThird.1, ?_⟩
  intro firstThird
  subst third
  exact secondThird.2 (rationalLE_antisymm secondThird.1 firstSecond)

theorem rationalLT_asymm {left right : IncRational}
    (strict : rationalLT left right) : ¬ rationalLT right left := by
  intro reverse
  exact strict.2 (rationalLE_antisymm strict.1 reverse.1)

theorem rationalLT_trichotomy (left right : IncRational) :
    rationalLT left right ∨ left = right ∨ rationalLT right left := by
  rcases rationalLE_total left right with ordered | reverse
  · by_cases equal : left = right
    · exact Or.inr (Or.inl equal)
    · exact Or.inl ⟨ordered, equal⟩
  · by_cases equal : left = right
    · exact Or.inr (Or.inl equal)
    · exact Or.inr (Or.inr ⟨reverse, fun rightLeft => equal rightLeft.symm⟩)

theorem rationalLE_of_not_lt {left right : IncRational}
    (notStrict : ¬ rationalLT right left) : rationalLE left right := by
  rcases rationalLE_total left right with ordered | reverse
  · exact ordered
  · by_cases equal : right = left
    · subst right
      exact rationalLE_refl _
    · exact False.elim (notStrict ⟨reverse, equal⟩)

theorem rationalLT_dense {left right : IncRational}
    (strict : rationalLT left right) :
    ∃ middle, rationalLT left middle ∧ rationalLT middle right := by
  revert strict
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep strict
  have crossStrict :
      leftRep.numerator * rightRep.denominator <
        rightRep.numerator * leftRep.denominator :=
    (rational_mk_lt_iff leftRep rightRep).mp strict
  have denominatorPositive :
      0 < (2 : Int) * leftRep.denominator * rightRep.denominator :=
    Int.mul_pos (Int.mul_pos (by omega) leftRep.denominator_pos)
      rightRep.denominator_pos
  let middleRep := rationalRepresentative
    (leftRep.numerator * rightRep.denominator +
      rightRep.numerator * leftRep.denominator)
    ((2 : Int) * leftRep.denominator * rightRep.denominator)
    denominatorPositive
  refine ⟨Quotient.mk rationalRepresentativeSetoid middleRep, ?_, ?_⟩
  · apply (rational_mk_lt_iff leftRep middleRep).mpr
    have added := Int.add_lt_add_left crossStrict
      (leftRep.numerator * rightRep.denominator)
    have scaled := Int.mul_lt_mul_of_pos_right added leftRep.denominator_pos
    change
      leftRep.numerator *
          ((2 : Int) * leftRep.denominator * rightRep.denominator) <
        (leftRep.numerator * rightRep.denominator +
          rightRep.numerator * leftRep.denominator) * leftRep.denominator
    calc
      _ = ((leftRep.numerator * rightRep.denominator) +
          (leftRep.numerator * rightRep.denominator)) *
            leftRep.denominator := by
              rw [← Int.two_mul]
              ac_rfl
      _ < ((leftRep.numerator * rightRep.denominator) +
          (rightRep.numerator * leftRep.denominator)) *
            leftRep.denominator := scaled
  · apply (rational_mk_lt_iff middleRep rightRep).mpr
    have added := Int.add_lt_add_right crossStrict
      (rightRep.numerator * leftRep.denominator)
    have scaled := Int.mul_lt_mul_of_pos_right added rightRep.denominator_pos
    change
      (leftRep.numerator * rightRep.denominator +
          rightRep.numerator * leftRep.denominator) * rightRep.denominator <
        rightRep.numerator *
          ((2 : Int) * leftRep.denominator * rightRep.denominator)
    calc
      _ < ((rightRep.numerator * leftRep.denominator) +
          (rightRep.numerator * leftRep.denominator)) *
            rightRep.denominator := scaled
      _ = _ := by
        rw [← Int.two_mul]
        ac_rfl

theorem rational_add_neg_one_lt (value : IncRational) :
    rationalLT (rationalAdd value (rationalOfInteger (-1))) value := by
  refine Quotient.inductionOn value ?_
  intro representative
  apply (rational_mk_lt_iff _ _).mpr
  change
    (representative.numerator * 1 + (-1) * representative.denominator) *
        representative.denominator <
      representative.numerator *
        (representative.denominator * 1)
  have decreased : representative.numerator - representative.denominator <
      representative.numerator := by
    have positive := representative.denominator_pos
    omega
  simpa using Int.mul_lt_mul_of_pos_right decreased representative.denominator_pos

theorem rational_zero_lt_one :
    rationalLT (rationalOfInteger 0) (rationalOfInteger 1) := by
  apply (rational_mk_lt_iff _ _).mpr
  decide

theorem rationalLT_add_left (offset : IncRational) {left right : IncRational}
    (strict : rationalLT left right) :
    rationalLT (rationalAdd offset left) (rationalAdd offset right) := by
  revert strict
  refine Quotient.inductionOn₃ offset left right ?_
  intro offsetRep leftRep rightRep strict
  apply (rational_mk_lt_iff _ _).mpr
  have crossStrict := (rational_mk_lt_iff leftRep rightRep).mp strict
  have scaled := Int.mul_lt_mul_of_pos_right crossStrict
    (Int.mul_pos offsetRep.denominator_pos offsetRep.denominator_pos)
  change
    (offsetRep.numerator * leftRep.denominator +
        leftRep.numerator * offsetRep.denominator) *
          (offsetRep.denominator * rightRep.denominator) <
      (offsetRep.numerator * rightRep.denominator +
        rightRep.numerator * offsetRep.denominator) *
          (offsetRep.denominator * leftRep.denominator)
  calc
    _ = offsetRep.numerator * leftRep.denominator *
          (offsetRep.denominator * rightRep.denominator) +
        (leftRep.numerator * rightRep.denominator) *
          (offsetRep.denominator * offsetRep.denominator) := by
            rw [Int.add_mul]
            congr 1 <;> ac_rfl
    _ < offsetRep.numerator * leftRep.denominator *
          (offsetRep.denominator * rightRep.denominator) +
        (rightRep.numerator * leftRep.denominator) *
          (offsetRep.denominator * offsetRep.denominator) :=
      Int.add_lt_add_left scaled _
    _ = (offsetRep.numerator * rightRep.denominator +
          rightRep.numerator * offsetRep.denominator) *
          (offsetRep.denominator * leftRep.denominator) := by
            rw [Int.add_mul]
            congr 1 <;> ac_rfl

theorem rationalLT_add_right (offset : IncRational) {left right : IncRational}
    (strict : rationalLT left right) :
    rationalLT (rationalAdd left offset) (rationalAdd right offset) := by
  simpa [rationalAdd_comm] using rationalLT_add_left offset strict

theorem rational_lt_add_one (value : IncRational) :
    rationalLT value (rationalAdd value (rationalOfInteger 1)) := by
  have shifted := rationalLT_add_left value rational_zero_lt_one
  simpa [rationalAdd_zero_right] using shifted

theorem rationalLT_add {left left' right right' : IncRational}
    (leftStrict : rationalLT left left')
    (rightStrict : rationalLT right right') :
    rationalLT (rationalAdd left right) (rationalAdd left' right') := by
  exact rationalLT_trans
    (rationalLT_add_right right leftStrict)
    (rationalLT_add_left left' rightStrict)

theorem rationalLT_add_cancel_right {left right : IncRational}
    (offset : IncRational)
    (strict : rationalLT (rationalAdd left offset)
      (rationalAdd right offset)) : rationalLT left right := by
  have shifted := rationalLT_add_right (rationalNeg offset) strict
  simpa [rationalAdd_add_neg_cancel] using shifted

theorem rationalLT_add_cancel_left {left right : IncRational}
    (offset : IncRational)
    (strict : rationalLT (rationalAdd offset left)
      (rationalAdd offset right)) : rationalLT left right := by
  rw [rationalAdd_comm offset left, rationalAdd_comm offset right] at strict
  exact rationalLT_add_cancel_right offset strict

/-- Between any lower bound and a positive upper bound there is a positive
rational. This is the density form needed when splitting strict cut bounds. -/
theorem rationalLT_exists_positive_between {lower upper : IncRational}
    (lowerUpper : rationalLT lower upper)
    (upperPositive : rationalLT (rationalOfInteger 0) upper) :
    ∃ middle, rationalLT (rationalOfInteger 0) middle ∧
      rationalLT lower middle ∧ rationalLT middle upper := by
  obtain ⟨candidate, lowerCandidate, candidateUpper⟩ :=
    rationalLT_dense lowerUpper
  by_cases candidatePositive :
      rationalLT (rationalOfInteger 0) candidate
  · exact ⟨candidate, candidatePositive, lowerCandidate, candidateUpper⟩
  · have candidateNonpositive :
        rationalLE candidate (rationalOfInteger 0) := by
      rcases rationalLE_total candidate (rationalOfInteger 0) with ordered | reverse
      · exact ordered
      · by_cases equal : candidate = rationalOfInteger 0
        · subst candidate
          exact rationalLE_refl _
        · exact False.elim (candidatePositive ⟨reverse, fun zeroCandidate =>
            equal zeroCandidate.symm⟩)
    obtain ⟨middle, zeroMiddle, middleUpper⟩ :=
      rationalLT_dense upperPositive
    exact ⟨middle, zeroMiddle,
      rationalLT_trans lowerCandidate
        (rationalLT_of_le_of_lt candidateNonpositive zeroMiddle),
      middleUpper⟩

theorem rational_exists_positive_below_two {first second : IncRational}
    (firstPositive : rationalLT (rationalOfInteger 0) first)
    (secondPositive : rationalLT (rationalOfInteger 0) second) :
    ∃ value, rationalLT (rationalOfInteger 0) value ∧
      rationalLT value first ∧ rationalLT value second := by
  rcases rationalLE_total first second with firstSecond | secondFirst
  · obtain ⟨value, valuePositive, valueFirst⟩ :=
      rationalLT_dense firstPositive
    exact ⟨value, valuePositive, valueFirst,
      rationalLT_of_lt_of_le valueFirst firstSecond⟩
  · obtain ⟨value, valuePositive, valueSecond⟩ :=
      rationalLT_dense secondPositive
    exact ⟨value, valuePositive,
      rationalLT_of_lt_of_le valueSecond secondFirst, valueSecond⟩

/-- A strict bound below a sum of positive rationals can be realized below a
sum of positive strict approximants of both summands. -/
theorem rationalLT_split_positive_add
    {value left right : IncRational}
    (leftPositive : rationalLT (rationalOfInteger 0) left)
    (rightPositive : rationalLT (rationalOfInteger 0) right)
    (below : rationalLT value (rationalAdd left right)) :
    ∃ leftPart rightPart,
      rationalLT (rationalOfInteger 0) leftPart ∧
      rationalLT leftPart left ∧
      rationalLT (rationalOfInteger 0) rightPart ∧
      rationalLT rightPart right ∧
      rationalLT value (rationalAdd leftPart rightPart) := by
  let translatedLeft := rationalAdd value (rationalNeg right)
  have translatedLeftRestore :
      rationalAdd translatedLeft right = value :=
    rationalAdd_sub_cancel value right
  have translatedLeftBelow : rationalLT translatedLeft left := by
    apply rationalLT_add_cancel_right right
    rw [translatedLeftRestore]
    exact below
  obtain ⟨leftPart, leftPartPositive, translatedLeftPart, leftPartBelow⟩ :=
    rationalLT_exists_positive_between translatedLeftBelow leftPositive
  have valueBelowLeftPlusRight :
      rationalLT value (rationalAdd leftPart right) := by
    have shifted := rationalLT_add_right right translatedLeftPart
    rw [translatedLeftRestore] at shifted
    exact shifted
  let translatedRight := rationalAdd value (rationalNeg leftPart)
  have translatedRightRestore :
      rationalAdd translatedRight leftPart = value :=
    rationalAdd_sub_cancel value leftPart
  have translatedRightBelow : rationalLT translatedRight right := by
    apply rationalLT_add_cancel_right leftPart
    rw [translatedRightRestore, rationalAdd_comm right leftPart]
    exact valueBelowLeftPlusRight
  obtain ⟨rightPart, rightPartPositive, translatedRightPart, rightPartBelow⟩ :=
    rationalLT_exists_positive_between translatedRightBelow rightPositive
  refine ⟨leftPart, rightPart, leftPartPositive, leftPartBelow,
    rightPartPositive, rightPartBelow, ?_⟩
  have shifted := rationalLT_add_right leftPart translatedRightPart
  rw [translatedRightRestore, rationalAdd_comm rightPart leftPart] at shifted
  exact shifted

def rationalNatScale (count : Nat) (value : IncRational) : IncRational :=
  rationalMul (rationalOfInteger (Int.ofNat count)) value

theorem rationalMul_zero_left (value : IncRational) :
    rationalMul (rationalOfInteger 0) value = rationalOfInteger 0 := by
  refine Quotient.inductionOn value ?_
  intro representative
  apply Quotient.sound
  change (0 * representative.numerator) * 1 =
    0 * (1 * representative.denominator)
  simp

theorem rationalMul_zero_right (value : IncRational) :
    rationalMul value (rationalOfInteger 0) = rationalOfInteger 0 := by
  rw [rationalMul_comm, rationalMul_zero_left]

theorem rationalLT_mul_right_of_positive {left right factor : IncRational}
    (strict : rationalLT left right)
    (factorPositive : rationalLT (rationalOfInteger 0) factor) :
    rationalLT (rationalMul left factor) (rationalMul right factor) := by
  revert strict factorPositive
  refine Quotient.inductionOn₃ left right factor ?_
  intro leftRep rightRep factorRep strict factorPositive
  have crossStrict := (rational_mk_lt_iff leftRep rightRep).mp strict
  have factorNumeratorPositive : 0 < factorRep.numerator := by
    have positiveCross := (rational_mk_lt_iff
      (rationalRepresentative 0 1 (by omega)) factorRep).mp factorPositive
    change 0 * factorRep.denominator < factorRep.numerator * 1 at positiveCross
    simpa using positiveCross
  apply (rational_mk_lt_iff _ _).mpr
  have scaled := Int.mul_lt_mul_of_pos_right crossStrict
    (Int.mul_pos factorNumeratorPositive factorRep.denominator_pos)
  change
    (leftRep.numerator * factorRep.numerator) *
        (rightRep.denominator * factorRep.denominator) <
      (rightRep.numerator * factorRep.numerator) *
        (leftRep.denominator * factorRep.denominator)
  calc
    _ = (leftRep.numerator * rightRep.denominator) *
        (factorRep.numerator * factorRep.denominator) := by ac_rfl
    _ < (rightRep.numerator * leftRep.denominator) *
        (factorRep.numerator * factorRep.denominator) := scaled
    _ = _ := by ac_rfl

theorem rationalLT_mul_left_of_positive {left right factor : IncRational}
    (strict : rationalLT left right)
    (factorPositive : rationalLT (rationalOfInteger 0) factor) :
    rationalLT (rationalMul factor left) (rationalMul factor right) := by
  simpa [rationalMul_comm] using
    rationalLT_mul_right_of_positive strict factorPositive

theorem rationalMul_positive {left right : IncRational}
    (leftPositive : rationalLT (rationalOfInteger 0) left)
    (rightPositive : rationalLT (rationalOfInteger 0) right) :
    rationalLT (rationalOfInteger 0) (rationalMul left right) := by
  have strict := rationalLT_mul_right_of_positive leftPositive rightPositive
  simpa [rationalMul_zero_left] using strict

theorem rationalMul_positive_reflect_right {left right : IncRational}
    (leftPositive : rationalLT (rationalOfInteger 0) left)
    (productPositive :
      rationalLT (rationalOfInteger 0) (rationalMul left right)) :
    rationalLT (rationalOfInteger 0) right := by
  revert leftPositive productPositive
  refine Quotient.inductionOn₂ left right ?_
  intro leftRep rightRep leftPositive productPositive
  have leftNumeratorPositive : 0 < leftRep.numerator := by
    have cross := (rational_mk_lt_iff
      (rationalRepresentative 0 1 (by omega)) leftRep).mp leftPositive
    change 0 * leftRep.denominator < leftRep.numerator * 1 at cross
    simpa using cross
  have productNumeratorPositive :
      0 < leftRep.numerator * rightRep.numerator := by
    have cross := (rational_mk_lt_iff
      (rationalRepresentative 0 1 (by omega)) (leftRep.mul rightRep)).mp
      productPositive
    change 0 * (leftRep.denominator * rightRep.denominator) <
      (leftRep.numerator * rightRep.numerator) * 1 at cross
    simpa using cross
  apply (rational_mk_lt_iff _ _).mpr
  change 0 * rightRep.denominator < rightRep.numerator * 1
  simpa using Int.pos_of_mul_pos_right productNumeratorPositive
    leftNumeratorPositive

theorem rationalMul_positive_reflect_left {left right : IncRational}
    (rightPositive : rationalLT (rationalOfInteger 0) right)
    (productPositive :
      rationalLT (rationalOfInteger 0) (rationalMul left right)) :
    rationalLT (rationalOfInteger 0) left := by
  apply rationalMul_positive_reflect_right rightPositive
  simpa [rationalMul_comm] using productPositive

theorem rationalLT_mul_of_positive
    {left left' right right' : IncRational}
    (leftStrict : rationalLT left left')
    (rightStrict : rationalLT right right')
    (rightPositive : rationalLT (rationalOfInteger 0) right)
    (leftPrimePositive : rationalLT (rationalOfInteger 0) left') :
    rationalLT (rationalMul left right) (rationalMul left' right') := by
  exact rationalLT_trans
    (rationalLT_mul_right_of_positive leftStrict rightPositive)
    (rationalLT_mul_left_of_positive rightStrict leftPrimePositive)

/-- A nonnegative bound below a product by a positive factor remains below the
product after replacing the second factor by a positive strict approximant. -/
theorem rationalLT_mul_positive_approx_right
    {value factor target : IncRational}
    (valueNonnegative : rationalLE (rationalOfInteger 0) value)
    (factorPositive : rationalLT (rationalOfInteger 0) factor)
    (targetPositive : rationalLT (rationalOfInteger 0) target)
    (below : rationalLT value (rationalMul factor target)) :
    ∃ approximant,
      rationalLT (rationalOfInteger 0) approximant ∧
      rationalLT approximant target ∧
      rationalLT value (rationalMul factor approximant) := by
  have factorNonzero : factor ≠ rationalOfInteger 0 := fun equal => by
    subst factor
    exact rationalLT_irrefl _ factorPositive
  obtain ⟨inverse, inverseLaw⟩ :=
    rational_nonzero_has_mul_inverse factorNonzero
  have inversePositive : rationalLT (rationalOfInteger 0) inverse := by
    apply rationalMul_positive_reflect_right factorPositive
    rw [inverseLaw]
    exact rational_zero_lt_one
  let translated := rationalMul value inverse
  have translatedNonnegative :
      rationalLE (rationalOfInteger 0) translated :=
    rationalMul_nonnegative valueNonnegative inversePositive.1
  have translatedBelow : rationalLT translated target := by
    have multiplied := rationalLT_mul_right_of_positive below inversePositive
    have restore : rationalMul (rationalMul factor target) inverse = target := by
      calc
        _ = rationalMul target (rationalMul factor inverse) := by
          rw [rationalMul_comm factor target,
            rationalMul_assoc target factor inverse]
        _ = rationalMul target (rationalOfInteger 1) := by rw [inverseLaw]
        _ = target := rationalMul_one_right target
    rw [restore] at multiplied
    exact multiplied
  obtain ⟨approximant, approximantPositive, translatedApproximant,
      approximantBelow⟩ :=
    rationalLT_exists_positive_between translatedBelow targetPositive
  refine ⟨approximant, approximantPositive, approximantBelow, ?_⟩
  have multiplied := rationalLT_mul_left_of_positive
    translatedApproximant factorPositive
  have restore : rationalMul factor translated = value := by
    calc
      _ = rationalMul value (rationalMul factor inverse) := by
        rw [← rationalMul_assoc factor value inverse,
          rationalMul_comm factor value,
          rationalMul_assoc value factor inverse]
      _ = rationalMul value (rationalOfInteger 1) := by rw [inverseLaw]
      _ = value := rationalMul_one_right value
  rw [restore] at multiplied
  exact multiplied

theorem rational_exists_positive_half {value : IncRational}
    (positive : rationalLT (rationalOfInteger 0) value) :
    ∃ half, rationalLT (rationalOfInteger 0) half ∧
      rationalAdd half half = value := by
  have twoNonzero : rationalOfInteger 2 ≠ rationalOfInteger 0 := fun equal => by
    have impossible := rationalOfInteger_injective equal
    omega
  obtain ⟨halfFactor, halfFactorLaw⟩ :=
    rational_nonzero_has_mul_inverse twoNonzero
  have twoPositive :
      rationalLT (rationalOfInteger 0) (rationalOfInteger 2) := by
    exact ⟨(rationalOfInteger_le_iff 0 2).mpr (by omega), fun equal => by
      have impossible := rationalOfInteger_injective equal
      omega⟩
  have halfFactorPositive :
      rationalLT (rationalOfInteger 0) halfFactor := by
    apply rationalMul_positive_reflect_right twoPositive
    rw [halfFactorLaw]
    exact rational_zero_lt_one
  have oneAddOne :
      rationalAdd (rationalOfInteger 1) (rationalOfInteger 1) =
        rationalOfInteger 2 := by
    apply Quotient.sound
    change (1 * 1 + 1 * 1) * 1 = 2 * (1 * 1)
    omega
  let half := rationalMul value halfFactor
  refine ⟨half, rationalMul_positive positive halfFactorPositive, ?_⟩
  calc
    rationalAdd half half =
        rationalMul value (rationalAdd halfFactor halfFactor) := by
      rw [rationalMul_add]
    _ = rationalMul value
        (rationalMul (rationalOfInteger 2) halfFactor) := by
      congr 1
      calc
        rationalAdd halfFactor halfFactor =
            rationalMul halfFactor
              (rationalAdd (rationalOfInteger 1) (rationalOfInteger 1)) := by
          rw [rationalMul_add, rationalMul_one_right]
        _ = rationalMul halfFactor (rationalOfInteger 2) := by
          rw [oneAddOne]
        _ = rationalMul (rationalOfInteger 2) halfFactor :=
          rationalMul_comm _ _
    _ = rationalMul value (rationalOfInteger 1) := by rw [halfFactorLaw]
    _ = value := rationalMul_one_right value

theorem rationalOfInteger_add (left right : Int) :
    rationalOfInteger (left + right) =
      rationalAdd (rationalOfInteger left) (rationalOfInteger right) := by
  apply Quotient.sound
  change (left + right) * (1 * 1) =
    (left * 1 + right * 1) * 1
  simp

theorem rationalNatScale_zero (value : IncRational) :
    rationalNatScale 0 value = rationalOfInteger 0 := by
  exact rationalMul_zero_left value

theorem rationalNatScale_succ (count : Nat) (value : IncRational) :
    rationalNatScale (count + 1) value =
      rationalAdd (rationalNatScale count value) value := by
  have castSucc : Int.ofNat (count + 1) = Int.ofNat count + 1 := by simp
  calc
    rationalNatScale (count + 1) value =
        rationalMul (rationalAdd (rationalOfInteger (Int.ofNat count))
          (rationalOfInteger 1)) value := by
            rw [rationalNatScale, castSucc, rationalOfInteger_add]
    _ = rationalMul value (rationalAdd (rationalOfInteger (Int.ofNat count))
          (rationalOfInteger 1)) := rationalMul_comm _ _
    _ = rationalAdd
          (rationalMul value (rationalOfInteger (Int.ofNat count)))
          (rationalMul value (rationalOfInteger 1)) :=
      rationalMul_add _ _ _
    _ = rationalAdd (rationalNatScale count value) value := by
      rw [rationalMul_comm value (rationalOfInteger (Int.ofNat count)),
        rationalMul_one_right]
      rfl

def rationalStepValue (start step : IncRational) (count : Nat) : IncRational :=
  rationalAdd start (rationalNatScale count step)

theorem rationalStepValue_zero (start step : IncRational) :
    rationalStepValue start step 0 = start := by
  simp [rationalStepValue, rationalNatScale_zero, rationalAdd_zero_right]

theorem rationalStepValue_succ (start step : IncRational) (count : Nat) :
    rationalStepValue start step (count + 1) =
      rationalAdd (rationalStepValue start step count) step := by
  simp [rationalStepValue, rationalNatScale_succ, rationalAdd_assoc]

theorem int_exists_nat_mul_gt (difference coefficient : Int)
    (coefficientPositive : 0 < coefficient) :
    ∃ count : Nat, difference < (Int.ofNat count) * coefficient := by
  cases difference with
  | ofNat value =>
      refine ⟨value + 1, ?_⟩
      have coefficientOne : (1 : Int) ≤ coefficient := by omega
      have countNonnegative : (0 : Int) ≤ Int.ofNat (value + 1) :=
        Int.ofNat_zero_le _
      have countBelowProduct := Int.mul_le_mul_of_nonneg_left
        coefficientOne countNonnegative
      have valueBelowCount : (Int.ofNat value) < Int.ofNat (value + 1) := by
        exact Int.ofNat_lt.mpr (by omega)
      have countBelow : Int.ofNat (value + 1) ≤
          Int.ofNat (value + 1) * coefficient := by
        simpa using countBelowProduct
      exact Int.lt_of_lt_of_le valueBelowCount countBelow
  | negSucc value =>
      exact ⟨0, by simp⟩

theorem rational_archimedean_steps {start target step : IncRational}
    (stepPositive : rationalLT (rationalOfInteger 0) step) :
    ∃ count : Nat,
      rationalLT target (rationalAdd start (rationalNatScale count step)) := by
  revert stepPositive
  refine Quotient.inductionOn₃ start target step ?_
  intro startRep targetRep stepRep stepPositive
  have stepNumeratorPositive : 0 < stepRep.numerator := by
    have cross := (rational_mk_lt_iff
      (rationalRepresentative 0 1 (by omega)) stepRep).mp stepPositive
    change 0 * stepRep.denominator < stepRep.numerator * 1 at cross
    simpa using cross
  let difference := targetRep.numerator * startRep.denominator *
      stepRep.denominator -
    startRep.numerator * stepRep.denominator * targetRep.denominator
  let coefficient := stepRep.numerator * startRep.denominator *
    targetRep.denominator
  have coefficientPositive : 0 < coefficient := by
    exact Int.mul_pos
      (Int.mul_pos stepNumeratorPositive startRep.denominator_pos)
      targetRep.denominator_pos
  obtain ⟨count, countLarge⟩ :=
    int_exists_nat_mul_gt difference coefficient coefficientPositive
  refine ⟨count, ?_⟩
  apply (rational_mk_lt_iff _ _).mpr
  change
    targetRep.numerator *
        (startRep.denominator * (1 * stepRep.denominator)) <
      (startRep.numerator * (1 * stepRep.denominator) +
        ((Int.ofNat count) * stepRep.numerator) * startRep.denominator) *
          targetRep.denominator
  have shifted := Int.add_lt_add_right countLarge
    (startRep.numerator * stepRep.denominator * targetRep.denominator)
  calc
    targetRep.numerator *
        (startRep.denominator * (1 * stepRep.denominator)) =
      difference +
        startRep.numerator * stepRep.denominator * targetRep.denominator := by
          simp [difference]
          ac_rfl
    _ < (Int.ofNat count) * coefficient +
        startRep.numerator * stepRep.denominator * targetRep.denominator := shifted
    _ = (startRep.numerator * (1 * stepRep.denominator) +
        ((Int.ofNat count) * stepRep.numerator) * startRep.denominator) *
          targetRep.denominator := by
            simp [coefficient, Int.add_mul]
            ac_rfl

theorem rationalNatSucc_pos (count : Nat) :
    rationalLT (rationalOfInteger 0) (rationalOfInteger (Int.ofNat (count + 1))) := by
  refine ⟨(rationalOfInteger_le_iff 0 (Int.ofNat (count + 1))).mpr
    (Int.ofNat_zero_le _), ?_⟩
  intro equal
  have integerEqual := rationalOfInteger_injective equal
  have naturalEqual : count + 1 = 0 := Int.ofNat_eq_zero.mp integerEqual.symm
  omega

theorem rationalNatSucc_ne_zero (count : Nat) :
    rationalOfInteger (Int.ofNat (count + 1)) ≠ rationalOfInteger 0 :=
  fun equal => (rationalNatSucc_pos count).2 equal.symm

/-- A canonical positive rational reciprocal of `count + 1`, obtained from the
field inverse existence proof. Used to index an explicit null sequence of
rational radii `1 / (n + 1)` for supremum-approximating real sequences
(cycle 42's extreme value theorem development). -/
noncomputable def rationalNatSuccInv (count : Nat) : IncRational :=
  Classical.choose (rational_nonzero_has_mul_inverse
    (rationalNatSucc_ne_zero count))

theorem rationalNatSuccInv_spec (count : Nat) :
    rationalMul (rationalOfInteger (Int.ofNat (count + 1)))
      (rationalNatSuccInv count) = rationalOfInteger 1 :=
  Classical.choose_spec (rational_nonzero_has_mul_inverse
    (rationalNatSucc_ne_zero count))

theorem rationalNatSuccInv_pos (count : Nat) :
    rationalLT (rationalOfInteger 0) (rationalNatSuccInv count) := by
  apply rationalMul_positive_reflect_right (rationalNatSucc_pos count)
  rw [rationalNatSuccInv_spec count]
  exact rational_zero_lt_one

/-- The reciprocals `1 / (n + 1)` are eventually below any positive rational
target -- the rational-arithmetic core fact needed to show the corresponding
real sequence of approximants converges. -/
theorem rationalNatSuccInv_eventually_le
    {epsilon : IncRational}
    (epsilonPositive : rationalLT (rationalOfInteger 0) epsilon) :
    ∃ threshold : Nat, ∀ n, threshold ≤ n →
      rationalLE (rationalNatSuccInv n) epsilon := by
  obtain ⟨count, countLarge⟩ := rational_archimedean_steps
    (start := rationalOfInteger 0) (target := rationalOfInteger 1)
    (step := epsilon) epsilonPositive
  have countLarge' : rationalLT (rationalOfInteger 1)
      (rationalMul (rationalOfInteger (Int.ofNat count)) epsilon) := by
    simpa [rationalNatScale, rationalAdd_zero_left] using countLarge
  refine ⟨count, ?_⟩
  intro n thresholdLe
  rcases rationalLT_trichotomy (rationalNatSuccInv n) epsilon with
    smaller | equal | greater
  · exact smaller.1
  · exact equal ▸ rationalLE_refl _
  · exfalso
    have succPositive := rationalNatSucc_pos n
    have scaledGreater :
        rationalLT
          (rationalMul (rationalOfInteger (Int.ofNat (n + 1))) epsilon)
          (rationalMul (rationalOfInteger (Int.ofNat (n + 1)))
            (rationalNatSuccInv n)) :=
      rationalLT_mul_left_of_positive greater succPositive
    rw [rationalNatSuccInv_spec n] at scaledGreater
    have countLeSucc : count ≤ n + 1 := by omega
    have countLtSucc : rationalLT (rationalOfInteger (Int.ofNat count))
        (rationalOfInteger (Int.ofNat (n + 1))) := by
      refine ⟨(rationalOfInteger_le_iff _ _).mpr
        (Int.ofNat_le.mpr countLeSucc), ?_⟩
      intro equal
      have integerEqual := rationalOfInteger_injective equal
      have naturalEqual : count = n + 1 := Int.ofNat_inj.mp integerEqual
      omega
    have scaledLarger :
        rationalLT
          (rationalMul (rationalOfInteger (Int.ofNat count)) epsilon)
          (rationalMul (rationalOfInteger (Int.ofNat (n + 1))) epsilon) :=
      rationalLT_mul_right_of_positive countLtSucc epsilonPositive
    have oneLtSucc : rationalLT (rationalOfInteger 1)
        (rationalMul (rationalOfInteger (Int.ofNat (n + 1))) epsilon) :=
      rationalLT_trans countLarge' scaledLarger
    exact rationalLT_irrefl _ (rationalLT_trans scaledGreater oneLtSucc)

noncomputable instance : DecidableEq IncRational :=
  Classical.typeDecidableEq IncRational

inductive RationalRole where
  | observe : IncRational → RationalRole

noncomputable instance : DecidableEq RationalRole :=
  Classical.typeDecidableEq RationalRole

noncomputable def rationalEndpoint (value : IncRational) :
    Endpoint IncRational RationalRole :=
  { i := rationalOfInteger 0
    role := .observe value
    sign := .neg
    mult := 1
    mult_pos := by omega }

noncomputable def rationalBoundary (value : IncRational) :
    Boundary IncRational RationalRole :=
  if value = rationalOfInteger 0 then [] else [rationalEndpoint value]

noncomputable def rationalRank (value : IncRational) : Nat :=
  if value = rationalOfInteger 0 then 0 else 1

theorem rationalBoundary_decreases :
    ∀ value endpoint, endpoint ∈ rationalBoundary value →
      rationalRank endpoint.i < rationalRank value := by
  intro value endpoint member
  by_cases zero : value = rationalOfInteger 0
  · simp [rationalBoundary, zero] at member
  · have endpointEq : endpoint = rationalEndpoint value := by
      simpa [rationalBoundary, zero] using member
    subst endpoint
    simp [rationalEndpoint, rationalRank, zero]

noncomputable def rationalIncidence :
    Incidence IncRational RationalRole GraphType where
  boundary := rationalBoundary
  typeFunc := fun _ => GraphType.unit
  glue := fun left right => some (rationalAdd left right)
  unit := rationalOfInteger 0
  guards := Guards.permissive IncRational
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro _ endpoint _; cases endpoint.sign <;> simp
  multiplicities := fun _ endpoint _ => endpoint.mult_pos
  well_founded := by
    intro value ⟨endpoint, member, equal⟩
    by_cases zero : value = rationalOfInteger 0
    · simp [rationalBoundary, zero] at member
    · have endpointEq : endpoint = rationalEndpoint value := by
        simpa [rationalBoundary, zero] using member
      subst endpoint
      simp [rationalEndpoint] at equal
      exact zero equal.symm
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

noncomputable def rationalAdditiveGroupResonanceSpec :
    AdditiveGroupResonanceSpec rationalIncidence where
  toFunctionalResonanceSpec := rationalResonanceSpec
  toAssociativeResonanceSpec := rationalAssociativeResonanceSpec
  inverse := rationalNeg
  inverse_mode := by
    intro value
    simpa [rationalIncidence] using rationalAdd_neg value

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

noncomputable def rationalFieldResonanceSpec :
    FieldResonanceSpec rationalIncidence where
  toDistributiveResonanceSpec := rationalDistributiveResonanceSpec
  zero_ne_one := rational_zero_ne_one
  additive_inverse := by
    intro value
    refine ⟨rationalNeg value, ?_⟩
    simpa [rationalIncidence] using rationalAdd_neg value
  multiplicative_inverse := by
    intro value nonzero
    exact rational_nonzero_has_mul_inverse nonzero

noncomputable def rationalOrderedFieldResonanceSpec :
    OrderedFieldResonanceSpec rationalIncidence where
  toFieldResonanceSpec := rationalFieldResonanceSpec
  le := rationalLE
  le_refl := rationalLE_refl
  le_antisymm := by intro i j; exact rationalLE_antisymm
  le_trans := by intro i j k; exact rationalLE_trans
  le_total := rationalLE_total
  add_monotone := by
    intro offset i j outI outJ ordered leftMode rightMode
    have leftEq : rationalAdd offset i = outI := by
      simpa [rationalIncidence] using leftMode
    have rightEq : rationalAdd offset j = outJ := by
      simpa [rationalIncidence] using rightMode
    subst outI
    subst outJ
    exact rationalLE_add_left offset ordered
  multiply_nonnegative := by
    intro i j out iNonnegative jNonnegative multiplied
    have outEq : rationalMul i j = out := by
      simpa [rationalMulResonance] using multiplied
    subst out
    exact rationalMul_nonnegative iNonnegative jNonnegative

theorem rationalIncidence_half_resonance :
    let half := Quotient.mk rationalRepresentativeSetoid
      (rationalRepresentative 1 2 (by omega))
    rationalIncidence.resonance half half (rationalOfInteger 1) := by
  simpa [rationalIncidence] using rational_half_add_half

theorem rationalBoundary_extensional :
    ∀ left right,
      rationalIncidence.typeFunc left = rationalIncidence.typeFunc right →
      boundaryMatched rationalIncidence (· = ·) left right →
      left = right := by
  intro left right _ matched
  by_cases leftZero : left = rationalOfInteger 0
  · subst left
    by_cases rightZero : right = rationalOfInteger 0
    · exact rightZero.symm
    · exfalso
      obtain ⟨candidate, member, _, _⟩ := matched.2
        (rationalEndpoint right) (by
          simp [rationalIncidence, rationalBoundary, rightZero])
      change candidate ∈ rationalBoundary (rationalOfInteger 0) at member
      simp [rationalBoundary] at member
  · by_cases rightZero : right = rationalOfInteger 0
    · subst right
      obtain ⟨candidate, member, _, _⟩ := matched.1
        (rationalEndpoint left) (by
          simp [rationalIncidence, rationalBoundary, leftZero])
      change candidate ∈ rationalBoundary (rationalOfInteger 0) at member
      simp [rationalBoundary] at member
    · obtain ⟨candidate, member, compatible, _⟩ := matched.1
        (rationalEndpoint left) (by
          simp [rationalIncidence, rationalBoundary, leftZero])
      have candidateEq : candidate = rationalEndpoint right := by
        simpa [rationalIncidence, rationalBoundary, rightZero] using member
      subst candidate
      simpa [boundaryCompatible, rationalEndpoint] using compatible.1

theorem rationalIncidence_approxBisim_iff (left right : IncRational) :
    approxBisim rationalIncidence left right ↔ left = right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact incidence_bisim_faithful rationalIncidence rationalRank
      rationalBoundary_decreases rationalBoundary_extensional
      bisimulation left right related
  · rintro rfl
    exact approxBisim_refl rationalIncidence left

theorem rationalQuotientResonanceCongruent :
    QuotientResonanceCongruent rationalIncidence :=
  quotientResonanceCongruent_of_faithful rationalIncidence
    rationalIncidence_approxBisim_iff

end IncidenceCore
