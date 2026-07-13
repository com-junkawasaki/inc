import IncidenceTheory.Rationals

namespace IncidenceCore

/-- A Dedekind real is a nonempty proper lower subset of the reconstructed
rationals with no greatest element. -/
structure IncReal where
  lower : IncRational → Prop
  inhabited : ∃ value, lower value
  proper : ∃ value, ¬ lower value
  downward : ∀ {smaller value}, lower value →
    rationalLT smaller value → lower smaller
  rounded : ∀ {value}, lower value →
    ∃ larger, lower larger ∧ rationalLT value larger

theorem IncReal.ext {left right : IncReal}
    (sameLower : ∀ value, left.lower value ↔ right.lower value) :
    left = right := by
  cases left with
  | mk leftLower leftInhabited leftProper leftDownward leftRounded =>
    cases right with
    | mk rightLower rightInhabited rightProper rightDownward rightRounded =>
      have lowerEq : leftLower = rightLower := by
        funext value
        exact propext (sameLower value)
      subst rightLower
      rfl

def rationalLowerCut (bound value : IncRational) : Prop :=
  rationalLT value bound

/-- The principal Dedekind cut determined by a rational. -/
def rationalToReal (bound : IncRational) : IncReal where
  lower := rationalLowerCut bound
  inhabited := ⟨rationalAdd bound (rationalOfInteger (-1)),
    rational_add_neg_one_lt bound⟩
  proper := ⟨bound, rationalLT_irrefl bound⟩
  downward := by
    intro smaller value valueBelow smallerValue
    exact rationalLT_trans smallerValue valueBelow
  rounded := by
    intro value valueBelow
    obtain ⟨middle, valueMiddle, middleBound⟩ := rationalLT_dense valueBelow
    exact ⟨middle, middleBound, valueMiddle⟩

theorem rationalToReal_lower_iff (bound value : IncRational) :
    (rationalToReal bound).lower value ↔ rationalLT value bound :=
  Iff.rfl

theorem rationalToReal_injective {left right : IncRational}
    (equal : rationalToReal left = rationalToReal right) : left = right := by
  have lowerEq := congrArg IncReal.lower equal
  rcases rationalLT_trichotomy left right with leftRight | equalOrRightLeft
  · obtain ⟨middle, leftMiddle, middleRight⟩ := rationalLT_dense leftRight
    have pointEq := congrFun lowerEq middle
    change rationalLT middle left = rationalLT middle right at pointEq
    have middleLeft : rationalLT middle left := by
      rw [pointEq]
      exact middleRight
    exact False.elim ((rationalLT_asymm leftMiddle) middleLeft)
  · rcases equalOrRightLeft with equal | rightLeft
    · exact equal
    · obtain ⟨middle, rightMiddle, middleLeft⟩ := rationalLT_dense rightLeft
      have pointEq := congrFun lowerEq middle
      change rationalLT middle left = rationalLT middle right at pointEq
      have middleRight : rationalLT middle right := by
        rw [← pointEq]
        exact middleLeft
      exact False.elim ((rationalLT_asymm rightMiddle) middleRight)

theorem rationalToReal_eq_iff (left right : IncRational) :
    rationalToReal left = rationalToReal right ↔ left = right := by
  constructor
  · exact rationalToReal_injective
  · rintro rfl
    rfl

/-- Dedekind order is inclusion of lower cuts. -/
def realLE (left right : IncReal) : Prop :=
  ∀ value : IncRational, left.lower value → right.lower value

theorem realLE_refl (value : IncReal) : realLE value value := by
  intro rational member
  exact member

theorem realLE_trans {first second third : IncReal}
    (firstSecond : realLE first second)
    (secondThird : realLE second third) : realLE first third := by
  intro rational member
  exact secondThird rational (firstSecond rational member)

theorem realLE_antisymm {left right : IncReal}
    (leftRight : realLE left right) (rightLeft : realLE right left) :
    left = right := by
  apply IncReal.ext
  intro rational
  exact ⟨fun member => leftRight rational member,
    fun member => rightLeft rational member⟩

theorem realLE_total (left right : IncReal) :
    realLE left right ∨ realLE right left := by
  classical
  by_cases included : realLE left right
  · exact Or.inl included
  · apply Or.inr
    have witness : ∃ rational, left.lower rational ∧ ¬ right.lower rational := by
      apply Classical.byContradiction
      intro noWitness
      apply included
      intro rational leftBelow
      apply Classical.byContradiction
      intro notRightBelow
      exact noWitness ⟨rational, leftBelow, notRightBelow⟩
    obtain ⟨separator, leftSeparator, notRightSeparator⟩ := witness
    intro rational rightBelow
    rcases rationalLT_trichotomy rational separator with
      rationalSeparator | equalOrSeparatorRational
    · exact left.downward leftSeparator rationalSeparator
    · rcases equalOrSeparatorRational with equal | separatorRational
      · subst rational
        exact False.elim (notRightSeparator rightBelow)
      · have rightSeparator := right.downward rightBelow separatorRational
        exact False.elim (notRightSeparator rightSeparator)

def realLT (left right : IncReal) : Prop :=
  realLE left right ∧ left ≠ right

theorem rationalToReal_lt_of_lower
    (value : IncReal) {rational : IncRational}
    (member : value.lower rational) :
    realLT (rationalToReal rational) value := by
  constructor
  · intro smaller smallerBelow
    exact value.downward member
      ((rationalToReal_lower_iff rational smaller).mp smallerBelow)
  · intro equal
    have rationalMember : (rationalToReal rational).lower rational := by
      rw [equal]
      exact member
    exact rationalLT_irrefl rational
      ((rationalToReal_lower_iff rational rational).mp rationalMember)

theorem realLT_irrefl (value : IncReal) : ¬ realLT value value := by
  intro strict
  exact strict.2 rfl

theorem realLT_trans {first second third : IncReal}
    (firstSecond : realLT first second)
    (secondThird : realLT second third) : realLT first third := by
  refine ⟨realLE_trans firstSecond.1 secondThird.1, ?_⟩
  intro firstThird
  subst third
  exact firstSecond.2 (realLE_antisymm firstSecond.1 secondThird.1)

theorem realLT_of_le_of_lt {first second third : IncReal}
    (firstSecond : realLE first second)
    (secondThird : realLT second third) : realLT first third := by
  refine ⟨realLE_trans firstSecond secondThird.1, ?_⟩
  intro equal
  subst third
  exact secondThird.2 (realLE_antisymm secondThird.1 firstSecond)

theorem realLT_of_lt_of_le {first second third : IncReal}
    (firstSecond : realLT first second)
    (secondThird : realLE second third) : realLT first third := by
  refine ⟨realLE_trans firstSecond.1 secondThird, ?_⟩
  intro equal
  subst third
  exact firstSecond.2 (realLE_antisymm firstSecond.1 secondThird)

theorem IncReal.lt_of_lower_of_not_lower (cut : IncReal)
    {memberValue nonmemberValue : IncRational}
    (member : cut.lower memberValue)
    (nonmember : ¬ cut.lower nonmemberValue) :
    rationalLT memberValue nonmemberValue := by
  rcases rationalLT_trichotomy memberValue nonmemberValue with
    memberNonmember | equalOrReverse
  · exact memberNonmember
  · rcases equalOrReverse with equal | reverse
    · subst nonmemberValue
      exact False.elim (nonmember member)
    · exact False.elim (nonmember (cut.downward member reverse))

/-- Addition of lower cuts: a rational lies below the sum when it lies strictly
below a sum of one member from each operand. -/
def realAdd (left right : IncReal) : IncReal where
  lower := fun value => ∃ leftValue rightValue,
    left.lower leftValue ∧ right.lower rightValue ∧
      rationalLT value (rationalAdd leftValue rightValue)
  inhabited := by
    obtain ⟨leftValue, leftMember⟩ := left.inhabited
    obtain ⟨rightValue, rightMember⟩ := right.inhabited
    exact ⟨rationalAdd (rationalAdd leftValue rightValue)
      (rationalOfInteger (-1)), leftValue, rightValue, leftMember,
      rightMember, rational_add_neg_one_lt _⟩
  proper := by
    obtain ⟨leftBound, leftNotMember⟩ := left.proper
    obtain ⟨rightBound, rightNotMember⟩ := right.proper
    refine ⟨rationalAdd leftBound rightBound, ?_⟩
    rintro ⟨leftValue, rightValue, leftMember, rightMember, boundBelowSum⟩
    have leftBelowBound :=
      left.lt_of_lower_of_not_lower leftMember leftNotMember
    have rightBelowBound :=
      right.lt_of_lower_of_not_lower rightMember rightNotMember
    have sumBelowBound := rationalLT_add leftBelowBound rightBelowBound
    exact (rationalLT_asymm boundBelowSum) sumBelowBound
  downward := by
    intro smaller value member smallerValue
    obtain ⟨leftValue, rightValue, leftMember, rightMember, valueBelow⟩ := member
    exact ⟨leftValue, rightValue, leftMember, rightMember,
      rationalLT_trans smallerValue valueBelow⟩
  rounded := by
    intro value member
    obtain ⟨leftValue, rightValue, leftMember, rightMember, valueBelow⟩ := member
    obtain ⟨middle, valueMiddle, middleBelow⟩ := rationalLT_dense valueBelow
    exact ⟨middle, ⟨leftValue, rightValue, leftMember, rightMember,
      middleBelow⟩, valueMiddle⟩

def realAddResonance (left right mode : IncReal) : Prop :=
  realAdd left right = mode

theorem realAdd_comm (left right : IncReal) :
    realAdd left right = realAdd right left := by
  apply IncReal.ext
  intro value
  constructor
  · rintro ⟨leftValue, rightValue, leftMember, rightMember, below⟩
    refine ⟨rightValue, leftValue, rightMember, leftMember, ?_⟩
    simpa [rationalAdd_comm] using below
  · rintro ⟨rightValue, leftValue, rightMember, leftMember, below⟩
    refine ⟨leftValue, rightValue, leftMember, rightMember, ?_⟩
    simpa [rationalAdd_comm] using below

theorem realAdd_rationalToReal (left right : IncRational) :
    realAdd (rationalToReal left) (rationalToReal right) =
      rationalToReal (rationalAdd left right) := by
  apply IncReal.ext
  intro value
  constructor
  · rintro ⟨leftValue, rightValue, leftBelow, rightBelow, valueBelow⟩
    exact rationalLT_trans valueBelow (rationalLT_add leftBelow rightBelow)
  · intro valueBelow
    let translated := rationalAdd value (rationalNeg right)
    have translatedRestore : rationalAdd translated right = value := by
      exact rationalAdd_sub_cancel value right
    have translatedBelowLeft : rationalLT translated left := by
      apply rationalLT_add_cancel_right right
      rw [translatedRestore]
      exact valueBelow
    obtain ⟨leftValue, translatedLeftValue, leftValueLeft⟩ :=
      rationalLT_dense translatedBelowLeft
    have valueBelowLeftPlusRight :
        rationalLT value (rationalAdd leftValue right) := by
      have shifted := rationalLT_add_right right translatedLeftValue
      rw [translatedRestore] at shifted
      exact shifted
    obtain ⟨sumValue, valueSumValue, sumValueBelow⟩ :=
      rationalLT_dense valueBelowLeftPlusRight
    let rightValue := rationalAdd sumValue (rationalNeg leftValue)
    have rightRestore : rationalAdd rightValue leftValue = sumValue := by
      exact rationalAdd_sub_cancel sumValue leftValue
    have rightValueBelowRight : rationalLT rightValue right := by
      apply rationalLT_add_cancel_right leftValue
      rw [rightRestore, rationalAdd_comm right leftValue]
      exact sumValueBelow
    refine ⟨leftValue, rightValue, leftValueLeft, rightValueBelowRight, ?_⟩
    have sumRestore : rationalAdd leftValue rightValue = sumValue := by
      rw [rationalAdd_comm]
      exact rightRestore
    rw [sumRestore]
    exact valueSumValue

def realZero : IncReal := rationalToReal (rationalOfInteger 0)

theorem realAdd_zero_right (value : IncReal) :
    realAdd value realZero = value := by
  apply IncReal.ext
  intro rational
  constructor
  · rintro ⟨valueMember, zeroMember, inValue, belowZero, belowSum⟩
    have sumBelowValue :
        rationalLT (rationalAdd valueMember zeroMember) valueMember := by
      have shifted := rationalLT_add_left valueMember belowZero
      simpa [rationalAdd_zero_right] using shifted
    exact value.downward inValue (rationalLT_trans belowSum sumBelowValue)
  · intro inValue
    obtain ⟨larger, largerInValue, rationalLarger⟩ := value.rounded inValue
    obtain ⟨middle, rationalMiddle, middleLarger⟩ :=
      rationalLT_dense rationalLarger
    let zeroMember := rationalAdd middle (rationalNeg larger)
    have zeroRestore : rationalAdd zeroMember larger = middle := by
      exact rationalAdd_sub_cancel middle larger
    have zeroMemberBelowZero :
        rationalLT zeroMember (rationalOfInteger 0) := by
      apply rationalLT_add_cancel_right larger
      rw [zeroRestore, rationalAdd_zero_left]
      exact middleLarger
    refine ⟨larger, zeroMember, largerInValue, zeroMemberBelowZero, ?_⟩
    have sumRestore : rationalAdd larger zeroMember = middle := by
      rw [rationalAdd_comm]
      exact zeroRestore
    rw [sumRestore]
    exact rationalMiddle

theorem realAdd_zero_left (value : IncReal) :
    realAdd realZero value = value := by
  rw [realAdd_comm, realAdd_zero_right]

theorem realAdd_assoc_forward (first second third : IncReal) :
    realLE (realAdd (realAdd first second) third)
      (realAdd first (realAdd second third)) := by
  intro value member
  obtain ⟨firstSecondValue, thirdValue, firstSecondMember, thirdMember,
    valueBelow⟩ := member
  obtain ⟨firstValue, secondValue, firstMember, secondMember,
    firstSecondBelow⟩ := firstSecondMember
  have valueBelowExpanded : rationalLT value
      (rationalAdd firstValue (rationalAdd secondValue thirdValue)) := by
    have intermediate := rationalLT_add_right thirdValue firstSecondBelow
    exact rationalLT_trans valueBelow (by
      simpa [rationalAdd_assoc] using intermediate)
  let translated := rationalAdd value (rationalNeg firstValue)
  have translatedRestore : rationalAdd translated firstValue = value := by
    exact rationalAdd_sub_cancel value firstValue
  have translatedBelow :
      rationalLT translated (rationalAdd secondValue thirdValue) := by
    apply rationalLT_add_cancel_right firstValue
    rw [translatedRestore, rationalAdd_comm
      (rationalAdd secondValue thirdValue) firstValue]
    exact valueBelowExpanded
  obtain ⟨secondThirdValue, translatedMiddle, middleBelow⟩ :=
    rationalLT_dense translatedBelow
  have secondThirdMember :
      (realAdd second third).lower secondThirdValue :=
    ⟨secondValue, thirdValue, secondMember, thirdMember, middleBelow⟩
  refine ⟨firstValue, secondThirdValue, firstMember, secondThirdMember, ?_⟩
  have shifted := rationalLT_add_right firstValue translatedMiddle
  rw [translatedRestore, rationalAdd_comm secondThirdValue firstValue] at shifted
  exact shifted

theorem realAdd_assoc (first second third : IncReal) :
    realAdd (realAdd first second) third =
      realAdd first (realAdd second third) := by
  apply realLE_antisymm
  · exact realAdd_assoc_forward first second third
  · have reverse := realAdd_assoc_forward third second first
    simpa [realAdd_comm] using reverse

/-- Negation of a lower cut uses the complement reflected through rational
zero, with strict rounding built into the existential witness. -/
def realNeg (value : IncReal) : IncReal where
  lower := fun rational => ∃ outside, ¬ value.lower outside ∧
    rationalLT rational (rationalNeg outside)
  inhabited := by
    obtain ⟨outside, notMember⟩ := value.proper
    exact ⟨rationalAdd (rationalNeg outside) (rationalOfInteger (-1)),
      outside, notMember, rational_add_neg_one_lt _⟩
  proper := by
    obtain ⟨memberValue, member⟩ := value.inhabited
    refine ⟨rationalNeg memberValue, ?_⟩
    rintro ⟨outside, notMember, below⟩
    have outsideBelowMember : rationalLT outside memberValue := by
      have reversed := rationalLT_neg_reverse below
      simpa [rationalNeg_neg] using reversed
    exact notMember (value.downward member outsideBelowMember)
  downward := by
    intro smaller rational member smallerRational
    obtain ⟨outside, notMember, below⟩ := member
    exact ⟨outside, notMember, rationalLT_trans smallerRational below⟩
  rounded := by
    intro rational member
    obtain ⟨outside, notMember, below⟩ := member
    obtain ⟨middle, rationalMiddle, middleBelow⟩ := rationalLT_dense below
    exact ⟨middle, ⟨outside, notMember, middleBelow⟩, rationalMiddle⟩

theorem realNeg_rationalToReal (value : IncRational) :
    realNeg (rationalToReal value) = rationalToReal (rationalNeg value) := by
  apply IncReal.ext
  intro rational
  constructor
  · rintro ⟨outside, notBelow, rationalBelow⟩
    have valueOutside : rationalLE value outside := by
      rcases rationalLE_total value outside with ordered | reverse
      · exact ordered
      · by_cases equal : outside = value
        · subst outside
          exact rationalLE_refl value
        · exact False.elim (notBelow ⟨reverse, equal⟩)
    exact rationalLT_of_lt_of_le rationalBelow
      (rationalLE_neg_reverse valueOutside)
  · intro rationalBelow
    exact ⟨value, rationalLT_irrefl value, rationalBelow⟩

theorem realNeg_order_reverse {left right : IncReal}
    (ordered : realLE left right) : realLE (realNeg right) (realNeg left) := by
  intro rational member
  obtain ⟨outside, notRight, below⟩ := member
  exact ⟨outside, fun leftMember => notRight (ordered outside leftMember), below⟩

theorem realNeg_neg (value : IncReal) : realNeg (realNeg value) = value := by
  apply IncReal.ext
  intro rational
  constructor
  · rintro ⟨outside, notNegMember, rationalBelow⟩
    apply Classical.byContradiction
    intro notMember
    have outsideBelowNegRational :
        rationalLT outside (rationalNeg rational) := by
      have reversed := rationalLT_neg_reverse rationalBelow
      simpa [rationalNeg_neg] using reversed
    exact notNegMember ⟨rational, notMember, outsideBelowNegRational⟩
  · intro member
    obtain ⟨larger, largerMember, rationalLarger⟩ := value.rounded member
    refine ⟨rationalNeg larger, ?_, ?_⟩
    · rintro ⟨outside, notMember, negLargerBelow⟩
      have outsideBelowLarger : rationalLT outside larger := by
        have reversed := rationalLT_neg_reverse negLargerBelow
        simpa [rationalNeg_neg] using reversed
      exact notMember (value.downward largerMember outsideBelowLarger)
    · simpa [rationalNeg_neg] using rationalLarger

theorem realNeg_zero : realNeg realZero = realZero := by
  simpa [realZero, rationalNeg_zero] using
    realNeg_rationalToReal (rationalOfInteger 0)

theorem realNeg_order_iff (left right : IncReal) :
    realLE (realNeg right) (realNeg left) ↔ realLE left right := by
  constructor
  · intro ordered
    have reversed := realNeg_order_reverse ordered
    simpa [realNeg_neg] using reversed
  · exact realNeg_order_reverse

theorem realAdd_neg_principal (value : IncRational) :
    realAdd (rationalToReal value) (realNeg (rationalToReal value)) =
      realZero := by
  rw [realNeg_rationalToReal, realAdd_rationalToReal, rationalAdd_neg]
  rfl

theorem nat_exists_minimal {predicate : Nat → Prop}
    (existsPredicate : ∃ count, predicate count) :
    ∃ count, predicate count ∧
      ∀ earlier, earlier < count → ¬ predicate earlier := by
  obtain ⟨witness, witnessProperty⟩ := existsPredicate
  have minimalFrom : ∀ count, predicate count →
      ∃ least, predicate least ∧
        ∀ earlier, earlier < least → ¬ predicate earlier := by
    intro count
    induction count using Nat.strongRecOn with
    | _ count induction =>
      intro countProperty
      by_cases earlierExists :
          ∃ earlier, earlier < count ∧ predicate earlier
      · obtain ⟨earlier, earlierLess, earlierProperty⟩ := earlierExists
        exact induction earlier earlierLess earlierProperty
      · exact ⟨count, countProperty, fun earlier earlierLess earlierProperty =>
          earlierExists ⟨earlier, earlierLess, earlierProperty⟩⟩
  exact minimalFrom witness witnessProperty

theorem IncReal.boundary_approximation (value : IncReal) {step : IncRational}
    (stepPositive : rationalLT (rationalOfInteger 0) step) :
    ∃ inside outside,
      value.lower inside ∧ ¬ value.lower outside ∧
        outside = rationalAdd inside step := by
  obtain ⟨start, startMember⟩ := value.inhabited
  obtain ⟨target, targetNotMember⟩ := value.proper
  obtain ⟨eventualCount, targetBelow⟩ :=
    rational_archimedean_steps (start := start) (target := target) stepPositive
  have exitExists : ∃ count, ¬ value.lower (rationalStepValue start step count) := by
    refine ⟨eventualCount, ?_⟩
    intro eventualMember
    exact targetNotMember (value.downward eventualMember targetBelow)
  obtain ⟨firstExit, firstExitProperty, exitMinimal⟩ :=
    nat_exists_minimal exitExists
  cases firstExit with
  | zero =>
      exact False.elim (firstExitProperty (by
        simpa [rationalStepValue_zero] using startMember))
  | succ previous =>
      have previousMember :
          value.lower (rationalStepValue start step previous) := by
        apply Classical.byContradiction
        intro previousNotMember
        exact (exitMinimal previous (Nat.lt_succ_self previous)) previousNotMember
      refine ⟨rationalStepValue start step previous,
        rationalStepValue start step (previous + 1), previousMember, ?_, ?_⟩
      · simpa using firstExitProperty
      · exact rationalStepValue_succ start step previous

theorem realAdd_neg (value : IncReal) :
    realAdd value (realNeg value) = realZero := by
  apply realLE_antisymm
  · intro rational member
    obtain ⟨inside, negMember, insideMember, negMemberProof, rationalBelow⟩ := member
    obtain ⟨outside, outsideNotMember, negBelowOutside⟩ := negMemberProof
    have insideBelowOutside :=
      value.lt_of_lower_of_not_lower insideMember outsideNotMember
    have insideNegBelow :
        rationalLT (rationalAdd inside negMember)
          (rationalAdd inside (rationalNeg outside)) :=
      rationalLT_add_left inside negBelowOutside
    have insideOutsideBelowZero :
        rationalLT (rationalAdd inside (rationalNeg outside))
          (rationalOfInteger 0) := by
      have shifted := rationalLT_add_right (rationalNeg outside)
        insideBelowOutside
      simpa [rationalAdd_neg] using shifted
    exact rationalLT_trans rationalBelow
      (rationalLT_trans insideNegBelow insideOutsideBelowZero)
  · intro rational rationalBelowZero
    have zeroBelowNegRational :
        rationalLT (rationalOfInteger 0) (rationalNeg rational) := by
      have reversed := rationalLT_neg_reverse rationalBelowZero
      simpa [rationalNeg_zero, rationalNeg_neg] using reversed
    obtain ⟨step, zeroBelowStep, stepBelowNegRational⟩ :=
      rationalLT_dense zeroBelowNegRational
    obtain ⟨inside, outside, insideMember, outsideNotMember, outsideStep⟩ :=
      value.boundary_approximation zeroBelowStep
    have rationalBelowNegStep : rationalLT rational (rationalNeg step) := by
      have reversed := rationalLT_neg_reverse stepBelowNegRational
      simpa [rationalNeg_neg] using reversed
    have insideNegOutsideEq :
        rationalAdd inside (rationalNeg outside) = rationalNeg step := by
      rw [outsideStep, rationalNeg_add, ← rationalAdd_assoc,
        rationalAdd_neg, rationalAdd_zero_left]
    have rationalBelowInsideNegOutside :
        rationalLT rational (rationalAdd inside (rationalNeg outside)) := by
      rw [insideNegOutsideEq]
      exact rationalBelowNegStep
    let translated := rationalAdd rational (rationalNeg inside)
    have translatedRestore : rationalAdd translated inside = rational := by
      exact rationalAdd_sub_cancel rational inside
    have translatedBelowNegOutside :
        rationalLT translated (rationalNeg outside) := by
      apply rationalLT_add_cancel_right inside
      rw [translatedRestore, rationalAdd_comm (rationalNeg outside) inside]
      exact rationalBelowInsideNegOutside
    obtain ⟨negInside, translatedNegInside, negInsideBelow⟩ :=
      rationalLT_dense translatedBelowNegOutside
    have negInsideMember : (realNeg value).lower negInside :=
      ⟨outside, outsideNotMember, negInsideBelow⟩
    refine ⟨inside, negInside, insideMember, negInsideMember, ?_⟩
    have shifted := rationalLT_add_right inside translatedNegInside
    rw [translatedRestore, rationalAdd_comm negInside inside] at shifted
    exact shifted

theorem realAdd_neg_left (value : IncReal) :
    realAdd (realNeg value) value = realZero := by
  rw [realAdd_comm, realAdd_neg]

theorem realAdd_cancel_left (offset left right : IncReal)
    (equal : realAdd offset left = realAdd offset right) : left = right := by
  have shifted := congrArg (realAdd (realNeg offset)) equal
  calc
    left = realAdd realZero left := (realAdd_zero_left left).symm
    _ = realAdd (realAdd (realNeg offset) offset) left := by
      rw [realAdd_neg_left]
    _ = realAdd (realNeg offset) (realAdd offset left) :=
      realAdd_assoc _ _ _
    _ = realAdd (realNeg offset) (realAdd offset right) := shifted
    _ = realAdd (realAdd (realNeg offset) offset) right :=
      (realAdd_assoc _ _ _).symm
    _ = realAdd realZero right := by rw [realAdd_neg_left]
    _ = right := realAdd_zero_left right

theorem realAdd_cancel_right (left right offset : IncReal)
    (equal : realAdd left offset = realAdd right offset) : left = right := by
  apply realAdd_cancel_left offset
  simpa [realAdd_comm] using equal

theorem real_eq_add_neg_of_add_eq {left offset result : IncReal}
    (equal : realAdd left offset = result) :
    left = realAdd result (realNeg offset) := by
  apply realAdd_cancel_right left (realAdd result (realNeg offset)) offset
  rw [equal, realAdd_assoc, realAdd_neg_left, realAdd_zero_right]

theorem realNeg_add (left right : IncReal) :
    realNeg (realAdd left right) =
      realAdd (realNeg left) (realNeg right) := by
  apply realAdd_cancel_left (realAdd left right)
  rw [realAdd_neg]
  symm
  calc
    realAdd (realAdd left right)
        (realAdd (realNeg left) (realNeg right)) =
      realAdd (realAdd left (realNeg left))
        (realAdd right (realNeg right)) := by
          rw [realAdd_assoc, ← realAdd_assoc right,
            realAdd_comm right (realNeg left),
            realAdd_assoc (realNeg left), ← realAdd_assoc left]
    _ = realZero := by rw [realAdd_neg, realAdd_neg, realAdd_zero_left]

theorem realNeg_eq_add_neg_of_add_eq {left offset result : IncReal}
    (equal : realAdd left offset = result) :
    realNeg offset = realAdd left (realNeg result) := by
  apply realAdd_cancel_right (realNeg offset)
    (realAdd left (realNeg result)) offset
  rw [realAdd_neg_left]
  symm
  calc
    realAdd (realAdd left (realNeg result)) offset =
        realAdd (realAdd left offset) (realNeg result) := by
      rw [realAdd_assoc, realAdd_comm (realNeg result) offset,
        ← realAdd_assoc]
    _ = realAdd result (realNeg result) := by rw [equal]
    _ = realZero := realAdd_neg result

noncomputable instance : DecidableEq IncReal :=
  Classical.typeDecidableEq IncReal

inductive RealRole where
  | observe : IncReal → RealRole

noncomputable instance : DecidableEq RealRole :=
  Classical.typeDecidableEq RealRole

noncomputable def realEndpoint (value : IncReal) : Endpoint IncReal RealRole :=
  { i := realZero
    role := .observe value
    sign := .neg
    mult := 1
    mult_pos := by omega }

noncomputable def realBoundary (value : IncReal) : Boundary IncReal RealRole :=
  if value = realZero then [] else [realEndpoint value]

noncomputable def realRank (value : IncReal) : Nat :=
  if value = realZero then 0 else 1

theorem realBoundary_decreases :
    ∀ value endpoint, endpoint ∈ realBoundary value →
      realRank endpoint.i < realRank value := by
  intro value endpoint member
  by_cases zero : value = realZero
  · simp [realBoundary, zero] at member
  · have endpointEq : endpoint = realEndpoint value := by
      simpa [realBoundary, zero] using member
    subst endpoint
    simp [realEndpoint, realRank, zero]

noncomputable def realIncidence : Incidence IncReal RealRole GraphType where
  boundary := realBoundary
  typeFunc := fun _ => GraphType.unit
  glue := fun left right => some (realAdd left right)
  unit := realZero
  guards := Guards.permissive IncReal
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro _ endpoint _; cases endpoint.sign <;> simp
  multiplicities := fun _ endpoint _ => endpoint.mult_pos
  well_founded := by
    intro value ⟨endpoint, member, equal⟩
    by_cases zero : value = realZero
    · simp [realBoundary, zero] at member
    · have endpointEq : endpoint = realEndpoint value := by
        simpa [realBoundary, zero] using member
      subst endpoint
      simp [realEndpoint] at equal
      exact zero equal.symm
  unit_left := fun value => congrArg some (realAdd_zero_left value)
  unit_right := fun value => congrArg some (realAdd_zero_right value)
  type_preserve := by intro _ _ _ _ _; rfl

noncomputable def realResonanceSpec :
    FunctionalResonanceSpec realIncidence where
  symmetric := by
    intro left right mode resonant
    simpa [realIncidence, realAdd_comm] using resonant
  unit_left := by intro value; simp [realIncidence, realAdd_zero_left]
  unit_right := by intro value; simp [realIncidence, realAdd_zero_right]
  type_compatible := by intro _ _ _ _; exact ⟨rfl, rfl⟩
  selected_complete := by intro _ _ _ resonant; exact resonant

noncomputable def realAssociativeResonanceSpec :
    AssociativeResonanceSpec realIncidence where
  reassociate := by
    intro first second third out
    constructor
    · rintro ⟨firstSecond, firstMode, outMode⟩
      have firstSecondEq : realAdd first second = firstSecond := by
        simpa [realIncidence] using firstMode
      subst firstSecond
      refine ⟨realAdd second third, ?_, ?_⟩
      · simp [realIncidence]
      · simpa [realIncidence, realAdd_assoc] using outMode
    · rintro ⟨secondThird, secondMode, outMode⟩
      have secondThirdEq : realAdd second third = secondThird := by
        simpa [realIncidence] using secondMode
      subst secondThird
      refine ⟨realAdd first second, ?_, ?_⟩
      · simp [realIncidence]
      · simpa [realIncidence, realAdd_assoc] using outMode

noncomputable def realAdditiveGroupResonanceSpec :
    AdditiveGroupResonanceSpec realIncidence where
  toFunctionalResonanceSpec := realResonanceSpec
  toAssociativeResonanceSpec := realAssociativeResonanceSpec
  inverse := realNeg
  inverse_mode := by
    intro value
    simpa [realIncidence] using realAdd_neg value

theorem realBoundary_extensional :
    ∀ left right,
      realIncidence.typeFunc left = realIncidence.typeFunc right →
      boundaryMatched realIncidence (· = ·) left right → left = right := by
  intro left right _ matched
  by_cases leftZero : left = realZero
  · subst left
    by_cases rightZero : right = realZero
    · exact rightZero.symm
    · exfalso
      obtain ⟨candidate, member, _, _⟩ := matched.2
        (realEndpoint right) (by simp [realIncidence, realBoundary, rightZero])
      change candidate ∈ realBoundary realZero at member
      simp [realBoundary] at member
  · by_cases rightZero : right = realZero
    · subst right
      obtain ⟨candidate, member, _, _⟩ := matched.1
        (realEndpoint left) (by simp [realIncidence, realBoundary, leftZero])
      change candidate ∈ realBoundary realZero at member
      simp [realBoundary] at member
    · obtain ⟨candidate, member, compatible, _⟩ := matched.1
        (realEndpoint left) (by simp [realIncidence, realBoundary, leftZero])
      have candidateEq : candidate = realEndpoint right := by
        simpa [realIncidence, realBoundary, rightZero] using member
      subst candidate
      simpa [boundaryCompatible, realEndpoint] using compatible.1

theorem realIncidence_approxBisim_iff (left right : IncReal) :
    approxBisim realIncidence left right ↔ left = right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact incidence_bisim_faithful realIncidence realRank
      realBoundary_decreases realBoundary_extensional
      bisimulation left right related
  · rintro rfl
    exact approxBisim_refl realIncidence left

theorem realQuotientResonanceCongruent :
    QuotientResonanceCongruent realIncidence :=
  quotientResonanceCongruent_of_faithful realIncidence
    realIncidence_approxBisim_iff

theorem realAdd_monotone_left {left left' right : IncReal}
    (ordered : realLE left left') :
    realLE (realAdd left right) (realAdd left' right) := by
  intro value member
  obtain ⟨leftValue, rightValue, leftMember, rightMember, below⟩ := member
  exact ⟨leftValue, rightValue, ordered leftValue leftMember,
    rightMember, below⟩

theorem realAdd_monotone_right {left right right' : IncReal}
    (ordered : realLE right right') :
    realLE (realAdd left right) (realAdd left right') := by
  rw [realAdd_comm left right, realAdd_comm left right']
  exact realAdd_monotone_left ordered

theorem realAdd_monotone {left left' right right' : IncReal}
    (leftOrdered : realLE left left') (rightOrdered : realLE right right') :
    realLE (realAdd left right) (realAdd left' right') :=
  realLE_trans (realAdd_monotone_left leftOrdered)
    (realAdd_monotone_right rightOrdered)

theorem rationalToReal_le_iff (left right : IncRational) :
    realLE (rationalToReal left) (rationalToReal right) ↔
      rationalLE left right := by
  constructor
  · intro included
    rcases rationalLT_trichotomy left right with leftRight | equalOrRightLeft
    · exact leftRight.1
    · rcases equalOrRightLeft with equal | rightLeft
      · subst right
        exact rationalLE_refl left
      · obtain ⟨middle, rightMiddle, middleLeft⟩ := rationalLT_dense rightLeft
        have middleRight : rationalLT middle right := included middle middleLeft
        exact False.elim ((rationalLT_asymm rightMiddle) middleRight)
  · intro ordered rational rationalLeft
    by_cases equal : left = right
    · subst right
      exact rationalLeft
    · exact rationalLT_trans rationalLeft ⟨ordered, equal⟩

theorem rationalToReal_lt_reflects {left right : IncRational}
    (strict : realLE (rationalToReal left) (rationalToReal right))
    (distinct : rationalToReal left ≠ rationalToReal right) :
    rationalLT left right := by
  exact ⟨(rationalToReal_le_iff left right).mp strict,
    fun equal => distinct (congrArg rationalToReal equal)⟩

theorem rationalToReal_lt_preserves {left right : IncRational}
    (strict : rationalLT left right) :
    realLT (rationalToReal left) (rationalToReal right) := by
  exact ⟨(rationalToReal_le_iff left right).mpr strict.1,
    fun equal => strict.2 (rationalToReal_injective equal)⟩

theorem realLT_has_rational_separator {left right : IncReal}
    (strict : realLT left right) :
    ∃ rational : IncRational,
      realLE left (rationalToReal rational) ∧
      realLT (rationalToReal rational) right := by
  have witnessExists : ∃ rational, right.lower rational ∧ ¬ left.lower rational := by
    apply Classical.byContradiction
    intro noWitness
    have reverse : realLE right left := by
      intro rational rightMember
      by_cases leftMember : left.lower rational
      · exact leftMember
      · exact False.elim (noWitness ⟨rational, rightMember, leftMember⟩)
    exact strict.2 (realLE_antisymm strict.1 reverse)
  obtain ⟨separator, rightMember, leftNotMember⟩ := witnessExists
  have leftBelow : realLE left (rationalToReal separator) := by
    intro rational member
    exact left.lt_of_lower_of_not_lower member leftNotMember
  exact ⟨separator, leftBelow,
    rationalToReal_lt_of_lower right rightMember⟩

theorem real_exists_rational_below (value : IncReal) :
    ∃ rational, realLT (rationalToReal rational) value := by
  obtain ⟨member, memberProof⟩ := value.inhabited
  exact ⟨member, rationalToReal_lt_of_lower value memberProof⟩

theorem real_exists_rational_above (value : IncReal) :
    ∃ rational, realLT value (rationalToReal rational) := by
  obtain ⟨bound, boundNotMember⟩ := value.proper
  let larger := rationalAdd bound (rationalOfInteger 1)
  have boundLarger : rationalLT bound larger := rational_lt_add_one bound
  have valueBelowBound : realLE value (rationalToReal bound) := by
    intro rational member
    exact value.lt_of_lower_of_not_lower member boundNotMember
  exact ⟨larger, realLT_of_le_of_lt valueBelowBound
    (rationalToReal_lt_preserves boundLarger)⟩

def RealUpperBound (family : IncReal → Prop) (upper : IncReal) : Prop :=
  ∀ value, family value → realLE value upper

/-- The supremum of a nonempty bounded family is the union of its lower cuts. -/
def realSup (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper) : IncReal where
  lower := fun rational => ∃ value, family value ∧ value.lower rational
  inhabited := by
    obtain ⟨value, member⟩ := nonempty
    obtain ⟨rational, below⟩ := value.inhabited
    exact ⟨rational, value, member, below⟩
  proper := by
    obtain ⟨upper, isUpper⟩ := bounded
    obtain ⟨rational, notBelow⟩ := upper.proper
    refine ⟨rational, ?_⟩
    rintro ⟨value, member, below⟩
    exact notBelow (isUpper value member rational below)
  downward := by
    intro smaller rational member smallerRational
    obtain ⟨value, inFamily, below⟩ := member
    exact ⟨value, inFamily, value.downward below smallerRational⟩
  rounded := by
    intro rational member
    obtain ⟨value, inFamily, below⟩ := member
    obtain ⟨larger, largerBelow, rationalLarger⟩ := value.rounded below
    exact ⟨larger, ⟨value, inFamily, largerBelow⟩, rationalLarger⟩

theorem realSup_is_upper_bound (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper) :
    RealUpperBound family (realSup family nonempty bounded) := by
  intro value member rational below
  exact ⟨value, member, below⟩

theorem realSup_is_least (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper)
    {upper : IncReal} (isUpper : RealUpperBound family upper) :
    realLE (realSup family nonempty bounded) upper := by
  intro rational member
  obtain ⟨value, inFamily, below⟩ := member
  exact isUpper value inFamily rational below

theorem real_least_upper_bound (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper) :
    RealUpperBound family (realSup family nonempty bounded) ∧
      ∀ {upper}, RealUpperBound family upper →
        realLE (realSup family nonempty bounded) upper :=
  ⟨realSup_is_upper_bound family nonempty bounded,
    fun isUpper => realSup_is_least family nonempty bounded isUpper⟩

structure NonnegativeReal where
  value : IncReal
  nonnegative : realLE realZero value

theorem NonnegativeReal.ext {left right : NonnegativeReal}
    (equal : left.value = right.value) : left = right := by
  cases left
  cases right
  cases equal
  rfl

theorem NonnegativeReal.negative_mem (value : NonnegativeReal)
    {rational : IncRational}
    (negative : rationalLT rational (rationalOfInteger 0)) :
    value.value.lower rational :=
  value.nonnegative rational negative

theorem NonnegativeReal.positive_upper (value : NonnegativeReal) :
    ∃ bound, ¬ value.value.lower bound ∧
      rationalLT (rationalOfInteger 0) bound := by
  obtain ⟨outside, outsideNotMember⟩ := value.value.proper
  have outsideNonnegative : rationalLE (rationalOfInteger 0) outside := by
    rcases rationalLE_total (rationalOfInteger 0) outside with ordered | reverse
    · exact ordered
    · by_cases equal : outside = rationalOfInteger 0
      · subst outside
        exact rationalLE_refl _
      · have outsideNegative :
            rationalLT outside (rationalOfInteger 0) :=
          ⟨reverse, equal⟩
        exact False.elim (outsideNotMember (value.negative_mem outsideNegative))
  let bound := rationalAdd outside (rationalOfInteger 1)
  have outsideBound : rationalLT outside bound := rational_lt_add_one outside
  refine ⟨bound, ?_, rationalLT_of_le_of_lt outsideNonnegative outsideBound⟩
  intro boundMember
  exact outsideNotMember (value.value.downward boundMember outsideBound)

theorem real_archimedean_nat_upper (value : IncReal) :
    ∃ count : Nat,
      realLT value
        (rationalToReal (rationalOfInteger (Int.ofNat count))) := by
  obtain ⟨bound, boundNotMember⟩ := value.proper
  obtain ⟨count, countBoundRaw⟩ := rational_archimedean_steps
    (start := rationalOfInteger 0) (target := bound)
    (step := rationalOfInteger 1) rational_zero_lt_one
  have countBound :
      rationalLT bound (rationalOfInteger (Int.ofNat count)) := by
    simpa [rationalStepValue, rationalNatScale,
      rationalAdd_zero_left, rationalMul_one_right] using countBoundRaw
  have valueBelowBound : realLE value (rationalToReal bound) := by
    intro rational member
    exact value.lt_of_lower_of_not_lower member boundNotMember
  exact ⟨count, realLT_of_le_of_lt valueBelowBound
    (rationalToReal_lt_preserves countBound)⟩

theorem NonnegativeReal.exists_positive_member (value : NonnegativeReal)
    (nonzero : value.value ≠ realZero) :
    ∃ rational, value.value.lower rational ∧
      rationalLT (rationalOfInteger 0) rational := by
  classical
  by_cases positiveExists : ∃ rational, value.value.lower rational ∧
      rationalLT (rationalOfInteger 0) rational
  · exact positiveExists
  · exact False.elim (nonzero (by
      apply Eq.symm
      apply realLE_antisymm value.nonnegative
      intro rational member
      obtain ⟨larger, largerMember, rationalLarger⟩ :=
        value.value.rounded member
      have largerNotPositive :
          ¬ rationalLT (rationalOfInteger 0) larger := by
        intro largerPositive
        exact positiveExists ⟨larger, largerMember, largerPositive⟩
      exact rationalLT_of_lt_of_le rationalLarger
        (rationalLE_of_not_lt largerNotPositive)))

theorem nonnegativeReal_exists_nat_reciprocal_below
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero) :
    ∃ count : Nat, ∃ inverse : IncRational,
      rationalLT (rationalOfInteger 0)
        (rationalOfInteger (Int.ofNat count)) ∧
      rationalMul (rationalOfInteger (Int.ofNat count)) inverse =
        rationalOfInteger 1 ∧
      realLT (rationalToReal inverse) value.value := by
  obtain ⟨inside, insideMember, insidePositive⟩ :=
    value.exists_positive_member nonzero
  obtain ⟨count, countLargeRaw⟩ := rational_archimedean_steps
    (start := rationalOfInteger 0) (target := rationalOfInteger 1)
    (step := inside) insidePositive
  let countRational := rationalOfInteger (Int.ofNat count)
  have countLarge :
      rationalLT (rationalOfInteger 1)
        (rationalMul countRational inside) := by
    simpa [rationalStepValue, rationalNatScale,
      rationalAdd_zero_left] using countLargeRaw
  have countPositive :
      rationalLT (rationalOfInteger 0) countRational := by
    cases count with
    | zero =>
        dsimp [countRational] at countLarge ⊢
        rw [rationalMul_zero_left] at countLarge
        exact False.elim
          ((rationalLT_asymm rational_zero_lt_one) countLarge)
    | succ count =>
        dsimp [countRational]
        refine ⟨(rationalOfInteger_le_iff 0
          (Int.ofNat (Nat.succ count))).mpr (Int.ofNat_zero_le _), ?_⟩
        intro equal
        have integerEqual := rationalOfInteger_injective equal
        omega
  have countNonzero : countRational ≠ rationalOfInteger 0 := fun equal => by
    exact countPositive.2 equal.symm
  obtain ⟨inverse, inverseLaw⟩ :=
    rational_nonzero_has_mul_inverse countNonzero
  have inversePositive : rationalLT (rationalOfInteger 0) inverse := by
    apply rationalMul_positive_reflect_right countPositive
    rw [inverseLaw]
    exact rational_zero_lt_one
  have inverseBelowInside : rationalLT inverse inside := by
    have multiplied := rationalLT_mul_right_of_positive
      countLarge inversePositive
    have leftRestore :
        rationalMul (rationalOfInteger 1) inverse = inverse :=
      rationalMul_one_left inverse
    have rightRestore :
        rationalMul (rationalMul countRational inside) inverse = inside := by
      calc
        _ = rationalMul countRational (rationalMul inside inverse) :=
          rationalMul_assoc countRational inside inverse
        _ = rationalMul countRational (rationalMul inverse inside) := by
          rw [rationalMul_comm inside inverse]
        _ = rationalMul (rationalMul countRational inverse) inside :=
          (rationalMul_assoc countRational inverse inside).symm
        _ = rationalMul inside (rationalMul countRational inverse) := by
          rw [rationalMul_comm]
        _ = rationalMul inside (rationalOfInteger 1) := by rw [inverseLaw]
        _ = inside := rationalMul_one_right inside
    rw [leftRestore, rightRestore] at multiplied
    exact multiplied
  exact ⟨count, inverse, countPositive, inverseLaw,
    realLT_trans (rationalToReal_lt_preserves inverseBelowInside)
      (rationalToReal_lt_of_lower value.value insideMember)⟩

theorem NonnegativeReal.exists_positive_member_above
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero)
    {rational : IncRational} (member : value.value.lower rational) :
    ∃ larger, value.value.lower larger ∧
      rationalLT (rationalOfInteger 0) larger ∧
      rationalLT rational larger := by
  obtain ⟨positive, positiveMember, positiveValue⟩ :=
    value.exists_positive_member nonzero
  obtain ⟨rounded, roundedMember, rationalRounded⟩ :=
    value.value.rounded member
  by_cases roundedPositive :
      rationalLT (rationalOfInteger 0) rounded
  · exact ⟨rounded, roundedMember, roundedPositive, rationalRounded⟩
  · have roundedNonpositive :
        rationalLE rounded (rationalOfInteger 0) :=
      rationalLE_of_not_lt roundedPositive
    have roundedBelowPositive : rationalLT rounded positive :=
      rationalLT_of_le_of_lt roundedNonpositive positiveValue
    exact ⟨positive, positiveMember, positiveValue,
      rationalLT_trans rationalRounded roundedBelowPositive⟩

theorem NonnegativeReal.exists_positive_member_above_two
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero)
    {first second : IncRational}
    (firstMember : value.value.lower first)
    (secondMember : value.value.lower second) :
    ∃ larger, value.value.lower larger ∧
      rationalLT (rationalOfInteger 0) larger ∧
      rationalLT first larger ∧ rationalLT second larger := by
  rcases rationalLE_total first second with firstSecond | secondFirst
  · obtain ⟨larger, largerMember, largerPositive, secondLarger⟩ :=
      value.exists_positive_member_above nonzero secondMember
    exact ⟨larger, largerMember, largerPositive,
      rationalLT_of_le_of_lt firstSecond secondLarger, secondLarger⟩
  · obtain ⟨larger, largerMember, largerPositive, firstLarger⟩ :=
      value.exists_positive_member_above nonzero firstMember
    exact ⟨larger, largerMember, largerPositive, firstLarger,
      rationalLT_of_le_of_lt secondFirst firstLarger⟩

/-- Addition restricted to the nonnegative cone. -/
def nonnegativeRealAdd (left right : NonnegativeReal) : NonnegativeReal where
  value := realAdd left.value right.value
  nonnegative := by
    have included := realAdd_monotone left.nonnegative right.nonnegative
    simpa [realAdd_zero_left] using included

theorem nonnegativeRealAdd_comm (left right : NonnegativeReal) :
    nonnegativeRealAdd left right = nonnegativeRealAdd right left := by
  apply NonnegativeReal.ext
  exact realAdd_comm left.value right.value

theorem nonnegativeRealAdd_assoc (first second third : NonnegativeReal) :
    nonnegativeRealAdd (nonnegativeRealAdd first second) third =
      nonnegativeRealAdd first (nonnegativeRealAdd second third) := by
  apply NonnegativeReal.ext
  exact realAdd_assoc first.value second.value third.value

def nonnegativeZero : NonnegativeReal where
  value := realZero
  nonnegative := realLE_refl realZero

theorem nonnegativeRealAdd_zero_right (value : NonnegativeReal) :
    nonnegativeRealAdd value nonnegativeZero = value := by
  apply NonnegativeReal.ext
  exact realAdd_zero_right value.value

theorem nonnegativeRealAdd_zero_left (value : NonnegativeReal) :
    nonnegativeRealAdd nonnegativeZero value = value := by
  rw [nonnegativeRealAdd_comm, nonnegativeRealAdd_zero_right]

/-- Multiplication on the nonnegative cone. All negative rationals are below
the product; nonnegative information is generated by strictly positive members
of the two operand cuts. -/
def nonnegativeRealMul (left right : NonnegativeReal) : NonnegativeReal where
  value :=
    { lower := fun rational =>
        rationalLT rational (rationalOfInteger 0) ∨
          ∃ leftValue rightValue,
            left.value.lower leftValue ∧ right.value.lower rightValue ∧
            rationalLT (rationalOfInteger 0) leftValue ∧
            rationalLT (rationalOfInteger 0) rightValue ∧
            rationalLT rational (rationalMul leftValue rightValue)
      inhabited := ⟨rationalOfInteger (-1), by
        left
        exact (rationalOfInteger_le_iff (-1) 0).mpr (by omega) |>
          fun ordered => ⟨ordered, by
            intro equal
            have impossible := rationalOfInteger_injective equal
            omega⟩⟩
      proper := by
        obtain ⟨leftBound, leftNotMember, leftBoundPositive⟩ := left.positive_upper
        obtain ⟨rightBound, rightNotMember, rightBoundPositive⟩ := right.positive_upper
        refine ⟨rationalMul leftBound rightBound, ?_⟩
        intro member
        rcases member with negative | generated
        · exact (rationalLT_asymm
            (rationalMul_positive leftBoundPositive rightBoundPositive)) negative
        · obtain ⟨leftValue, rightValue, leftMember, rightMember,
            leftPositive, rightPositive, boundBelowProduct⟩ := generated
          have leftBelowBound := left.value.lt_of_lower_of_not_lower
            leftMember leftNotMember
          have rightBelowBound := right.value.lt_of_lower_of_not_lower
            rightMember rightNotMember
          have productBelowBound := rationalLT_mul_of_positive
            leftBelowBound rightBelowBound rightPositive leftBoundPositive
          exact (rationalLT_asymm boundBelowProduct) productBelowBound
      downward := by
        intro smaller rational member smallerRational
        rcases member with negative | generated
        · exact Or.inl (rationalLT_trans smallerRational negative)
        · obtain ⟨leftValue, rightValue, leftMember, rightMember,
            leftPositive, rightPositive, below⟩ := generated
          exact Or.inr ⟨leftValue, rightValue, leftMember, rightMember,
            leftPositive, rightPositive, rationalLT_trans smallerRational below⟩
      rounded := by
        intro rational member
        rcases member with negative | generated
        · obtain ⟨middle, rationalMiddle, middleNegative⟩ := rationalLT_dense negative
          exact ⟨middle, Or.inl middleNegative, rationalMiddle⟩
        · obtain ⟨leftValue, rightValue, leftMember, rightMember,
            leftPositive, rightPositive, below⟩ := generated
          obtain ⟨middle, rationalMiddle, middleBelow⟩ := rationalLT_dense below
          exact ⟨middle, Or.inr ⟨leftValue, rightValue, leftMember,
            rightMember, leftPositive, rightPositive, middleBelow⟩,
            rationalMiddle⟩ }
  nonnegative := by
    intro rational negative
    exact Or.inl negative

theorem nonnegativeRealMul_comm (left right : NonnegativeReal) :
    (nonnegativeRealMul left right).value =
      (nonnegativeRealMul right left).value := by
  apply IncReal.ext
  intro rational
  constructor
  · intro member
    rcases member with negative | generated
    · exact Or.inl negative
    · obtain ⟨leftValue, rightValue, leftMember, rightMember,
          leftPositive, rightPositive, below⟩ := generated
      exact Or.inr ⟨rightValue, leftValue, rightMember, leftMember,
        rightPositive, leftPositive, by simpa [rationalMul_comm] using below⟩
  · intro member
    rcases member with negative | generated
    · exact Or.inl negative
    · obtain ⟨rightValue, leftValue, rightMember, leftMember,
          rightPositive, leftPositive, below⟩ := generated
      exact Or.inr ⟨leftValue, rightValue, leftMember, rightMember,
        leftPositive, rightPositive, by simpa [rationalMul_comm] using below⟩

theorem nonnegativeRealMul_ne_zero
    (left right : NonnegativeReal)
    (leftNonzero : left.value ≠ realZero)
    (rightNonzero : right.value ≠ realZero) :
    (nonnegativeRealMul left right).value ≠ realZero := by
  obtain ⟨leftValue, leftMember, leftPositive⟩ :=
    left.exists_positive_member leftNonzero
  obtain ⟨rightValue, rightMember, rightPositive⟩ :=
    right.exists_positive_member rightNonzero
  have productPositive := rationalMul_positive leftPositive rightPositive
  obtain ⟨witness, witnessPositive, _, witnessBelow⟩ :=
    rationalLT_exists_positive_between productPositive productPositive
  intro productZero
  have witnessMember :
      (nonnegativeRealMul left right).value.lower witness :=
    Or.inr ⟨leftValue, rightValue, leftMember, rightMember,
      leftPositive, rightPositive, witnessBelow⟩
  rw [productZero] at witnessMember
  exact (rationalLT_asymm witnessPositive) witnessMember

theorem nonnegativeRealMul_comm_bundle (left right : NonnegativeReal) :
    nonnegativeRealMul left right = nonnegativeRealMul right left :=
  NonnegativeReal.ext (nonnegativeRealMul_comm left right)

def nonnegativeOne : NonnegativeReal where
  value := rationalToReal (rationalOfInteger 1)
  nonnegative := (rationalToReal_le_iff _ _).mpr
    ((rationalOfInteger_le_iff 0 1).mpr (by omega))

theorem nonnegativeRealMul_zero_left (value : NonnegativeReal) :
    (nonnegativeRealMul nonnegativeZero value).value = realZero := by
  apply IncReal.ext
  intro rational
  constructor
  · intro member
    rcases member with negative | generated
    · exact negative
    · obtain ⟨zeroValue, rightValue, zeroMember, rightMember,
          zeroPositive, rightPositive, below⟩ := generated
      exact False.elim ((rationalLT_asymm zeroPositive) zeroMember)
  · intro negative
    exact Or.inl negative

theorem nonnegativeRealMul_zero_right (value : NonnegativeReal) :
    (nonnegativeRealMul value nonnegativeZero).value = realZero := by
  rw [nonnegativeRealMul_comm, nonnegativeRealMul_zero_left]

theorem nonnegativeRealMul_zero_left_bundle (value : NonnegativeReal) :
    nonnegativeRealMul nonnegativeZero value = nonnegativeZero :=
  NonnegativeReal.ext (nonnegativeRealMul_zero_left value)

theorem nonnegativeRealMul_zero_right_bundle (value : NonnegativeReal) :
    nonnegativeRealMul value nonnegativeZero = nonnegativeZero :=
  NonnegativeReal.ext (nonnegativeRealMul_zero_right value)

theorem nonnegativeRealMul_one_right (value : NonnegativeReal) :
    (nonnegativeRealMul value nonnegativeOne).value = value.value := by
  apply IncReal.ext
  intro rational
  constructor
  · intro member
    rcases member with negative | generated
    · exact value.negative_mem negative
    · obtain ⟨valueMember, oneMember, inValue, belowOne,
          valuePositive, onePositive, belowProduct⟩ := generated
      have productBelowValue :
          rationalLT (rationalMul valueMember oneMember) valueMember := by
        have multiplied := rationalLT_mul_left_of_positive belowOne valuePositive
        simpa [rationalMul_one_right] using multiplied
      exact value.value.downward inValue
        (rationalLT_trans belowProduct productBelowValue)
  · intro inValue
    by_cases negative : rationalLT rational (rationalOfInteger 0)
    · exact Or.inl negative
    · have zeroLE : rationalLE (rationalOfInteger 0) rational := by
        rcases rationalLE_total (rationalOfInteger 0) rational with ordered | reverse
        · exact ordered
        · by_cases equal : rational = rationalOfInteger 0
          · subst rational
            exact rationalLE_refl _
          · exact False.elim (negative ⟨reverse, equal⟩)
      obtain ⟨larger, largerMember, rationalLarger⟩ := value.value.rounded inValue
      have largerPositive : rationalLT (rationalOfInteger 0) larger :=
        rationalLT_of_le_of_lt zeroLE rationalLarger
      obtain ⟨middle, rationalMiddle, middleLarger⟩ :=
        rationalLT_dense rationalLarger
      have middlePositive : rationalLT (rationalOfInteger 0) middle :=
        rationalLT_of_le_of_lt zeroLE rationalMiddle
      have largerNonzero : larger ≠ rationalOfInteger 0 := fun equal => by
        subst larger
        exact rationalLT_irrefl _ largerPositive
      obtain ⟨inverse, inverseLaw⟩ :=
        rational_nonzero_has_mul_inverse largerNonzero
      have inversePositive : rationalLT (rationalOfInteger 0) inverse := by
        apply rationalMul_positive_reflect_right largerPositive
        rw [inverseLaw]
        exact rational_zero_lt_one
      let oneMember := rationalMul middle inverse
      have oneMemberPositive : rationalLT (rationalOfInteger 0) oneMember :=
        rationalMul_positive middlePositive inversePositive
      have oneMemberBelowOne :
          rationalLT oneMember (rationalOfInteger 1) := by
        have multiplied := rationalLT_mul_right_of_positive middleLarger inversePositive
        rw [inverseLaw] at multiplied
        exact multiplied
      have productRestore : rationalMul larger oneMember = middle := by
        calc
          rationalMul larger (rationalMul middle inverse) =
              rationalMul (rationalMul larger middle) inverse :=
            (rationalMul_assoc larger middle inverse).symm
          _ = rationalMul (rationalMul middle larger) inverse := by
            rw [rationalMul_comm larger middle]
          _ = rationalMul middle (rationalMul larger inverse) :=
            rationalMul_assoc middle larger inverse
          _ = rationalMul middle (rationalOfInteger 1) := by rw [inverseLaw]
          _ = middle := rationalMul_one_right middle
      exact Or.inr ⟨larger, oneMember, largerMember, oneMemberBelowOne,
        largerPositive, oneMemberPositive, by
          rw [productRestore]
          exact rationalMiddle⟩

theorem nonnegativeRealMul_one_left (value : NonnegativeReal) :
    (nonnegativeRealMul nonnegativeOne value).value = value.value := by
  rw [nonnegativeRealMul_comm, nonnegativeRealMul_one_right]

theorem nonnegativeRealMul_one_right_bundle (value : NonnegativeReal) :
    nonnegativeRealMul value nonnegativeOne = value :=
  NonnegativeReal.ext (nonnegativeRealMul_one_right value)

theorem nonnegativeRealMul_one_left_bundle (value : NonnegativeReal) :
    nonnegativeRealMul nonnegativeOne value = value :=
  NonnegativeReal.ext (nonnegativeRealMul_one_left value)

theorem nonnegativeRealMul_assoc_forward
    (first second third : NonnegativeReal) :
    realLE (nonnegativeRealMul (nonnegativeRealMul first second) third).value
      (nonnegativeRealMul first (nonnegativeRealMul second third)).value := by
  intro rational member
  by_cases rationalNegative : rationalLT rational (rationalOfInteger 0)
  · exact Or.inl rationalNegative
  · rcases member with negative | generated
    · exact False.elim (rationalNegative negative)
    · obtain ⟨firstSecondValue, thirdValue, firstSecondMember, thirdMember,
          firstSecondPositive, thirdPositive, rationalBelow⟩ := generated
      rcases firstSecondMember with firstSecondNegative | firstSecondGenerated
      · exact False.elim
          ((rationalLT_asymm firstSecondPositive) firstSecondNegative)
      · obtain ⟨firstValue, secondValue, firstMember, secondMember,
            firstPositive, secondPositive, firstSecondBelow⟩ :=
          firstSecondGenerated
        have rationalBelowExpanded : rationalLT rational
            (rationalMul firstValue (rationalMul secondValue thirdValue)) := by
          have expanded := rationalLT_mul_right_of_positive
            firstSecondBelow thirdPositive
          exact rationalLT_trans rationalBelow (by
            simpa [rationalMul_assoc] using expanded)
        have firstNonzero : firstValue ≠ rationalOfInteger 0 := fun equal => by
          subst firstValue
          exact rationalLT_irrefl _ firstPositive
        obtain ⟨inverse, inverseLaw⟩ :=
          rational_nonzero_has_mul_inverse firstNonzero
        have inversePositive : rationalLT (rationalOfInteger 0) inverse := by
          apply rationalMul_positive_reflect_right firstPositive
          rw [inverseLaw]
          exact rational_zero_lt_one
        let translated := rationalMul rational inverse
        have rationalNonnegative : rationalLE (rationalOfInteger 0) rational := by
          rcases rationalLE_total (rationalOfInteger 0) rational with ordered | reverse
          · exact ordered
          · by_cases equal : rational = rationalOfInteger 0
            · subst rational
              exact rationalLE_refl _
            · exact False.elim (rationalNegative ⟨reverse, equal⟩)
        have translatedNonnegative :
            rationalLE (rationalOfInteger 0) translated :=
          rationalMul_nonnegative rationalNonnegative inversePositive.1
        have translatedBelow : rationalLT translated
            (rationalMul secondValue thirdValue) := by
          have multiplied := rationalLT_mul_right_of_positive
            rationalBelowExpanded inversePositive
          have restore : rationalMul
              (rationalMul firstValue (rationalMul secondValue thirdValue))
              inverse = rationalMul secondValue thirdValue := by
            calc
              _ = rationalMul (rationalMul secondValue thirdValue)
                  (rationalMul firstValue inverse) := by
                rw [rationalMul_comm firstValue
                  (rationalMul secondValue thirdValue)]
                exact rationalMul_assoc
                  (rationalMul secondValue thirdValue) firstValue inverse
              _ = rationalMul (rationalMul secondValue thirdValue)
                  (rationalOfInteger 1) := by rw [inverseLaw]
              _ = _ := rationalMul_one_right _
          rw [restore] at multiplied
          exact multiplied
        obtain ⟨secondThirdValue, translatedMiddle, middleBelow⟩ :=
          rationalLT_dense translatedBelow
        have secondThirdPositive :
            rationalLT (rationalOfInteger 0) secondThirdValue :=
          rationalLT_of_le_of_lt translatedNonnegative translatedMiddle
        have secondThirdMember :
            (nonnegativeRealMul second third).value.lower secondThirdValue :=
          Or.inr ⟨secondValue, thirdValue, secondMember, thirdMember,
            secondPositive, thirdPositive, middleBelow⟩
        have restoredLeft :
            rationalMul firstValue translated = rational := by
          calc
            _ = rationalMul rational (rationalMul firstValue inverse) := by
              rw [← rationalMul_assoc firstValue rational inverse,
                rationalMul_comm firstValue rational,
                rationalMul_assoc rational firstValue inverse]
            _ = rationalMul rational (rationalOfInteger 1) := by rw [inverseLaw]
            _ = rational := rationalMul_one_right _
        have finalBelow := rationalLT_mul_left_of_positive
          translatedMiddle firstPositive
        rw [restoredLeft] at finalBelow
        exact Or.inr ⟨firstValue, secondThirdValue, firstMember,
          secondThirdMember, firstPositive, secondThirdPositive, finalBelow⟩

theorem nonnegativeRealMul_assoc
    (first second third : NonnegativeReal) :
    nonnegativeRealMul (nonnegativeRealMul first second) third =
      nonnegativeRealMul first (nonnegativeRealMul second third) := by
  apply NonnegativeReal.ext
  apply realLE_antisymm
  · exact nonnegativeRealMul_assoc_forward first second third
  · have reverse := nonnegativeRealMul_assoc_forward third second first
    simpa [nonnegativeRealMul_comm_bundle] using reverse

theorem nonnegativeRealMul_add_le
    (factor left right : NonnegativeReal) :
    realLE
      (nonnegativeRealMul factor (nonnegativeRealAdd left right)).value
      (nonnegativeRealAdd (nonnegativeRealMul factor left)
        (nonnegativeRealMul factor right)).value := by
  by_cases leftZero : left.value = realZero
  · have leftEq : left = nonnegativeZero :=
      NonnegativeReal.ext leftZero
    subst left
    rw [nonnegativeRealAdd_zero_left,
      nonnegativeRealMul_zero_right_bundle,
      nonnegativeRealAdd_zero_left]
    exact realLE_refl _
  · by_cases rightZero : right.value = realZero
    · have rightEq : right = nonnegativeZero :=
        NonnegativeReal.ext rightZero
      subst right
      rw [nonnegativeRealAdd_zero_right,
        nonnegativeRealMul_zero_right_bundle,
        nonnegativeRealAdd_zero_right]
      exact realLE_refl _
    · intro rational member
      by_cases rationalNegative : rationalLT rational (rationalOfInteger 0)
      · exact (nonnegativeRealAdd (nonnegativeRealMul factor left)
          (nonnegativeRealMul factor right)).negative_mem rationalNegative
      · rcases member with negative | generated
        · exact False.elim (rationalNegative negative)
        · obtain ⟨factorValue, sumValue, factorMember, sumMember,
              factorPositive, sumPositive, rationalBelow⟩ := generated
          obtain ⟨leftValue, rightValue, leftMember, rightMember, sumBelow⟩ :=
            sumMember
          obtain ⟨leftPositiveValue, leftPositiveMember,
              leftPositive, leftBelow⟩ :=
            left.exists_positive_member_above leftZero leftMember
          obtain ⟨rightPositiveValue, rightPositiveMember,
              rightPositive, rightBelow⟩ :=
            right.exists_positive_member_above rightZero rightMember
          have sumBelowPositive : rationalLT sumValue
              (rationalAdd leftPositiveValue rightPositiveValue) :=
            rationalLT_trans sumBelow (rationalLT_add leftBelow rightBelow)
          have expandedBelow : rationalLT rational
              (rationalAdd
                (rationalMul factorValue leftPositiveValue)
                (rationalMul factorValue rightPositiveValue)) := by
            have multiplied := rationalLT_mul_left_of_positive
              sumBelowPositive factorPositive
            rw [rationalMul_add] at multiplied
            exact rationalLT_trans rationalBelow multiplied
          have leftProductPositive :=
            rationalMul_positive factorPositive leftPositive
          have rightProductPositive :=
            rationalMul_positive factorPositive rightPositive
          obtain ⟨leftPart, rightPart, leftPartPositive, leftPartBelow,
              rightPartPositive, rightPartBelow, finalBelow⟩ :=
            rationalLT_split_positive_add leftProductPositive
              rightProductPositive expandedBelow
          exact ⟨leftPart, rightPart,
            Or.inr ⟨factorValue, leftPositiveValue, factorMember,
              leftPositiveMember, factorPositive, leftPositive, leftPartBelow⟩,
            Or.inr ⟨factorValue, rightPositiveValue, factorMember,
              rightPositiveMember, factorPositive, rightPositive,
              rightPartBelow⟩,
            finalBelow⟩

theorem nonnegativeRealAdd_mul_le
    (factor left right : NonnegativeReal) :
    realLE
      (nonnegativeRealAdd (nonnegativeRealMul factor left)
        (nonnegativeRealMul factor right)).value
      (nonnegativeRealMul factor (nonnegativeRealAdd left right)).value := by
  by_cases factorZero : factor.value = realZero
  · have factorEq : factor = nonnegativeZero :=
      NonnegativeReal.ext factorZero
    subst factor
    rw [nonnegativeRealMul_zero_left_bundle,
      nonnegativeRealMul_zero_left_bundle,
      nonnegativeRealAdd_zero_left,
      nonnegativeRealMul_zero_left_bundle]
    exact realLE_refl _
  · by_cases leftZero : left.value = realZero
    · have leftEq : left = nonnegativeZero :=
        NonnegativeReal.ext leftZero
      subst left
      rw [nonnegativeRealMul_zero_right_bundle,
        nonnegativeRealAdd_zero_left,
        nonnegativeRealAdd_zero_left]
      exact realLE_refl _
    · by_cases rightZero : right.value = realZero
      · have rightEq : right = nonnegativeZero :=
          NonnegativeReal.ext rightZero
        subst right
        rw [nonnegativeRealMul_zero_right_bundle,
          nonnegativeRealAdd_zero_right,
          nonnegativeRealAdd_zero_right]
        exact realLE_refl _
      · intro rational member
        by_cases rationalNegative : rationalLT rational (rationalOfInteger 0)
        · exact Or.inl rationalNegative
        · obtain ⟨leftProductValue, rightProductValue,
              leftProductMember, rightProductMember, rationalBelow⟩ := member
          have leftProductNonzero :=
            nonnegativeRealMul_ne_zero factor left factorZero leftZero
          have rightProductNonzero :=
            nonnegativeRealMul_ne_zero factor right factorZero rightZero
          obtain ⟨leftPositiveValue, leftPositiveMember,
              leftPositive, leftProductBelow⟩ :=
            (nonnegativeRealMul factor left).exists_positive_member_above
              leftProductNonzero leftProductMember
          obtain ⟨rightPositiveValue, rightPositiveMember,
              rightPositive, rightProductBelow⟩ :=
            (nonnegativeRealMul factor right).exists_positive_member_above
              rightProductNonzero rightProductMember
          rcases leftPositiveMember with leftNegative | leftGenerated
          · exact False.elim
              ((rationalLT_asymm leftPositive) leftNegative)
          · rcases rightPositiveMember with rightNegative | rightGenerated
            · exact False.elim
                ((rationalLT_asymm rightPositive) rightNegative)
            · obtain ⟨leftFactor, leftValue, leftFactorMember,
                  leftMember, leftFactorPositive, leftValuePositive,
                  leftBelowProduct⟩ := leftGenerated
              obtain ⟨rightFactor, rightValue, rightFactorMember,
                  rightMember, rightFactorPositive, rightValuePositive,
                  rightBelowProduct⟩ := rightGenerated
              obtain ⟨commonFactor, commonFactorMember, commonFactorPositive,
                  leftFactorBelow, rightFactorBelow⟩ :=
                factor.exists_positive_member_above_two factorZero
                  leftFactorMember rightFactorMember
              have leftExpanded : rationalLT leftProductValue
                  (rationalMul commonFactor leftValue) :=
                rationalLT_trans leftProductBelow
                  (rationalLT_trans leftBelowProduct
                    (rationalLT_mul_right_of_positive leftFactorBelow
                      leftValuePositive))
              have rightExpanded : rationalLT rightProductValue
                  (rationalMul commonFactor rightValue) :=
                rationalLT_trans rightProductBelow
                  (rationalLT_trans rightBelowProduct
                    (rationalLT_mul_right_of_positive rightFactorBelow
                      rightValuePositive))
              have expandedBelow : rationalLT rational
                  (rationalMul commonFactor
                    (rationalAdd leftValue rightValue)) := by
                have summed := rationalLT_add leftExpanded rightExpanded
                rw [← rationalMul_add] at summed
                exact rationalLT_trans rationalBelow summed
              have sumPositive : rationalLT (rationalOfInteger 0)
                  (rationalAdd leftValue rightValue) := by
                have summed := rationalLT_add leftValuePositive rightValuePositive
                simpa [rationalAdd_zero_left] using summed
              have rationalNonnegative :
                  rationalLE (rationalOfInteger 0) rational :=
                rationalLE_of_not_lt rationalNegative
              obtain ⟨sumApproximant, sumApproximantPositive,
                  sumApproximantBelow, finalBelow⟩ :=
                rationalLT_mul_positive_approx_right rationalNonnegative
                  commonFactorPositive sumPositive expandedBelow
              have sumMember :
                  (nonnegativeRealAdd left right).value.lower sumApproximant :=
                ⟨leftValue, rightValue, leftMember, rightMember,
                  sumApproximantBelow⟩
              exact Or.inr ⟨commonFactor, sumApproximant,
                commonFactorMember, sumMember, commonFactorPositive,
                sumApproximantPositive, finalBelow⟩

theorem nonnegativeRealMul_add
    (factor left right : NonnegativeReal) :
    nonnegativeRealMul factor (nonnegativeRealAdd left right) =
      nonnegativeRealAdd (nonnegativeRealMul factor left)
        (nonnegativeRealMul factor right) := by
  apply NonnegativeReal.ext
  exact realLE_antisymm
    (nonnegativeRealMul_add_le factor left right)
    (nonnegativeRealAdd_mul_le factor left right)

theorem nonnegativeRealAdd_mul
    (left right factor : NonnegativeReal) :
    nonnegativeRealMul (nonnegativeRealAdd left right) factor =
      nonnegativeRealAdd (nonnegativeRealMul left factor)
        (nonnegativeRealMul right factor) := by
  rw [nonnegativeRealMul_comm_bundle (nonnegativeRealAdd left right) factor,
    nonnegativeRealMul_add,
    nonnegativeRealMul_comm_bundle factor left,
    nonnegativeRealMul_comm_bundle factor right]

theorem nonnegativeRealMul_monotone_left
    {left left' right : NonnegativeReal}
    (ordered : realLE left.value left'.value) :
    realLE (nonnegativeRealMul left right).value
      (nonnegativeRealMul left' right).value := by
  intro rational member
  rcases member with negative | generated
  · exact Or.inl negative
  · obtain ⟨leftValue, rightValue, leftMember, rightMember,
        leftPositive, rightPositive, below⟩ := generated
    exact Or.inr ⟨leftValue, rightValue, ordered leftValue leftMember,
      rightMember, leftPositive, rightPositive, below⟩

theorem nonnegativeRealMul_monotone_right
    {left right right' : NonnegativeReal}
    (ordered : realLE right.value right'.value) :
    realLE (nonnegativeRealMul left right).value
      (nonnegativeRealMul left right').value := by
  rw [nonnegativeRealMul_comm left right, nonnegativeRealMul_comm left right']
  exact nonnegativeRealMul_monotone_left ordered

theorem nonnegativeRealMul_monotone
    {left left' right right' : NonnegativeReal}
    (leftOrdered : realLE left.value left'.value)
    (rightOrdered : realLE right.value right'.value) :
    realLE (nonnegativeRealMul left right).value
      (nonnegativeRealMul left' right').value :=
  realLE_trans (nonnegativeRealMul_monotone_left leftOrdered)
    (nonnegativeRealMul_monotone_right rightOrdered)

/-- Reciprocal cut of a nonzero nonnegative real. Membership is relational:
`q` lies below an inverse witness of some positive rational outside the source
cut. No global computational inverse selector is assumed. -/
noncomputable def nonnegativeRealInv (value : NonnegativeReal)
    (nonzero : value.value ≠ realZero) : NonnegativeReal where
  value :=
    { lower := fun rational =>
        rationalLT rational (rationalOfInteger 0) ∨
          ∃ outside inverse,
            ¬ value.value.lower outside ∧
            rationalLT (rationalOfInteger 0) outside ∧
            rationalMulResonance outside inverse (rationalOfInteger 1) ∧
            rationalLT rational inverse
      inhabited := ⟨rationalOfInteger (-1), Or.inl (by
        exact ⟨(rationalOfInteger_le_iff (-1) 0).mpr (by omega),
          fun equal => by
            have impossible := rationalOfInteger_injective equal
            omega⟩)⟩
      proper := by
        obtain ⟨inside, insideMember, insidePositive⟩ :=
          value.exists_positive_member nonzero
        have insideNonzero : inside ≠ rationalOfInteger 0 := fun equal => by
          subst inside
          exact rationalLT_irrefl _ insidePositive
        obtain ⟨insideInverse, insideInverseLaw⟩ :=
          rational_nonzero_has_mul_inverse insideNonzero
        have insideInversePositive :
            rationalLT (rationalOfInteger 0) insideInverse := by
          apply rationalMul_positive_reflect_right insidePositive
          rw [insideInverseLaw]
          exact rational_zero_lt_one
        refine ⟨insideInverse, ?_⟩
        intro inverseMember
        rcases inverseMember with negative | generated
        · exact (rationalLT_asymm insideInversePositive) negative
        · obtain ⟨outside, inverse, outsideNotMember, outsidePositive,
              inverseLaw, insideInverseBelow⟩ := generated
          have oneBelowInsideInverseProduct : rationalLT
              (rationalOfInteger 1) (rationalMul inside inverse) := by
            have multiplied := rationalLT_mul_left_of_positive
              insideInverseBelow insidePositive
            rw [insideInverseLaw] at multiplied
            exact multiplied
          have outsideBelowInside : rationalLT outside inside := by
            have multiplied := rationalLT_mul_left_of_positive
              oneBelowInsideInverseProduct outsidePositive
            have restore : rationalMul outside
                (rationalMul inside inverse) = inside := by
              calc
                _ = rationalMul (rationalMul outside inside) inverse :=
                  (rationalMul_assoc outside inside inverse).symm
                _ = rationalMul (rationalMul inside outside) inverse := by
                  rw [rationalMul_comm outside inside]
                _ = rationalMul inside (rationalMul outside inverse) :=
                  rationalMul_assoc inside outside inverse
                _ = rationalMul inside (rationalOfInteger 1) := by
                  rw [inverseLaw]
                _ = inside := rationalMul_one_right inside
            rw [rationalMul_one_right, restore] at multiplied
            exact multiplied
          exact outsideNotMember
            (value.value.downward insideMember outsideBelowInside)
      downward := by
        intro smaller rational member smallerRational
        rcases member with negative | generated
        · exact Or.inl (rationalLT_trans smallerRational negative)
        · obtain ⟨outside, inverse, outsideNotMember, outsidePositive,
              inverseLaw, rationalBelow⟩ := generated
          exact Or.inr ⟨outside, inverse, outsideNotMember, outsidePositive,
            inverseLaw, rationalLT_trans smallerRational rationalBelow⟩
      rounded := by
        intro rational member
        rcases member with negative | generated
        · obtain ⟨middle, rationalMiddle, middleNegative⟩ :=
            rationalLT_dense negative
          exact ⟨middle, Or.inl middleNegative, rationalMiddle⟩
        · obtain ⟨outside, inverse, outsideNotMember, outsidePositive,
              inverseLaw, rationalBelow⟩ := generated
          obtain ⟨middle, rationalMiddle, middleBelow⟩ :=
            rationalLT_dense rationalBelow
          exact ⟨middle, Or.inr ⟨outside, inverse, outsideNotMember,
            outsidePositive, inverseLaw, middleBelow⟩, rationalMiddle⟩ }
  nonnegative := by
    intro rational negative
    exact Or.inl negative

theorem nonnegativeRealInv_order_reverse
    {left right : NonnegativeReal}
    (leftNonzero : left.value ≠ realZero)
    (rightNonzero : right.value ≠ realZero)
    (ordered : realLE left.value right.value) :
    realLE (nonnegativeRealInv right rightNonzero).value
      (nonnegativeRealInv left leftNonzero).value := by
  intro rational member
  rcases member with negative | generated
  · exact Or.inl negative
  · obtain ⟨outside, inverse, outsideNotRight, outsidePositive,
        inverseLaw, rationalBelow⟩ := generated
    exact Or.inr ⟨outside, inverse,
      (fun outsideLeft => outsideNotRight (ordered outside outsideLeft)),
      outsidePositive, inverseLaw, rationalBelow⟩

theorem nonnegativeRealMul_inv_le_one
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero) :
    realLE (nonnegativeRealMul value (nonnegativeRealInv value nonzero)).value
      nonnegativeOne.value := by
  intro rational member
  rcases member with negative | generated
  · exact rationalLT_trans negative rational_zero_lt_one
  · obtain ⟨inside, inverseValue, insideMember, inverseMember,
        insidePositive, inverseValuePositive, rationalBelow⟩ := generated
    rcases inverseMember with inverseNegative | inverseGenerated
    · exact False.elim
        ((rationalLT_asymm inverseValuePositive) inverseNegative)
    · obtain ⟨outside, outsideInverse, outsideNotMember, outsidePositive,
          outsideInverseLaw, inverseBelow⟩ := inverseGenerated
      have insideBelowOutside := value.value.lt_of_lower_of_not_lower
        insideMember outsideNotMember
      have productBelowOne : rationalLT
          (rationalMul inside inverseValue) (rationalOfInteger 1) := by
        have strict := rationalLT_mul_of_positive insideBelowOutside
          inverseBelow inverseValuePositive outsidePositive
        rw [outsideInverseLaw] at strict
        exact strict
      exact rationalLT_trans rationalBelow productBelowOne

theorem one_le_nonnegativeRealMul_inv
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero) :
    realLE nonnegativeOne.value
      (nonnegativeRealMul value (nonnegativeRealInv value nonzero)).value := by
  intro rational rationalBelowOne
  by_cases rationalNegative : rationalLT rational (rationalOfInteger 0)
  · exact Or.inl rationalNegative
  · have rationalNonnegative :
        rationalLE (rationalOfInteger 0) rational :=
      rationalLE_of_not_lt rationalNegative
    let gap := rationalAdd (rationalOfInteger 1) (rationalNeg rational)
    have gapPositive : rationalLT (rationalOfInteger 0) gap := by
      have shifted := rationalLT_add_right (rationalNeg rational)
        rationalBelowOne
      simpa [gap, rationalAdd_neg] using shifted
    obtain ⟨positiveMember, positiveMemberProof, positiveMemberPositive⟩ :=
      value.exists_positive_member nonzero
    have gapProductPositive : rationalLT (rationalOfInteger 0)
        (rationalMul gap positiveMember) :=
      rationalMul_positive gapPositive positiveMemberPositive
    obtain ⟨step, stepPositive, stepBelowMember, stepBelowGapProduct⟩ :=
      rational_exists_positive_below_two positiveMemberPositive
        gapProductPositive
    obtain ⟨inside, outside, insideMember, outsideNotMember, outsideStep⟩ :=
      value.value.boundary_approximation stepPositive
    have positiveMemberBelowOutside : rationalLT positiveMember outside :=
      value.value.lt_of_lower_of_not_lower positiveMemberProof outsideNotMember
    have insidePositive : rationalLT (rationalOfInteger 0) inside := by
      have memberMinusStepBelowInside : rationalLT
          (rationalAdd positiveMember (rationalNeg step)) inside := by
        have shifted := rationalLT_add_right (rationalNeg step)
          positiveMemberBelowOutside
        rw [outsideStep, rationalAdd_add_neg_cancel] at shifted
        exact shifted
      have zeroBelowMemberMinusStep : rationalLT (rationalOfInteger 0)
          (rationalAdd positiveMember (rationalNeg step)) := by
        have shifted := rationalLT_add_right (rationalNeg step) stepBelowMember
        rw [rationalAdd_neg] at shifted
        exact shifted
      exact rationalLT_trans zeroBelowMemberMinusStep memberMinusStepBelowInside
    have outsidePositive : rationalLT (rationalOfInteger 0) outside :=
      rationalLT_trans insidePositive (by
        rw [outsideStep]
        have shifted := rationalLT_add_left inside stepPositive
        simpa [rationalAdd_zero_right] using shifted)
    have stepBelowGapOutside :
        rationalLT step (rationalMul gap outside) := by
      have multiplied := rationalLT_mul_left_of_positive
        positiveMemberBelowOutside gapPositive
      exact rationalLT_trans stepBelowGapProduct multiplied
    have rationalAddGap : rationalAdd rational gap = rationalOfInteger 1 := by
      dsimp [gap]
      calc
        _ = rationalAdd (rationalAdd rational (rationalNeg rational))
            (rationalOfInteger 1) := by
          rw [rationalAdd_comm (rationalOfInteger 1),
            ← rationalAdd_assoc]
        _ = rationalOfInteger 1 := by
          rw [rationalAdd_neg, rationalAdd_zero_left]
    have rationalOutsideBelowInside :
        rationalLT (rationalMul rational outside) inside := by
      have added := rationalLT_add_left (rationalMul rational outside)
        stepBelowGapOutside
      have sumRestore : rationalAdd (rationalMul rational outside)
          (rationalMul gap outside) = outside := by
        calc
          _ = rationalMul outside (rationalAdd rational gap) := by
            rw [rationalMul_add]
            simp only [rationalMul_comm]
          _ = rationalMul outside (rationalOfInteger 1) := by rw [rationalAddGap]
          _ = outside := rationalMul_one_right outside
      rw [sumRestore] at added
      have added' : rationalLT
          (rationalAdd (rationalMul rational outside) step)
          (rationalAdd inside step) := by
        rw [← outsideStep]
        exact added
      exact rationalLT_add_cancel_right step added'
    have outsideNonzero : outside ≠ rationalOfInteger 0 := fun equal => by
      have impossible := outsidePositive
      rw [equal] at impossible
      exact rationalLT_irrefl _ impossible
    obtain ⟨outsideInverse, outsideInverseLaw⟩ :=
      rational_nonzero_has_mul_inverse outsideNonzero
    have outsideInversePositive :
        rationalLT (rationalOfInteger 0) outsideInverse := by
      apply rationalMul_positive_reflect_right outsidePositive
      rw [outsideInverseLaw]
      exact rational_zero_lt_one
    have rationalBelowInsideInverse : rationalLT rational
        (rationalMul inside outsideInverse) := by
      have multiplied := rationalLT_mul_right_of_positive
        rationalOutsideBelowInside outsideInversePositive
      have restore : rationalMul (rationalMul rational outside)
          outsideInverse = rational := by
        rw [rationalMul_assoc, outsideInverseLaw, rationalMul_one_right]
      rw [restore] at multiplied
      exact multiplied
    obtain ⟨inverseValue, inverseValuePositive, inverseValueBelow,
        finalBelow⟩ := rationalLT_mul_positive_approx_right
      rationalNonnegative insidePositive outsideInversePositive
      rationalBelowInsideInverse
    have inverseMember :
        (nonnegativeRealInv value nonzero).value.lower inverseValue :=
      Or.inr ⟨outside, outsideInverse, outsideNotMember, outsidePositive,
        outsideInverseLaw, inverseValueBelow⟩
    exact Or.inr ⟨inside, inverseValue, insideMember, inverseMember,
      insidePositive, inverseValuePositive, finalBelow⟩

theorem nonnegativeRealMul_inv
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero) :
    nonnegativeRealMul value (nonnegativeRealInv value nonzero) =
      nonnegativeOne := by
  apply NonnegativeReal.ext
  exact realLE_antisymm
    (nonnegativeRealMul_inv_le_one value nonzero)
    (one_le_nonnegativeRealMul_inv value nonzero)

/-- Canonical positive part of a real, bundled in the nonnegative cone. -/
noncomputable def realPositivePart (value : IncReal) : NonnegativeReal :=
  by
    classical
    exact if nonnegative : realLE realZero value then
      ⟨value, nonnegative⟩
    else
      nonnegativeZero

/-- Canonical negative magnitude. The same order branch as `realPositivePart`
makes the signed decomposition computationally transparent. -/
noncomputable def realNegativePart (value : IncReal) : NonnegativeReal :=
  by
    classical
    exact if nonnegative : realLE realZero value then
      nonnegativeZero
    else
      { value := realNeg value
        nonnegative := by
          have valueNonpositive : realLE value realZero := by
            rcases realLE_total value realZero with ordered | reverse
            · exact ordered
            · exact False.elim (nonnegative reverse)
          have reversed := (realNeg_order_iff value realZero).mpr valueNonpositive
          simpa [realNeg_zero] using reversed }

theorem real_signed_decomposition (value : IncReal) :
    realAdd (realPositivePart value).value
      (realNeg (realNegativePart value).value) = value := by
  classical
  by_cases nonnegative : realLE realZero value
  · simp [realPositivePart, realNegativePart, nonnegative, nonnegativeZero,
      realNeg_zero, realAdd_zero_right]
  · simp [realPositivePart, realNegativePart, nonnegative, nonnegativeZero,
      realNeg_neg, realAdd_zero_left]

theorem realPositivePart_of_nonnegative (value : IncReal)
    (nonnegative : realLE realZero value) :
    realPositivePart value = ⟨value, nonnegative⟩ := by
  apply NonnegativeReal.ext
  classical
  simp [realPositivePart, nonnegative]

theorem realNegativePart_of_nonnegative (value : IncReal)
    (nonnegative : realLE realZero value) :
    realNegativePart value = nonnegativeZero := by
  apply NonnegativeReal.ext
  classical
  simp [realNegativePart, nonnegative, nonnegativeZero]

theorem realPositivePart_of_not_nonnegative (value : IncReal)
    (notNonnegative : ¬ realLE realZero value) :
    realPositivePart value = nonnegativeZero := by
  apply NonnegativeReal.ext
  classical
  simp [realPositivePart, notNonnegative, nonnegativeZero]

theorem realNegativePart_of_not_nonnegative (value : IncReal)
    (notNonnegative : ¬ realLE realZero value) :
    realNegativePart value =
      { value := realNeg value
        nonnegative := by
          have valueNonpositive : realLE value realZero := by
            rcases realLE_total value realZero with ordered | reverse
            · exact ordered
            · exact False.elim (notNonnegative reverse)
          have reversed := (realNeg_order_iff value realZero).mpr valueNonpositive
          simpa [realNeg_zero] using reversed } := by
  apply NonnegativeReal.ext
  classical
  simp [realNegativePart, notNonnegative]

theorem realPositivePart_neg (value : IncReal) :
    realPositivePart (realNeg value) = realNegativePart value := by
  classical
  by_cases valueNonnegative : realLE realZero value
  · by_cases negNonnegative : realLE realZero (realNeg value)
    · have valueNonpositive : realLE value realZero := by
        have reversed := (realNeg_order_iff value realZero).mp (by
          simpa [realNeg_zero] using negNonnegative)
        exact reversed
      have valueZero := realLE_antisymm valueNonnegative valueNonpositive
      subst value
      apply NonnegativeReal.ext
      simp [realPositivePart, realNegativePart, realLE_refl,
        realNeg_zero, nonnegativeZero]
    · rw [realPositivePart_of_not_nonnegative _ negNonnegative,
        realNegativePart_of_nonnegative _ valueNonnegative]
  · have negNonnegative : realLE realZero (realNeg value) := by
      have valueNonpositive : realLE value realZero := by
        rcases realLE_total value realZero with ordered | reverse
        · exact ordered
        · exact False.elim (valueNonnegative reverse)
      have reversed := (realNeg_order_iff value realZero).mpr valueNonpositive
      simpa [realNeg_zero] using reversed
    rw [realPositivePart_of_nonnegative _ negNonnegative,
      realNegativePart_of_not_nonnegative _ valueNonnegative]

theorem realNegativePart_neg (value : IncReal) :
    realNegativePart (realNeg value) = realPositivePart value := by
  have swapped := realPositivePart_neg (realNeg value)
  simpa [realNeg_neg] using swapped.symm

theorem real_eq_neg_negativePart (value : IncReal)
    (notNonnegative : ¬ realLE realZero value) :
    value = realNeg (realNegativePart value).value := by
  rw [realNegativePart_of_not_nonnegative value notNonnegative]
  simp [realNeg_neg]

/-- Signed multiplication reconstructed from the nonnegative semiring by the
identity `(p-n)(q-m) = (pq+nm) - (pm+nq)`. -/
noncomputable def realMul (left right : IncReal) : IncReal :=
  let positive := nonnegativeRealAdd
    (nonnegativeRealMul (realPositivePart left) (realPositivePart right))
    (nonnegativeRealMul (realNegativePart left) (realNegativePart right))
  let negative := nonnegativeRealAdd
    (nonnegativeRealMul (realPositivePart left) (realNegativePart right))
    (nonnegativeRealMul (realNegativePart left) (realPositivePart right))
  realAdd positive.value (realNeg negative.value)

def realOne : IncReal := nonnegativeOne.value

theorem realPositivePart_one : realPositivePart realOne = nonnegativeOne := by
  apply NonnegativeReal.ext
  rw [realPositivePart_of_nonnegative realOne nonnegativeOne.nonnegative]
  rfl

theorem realNegativePart_one : realNegativePart realOne = nonnegativeZero := by
  exact realNegativePart_of_nonnegative realOne nonnegativeOne.nonnegative

theorem realMul_comm (left right : IncReal) :
    realMul left right = realMul right left := by
  have positiveEq :
      nonnegativeRealAdd
          (nonnegativeRealMul (realPositivePart left) (realPositivePart right))
          (nonnegativeRealMul (realNegativePart left) (realNegativePart right)) =
        nonnegativeRealAdd
          (nonnegativeRealMul (realPositivePart right) (realPositivePart left))
          (nonnegativeRealMul (realNegativePart right) (realNegativePart left)) := by
    rw [nonnegativeRealMul_comm_bundle (realPositivePart left),
      nonnegativeRealMul_comm_bundle (realNegativePart left)]
  have negativeEq :
      nonnegativeRealAdd
          (nonnegativeRealMul (realPositivePart left) (realNegativePart right))
          (nonnegativeRealMul (realNegativePart left) (realPositivePart right)) =
        nonnegativeRealAdd
          (nonnegativeRealMul (realPositivePart right) (realNegativePart left))
          (nonnegativeRealMul (realNegativePart right) (realPositivePart left)) := by
    rw [nonnegativeRealMul_comm_bundle (realPositivePart left),
      nonnegativeRealMul_comm_bundle (realNegativePart left),
      nonnegativeRealAdd_comm]
  simp only [realMul]
  rw [positiveEq, negativeEq]

theorem realMul_neg_right (left right : IncReal) :
    realMul left (realNeg right) = realNeg (realMul left right) := by
  simp only [realMul]
  rw [realPositivePart_neg, realNegativePart_neg, realNeg_add,
    realNeg_neg, realAdd_comm]

theorem realMul_neg_left (left right : IncReal) :
    realMul (realNeg left) right = realNeg (realMul left right) := by
  rw [realMul_comm, realMul_neg_right, realMul_comm]

theorem realMul_neg_neg (left right : IncReal) :
    realMul (realNeg left) (realNeg right) = realMul left right := by
  rw [realMul_neg_left, realMul_neg_right, realNeg_neg]

theorem realMul_of_nonnegative (left right : IncReal)
    (leftNonnegative : realLE realZero left)
    (rightNonnegative : realLE realZero right) :
    realMul left right =
      (nonnegativeRealMul ⟨left, leftNonnegative⟩
        ⟨right, rightNonnegative⟩).value := by
  rw [realMul, realPositivePart_of_nonnegative left leftNonnegative,
    realPositivePart_of_nonnegative right rightNonnegative,
    realNegativePart_of_nonnegative left leftNonnegative,
    realNegativePart_of_nonnegative right rightNonnegative,
    nonnegativeRealMul_zero_left_bundle,
    nonnegativeRealMul_zero_right_bundle,
    nonnegativeRealAdd_zero_right, nonnegativeRealAdd_zero_left,
    nonnegativeRealMul_zero_left_bundle]
  change realAdd _ (realNeg realZero) = _
  rw [realNeg_zero, realAdd_zero_right]

theorem realMul_assoc_nonnegative
    (first second third : NonnegativeReal) :
    realMul (realMul first.value second.value) third.value =
      realMul first.value (realMul second.value third.value) := by
  rw [realMul_of_nonnegative first.value second.value
      first.nonnegative second.nonnegative,
    realMul_of_nonnegative
      (nonnegativeRealMul first second).value third.value
      (nonnegativeRealMul first second).nonnegative third.nonnegative,
    realMul_of_nonnegative second.value third.value
      second.nonnegative third.nonnegative,
    realMul_of_nonnegative first.value
      (nonnegativeRealMul second third).value first.nonnegative
      (nonnegativeRealMul second third).nonnegative,
    nonnegativeRealMul_assoc]

theorem realMul_assoc (first second third : IncReal) :
    realMul (realMul first second) third =
      realMul first (realMul second third) := by
  classical
  by_cases firstNonnegative : realLE realZero first
  · let firstPart : NonnegativeReal := ⟨first, firstNonnegative⟩
    by_cases secondNonnegative : realLE realZero second
    · let secondPart : NonnegativeReal := ⟨second, secondNonnegative⟩
      by_cases thirdNonnegative : realLE realZero third
      · let thirdPart : NonnegativeReal := ⟨third, thirdNonnegative⟩
        exact realMul_assoc_nonnegative firstPart secondPart thirdPart
      · let thirdPart := realNegativePart third
        have thirdEq : third = realNeg thirdPart.value := by
          exact real_eq_neg_negativePart third thirdNonnegative
        rw [thirdEq]
        simp only [realMul_neg_right]
        exact congrArg realNeg
          (realMul_assoc_nonnegative firstPart secondPart thirdPart)

    · let secondPart := realNegativePart second
      have secondEq : second = realNeg secondPart.value := by
        exact real_eq_neg_negativePart second secondNonnegative
      by_cases thirdNonnegative : realLE realZero third
      · let thirdPart : NonnegativeReal := ⟨third, thirdNonnegative⟩
        rw [secondEq]
        simp only [realMul_neg_right, realMul_neg_left]
        exact congrArg realNeg
          (realMul_assoc_nonnegative firstPart secondPart thirdPart)
      · let thirdPart := realNegativePart third
        have thirdEq : third = realNeg thirdPart.value := by
          exact real_eq_neg_negativePart third thirdNonnegative
        rw [secondEq, thirdEq]
        simp only [realMul_neg_right, realMul_neg_left, realNeg_neg]
        exact realMul_assoc_nonnegative firstPart secondPart thirdPart
  · let firstPart := realNegativePart first
    have firstEq : first = realNeg firstPart.value := by
      exact real_eq_neg_negativePart first firstNonnegative
    by_cases secondNonnegative : realLE realZero second
    · let secondPart : NonnegativeReal := ⟨second, secondNonnegative⟩
      by_cases thirdNonnegative : realLE realZero third
      · let thirdPart : NonnegativeReal := ⟨third, thirdNonnegative⟩
        rw [firstEq]
        simp only [realMul_neg_left]
        exact congrArg realNeg
          (realMul_assoc_nonnegative firstPart secondPart thirdPart)
      · let thirdPart := realNegativePart third
        have thirdEq : third = realNeg thirdPart.value := by
          exact real_eq_neg_negativePart third thirdNonnegative
        rw [firstEq, thirdEq]
        simp only [realMul_neg_right, realMul_neg_left, realNeg_neg]
        exact realMul_assoc_nonnegative firstPart secondPart thirdPart
    · let secondPart := realNegativePart second
      have secondEq : second = realNeg secondPart.value := by
        exact real_eq_neg_negativePart second secondNonnegative
      by_cases thirdNonnegative : realLE realZero third
      · let thirdPart : NonnegativeReal := ⟨third, thirdNonnegative⟩
        rw [firstEq, secondEq]
        simp only [realMul_neg_right, realMul_neg_left, realNeg_neg]
        exact realMul_assoc_nonnegative firstPart secondPart thirdPart
      · let thirdPart := realNegativePart third
        have thirdEq : third = realNeg thirdPart.value := by
          exact real_eq_neg_negativePart third thirdNonnegative
        rw [firstEq, secondEq, thirdEq]
        simp only [realMul_neg_right, realMul_neg_left, realNeg_neg]
        exact congrArg realNeg
          (realMul_assoc_nonnegative firstPart secondPart thirdPart)

theorem realMul_add_nonnegative
    (factor left right : NonnegativeReal) :
    realMul factor.value (realAdd left.value right.value) =
      realAdd (realMul factor.value left.value)
        (realMul factor.value right.value) := by
  change realMul factor.value (nonnegativeRealAdd left right).value =
    realAdd (realMul factor.value left.value)
      (realMul factor.value right.value)
  rw [realMul_of_nonnegative factor.value
      (nonnegativeRealAdd left right).value factor.nonnegative
      (nonnegativeRealAdd left right).nonnegative,
    realMul_of_nonnegative factor.value left.value
      factor.nonnegative left.nonnegative,
    realMul_of_nonnegative factor.value right.value
      factor.nonnegative right.nonnegative]
  exact congrArg NonnegativeReal.value
    (nonnegativeRealMul_add factor left right)

theorem realMul_add_neg_factor_nonnegative
    (factor left right : NonnegativeReal) :
    realMul (realNeg factor.value) (realAdd left.value right.value) =
      realAdd (realMul (realNeg factor.value) left.value)
        (realMul (realNeg factor.value) right.value) := by
  rw [realMul_neg_left, realMul_neg_left, realMul_neg_left,
    realMul_add_nonnegative, realNeg_add]

theorem realMul_add_negated_nonnegative
    (factor left right : NonnegativeReal) :
    realMul factor.value
        (realAdd (realNeg left.value) (realNeg right.value)) =
      realAdd (realMul factor.value (realNeg left.value))
        (realMul factor.value (realNeg right.value)) := by
  rw [← realNeg_add, realMul_neg_right, realMul_neg_right,
    realMul_neg_right, realMul_add_nonnegative, realNeg_add]

theorem realMul_add_all_negated_nonnegative
    (factor left right : NonnegativeReal) :
    realMul (realNeg factor.value)
        (realAdd (realNeg left.value) (realNeg right.value)) =
      realAdd (realMul (realNeg factor.value) (realNeg left.value))
        (realMul (realNeg factor.value) (realNeg right.value)) := by
  rw [realMul_neg_left, realMul_neg_left, realMul_neg_left,
    realMul_add_negated_nonnegative, realNeg_add]

theorem realMul_add_sub_nonnegative
    (factor left right : NonnegativeReal) :
    realMul factor.value (realAdd left.value (realNeg right.value)) =
      realAdd (realMul factor.value left.value)
        (realNeg (realMul factor.value right.value)) := by
  let difference := realAdd left.value (realNeg right.value)
  by_cases differenceNonnegative : realLE realZero difference
  · let differencePart : NonnegativeReal :=
      ⟨difference, differenceNonnegative⟩
    have restore : realAdd differencePart.value right.value = left.value := by
      change realAdd (realAdd left.value (realNeg right.value)) right.value =
        left.value
      rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
    have distributed := realMul_add_nonnegative factor differencePart right
    rw [restore] at distributed
    exact real_eq_add_neg_of_add_eq distributed.symm
  · let differencePart := realNegativePart difference
    have differenceEq : difference = realNeg differencePart.value :=
      real_eq_neg_negativePart difference differenceNonnegative
    have magnitudeEq : differencePart.value = realNeg difference := by
      have negated := congrArg realNeg differenceEq
      simpa [realNeg_neg] using negated.symm
    have restore : realAdd left.value differencePart.value = right.value := by
      rw [magnitudeEq]
      change realAdd left.value
        (realNeg (realAdd left.value (realNeg right.value))) = right.value
      rw [realNeg_add, realNeg_neg, ← realAdd_assoc,
        realAdd_neg, realAdd_zero_left]
    have distributed := realMul_add_nonnegative factor left differencePart
    rw [restore] at distributed
    change realMul factor.value difference = _
    rw [differenceEq, realMul_neg_right]
    exact realNeg_eq_add_neg_of_add_eq distributed.symm

theorem realMul_add_sub_neg_factor_nonnegative
    (factor left right : NonnegativeReal) :
    realMul (realNeg factor.value)
        (realAdd left.value (realNeg right.value)) =
      realAdd (realMul (realNeg factor.value) left.value)
        (realNeg (realMul (realNeg factor.value) right.value)) := by
  rw [realMul_neg_left, realMul_neg_left, realMul_neg_left,
    realMul_add_sub_nonnegative, realNeg_add, realNeg_neg]

theorem realMul_add (factor left right : IncReal) :
    realMul factor (realAdd left right) =
      realAdd (realMul factor left) (realMul factor right) := by
  classical
  by_cases factorNonnegative : realLE realZero factor
  · let factorPart : NonnegativeReal := ⟨factor, factorNonnegative⟩
    by_cases leftNonnegative : realLE realZero left
    · let leftPart : NonnegativeReal := ⟨left, leftNonnegative⟩
      by_cases rightNonnegative : realLE realZero right
      · let rightPart : NonnegativeReal := ⟨right, rightNonnegative⟩
        exact realMul_add_nonnegative factorPart leftPart rightPart
      · let rightPart := realNegativePart right
        have rightEq := real_eq_neg_negativePart right rightNonnegative
        rw [rightEq]
        simpa [realMul_neg_right] using
          realMul_add_sub_nonnegative factorPart leftPart rightPart
    · let leftPart := realNegativePart left
      have leftEq := real_eq_neg_negativePart left leftNonnegative
      by_cases rightNonnegative : realLE realZero right
      · let rightPart : NonnegativeReal := ⟨right, rightNonnegative⟩
        rw [leftEq]
        rw [realAdd_comm (realNeg leftPart.value) rightPart.value,
          realMul_neg_right]
        rw [realAdd_comm
          (realNeg (realMul factorPart.value leftPart.value))
          (realMul factorPart.value rightPart.value)]
        exact realMul_add_sub_nonnegative factorPart rightPart leftPart
      · let rightPart := realNegativePart right
        have rightEq := real_eq_neg_negativePart right rightNonnegative
        rw [leftEq, rightEq]
        exact realMul_add_negated_nonnegative factorPart leftPart rightPart
  · let factorPart := realNegativePart factor
    have factorEq := real_eq_neg_negativePart factor factorNonnegative
    by_cases leftNonnegative : realLE realZero left
    · let leftPart : NonnegativeReal := ⟨left, leftNonnegative⟩
      by_cases rightNonnegative : realLE realZero right
      · let rightPart : NonnegativeReal := ⟨right, rightNonnegative⟩
        rw [factorEq]
        exact realMul_add_neg_factor_nonnegative factorPart leftPart rightPart
      · let rightPart := realNegativePart right
        have rightEq := real_eq_neg_negativePart right rightNonnegative
        rw [factorEq, rightEq]
        simpa [realMul_neg_right] using
          realMul_add_sub_neg_factor_nonnegative factorPart leftPart rightPart
    · let leftPart := realNegativePart left
      have leftEq := real_eq_neg_negativePart left leftNonnegative
      by_cases rightNonnegative : realLE realZero right
      · let rightPart : NonnegativeReal := ⟨right, rightNonnegative⟩
        rw [factorEq, leftEq]
        rw [realAdd_comm (realNeg leftPart.value) rightPart.value,
          realMul_neg_right]
        rw [realAdd_comm
          (realNeg (realMul (realNeg factorPart.value) leftPart.value))
          (realMul (realNeg factorPart.value) rightPart.value)]
        exact realMul_add_sub_neg_factor_nonnegative factorPart rightPart leftPart
      · let rightPart := realNegativePart right
        have rightEq := real_eq_neg_negativePart right rightNonnegative
        rw [factorEq, leftEq, rightEq]
        exact realMul_add_all_negated_nonnegative factorPart leftPart rightPart

theorem realAdd_mul (left right factor : IncReal) :
    realMul (realAdd left right) factor =
      realAdd (realMul left factor) (realMul right factor) := by
  rw [realMul_comm, realMul_add,
    realMul_comm factor left, realMul_comm factor right]

theorem realMul_of_nonnegative_not_nonnegative
    (left right : IncReal)
    (leftNonnegative : realLE realZero left)
    (rightNotNonnegative : ¬ realLE realZero right) :
    realMul left right = realNeg
      (nonnegativeRealMul
        ⟨left, leftNonnegative⟩
        { value := realNeg right
          nonnegative := by
            have rightNonpositive : realLE right realZero := by
              rcases realLE_total right realZero with ordered | reverse
              · exact ordered
              · exact False.elim (rightNotNonnegative reverse)
            have reversed :=
              (realNeg_order_iff right realZero).mpr rightNonpositive
            simpa [realNeg_zero] using reversed }).value := by
  rw [realMul,
    realPositivePart_of_nonnegative left leftNonnegative,
    realNegativePart_of_nonnegative left leftNonnegative,
    realPositivePart_of_not_nonnegative right rightNotNonnegative,
    realNegativePart_of_not_nonnegative right rightNotNonnegative,
    nonnegativeRealMul_zero_right_bundle,
    nonnegativeRealMul_zero_left_bundle,
    nonnegativeRealAdd_zero_left,
    nonnegativeRealMul_zero_left_bundle,
    nonnegativeRealAdd_zero_right]
  change realAdd realZero (realNeg _) = _
  rw [realAdd_zero_left]

theorem realMul_of_not_nonnegative_nonnegative
    (left right : IncReal)
    (leftNotNonnegative : ¬ realLE realZero left)
    (rightNonnegative : realLE realZero right) :
    realMul left right = realNeg
      (nonnegativeRealMul
        { value := realNeg left
          nonnegative := by
            have leftNonpositive : realLE left realZero := by
              rcases realLE_total left realZero with ordered | reverse
              · exact ordered
              · exact False.elim (leftNotNonnegative reverse)
            have reversed :=
              (realNeg_order_iff left realZero).mpr leftNonpositive
            simpa [realNeg_zero] using reversed }
        ⟨right, rightNonnegative⟩).value := by
  rw [realMul_comm]
  simpa [nonnegativeRealMul_comm] using
    realMul_of_nonnegative_not_nonnegative right left
      rightNonnegative leftNotNonnegative

theorem realMul_of_not_nonnegative
    (left right : IncReal)
    (leftNotNonnegative : ¬ realLE realZero left)
    (rightNotNonnegative : ¬ realLE realZero right) :
    realMul left right =
      (nonnegativeRealMul
        { value := realNeg left
          nonnegative := by
            have leftNonpositive : realLE left realZero := by
              rcases realLE_total left realZero with ordered | reverse
              · exact ordered
              · exact False.elim (leftNotNonnegative reverse)
            have reversed :=
              (realNeg_order_iff left realZero).mpr leftNonpositive
            simpa [realNeg_zero] using reversed }
        { value := realNeg right
          nonnegative := by
            have rightNonpositive : realLE right realZero := by
              rcases realLE_total right realZero with ordered | reverse
              · exact ordered
              · exact False.elim (rightNotNonnegative reverse)
            have reversed :=
              (realNeg_order_iff right realZero).mpr rightNonpositive
            simpa [realNeg_zero] using reversed }).value := by
  rw [realMul,
    realPositivePart_of_not_nonnegative left leftNotNonnegative,
    realNegativePart_of_not_nonnegative left leftNotNonnegative,
    realPositivePart_of_not_nonnegative right rightNotNonnegative,
    realNegativePart_of_not_nonnegative right rightNotNonnegative,
    nonnegativeRealMul_zero_left_bundle,
    nonnegativeRealAdd_zero_left,
    nonnegativeRealMul_zero_left_bundle,
    nonnegativeRealMul_zero_right_bundle,
    nonnegativeRealAdd_zero_left]
  change realAdd _ (realNeg realZero) = _
  exact calc
    realAdd _ (realNeg realZero) = realAdd _ realZero :=
      congrArg _ realNeg_zero
    _ = _ := realAdd_zero_right _

theorem realMul_zero_left (value : IncReal) :
    realMul realZero value = realZero := by
  rw [realMul_comm, realMul]
  rw [realPositivePart_of_nonnegative realZero (realLE_refl _),
    realNegativePart_of_nonnegative realZero (realLE_refl _)]
  change realAdd
    (nonnegativeRealAdd
      (nonnegativeRealMul (realPositivePart value) nonnegativeZero)
      (nonnegativeRealMul (realNegativePart value) nonnegativeZero)).value
    (realNeg
      (nonnegativeRealAdd
        (nonnegativeRealMul (realPositivePart value) nonnegativeZero)
        (nonnegativeRealMul (realNegativePart value) nonnegativeZero)).value) = _
  rw [nonnegativeRealMul_zero_right_bundle,
    nonnegativeRealMul_zero_right_bundle,
    nonnegativeRealAdd_zero_left]
  change realAdd realZero (realNeg realZero) = realZero
  rw [realNeg_zero, realAdd_zero_left]

theorem realMul_zero_right (value : IncReal) :
    realMul value realZero = realZero := by
  rw [realMul_comm, realMul_zero_left]

theorem realNeg_ne_zero {value : IncReal} (nonzero : value ≠ realZero) :
    realNeg value ≠ realZero := by
  intro negZero
  apply nonzero
  have restored := congrArg realNeg negZero
  simpa [realNeg_neg, realNeg_zero] using restored

theorem realNegativePart_ne_zero {value : IncReal}
    (notNonnegative : ¬ realLE realZero value)
    (nonzero : value ≠ realZero) :
    (realNegativePart value).value ≠ realZero := by
  rw [realNegativePart_of_not_nonnegative value notNonnegative]
  exact realNeg_ne_zero nonzero

theorem realMul_ne_zero {left right : IncReal}
    (leftNonzero : left ≠ realZero)
    (rightNonzero : right ≠ realZero) :
    realMul left right ≠ realZero := by
  classical
  by_cases leftNonnegative : realLE realZero left
  · by_cases rightNonnegative : realLE realZero right
    · rw [realMul_of_nonnegative left right
        leftNonnegative rightNonnegative]
      exact nonnegativeRealMul_ne_zero
        ⟨left, leftNonnegative⟩ ⟨right, rightNonnegative⟩
        leftNonzero rightNonzero
    · rw [realMul_of_nonnegative_not_nonnegative left right
        leftNonnegative rightNonnegative]
      apply realNeg_ne_zero
      apply nonnegativeRealMul_ne_zero
      · exact leftNonzero
      · exact realNeg_ne_zero rightNonzero
  · by_cases rightNonnegative : realLE realZero right
    · rw [realMul_of_not_nonnegative_nonnegative left right
        leftNonnegative rightNonnegative]
      apply realNeg_ne_zero
      apply nonnegativeRealMul_ne_zero
      · exact realNeg_ne_zero leftNonzero
      · exact rightNonzero
    · rw [realMul_of_not_nonnegative left right
        leftNonnegative rightNonnegative]
      apply nonnegativeRealMul_ne_zero
      · exact realNeg_ne_zero leftNonzero
      · exact realNeg_ne_zero rightNonzero

theorem real_eq_of_add_neg_eq_zero {left right : IncReal}
    (differenceZero : realAdd left (realNeg right) = realZero) :
    left = right := by
  apply realAdd_cancel_right left right (realNeg right)
  rw [differenceZero, realAdd_neg]

theorem realMul_cancel_left {factor left right : IncReal}
    (factorNonzero : factor ≠ realZero)
    (equal : realMul factor left = realMul factor right) :
    left = right := by
  have productDifferenceZero :
      realMul factor (realAdd left (realNeg right)) = realZero := by
    rw [realMul_add, realMul_neg_right, equal, realAdd_neg]
  have differenceZero : realAdd left (realNeg right) = realZero := by
    by_cases differenceZero : realAdd left (realNeg right) = realZero
    · exact differenceZero
    · exact False.elim
        ((realMul_ne_zero factorNonzero differenceZero)
          productDifferenceZero)
  exact real_eq_of_add_neg_eq_zero differenceZero

theorem realMul_cancel_right {factor left right : IncReal}
    (factorNonzero : factor ≠ realZero)
    (equal : realMul left factor = realMul right factor) :
    left = right := by
  apply realMul_cancel_left factorNonzero
  simpa [realMul_comm] using equal

theorem realMul_one_left (value : IncReal) :
    realMul realOne value = value := by
  rw [realMul, realPositivePart_one, realNegativePart_one,
    nonnegativeRealMul_one_left_bundle,
    nonnegativeRealMul_zero_left_bundle,
    nonnegativeRealAdd_zero_right,
    nonnegativeRealMul_one_left_bundle,
    nonnegativeRealMul_zero_left_bundle,
    nonnegativeRealAdd_zero_right]
  exact real_signed_decomposition value

theorem realMul_one_right (value : IncReal) :
    realMul value realOne = value := by
  rw [realMul_comm, realMul_one_left]

/-- Multiplicative inverse of a nonzero signed real, obtained by applying the
relational reciprocal cut to its positive magnitude and restoring its sign. -/
noncomputable def realInv (value : IncReal) (nonzero : value ≠ realZero) :
    IncReal := by
  classical
  exact if nonnegative : realLE realZero value then
    (nonnegativeRealInv ⟨value, nonnegative⟩ nonzero).value
  else
    realNeg (nonnegativeRealInv (realNegativePart value)
      (realNegativePart_ne_zero nonnegative nonzero)).value

noncomputable def realInvOrZero (value : IncReal) : IncReal := by
  classical
  exact if nonzero : value ≠ realZero then realInv value nonzero else realZero

theorem realInvOrZero_of_ne (value : IncReal) (nonzero : value ≠ realZero) :
    realInvOrZero value = realInv value nonzero := by
  classical
  rw [realInvOrZero]
  simp only [dif_pos nonzero]

theorem realInvOrZero_zero : realInvOrZero realZero = realZero := by
  classical
  rw [realInvOrZero]
  simp

theorem realInv_of_nonnegative
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero) :
    realInv value.value nonzero = (nonnegativeRealInv value nonzero).value := by
  classical
  rw [realInv]
  simp only [dif_pos value.nonnegative]

theorem realMul_inv (value : IncReal) (nonzero : value ≠ realZero) :
    realMul value (realInv value nonzero) = realOne := by
  classical
  by_cases nonnegative : realLE realZero value
  · rw [realInv]
    simp only [dif_pos nonnegative]
    rw [realMul_of_nonnegative value
      (nonnegativeRealInv ⟨value, nonnegative⟩ nonzero).value
      nonnegative
      (nonnegativeRealInv ⟨value, nonnegative⟩ nonzero).nonnegative]
    exact congrArg NonnegativeReal.value
      (nonnegativeRealMul_inv ⟨value, nonnegative⟩ nonzero)
  · let magnitude := realNegativePart value
    have magnitudeNonzero : magnitude.value ≠ realZero :=
      realNegativePart_ne_zero nonnegative nonzero
    have valueEq : value = realNeg magnitude.value :=
      real_eq_neg_negativePart value nonnegative
    rw [realInv]
    simp only [dif_neg nonnegative]
    change realMul value
      (realNeg (nonnegativeRealInv magnitude magnitudeNonzero).value) = realOne
    rw [valueEq, realMul_neg_neg]
    rw [realMul_of_nonnegative magnitude.value
      (nonnegativeRealInv magnitude magnitudeNonzero).value
      magnitude.nonnegative
      (nonnegativeRealInv magnitude magnitudeNonzero).nonnegative]
    exact congrArg NonnegativeReal.value
      (nonnegativeRealMul_inv magnitude magnitudeNonzero)

theorem realInv_mul (value : IncReal) (nonzero : value ≠ realZero) :
    realMul (realInv value nonzero) value = realOne := by
  rw [realMul_comm, realMul_inv]

theorem realInv_sub_realInv
    (left right : IncReal)
    (leftNonzero : left ≠ realZero)
    (rightNonzero : right ≠ realZero) :
    realAdd (realInv left leftNonzero)
        (realNeg (realInv right rightNonzero)) =
      realMul
        (realMul (realInv left leftNonzero)
          (realInv right rightNonzero))
        (realAdd right (realNeg left)) := by
  rw [realMul_add, realMul_neg_right]
  have firstTerm :
      realMul
          (realMul (realInv left leftNonzero)
            (realInv right rightNonzero)) right =
        realInv left leftNonzero := by
    rw [realMul_assoc, realInv_mul, realMul_one_right]
  have secondTerm :
      realMul
          (realMul (realInv left leftNonzero)
            (realInv right rightNonzero)) left =
        realInv right rightNonzero := by
    calc
      _ = realMul (realInv right rightNonzero)
          (realMul (realInv left leftNonzero) left) := by
            rw [← realMul_assoc, realMul_comm
              (realInv left leftNonzero) (realInv right rightNonzero),
              realMul_assoc]
      _ = realInv right rightNonzero := by
            rw [realInv_mul, realMul_one_right]
  rw [firstTerm, secondTerm]

def realMulResonance (left right mode : IncReal) : Prop :=
  realMul left right = mode

theorem real_zero_ne_one : realZero ≠ realOne := by
  intro equal
  have rationalEqual : rationalOfInteger 0 = rationalOfInteger 1 :=
    rationalToReal_injective equal
  have integerEqual := rationalOfInteger_injective rationalEqual
  omega

noncomputable def realDistributiveResonanceSpec :
    DistributiveResonanceSpec realIncidence where
  one := realOne
  multiply := realMulResonance
  symmetric := by
    intro i j k multiplied
    simpa [realMulResonance, realMul_comm] using multiplied
  unit_left := by intro i; exact realMul_one_left i
  unit_right := by intro i; exact realMul_one_right i
  associative := by
    intro i j k out
    constructor
    · rintro ⟨ij, hij, hout⟩
      subst ij
      refine ⟨realMul j k, rfl, ?_⟩
      simpa [realMulResonance, realMul_assoc] using hout
    · rintro ⟨jk, hjk, hout⟩
      subst jk
      refine ⟨realMul i j, rfl, ?_⟩
      simpa [realMulResonance, realMul_assoc] using hout
  distributes := by
    intro i j k out
    constructor
    · rintro ⟨jk, hjk, hout⟩
      have hjkEq : realAdd j k = jk := by
        simpa [realIncidence] using hjk
      subst jk
      refine ⟨realMul i j, realMul i k, rfl, rfl, ?_⟩
      simpa [realIncidence, realMulResonance, realMul_add] using hout
    · rintro ⟨ij, ik, hij, hik, hout⟩
      subst ij
      subst ik
      refine ⟨realAdd j k, ?_, ?_⟩
      · simp [realIncidence]
      · simpa [realIncidence, realMulResonance, realMul_add] using hout

noncomputable def realFieldResonanceSpec :
    FieldResonanceSpec realIncidence where
  toDistributiveResonanceSpec := realDistributiveResonanceSpec
  zero_ne_one := real_zero_ne_one
  additive_inverse := by
    intro value
    refine ⟨realNeg value, ?_⟩
    simpa [realIncidence] using realAdd_neg value
  multiplicative_inverse := by
    intro value nonzero
    exact ⟨realInv value nonzero, realMul_inv value nonzero⟩

noncomputable def realOrderedFieldResonanceSpec :
    OrderedFieldResonanceSpec realIncidence where
  toFieldResonanceSpec := realFieldResonanceSpec
  le := realLE
  le_refl := realLE_refl
  le_antisymm := by intro i j; exact realLE_antisymm
  le_trans := by intro i j k; exact realLE_trans
  le_total := realLE_total
  add_monotone := by
    intro offset i j outI outJ ordered leftMode rightMode
    have leftEq : realAdd offset i = outI := by
      simpa [realIncidence] using leftMode
    have rightEq : realAdd offset j = outJ := by
      simpa [realIncidence] using rightMode
    subst outI
    subst outJ
    exact realAdd_monotone_right ordered
  multiply_nonnegative := by
    intro i j out iNonnegative jNonnegative multiplied
    have outEq : realMul i j = out := by
      simpa [realMulResonance] using multiplied
    subst out
    rw [realMul_of_nonnegative i j iNonnegative jNonnegative]
    exact (nonnegativeRealMul ⟨i, iNonnegative⟩
      ⟨j, jNonnegative⟩).nonnegative

theorem nonnegativeRealMul_rationalToReal_positive
    {left right : IncRational}
    (leftPositive : rationalLT (rationalOfInteger 0) left)
    (rightPositive : rationalLT (rationalOfInteger 0) right) :
    (nonnegativeRealMul
      { value := rationalToReal left
        nonnegative := (rationalToReal_le_iff _ _).mpr leftPositive.1 }
      { value := rationalToReal right
        nonnegative := (rationalToReal_le_iff _ _).mpr rightPositive.1 }).value =
      rationalToReal (rationalMul left right) := by
  apply IncReal.ext
  intro rational
  constructor
  · intro member
    rcases member with negative | generated
    · exact rationalLT_trans negative
        (rationalMul_positive leftPositive rightPositive)
    · obtain ⟨leftValue, rightValue, leftMember, rightMember,
          leftValuePositive, rightValuePositive, below⟩ := generated
      have productBelow := rationalLT_mul_of_positive leftMember rightMember
        rightValuePositive leftPositive
      exact rationalLT_trans below productBelow
  · intro below
    by_cases negative : rationalLT rational (rationalOfInteger 0)
    · exact Or.inl negative
    · have rationalNonnegative :
          rationalLE (rationalOfInteger 0) rational :=
        rationalLE_of_not_lt negative
      obtain ⟨rightValue, rightValuePositive, rightMember,
          firstBelow⟩ := rationalLT_mul_positive_approx_right
        rationalNonnegative leftPositive rightPositive below
      have firstBelowComm : rationalLT rational
          (rationalMul rightValue left) := by
        simpa [rationalMul_comm] using firstBelow
      obtain ⟨leftValue, leftValuePositive, leftMember,
          finalBelow⟩ := rationalLT_mul_positive_approx_right
        rationalNonnegative rightValuePositive leftPositive firstBelowComm
      exact Or.inr ⟨leftValue, rightValue, leftMember, rightMember,
        leftValuePositive, rightValuePositive, by
          simpa [rationalMul_comm] using finalBelow⟩

theorem realMul_rationalToReal_positive
    {left right : IncRational}
    (leftPositive : rationalLT (rationalOfInteger 0) left)
    (rightPositive : rationalLT (rationalOfInteger 0) right) :
    realMul (rationalToReal left) (rationalToReal right) =
      rationalToReal (rationalMul left right) := by
  rw [realMul_of_nonnegative (rationalToReal left) (rationalToReal right)
    ((rationalToReal_le_iff _ _).mpr leftPositive.1)
    ((rationalToReal_le_iff _ _).mpr rightPositive.1)]
  exact nonnegativeRealMul_rationalToReal_positive leftPositive rightPositive

theorem nonnegativeRealInv_rationalToReal_positive
    {value inverse : IncRational}
    (valuePositive : rationalLT (rationalOfInteger 0) value)
    (valueRealNonzero : rationalToReal value ≠ realZero)
    (inverseLaw : rationalMul value inverse = rationalOfInteger 1) :
    nonnegativeRealInv
        { value := rationalToReal value
          nonnegative := (rationalToReal_le_iff _ _).mpr valuePositive.1 }
        valueRealNonzero =
      { value := rationalToReal inverse
        nonnegative := by
          have inversePositive :
              rationalLT (rationalOfInteger 0) inverse := by
            apply rationalMul_positive_reflect_right valuePositive
            rw [inverseLaw]
            exact rational_zero_lt_one
          exact (rationalToReal_le_iff _ _).mpr inversePositive.1 } := by
  have inversePositive : rationalLT (rationalOfInteger 0) inverse := by
    apply rationalMul_positive_reflect_right valuePositive
    rw [inverseLaw]
    exact rational_zero_lt_one
  let source : NonnegativeReal :=
    { value := rationalToReal value
      nonnegative := (rationalToReal_le_iff _ _).mpr valuePositive.1 }
  let target : NonnegativeReal :=
    { value := rationalToReal inverse
      nonnegative := (rationalToReal_le_iff _ _).mpr inversePositive.1 }
  apply NonnegativeReal.ext
  apply realMul_cancel_left valueRealNonzero
  rw [realMul_of_nonnegative source.value
      (nonnegativeRealInv source valueRealNonzero).value source.nonnegative
      (nonnegativeRealInv source valueRealNonzero).nonnegative,
    realMul_of_nonnegative source.value target.value source.nonnegative
      target.nonnegative]
  change (nonnegativeRealMul source (nonnegativeRealInv source valueRealNonzero)).value =
    (nonnegativeRealMul source target).value
  rw [nonnegativeRealMul_inv,
    nonnegativeRealMul_rationalToReal_positive valuePositive inversePositive,
    inverseLaw]
  rfl

/-- Absolute value as the sum of the canonical positive and negative
magnitudes. Exactly one part is nonzero away from the origin. -/
noncomputable def realAbs (value : IncReal) : NonnegativeReal :=
  nonnegativeRealAdd (realPositivePart value) (realNegativePart value)

theorem realAbs_of_nonnegative (value : IncReal)
    (nonnegative : realLE realZero value) :
    realAbs value = ⟨value, nonnegative⟩ := by
  rw [realAbs, realPositivePart_of_nonnegative value nonnegative,
    realNegativePart_of_nonnegative value nonnegative,
    nonnegativeRealAdd_zero_right]

theorem realAbs_of_not_nonnegative (value : IncReal)
    (notNonnegative : ¬ realLE realZero value) :
    realAbs value = realNegativePart value := by
  rw [realAbs, realPositivePart_of_not_nonnegative value notNonnegative,
    nonnegativeRealAdd_zero_left]

theorem realAbs_neg (value : IncReal) :
    realAbs (realNeg value) = realAbs value := by
  change nonnegativeRealAdd (realPositivePart (realNeg value))
    (realNegativePart (realNeg value)) =
      nonnegativeRealAdd (realPositivePart value) (realNegativePart value)
  rw [realPositivePart_neg, realNegativePart_neg,
    nonnegativeRealAdd_comm]

theorem realAbs_zero : realAbs realZero = nonnegativeZero := by
  rw [realAbs_of_nonnegative realZero (realLE_refl _)]
  rfl

theorem realAbs_eq_zero_iff (value : IncReal) :
    (realAbs value).value = realZero ↔ value = realZero := by
  constructor
  · intro absoluteZero
    by_cases nonnegative : realLE realZero value
    · rw [realAbs_of_nonnegative value nonnegative] at absoluteZero
      exact absoluteZero
    · rw [realAbs_of_not_nonnegative value nonnegative,
        realNegativePart_of_not_nonnegative value nonnegative] at absoluteZero
      have restored := congrArg realNeg absoluteZero
      simpa [realNeg_neg, realNeg_zero] using restored
  · intro valueZero
    subst value
    exact congrArg NonnegativeReal.value realAbs_zero

theorem real_le_abs (value : IncReal) :
    realLE value (realAbs value).value := by
  by_cases nonnegative : realLE realZero value
  · rw [realAbs_of_nonnegative value nonnegative]
    exact realLE_refl value
  · rw [realAbs_of_not_nonnegative value nonnegative]
    have valueNonpositive : realLE value realZero := by
      rcases realLE_total value realZero with ordered | reverse
      · exact ordered
      · exact False.elim (nonnegative reverse)
    exact realLE_trans valueNonpositive (realNegativePart value).nonnegative

theorem real_neg_le_abs (value : IncReal) :
    realLE (realNeg value) (realAbs value).value := by
  have bounded := real_le_abs (realNeg value)
  rw [realAbs_neg] at bounded
  exact bounded

theorem realAbs_add_le (left right : IncReal) :
    realLE (realAbs (realAdd left right)).value
      (nonnegativeRealAdd (realAbs left) (realAbs right)).value := by
  let sum := realAdd left right
  by_cases sumNonnegative : realLE realZero sum
  · rw [realAbs_of_nonnegative sum sumNonnegative]
    exact realAdd_monotone (real_le_abs left) (real_le_abs right)
  · rw [realAbs_of_not_nonnegative sum sumNonnegative,
      realNegativePart_of_not_nonnegative sum sumNonnegative]
    change realLE (realNeg (realAdd left right))
      (realAdd (realAbs left).value (realAbs right).value)
    rw [realNeg_add]
    exact realAdd_monotone (real_neg_le_abs left) (real_neg_le_abs right)

theorem realAbs_mul_nonnegative (left right : NonnegativeReal) :
    realAbs (realMul left.value right.value) =
      nonnegativeRealMul (realAbs left.value) (realAbs right.value) := by
  rw [realMul_of_nonnegative left.value right.value
      left.nonnegative right.nonnegative,
    realAbs_of_nonnegative
      (nonnegativeRealMul left right).value
      (nonnegativeRealMul left right).nonnegative,
    realAbs_of_nonnegative left.value left.nonnegative,
    realAbs_of_nonnegative right.value right.nonnegative]

theorem realAbs_mul (left right : IncReal) :
    realAbs (realMul left right) =
      nonnegativeRealMul (realAbs left) (realAbs right) := by
  by_cases leftNonnegative : realLE realZero left
  · let leftPart : NonnegativeReal := ⟨left, leftNonnegative⟩
    by_cases rightNonnegative : realLE realZero right
    · let rightPart : NonnegativeReal := ⟨right, rightNonnegative⟩
      exact realAbs_mul_nonnegative leftPart rightPart
    · let rightPart := realNegativePart right
      have rightEq := real_eq_neg_negativePart right rightNonnegative
      rw [rightEq, realMul_neg_right, realAbs_neg, realAbs_neg]
      exact realAbs_mul_nonnegative leftPart rightPart
  · let leftPart := realNegativePart left
    have leftEq := real_eq_neg_negativePart left leftNonnegative
    by_cases rightNonnegative : realLE realZero right
    · let rightPart : NonnegativeReal := ⟨right, rightNonnegative⟩
      rw [leftEq, realMul_neg_left, realAbs_neg, realAbs_neg]
      exact realAbs_mul_nonnegative leftPart rightPart
    · let rightPart := realNegativePart right
      have rightEq := real_eq_neg_negativePart right rightNonnegative
      rw [leftEq, rightEq, realMul_neg_neg, realAbs_neg, realAbs_neg]
      exact realAbs_mul_nonnegative leftPart rightPart

theorem realAbs_mul_abs_inv
    (value : IncReal) (nonzero : value ≠ realZero) :
    nonnegativeRealMul (realAbs value) (realAbs (realInv value nonzero)) =
      nonnegativeOne := by
  rw [← realAbs_mul, realMul_inv]
  exact realAbs_of_nonnegative realOne nonnegativeOne.nonnegative

theorem realAbs_inv_eq_nonnegativeRealInv
    (value : IncReal) (nonzero : value ≠ realZero) :
    realAbs (realInv value nonzero) =
      nonnegativeRealInv (realAbs value)
        (by
          intro absoluteZero
          exact nonzero ((realAbs_eq_zero_iff value).mp absoluteZero)) := by
  let magnitude := realAbs value
  have magnitudeNonzero : magnitude.value ≠ realZero := by
    intro absoluteZero
    exact nonzero ((realAbs_eq_zero_iff value).mp absoluteZero)
  let canonicalInverse := nonnegativeRealInv magnitude magnitudeNonzero
  apply NonnegativeReal.ext
  apply realMul_cancel_left magnitudeNonzero
  rw [realMul_of_nonnegative magnitude.value
      (realAbs (realInv value nonzero)).value
      magnitude.nonnegative (realAbs (realInv value nonzero)).nonnegative,
    realMul_of_nonnegative magnitude.value canonicalInverse.value
      magnitude.nonnegative canonicalInverse.nonnegative]
  change (nonnegativeRealMul magnitude (realAbs (realInv value nonzero))).value =
    (nonnegativeRealMul magnitude canonicalInverse).value
  rw [realAbs_mul_abs_inv, nonnegativeRealMul_inv]

/-- The order-valued metric candidate induced by absolute difference. -/
noncomputable def realDist (left right : IncReal) : NonnegativeReal :=
  realAbs (realAdd left (realNeg right))

theorem realDist_self (value : IncReal) :
    realDist value value = nonnegativeZero := by
  rw [realDist, realAdd_neg, realAbs_zero]

theorem realDist_comm (left right : IncReal) :
    realDist left right = realDist right left := by
  rw [realDist, realDist]
  have differenceNeg :
      realNeg (realAdd left (realNeg right)) =
        realAdd right (realNeg left) := by
    rw [realNeg_add, realNeg_neg, realAdd_comm]
  rw [← differenceNeg, realAbs_neg]

theorem realDist_inv
    (left right : IncReal)
    (leftNonzero : left ≠ realZero)
    (rightNonzero : right ≠ realZero) :
    realDist (realInv left leftNonzero) (realInv right rightNonzero) =
      nonnegativeRealMul
        (nonnegativeRealMul
          (realAbs (realInv left leftNonzero))
          (realAbs (realInv right rightNonzero)))
        (realDist left right) := by
  rw [realDist, realInv_sub_realInv left right leftNonzero rightNonzero,
    realAbs_mul, realAbs_mul, realDist_comm]
  rfl

theorem realDist_eq_zero_iff (left right : IncReal) :
    (realDist left right).value = realZero ↔ left = right := by
  rw [realDist, realAbs_eq_zero_iff]
  constructor
  · exact real_eq_of_add_neg_eq_zero
  · intro equal
    subst right
    exact realAdd_neg left

theorem realDist_triangle (first second third : IncReal) :
    realLE (realDist first third).value
      (nonnegativeRealAdd (realDist first second)
        (realDist second third)).value := by
  have differenceDecompose :
      realAdd first (realNeg third) =
        realAdd (realAdd first (realNeg second))
          (realAdd second (realNeg third)) := by
    symm
    calc
      realAdd (realAdd first (realNeg second))
          (realAdd second (realNeg third)) =
        realAdd first
          (realAdd (realNeg second) (realAdd second (realNeg third))) :=
        realAdd_assoc _ _ _
      _ = realAdd first
          (realAdd (realAdd (realNeg second) second) (realNeg third)) := by
        exact congrArg (realAdd first)
          (realAdd_assoc (realNeg second) second (realNeg third)).symm
      _ = realAdd first (realNeg third) := by
        rw [realAdd_neg_left, realAdd_zero_left]
  change realLE
    (realAbs (realAdd first (realNeg third))).value
    (nonnegativeRealAdd
      (realAbs (realAdd first (realNeg second)))
      (realAbs (realAdd second (realNeg third)))).value
  rw [differenceDecompose]
  exact realAbs_add_le _ _

theorem realDist_neg (left right : IncReal) :
    realDist (realNeg left) (realNeg right) = realDist left right := by
  rw [realDist, realDist, realNeg_neg]
  have differenceNeg :
      realAdd (realNeg left) right =
        realNeg (realAdd left (realNeg right)) := by
    rw [realNeg_add, realNeg_neg]
  rw [differenceNeg, realAbs_neg]

theorem realDist_add_le (left right left' right' : IncReal) :
    realLE (realDist (realAdd left right) (realAdd left' right')).value
      (nonnegativeRealAdd (realDist left left')
        (realDist right right')).value := by
  have differenceDecompose :
      realAdd (realAdd left right)
          (realNeg (realAdd left' right')) =
        realAdd (realAdd left (realNeg left'))
          (realAdd right (realNeg right')) := by
    rw [realNeg_add]
    calc
      realAdd (realAdd left right)
          (realAdd (realNeg left') (realNeg right')) =
        realAdd left
          (realAdd right (realAdd (realNeg left') (realNeg right'))) :=
        realAdd_assoc _ _ _
      _ = realAdd left
          (realAdd (realNeg left') (realAdd right (realNeg right'))) := by
        apply congrArg (realAdd left)
        calc
          realAdd right (realAdd (realNeg left') (realNeg right')) =
              realAdd (realAdd right (realNeg left')) (realNeg right') :=
            (realAdd_assoc _ _ _).symm
          _ = realAdd (realAdd (realNeg left') right) (realNeg right') := by
            rw [realAdd_comm right (realNeg left')]
          _ = realAdd (realNeg left') (realAdd right (realNeg right')) :=
            realAdd_assoc _ _ _
      _ = realAdd (realAdd left (realNeg left'))
          (realAdd right (realNeg right')) :=
        (realAdd_assoc _ _ _).symm
  change realLE
    (realAbs (realAdd (realAdd left right)
      (realNeg (realAdd left' right')))).value
    (nonnegativeRealAdd
      (realAbs (realAdd left (realNeg left')))
      (realAbs (realAdd right (realNeg right')))).value
  rw [differenceDecompose]
  exact realAbs_add_le _ _

abbrev RealSequence := Nat → IncReal

/-- Metric convergence, quantified over reconstructed positive rational
radii. This keeps the definition internal to the rational/real tower. -/
def RealSequenceConverges (sequence : RealSequence) (limit : IncReal) : Prop :=
  ∀ epsilon : IncRational,
    rationalLT (rationalOfInteger 0) epsilon →
      ∃ threshold : Nat, ∀ index, threshold ≤ index →
        realLE (realDist (sequence index) limit).value
          (rationalToReal epsilon)

def RealSequenceCauchy (sequence : RealSequence) : Prop :=
  ∀ epsilon : IncRational,
    rationalLT (rationalOfInteger 0) epsilon →
      ∃ threshold : Nat, ∀ left right,
        threshold ≤ left → threshold ≤ right →
          realLE (realDist (sequence left) (sequence right)).value
            (rationalToReal epsilon)

theorem realSequenceConverges_const (value : IncReal) :
    RealSequenceConverges (fun _ => value) value := by
  intro epsilon epsilonPositive
  refine ⟨0, ?_⟩
  intro index _
  rw [realDist_self]
  change realLE realZero (rationalToReal epsilon)
  exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realSequenceCauchy_const (value : IncReal) :
    RealSequenceCauchy (fun _ => value) := by
  intro epsilon epsilonPositive
  refine ⟨0, ?_⟩
  intro left right _ _
  rw [realDist_self]
  change realLE realZero (rationalToReal epsilon)
  exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realSequenceConverges_cauchy
    {sequence : RealSequence} {limit : IncReal}
    (converges : RealSequenceConverges sequence limit) :
    RealSequenceCauchy sequence := by
  intro epsilon epsilonPositive
  obtain ⟨half, halfPositive, halfAdd⟩ :=
    rational_exists_positive_half epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := converges half halfPositive
  refine ⟨threshold, ?_⟩
  intro left right leftLarge rightLarge
  have leftBound := eventuallyClose left leftLarge
  have rightBound := eventuallyClose right rightLarge
  have rightBound' : realLE (realDist limit (sequence right)).value
      (rationalToReal half) := by
    rw [realDist_comm]
    exact rightBound
  have triangle := realDist_triangle (sequence left) limit (sequence right)
  have summed := realAdd_monotone leftBound rightBound'
  have bounded := realLE_trans triangle summed
  change realLE (realDist (sequence left) (sequence right)).value
    (rationalToReal epsilon)
  calc
    realLE (realDist (sequence left) (sequence right)).value
        (realAdd (rationalToReal half) (rationalToReal half)) := bounded
    _ = rationalToReal epsilon := by
      rw [realAdd_rationalToReal, halfAdd]

theorem nonnegativeReal_eq_zero_of_le_all_positive
    (value : NonnegativeReal)
    (bounded : ∀ epsilon : IncRational,
      rationalLT (rationalOfInteger 0) epsilon →
        realLE value.value (rationalToReal epsilon)) :
    value.value = realZero := by
  apply Eq.symm
  apply realLE_antisymm value.nonnegative
  intro rational member
  obtain ⟨larger, largerMember, rationalLarger⟩ := value.value.rounded member
  by_cases rationalNegative : rationalLT rational (rationalOfInteger 0)
  · exact rationalNegative
  · have rationalNonnegative :
        rationalLE (rationalOfInteger 0) rational :=
      rationalLE_of_not_lt rationalNegative
    have largerPositive : rationalLT (rationalOfInteger 0) larger :=
      rationalLT_of_le_of_lt rationalNonnegative rationalLarger
    obtain ⟨epsilon, epsilonPositive, epsilonLarger⟩ :=
      rationalLT_dense largerPositive
    have largerBelowEpsilon := bounded epsilon epsilonPositive larger largerMember
    exact False.elim
      ((rationalLT_asymm epsilonLarger) largerBelowEpsilon)

theorem realSequence_limit_unique
    {sequence : RealSequence} {firstLimit secondLimit : IncReal}
    (firstConverges : RealSequenceConverges sequence firstLimit)
    (secondConverges : RealSequenceConverges sequence secondLimit) :
    firstLimit = secondLimit := by
  have distanceBounded : ∀ epsilon : IncRational,
      rationalLT (rationalOfInteger 0) epsilon →
        realLE (realDist firstLimit secondLimit).value
          (rationalToReal epsilon) := by
    intro epsilon epsilonPositive
    obtain ⟨half, halfPositive, halfAdd⟩ :=
      rational_exists_positive_half epsilonPositive
    obtain ⟨firstThreshold, firstEventually⟩ :=
      firstConverges half halfPositive
    obtain ⟨secondThreshold, secondEventually⟩ :=
      secondConverges half halfPositive
    let index := Nat.max firstThreshold secondThreshold
    have firstLarge : firstThreshold ≤ index := Nat.le_max_left _ _
    have secondLarge : secondThreshold ≤ index := Nat.le_max_right _ _
    have firstBound : realLE
        (realDist firstLimit (sequence index)).value
        (rationalToReal half) := by
      rw [realDist_comm]
      exact firstEventually index firstLarge
    have secondBound := secondEventually index secondLarge
    have triangle := realDist_triangle firstLimit (sequence index) secondLimit
    have summed := realAdd_monotone firstBound secondBound
    have result := realLE_trans triangle summed
    rw [realAdd_rationalToReal, halfAdd] at result
    exact result
  have distanceZero := nonnegativeReal_eq_zero_of_le_all_positive
    (realDist firstLimit secondLimit) distanceBounded
  exact (realDist_eq_zero_iff firstLimit secondLimit).mp distanceZero

theorem realSequenceConverges_neg
    {sequence : RealSequence} {limit : IncReal}
    (converges : RealSequenceConverges sequence limit) :
    RealSequenceConverges (fun index => realNeg (sequence index))
      (realNeg limit) := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := converges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  rw [realDist_neg]
  exact eventuallyClose index indexLarge

theorem realSequenceConverges_add
    {leftSequence rightSequence : RealSequence}
    {leftLimit rightLimit : IncReal}
    (leftConverges : RealSequenceConverges leftSequence leftLimit)
    (rightConverges : RealSequenceConverges rightSequence rightLimit) :
    RealSequenceConverges
      (fun index => realAdd (leftSequence index) (rightSequence index))
      (realAdd leftLimit rightLimit) := by
  intro epsilon epsilonPositive
  obtain ⟨half, halfPositive, halfAdd⟩ :=
    rational_exists_positive_half epsilonPositive
  obtain ⟨leftThreshold, leftEventually⟩ :=
    leftConverges half halfPositive
  obtain ⟨rightThreshold, rightEventually⟩ :=
    rightConverges half halfPositive
  refine ⟨Nat.max leftThreshold rightThreshold, ?_⟩
  intro index indexLarge
  have leftLarge : leftThreshold ≤ index :=
    Nat.le_trans (Nat.le_max_left _ _) indexLarge
  have rightLarge : rightThreshold ≤ index :=
    Nat.le_trans (Nat.le_max_right _ _) indexLarge
  have distanceBound := realDist_add_le
    (leftSequence index) (rightSequence index) leftLimit rightLimit
  have summed := realAdd_monotone
    (leftEventually index leftLarge) (rightEventually index rightLarge)
  have result := realLE_trans distanceBound summed
  rw [realAdd_rationalToReal, halfAdd] at result
  exact result

theorem realSequenceConverges_sub
    {leftSequence rightSequence : RealSequence}
    {leftLimit rightLimit : IncReal}
    (leftConverges : RealSequenceConverges leftSequence leftLimit)
    (rightConverges : RealSequenceConverges rightSequence rightLimit) :
    RealSequenceConverges
      (fun index => realAdd (leftSequence index)
        (realNeg (rightSequence index)))
      (realAdd leftLimit (realNeg rightLimit)) :=
  realSequenceConverges_add leftConverges
    (realSequenceConverges_neg rightConverges)

theorem real_le_add_of_dist_le {left right radius : IncReal}
    (bounded : realLE (realDist left right).value radius) :
    realLE left (realAdd right radius) := by
  have differenceBound :
      realLE (realAdd left (realNeg right)) radius :=
    realLE_trans (real_le_abs (realAdd left (realNeg right))) bounded
  have translated := realAdd_monotone_left
    (right := right) differenceBound
  have restore : realAdd (realAdd left (realNeg right)) right = left := by
    rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
  rw [restore, realAdd_comm radius right] at translated
  exact translated

theorem realDist_le_of_le_of_le_add
    {left right : IncReal} (radius : NonnegativeReal)
    (leftRight : realLE left right)
    (rightBound : realLE right (realAdd left radius.value)) :
    realLE (realDist left right).value radius.value := by
  let difference := realAdd left (realNeg right)
  have differenceNonpositive : realLE difference realZero := by
    have translated := realAdd_monotone_left
      (right := realNeg right) leftRight
    rw [realAdd_neg] at translated
    exact translated
  by_cases differenceNonnegative : realLE realZero difference
  · have differenceZero := realLE_antisymm differenceNonnegative
      differenceNonpositive
    change realLE (realAbs difference).value radius.value
    rw [← differenceZero, realAbs_zero]
    exact radius.nonnegative
  · change realLE (realAbs difference).value radius.value
    rw [realAbs_of_not_nonnegative difference differenceNonnegative,
      realNegativePart_of_not_nonnegative difference differenceNonnegative]
    have translated := realAdd_monotone_left
      (right := realNeg left) rightBound
    have leftRestore : realAdd (realAdd left radius.value)
        (realNeg left) = radius.value := by
      calc
        _ = realAdd radius.value (realAdd left (realNeg left)) := by
          rw [realAdd_comm left radius.value, realAdd_assoc]
        _ = radius.value := by rw [realAdd_neg, realAdd_zero_right]
    rw [leftRestore] at translated
    have negDifference : realNeg difference =
        realAdd right (realNeg left) := by
      rw [realNeg_add, realNeg_neg, realAdd_comm]
    change realLE (realNeg difference) radius.value
    rw [negDifference]
    exact translated

theorem realAdd_neg_le_of_le_add {left right radius : IncReal}
    (ordered : realLE left (realAdd right radius)) :
    realLE (realAdd left (realNeg radius)) right := by
  have translated := realAdd_monotone_left
    (right := realNeg radius) ordered
  have restore : realAdd (realAdd right radius) (realNeg radius) = right := by
    rw [realAdd_assoc, realAdd_neg, realAdd_zero_right]
  rw [restore] at translated
  exact translated

theorem realLE_add_of_add_neg_le {left right radius : IncReal}
    (ordered : realLE (realAdd left (realNeg radius)) right) :
    realLE left (realAdd right radius) := by
  have translated := realAdd_monotone_left (right := radius) ordered
  have restore : realAdd (realAdd left (realNeg radius)) radius = left := by
    rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
  rw [restore] at translated
  exact translated

theorem realDist_le_of_le_add_both
    {left right : IncReal} (radius : NonnegativeReal)
    (leftBound : realLE left (realAdd right radius.value))
    (rightBound : realLE right (realAdd left radius.value)) :
    realLE (realDist left right).value radius.value := by
  rcases realLE_total left right with leftRight | rightLeft
  · exact realDist_le_of_le_of_le_add radius leftRight rightBound
  · rw [realDist_comm]
    exact realDist_le_of_le_of_le_add radius rightLeft leftBound

theorem realAbs_le_dist_add_abs (left right : IncReal) :
    realLE (realAbs left).value
      (realAdd (realDist left right).value (realAbs right).value) := by
  have restore : realAdd (realAdd left (realNeg right)) right = left := by
    rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
  have bounded := realAbs_add_le (realAdd left (realNeg right)) right
  rw [restore] at bounded
  exact bounded

theorem realDist_abs_le (left right : IncReal) :
    realLE (realDist (realAbs left).value (realAbs right).value).value
      (realDist left right).value := by
  let radius := realDist left right
  have leftBound : realLE (realAbs left).value
      (realAdd (realAbs right).value radius.value) := by
    rw [realAdd_comm]
    exact realAbs_le_dist_add_abs left right
  have rightBound : realLE (realAbs right).value
      (realAdd (realAbs left).value radius.value) := by
    have bounded := realAbs_le_dist_add_abs right left
    rw [realDist_comm right left] at bounded
    simpa [realAdd_comm] using bounded
  exact realDist_le_of_le_add_both radius leftBound rightBound

theorem realDist_mul_left (factor left right : IncReal) :
    realDist (realMul factor left) (realMul factor right) =
      nonnegativeRealMul (realAbs factor) (realDist left right) := by
  have differenceFactor :
      realAdd (realMul factor left) (realNeg (realMul factor right)) =
        realMul factor (realAdd left (realNeg right)) := by
    rw [← realMul_neg_right, ← realMul_add]
  change realAbs
      (realAdd (realMul factor left) (realNeg (realMul factor right))) =
    nonnegativeRealMul (realAbs factor)
      (realAbs (realAdd left (realNeg right)))
  rw [differenceFactor, realAbs_mul]

theorem realDist_mul_right (left right factor : IncReal) :
    realDist (realMul left factor) (realMul right factor) =
      nonnegativeRealMul (realDist left right) (realAbs factor) := by
  rw [realMul_comm left factor, realMul_comm right factor,
    realDist_mul_left, nonnegativeRealMul_comm_bundle]

theorem realDist_zero_right (value : IncReal) :
    realDist value realZero = realAbs value := by
  rw [realDist, realNeg_zero, realAdd_zero_right]

theorem realDist_zero_left (value : IncReal) :
    realDist realZero value = realAbs value := by
  rw [realDist_comm, realDist_zero_right]

theorem realSequenceConverges_abs
    {sequence : RealSequence} {limit : IncReal}
    (converges : RealSequenceConverges sequence limit) :
    RealSequenceConverges (fun index => (realAbs (sequence index)).value)
      (realAbs limit).value := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := converges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  exact realLE_trans (realDist_abs_le (sequence index) limit)
    (eventuallyClose index indexLarge)

theorem realSequenceConverges_eventually_ne_zero
    {sequence : RealSequence} {limit : IncReal}
    (limitNonzero : limit ≠ realZero)
    (converges : RealSequenceConverges sequence limit) :
    ∃ threshold, ∀ index, threshold ≤ index → sequence index ≠ realZero := by
  have absoluteNonzero : (realAbs limit).value ≠ realZero := by
    intro absoluteZero
    exact limitNonzero ((realAbs_eq_zero_iff limit).mp absoluteZero)
  obtain ⟨radius, radiusMember, radiusPositive⟩ :=
    (realAbs limit).exists_positive_member absoluteNonzero
  obtain ⟨threshold, eventuallyClose⟩ :=
    converges radius radiusPositive
  have radiusStrict : realLT (rationalToReal radius) (realAbs limit).value :=
    rationalToReal_lt_of_lower (realAbs limit).value radiusMember
  refine ⟨threshold, ?_⟩
  intro index indexLarge sequenceZero
  have close := eventuallyClose index indexLarge
  rw [sequenceZero, realDist_zero_left] at close
  exact radiusStrict.2 (realLE_antisymm radiusStrict.1 close)

theorem realSequenceConverges_eventually_abs_lower
    {sequence : RealSequence} {limit : IncReal}
    (limitNonzero : limit ≠ realZero)
    (converges : RealSequenceConverges sequence limit) :
    ∃ radius : IncRational,
      rationalLT (rationalOfInteger 0) radius ∧
      ∃ threshold, ∀ index, threshold ≤ index →
        realLE (rationalToReal radius) (realAbs (sequence index)).value := by
  have absoluteNonzero : (realAbs limit).value ≠ realZero := by
    intro absoluteZero
    exact limitNonzero ((realAbs_eq_zero_iff limit).mp absoluteZero)
  obtain ⟨inside, insideMember, insidePositive⟩ :=
    (realAbs limit).exists_positive_member absoluteNonzero
  obtain ⟨radius, radiusPositive, radiusAdd⟩ :=
    rational_exists_positive_half insidePositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    converges radius radiusPositive
  have insideStrict :
      realLT (rationalToReal inside) (realAbs limit).value :=
    rationalToReal_lt_of_lower (realAbs limit).value insideMember
  refine ⟨radius, radiusPositive, threshold, ?_⟩
  intro index indexLarge
  rcases realLE_total (rationalToReal radius)
      (realAbs (sequence index)).value with lower | absoluteBelowRadius
  · exact lower
  · exfalso
    have limitBound := realAbs_le_dist_add_abs limit (sequence index)
    have distanceBound :
        realLE (realDist limit (sequence index)).value
          (rationalToReal radius) := by
      rw [realDist_comm]
      exact eventuallyClose index indexLarge
    have sumBound := realAdd_monotone distanceBound absoluteBelowRadius
    have limitBelowInside := realLE_trans limitBound sumBound
    rw [realAdd_rationalToReal, radiusAdd] at limitBelowInside
    exact insideStrict.2 (realLE_antisymm insideStrict.1 limitBelowInside)

theorem realSequenceConverges_eventually_inv_abs_upper
    {sequence : RealSequence} {limit : IncReal}
    (limitNonzero : limit ≠ realZero)
    (converges : RealSequenceConverges sequence limit) :
    ∃ bound : IncRational,
      rationalLT (rationalOfInteger 0) bound ∧
      ∃ threshold, ∀ index, threshold ≤ index →
        ∃ indexNonzero : sequence index ≠ realZero,
          realLE (realAbs (realInv (sequence index) indexNonzero)).value
            (rationalToReal bound) := by
  obtain ⟨radius, radiusPositive, threshold, eventuallyLower⟩ :=
    realSequenceConverges_eventually_abs_lower limitNonzero converges
  have radiusRealNonzero : rationalToReal radius ≠ realZero := by
    intro equal
    have injected := rationalToReal_injective equal
    rw [injected] at radiusPositive
    exact rationalLT_irrefl (rationalOfInteger 0) radiusPositive
  have radiusNonzero : radius ≠ rationalOfInteger 0 := by
    intro radiusZero
    rw [radiusZero] at radiusPositive
    exact rationalLT_irrefl (rationalOfInteger 0) radiusPositive
  obtain ⟨bound, inverseLaw⟩ :=
    rational_nonzero_has_mul_inverse radiusNonzero
  have boundPositive : rationalLT (rationalOfInteger 0) bound := by
    apply rationalMul_positive_reflect_right radiusPositive
    rw [inverseLaw]
    exact rational_zero_lt_one
  refine ⟨bound, boundPositive, threshold, ?_⟩
  intro index indexLarge
  have lower := eventuallyLower index indexLarge
  have indexNonzero : sequence index ≠ realZero := by
    intro indexZero
    rw [indexZero, realAbs_zero] at lower
    have radiusNonpositive := realLE_trans lower nonnegativeZero.nonnegative
    have positiveOrder : realLT realZero (rationalToReal radius) :=
      ⟨(rationalToReal_le_iff _ _).mpr radiusPositive.1,
        fun equal => radiusRealNonzero equal.symm⟩
    exact positiveOrder.2
      (realLE_antisymm positiveOrder.1 radiusNonpositive)
  refine ⟨indexNonzero, ?_⟩
  rw [realAbs_inv_eq_nonnegativeRealInv]
  let radiusReal : NonnegativeReal :=
    { value := rationalToReal radius
      nonnegative := (rationalToReal_le_iff _ _).mpr radiusPositive.1 }
  have reversed := nonnegativeRealInv_order_reverse
    (left := radiusReal) (right := realAbs (sequence index))
    radiusRealNonzero
    (by
      intro absoluteZero
      exact indexNonzero
        ((realAbs_eq_zero_iff (sequence index)).mp absoluteZero)) lower
  rw [nonnegativeRealInv_rationalToReal_positive
    radiusPositive radiusRealNonzero inverseLaw] at reversed
  exact reversed

theorem realSequenceConverges_mul_const
    {sequence : RealSequence} {limit factor : IncReal}
    (converges : RealSequenceConverges sequence limit) :
    RealSequenceConverges (fun index => realMul factor (sequence index))
      (realMul factor limit) := by
  intro epsilon epsilonPositive
  obtain ⟨bound, boundNotMember, boundPositive⟩ :=
    (realAbs factor).positive_upper
  have absoluteBound : realLE (realAbs factor).value
      (rationalToReal bound) := by
    intro rational member
    exact (realAbs factor).value.lt_of_lower_of_not_lower
      member boundNotMember
  have boundNonzero : bound ≠ rationalOfInteger 0 := fun equal => by
    subst bound
    exact rationalLT_irrefl _ boundPositive
  obtain ⟨boundInverse, boundInverseLaw⟩ :=
    rational_nonzero_has_mul_inverse boundNonzero
  have boundInversePositive :
      rationalLT (rationalOfInteger 0) boundInverse := by
    apply rationalMul_positive_reflect_right boundPositive
    rw [boundInverseLaw]
    exact rational_zero_lt_one
  let delta := rationalMul epsilon boundInverse
  have deltaPositive : rationalLT (rationalOfInteger 0) delta :=
    rationalMul_positive epsilonPositive boundInversePositive
  have boundDelta : rationalMul bound delta = epsilon := by
    calc
      _ = rationalMul epsilon (rationalMul bound boundInverse) := by
        rw [← rationalMul_assoc bound epsilon boundInverse,
          rationalMul_comm bound epsilon,
          rationalMul_assoc epsilon bound boundInverse]
      _ = rationalMul epsilon (rationalOfInteger 1) := by rw [boundInverseLaw]
      _ = epsilon := rationalMul_one_right epsilon
  obtain ⟨threshold, eventuallyClose⟩ := converges delta deltaPositive
  let boundReal : NonnegativeReal :=
    { value := rationalToReal bound
      nonnegative := (rationalToReal_le_iff _ _).mpr boundPositive.1 }
  let deltaReal : NonnegativeReal :=
    { value := rationalToReal delta
      nonnegative := (rationalToReal_le_iff _ _).mpr deltaPositive.1 }
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  rw [realDist_mul_left]
  have productBound := nonnegativeRealMul_monotone
    (left := realAbs factor) (left' := boundReal)
    (right := realDist (sequence index) limit) (right' := deltaReal)
    absoluteBound (eventuallyClose index indexLarge)
  have principalProduct := nonnegativeRealMul_rationalToReal_positive
    boundPositive deltaPositive
  rw [principalProduct, boundDelta] at productBound
  exact productBound

theorem realSequenceConverges_mul_zero
    {leftSequence rightSequence : RealSequence}
    (leftConverges : RealSequenceConverges leftSequence realZero)
    (rightConverges : RealSequenceConverges rightSequence realZero) :
    RealSequenceConverges
      (fun index => realMul (leftSequence index) (rightSequence index))
      realZero := by
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, deltaBelowOne, deltaBelowEpsilon⟩ :=
    rational_exists_positive_below_two rational_zero_lt_one epsilonPositive
  obtain ⟨leftThreshold, leftEventually⟩ :=
    leftConverges delta deltaPositive
  obtain ⟨rightThreshold, rightEventually⟩ :=
    rightConverges delta deltaPositive
  let deltaReal : NonnegativeReal :=
    { value := rationalToReal delta
      nonnegative := (rationalToReal_le_iff _ _).mpr deltaPositive.1 }
  refine ⟨Nat.max leftThreshold rightThreshold, ?_⟩
  intro index indexLarge
  have leftLarge : leftThreshold ≤ index :=
    Nat.le_trans (Nat.le_max_left _ _) indexLarge
  have rightLarge : rightThreshold ≤ index :=
    Nat.le_trans (Nat.le_max_right _ _) indexLarge
  rw [realDist_zero_right, realAbs_mul]
  have productBound := nonnegativeRealMul_monotone
    (left := realAbs (leftSequence index)) (left' := deltaReal)
    (right := realAbs (rightSequence index)) (right' := deltaReal)
    (by simpa [realDist_zero_right] using leftEventually index leftLarge)
    (by simpa [realDist_zero_right] using rightEventually index rightLarge)
  have principalProduct := nonnegativeRealMul_rationalToReal_positive
    deltaPositive deltaPositive
  rw [principalProduct] at productBound
  have deltaSquareBelowDelta :
      rationalLT (rationalMul delta delta) delta := by
    have multiplied := rationalLT_mul_left_of_positive deltaBelowOne deltaPositive
    simpa [rationalMul_one_right] using multiplied
  have deltaSquareBelowEpsilon :=
    rationalLT_trans deltaSquareBelowDelta deltaBelowEpsilon
  exact realLE_trans productBound
    ((rationalToReal_le_iff _ _).mpr deltaSquareBelowEpsilon.1)

theorem realSequenceConverges_mul
    {leftSequence rightSequence : RealSequence}
    {leftLimit rightLimit : IncReal}
    (leftConverges : RealSequenceConverges leftSequence leftLimit)
    (rightConverges : RealSequenceConverges rightSequence rightLimit) :
    RealSequenceConverges
      (fun index => realMul (leftSequence index) (rightSequence index))
      (realMul leftLimit rightLimit) := by
  let leftError : RealSequence := fun index =>
    realAdd (leftSequence index) (realNeg leftLimit)
  let rightError : RealSequence := fun index =>
    realAdd (rightSequence index) (realNeg rightLimit)
  have leftErrorConverges : RealSequenceConverges leftError realZero := by
    have result := realSequenceConverges_sub leftConverges
      (realSequenceConverges_const leftLimit)
    simpa [leftError, realAdd_neg] using result
  have rightErrorConverges : RealSequenceConverges rightError realZero := by
    have result := realSequenceConverges_sub rightConverges
      (realSequenceConverges_const rightLimit)
    simpa [rightError, realAdd_neg] using result
  let quadratic : RealSequence := fun index =>
    realMul (leftError index) (rightError index)
  have quadraticConverges : RealSequenceConverges quadratic realZero :=
    realSequenceConverges_mul_zero leftErrorConverges rightErrorConverges
  let leftLinear : RealSequence := fun index =>
    realMul (leftError index) rightLimit
  have leftLinearConverges : RealSequenceConverges leftLinear realZero := by
    have result := realSequenceConverges_mul_const
      (factor := rightLimit) leftErrorConverges
    simpa [leftLinear, realMul_comm, realMul_zero_right] using result
  let rightLinear : RealSequence := fun index =>
    realMul leftLimit (rightError index)
  have rightLinearConverges : RealSequenceConverges rightLinear realZero := by
    simpa [rightLinear, realMul_zero_right] using
      (realSequenceConverges_mul_const
        (factor := leftLimit) rightErrorConverges)
  let error : RealSequence := fun index =>
    realAdd (realAdd (quadratic index) (leftLinear index))
      (rightLinear index)
  have errorConverges : RealSequenceConverges error realZero := by
    have firstSum := realSequenceConverges_add quadraticConverges
      leftLinearConverges
    have total := realSequenceConverges_add firstSum rightLinearConverges
    simpa [error, realAdd_zero_left] using total
  let assembled : RealSequence := fun index =>
    realAdd (error index) (realMul leftLimit rightLimit)
  have assembledConverges : RealSequenceConverges assembled
      (realMul leftLimit rightLimit) := by
    have result := realSequenceConverges_add errorConverges
      (realSequenceConverges_const (realMul leftLimit rightLimit))
    simpa [assembled, realAdd_zero_left] using result
  have pointwise : ∀ index,
      realMul (leftSequence index) (rightSequence index) = assembled index := by
    intro index
    have leftRestore : realAdd (leftError index) leftLimit =
        leftSequence index := by
      simp only [leftError]
      rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
    have rightRestore : realAdd (rightError index) rightLimit =
        rightSequence index := by
      simp only [rightError]
      rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
    calc
      realMul (leftSequence index) (rightSequence index) =
          realMul (realAdd (leftError index) leftLimit)
            (realAdd (rightError index) rightLimit) := by
              rw [leftRestore, rightRestore]
      _ = realAdd
          (realAdd (realMul (leftError index) (rightError index))
            (realMul (leftError index) rightLimit))
          (realAdd (realMul leftLimit (rightError index))
            (realMul leftLimit rightLimit)) := by
              rw [realAdd_mul]
              congr 1 <;> rw [realMul_add]
      _ = assembled index := by
            dsimp only [assembled, error, quadratic, leftLinear, rightLinear]
            exact (realAdd_assoc
              (realAdd (realMul (leftError index) (rightError index))
                (realMul (leftError index) rightLimit))
              (realMul leftLimit (rightError index))
              (realMul leftLimit rightLimit)).symm
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    assembledConverges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  change realLE (realDist
    (realMul (leftSequence index) (rightSequence index))
    (realMul leftLimit rightLimit)).value (rationalToReal epsilon)
  rw [pointwise index]
  exact eventuallyClose index indexLarge

theorem realSequenceConverges_invOrZero
    {sequence : RealSequence} {limit : IncReal}
    (limitNonzero : limit ≠ realZero)
    (converges : RealSequenceConverges sequence limit) :
    RealSequenceConverges (fun index => realInvOrZero (sequence index))
      (realInvOrZero limit) := by
  obtain ⟨tailBound, tailBoundPositive, tailThreshold, tailEventually⟩ :=
    realSequenceConverges_eventually_inv_abs_upper limitNonzero converges
  obtain ⟨limitBound, limitBoundNotMember, limitBoundPositive⟩ :=
    (realAbs (realInv limit limitNonzero)).positive_upper
  have limitAbsoluteBound :
      realLE (realAbs (realInv limit limitNonzero)).value
        (rationalToReal limitBound) := by
    intro rational member
    exact (realAbs (realInv limit limitNonzero)).value.lt_of_lower_of_not_lower
      member limitBoundNotMember
  let productBound := rationalMul tailBound limitBound
  have productBoundPositive :
      rationalLT (rationalOfInteger 0) productBound :=
    rationalMul_positive tailBoundPositive limitBoundPositive
  have productBoundNonzero : productBound ≠ rationalOfInteger 0 := by
    intro equal
    rw [equal] at productBoundPositive
    exact rationalLT_irrefl _ productBoundPositive
  obtain ⟨productBoundInverse, productBoundInverseLaw⟩ :=
    rational_nonzero_has_mul_inverse productBoundNonzero
  have productBoundInversePositive :
      rationalLT (rationalOfInteger 0) productBoundInverse := by
    apply rationalMul_positive_reflect_right productBoundPositive
    rw [productBoundInverseLaw]
    exact rational_zero_lt_one
  intro epsilon epsilonPositive
  let delta := rationalMul epsilon productBoundInverse
  have deltaPositive : rationalLT (rationalOfInteger 0) delta :=
    rationalMul_positive epsilonPositive productBoundInversePositive
  have productDelta : rationalMul productBound delta = epsilon := by
    calc
      _ = rationalMul epsilon
          (rationalMul productBound productBoundInverse) := by
            rw [← rationalMul_assoc productBound epsilon productBoundInverse,
              rationalMul_comm productBound epsilon,
              rationalMul_assoc epsilon productBound productBoundInverse]
      _ = rationalMul epsilon (rationalOfInteger 1) := by
            rw [productBoundInverseLaw]
      _ = epsilon := rationalMul_one_right epsilon
  obtain ⟨closeThreshold, eventuallyClose⟩ :=
    converges delta deltaPositive
  let tailBoundReal : NonnegativeReal :=
    { value := rationalToReal tailBound
      nonnegative := (rationalToReal_le_iff _ _).mpr tailBoundPositive.1 }
  let limitBoundReal : NonnegativeReal :=
    { value := rationalToReal limitBound
      nonnegative := (rationalToReal_le_iff _ _).mpr limitBoundPositive.1 }
  let deltaReal : NonnegativeReal :=
    { value := rationalToReal delta
      nonnegative := (rationalToReal_le_iff _ _).mpr deltaPositive.1 }
  let productBoundReal : NonnegativeReal :=
    { value := rationalToReal productBound
      nonnegative :=
        (rationalToReal_le_iff _ _).mpr productBoundPositive.1 }
  refine ⟨Nat.max tailThreshold closeThreshold, ?_⟩
  intro index indexLarge
  have tailLarge : tailThreshold ≤ index :=
    Nat.le_trans (Nat.le_max_left _ _) indexLarge
  have closeLarge : closeThreshold ≤ index :=
    Nat.le_trans (Nat.le_max_right _ _) indexLarge
  obtain ⟨indexNonzero, indexInverseBound⟩ := tailEventually index tailLarge
  change realLE
    (realDist (realInvOrZero (sequence index)) (realInvOrZero limit)).value
    (rationalToReal epsilon)
  rw [realInvOrZero_of_ne (sequence index) indexNonzero,
    realInvOrZero_of_ne limit limitNonzero,
    realDist_inv (sequence index) limit indexNonzero limitNonzero]
  have inverseProductBound := nonnegativeRealMul_monotone
    (left := realAbs (realInv (sequence index) indexNonzero))
    (left' := tailBoundReal)
    (right := realAbs (realInv limit limitNonzero))
    (right' := limitBoundReal)
    indexInverseBound limitAbsoluteBound
  have totalBound := nonnegativeRealMul_monotone
    (left := nonnegativeRealMul
      (realAbs (realInv (sequence index) indexNonzero))
      (realAbs (realInv limit limitNonzero)))
    (left' := nonnegativeRealMul tailBoundReal limitBoundReal)
    (right := realDist (sequence index) limit)
    (right' := deltaReal)
    inverseProductBound (eventuallyClose index closeLarge)
  have firstPrincipal := nonnegativeRealMul_rationalToReal_positive
    tailBoundPositive limitBoundPositive
  have secondPrincipal := nonnegativeRealMul_rationalToReal_positive
    productBoundPositive deltaPositive
  have firstBundle :
      nonnegativeRealMul tailBoundReal limitBoundReal = productBoundReal := by
    apply NonnegativeReal.ext
    exact firstPrincipal
  have secondBundle :
      nonnegativeRealMul productBoundReal deltaReal =
        { value := rationalToReal (rationalMul productBound delta)
          nonnegative := (rationalToReal_le_iff _ _).mpr
            (rationalMul_positive productBoundPositive deltaPositive).1 } := by
    apply NonnegativeReal.ext
    exact secondPrincipal
  rw [firstBundle, secondBundle] at totalBound
  change realLE
    (nonnegativeRealMul
      (nonnegativeRealMul
        (realAbs (realInv (sequence index) indexNonzero))
        (realAbs (realInv limit limitNonzero)))
      (realDist (sequence index) limit)).value
    (rationalToReal (rationalMul productBound delta)) at totalBound
  rw [productDelta] at totalBound
  exact totalBound

noncomputable def realDiv (numerator denominator : IncReal) : IncReal :=
  realMul numerator (realInvOrZero denominator)

theorem realSequenceConverges_div
    {numeratorSequence denominatorSequence : RealSequence}
    {numeratorLimit denominatorLimit : IncReal}
    (denominatorLimitNonzero : denominatorLimit ≠ realZero)
    (numeratorConverges :
      RealSequenceConverges numeratorSequence numeratorLimit)
    (denominatorConverges :
      RealSequenceConverges denominatorSequence denominatorLimit) :
    RealSequenceConverges
      (fun index => realDiv (numeratorSequence index)
        (denominatorSequence index))
      (realDiv numeratorLimit denominatorLimit) := by
  exact realSequenceConverges_mul numeratorConverges
    (realSequenceConverges_invOrZero denominatorLimitNonzero
      denominatorConverges)

def RealSequentiallyContinuousAt
    (function : IncReal → IncReal) (point : IncReal) : Prop :=
  ∀ sequence : RealSequence,
    RealSequenceConverges sequence point →
      RealSequenceConverges (fun index => function (sequence index))
        (function point)

def RealBinarySequentiallyContinuous
    (operation : IncReal → IncReal → IncReal) : Prop :=
  ∀ leftSequence rightSequence : RealSequence,
    ∀ leftLimit rightLimit : IncReal,
      RealSequenceConverges leftSequence leftLimit →
      RealSequenceConverges rightSequence rightLimit →
      RealSequenceConverges
        (fun index => operation (leftSequence index) (rightSequence index))
        (operation leftLimit rightLimit)

theorem realMul_sequentiallyContinuous :
    RealBinarySequentiallyContinuous realMul := by
  intro leftSequence rightSequence leftLimit rightLimit
    leftConverges rightConverges
  exact realSequenceConverges_mul leftConverges rightConverges

theorem realSequentiallyContinuousAt_mul_const
    (factor point : IncReal) :
    RealSequentiallyContinuousAt (fun value => realMul factor value) point := by
  intro sequence converges
  exact realSequenceConverges_mul_const converges

theorem realSequentiallyContinuousAt_invOrZero
    (point : IncReal) (pointNonzero : point ≠ realZero) :
    RealSequentiallyContinuousAt realInvOrZero point := by
  intro sequence converges
  exact realSequenceConverges_invOrZero pointNonzero converges

theorem realSequentiallyContinuousAt_id (point : IncReal) :
    RealSequentiallyContinuousAt (fun value => value) point := by
  intro sequence converges
  exact converges

theorem realSequentiallyContinuousAt_const (constant point : IncReal) :
    RealSequentiallyContinuousAt (fun _ => constant) point := by
  intro sequence _
  exact realSequenceConverges_const constant

theorem realSequentiallyContinuousAt_neg (point : IncReal) :
    RealSequentiallyContinuousAt realNeg point := by
  intro sequence converges
  exact realSequenceConverges_neg converges

theorem realSequentiallyContinuousAt_abs (point : IncReal) :
    RealSequentiallyContinuousAt (fun value => (realAbs value).value) point := by
  intro sequence converges
  exact realSequenceConverges_abs converges

theorem realSequentiallyContinuousAt_comp
    {first second : IncReal → IncReal} {point : IncReal}
    (firstContinuous : RealSequentiallyContinuousAt first point)
    (secondContinuous : RealSequentiallyContinuousAt second (first point)) :
    RealSequentiallyContinuousAt (fun value => second (first value)) point := by
  intro sequence converges
  exact secondContinuous _ (firstContinuous _ converges)

def RealFunctionLimitAt
    (function : IncReal → IncReal) (point limit : IncReal) : Prop :=
  ∀ epsilon : IncRational,
    rationalLT (rationalOfInteger 0) epsilon →
    ∃ delta : IncRational,
      rationalLT (rationalOfInteger 0) delta ∧
      ∀ input, realLE (realDist input point).value (rationalToReal delta) →
        realLE (realDist (function input) limit).value
          (rationalToReal epsilon)

def RealContinuousAt (function : IncReal → IncReal) (point : IncReal) : Prop :=
  RealFunctionLimitAt function point (function point)

theorem realFunctionLimitAt_const (constant point : IncReal) :
    RealFunctionLimitAt (fun _ => constant) point constant := by
  intro epsilon epsilonPositive
  refine ⟨epsilon, epsilonPositive, ?_⟩
  intro input _
  rw [realDist_self]
  exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realFunctionLimitAt_id (point : IncReal) :
    RealFunctionLimitAt (fun value => value) point point := by
  intro epsilon epsilonPositive
  exact ⟨epsilon, epsilonPositive, fun input close => close⟩

theorem realContinuousAt_const (constant point : IncReal) :
    RealContinuousAt (fun _ => constant) point :=
  realFunctionLimitAt_const constant point

theorem realContinuousAt_id (point : IncReal) :
    RealContinuousAt (fun value => value) point :=
  realFunctionLimitAt_id point

theorem realFunctionLimitAt_value
    {function : IncReal → IncReal} {point limit : IncReal}
    (converges : RealFunctionLimitAt function point limit) :
    function point = limit := by
  have distanceBounded : ∀ epsilon : IncRational,
      rationalLT (rationalOfInteger 0) epsilon →
      realLE (realDist (function point) limit).value
        (rationalToReal epsilon) := by
    intro epsilon epsilonPositive
    obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
      converges epsilon epsilonPositive
    apply eventuallyClose point
    rw [realDist_self]
    exact (rationalToReal_le_iff _ _).mpr deltaPositive.1
  have distanceZero := nonnegativeReal_eq_zero_of_le_all_positive
    (realDist (function point) limit) distanceBounded
  exact (realDist_eq_zero_iff (function point) limit).mp distanceZero

theorem realFunctionLimitAt_unique
    {function : IncReal → IncReal} {point firstLimit secondLimit : IncReal}
    (first : RealFunctionLimitAt function point firstLimit)
    (second : RealFunctionLimitAt function point secondLimit) :
    firstLimit = secondLimit := by
  rw [← realFunctionLimitAt_value first, realFunctionLimitAt_value second]

theorem realFunctionLimitAt_unique_of_eq_ne_zero
    {firstFunction secondFunction : IncReal → IncReal}
    {firstLimit secondLimit : IncReal}
    (agree : ∀ input, input ≠ realZero →
      firstFunction input = secondFunction input)
    (firstConverges :
      RealFunctionLimitAt firstFunction realZero firstLimit)
    (secondConverges :
      RealFunctionLimitAt secondFunction realZero secondLimit) :
    firstLimit = secondLimit := by
  have distanceBounded : ∀ epsilon : IncRational,
      rationalLT (rationalOfInteger 0) epsilon →
      realLE (realDist firstLimit secondLimit).value
        (rationalToReal epsilon) := by
    intro epsilon epsilonPositive
    obtain ⟨half, halfPositive, halfAdd⟩ :=
      rational_exists_positive_half epsilonPositive
    obtain ⟨firstRadius, firstRadiusPositive, firstClose⟩ :=
      firstConverges half halfPositive
    obtain ⟨secondRadius, secondRadiusPositive, secondClose⟩ :=
      secondConverges half halfPositive
    obtain ⟨sample, samplePositive, sampleBelowFirst, sampleBelowSecond⟩ :=
      rational_exists_positive_below_two firstRadiusPositive
        secondRadiusPositive
    let input := rationalToReal sample
    have inputNonnegative : realLE realZero input :=
      (rationalToReal_le_iff _ _).mpr samplePositive.1
    have inputNonzero : input ≠ realZero := by
      intro equal
      have injected := rationalToReal_injective equal
      rw [injected] at samplePositive
      exact rationalLT_irrefl _ samplePositive
    have firstInputClose : realLE (realDist input realZero).value
        (rationalToReal firstRadius) := by
      rw [realDist_zero_right,
        realAbs_of_nonnegative input inputNonnegative]
      exact (rationalToReal_le_iff _ _).mpr sampleBelowFirst.1
    have secondInputClose : realLE (realDist input realZero).value
        (rationalToReal secondRadius) := by
      rw [realDist_zero_right,
        realAbs_of_nonnegative input inputNonnegative]
      exact (rationalToReal_le_iff _ _).mpr sampleBelowSecond.1
    have firstBound : realLE
        (realDist firstLimit (firstFunction input)).value
        (rationalToReal half) := by
      rw [realDist_comm]
      exact firstClose input firstInputClose
    have secondBound : realLE
        (realDist (firstFunction input) secondLimit).value
        (rationalToReal half) := by
      rw [agree input inputNonzero]
      exact secondClose input secondInputClose
    have triangle := realDist_triangle firstLimit
      (firstFunction input) secondLimit
    have summed := realAdd_monotone firstBound secondBound
    have bounded := realLE_trans triangle summed
    calc
      realLE (realDist firstLimit secondLimit).value
          (realAdd (rationalToReal half) (rationalToReal half)) := bounded
      _ = rationalToReal epsilon := by
        rw [realAdd_rationalToReal, halfAdd]
  have distanceZero := nonnegativeReal_eq_zero_of_le_all_positive
    (realDist firstLimit secondLimit) distanceBounded
  exact (realDist_eq_zero_iff firstLimit secondLimit).mp distanceZero

theorem realFunctionLimitAt_comp
    {first second : IncReal → IncReal}
    {point middle limit : IncReal}
    (firstLimit : RealFunctionLimitAt first point middle)
    (secondLimit : RealFunctionLimitAt second middle limit) :
    RealFunctionLimitAt (fun value => second (first value)) point limit := by
  intro epsilon epsilonPositive
  obtain ⟨middleRadius, middleRadiusPositive, secondClose⟩ :=
    secondLimit epsilon epsilonPositive
  obtain ⟨inputRadius, inputRadiusPositive, firstClose⟩ :=
    firstLimit middleRadius middleRadiusPositive
  exact ⟨inputRadius, inputRadiusPositive, fun input close =>
    secondClose (first input) (firstClose input close)⟩

theorem realFunctionLimitAt_add
    {left right : IncReal → IncReal}
    {point leftLimit rightLimit : IncReal}
    (leftConverges : RealFunctionLimitAt left point leftLimit)
    (rightConverges : RealFunctionLimitAt right point rightLimit) :
    RealFunctionLimitAt (fun value => realAdd (left value) (right value))
      point (realAdd leftLimit rightLimit) := by
  intro epsilon epsilonPositive
  obtain ⟨half, halfPositive, halfAdd⟩ :=
    rational_exists_positive_half epsilonPositive
  obtain ⟨leftRadius, leftRadiusPositive, leftClose⟩ :=
    leftConverges half halfPositive
  obtain ⟨rightRadius, rightRadiusPositive, rightClose⟩ :=
    rightConverges half halfPositive
  rcases rationalLE_total leftRadius rightRadius with ordered | reverse
  · refine ⟨leftRadius, leftRadiusPositive, ?_⟩
    intro input inputClose
    have rightInputClose : realLE (realDist input point).value
        (rationalToReal rightRadius) :=
      realLE_trans inputClose ((rationalToReal_le_iff _ _).mpr ordered)
    have distanceBound := realDist_add_le
      (left input) (right input) leftLimit rightLimit
    have summed := realAdd_monotone
      (leftClose input inputClose) (rightClose input rightInputClose)
    have result := realLE_trans distanceBound summed
    rw [realAdd_rationalToReal, halfAdd] at result
    exact result
  · refine ⟨rightRadius, rightRadiusPositive, ?_⟩
    intro input inputClose
    have leftInputClose : realLE (realDist input point).value
        (rationalToReal leftRadius) :=
      realLE_trans inputClose ((rationalToReal_le_iff _ _).mpr reverse)
    have distanceBound := realDist_add_le
      (left input) (right input) leftLimit rightLimit
    have summed := realAdd_monotone
      (leftClose input leftInputClose) (rightClose input inputClose)
    have result := realLE_trans distanceBound summed
    rw [realAdd_rationalToReal, halfAdd] at result
    exact result

theorem realFunctionLimitAt_neg
    {function : IncReal → IncReal} {point limit : IncReal}
    (converges : RealFunctionLimitAt function point limit) :
    RealFunctionLimitAt (fun value => realNeg (function value))
      point (realNeg limit) := by
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    converges epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro input inputClose
  rw [realDist_neg]
  exact eventuallyClose input inputClose

theorem realFunctionLimitAt_mul_const
    (factor : IncReal)
    {function : IncReal → IncReal} {point limit : IncReal}
    (converges : RealFunctionLimitAt function point limit) :
    RealFunctionLimitAt (fun value => realMul factor (function value))
      point (realMul factor limit) := by
  intro epsilon epsilonPositive
  obtain ⟨bound, boundNotMember, boundPositive⟩ :=
    (realAbs factor).positive_upper
  have absoluteBound : realLE (realAbs factor).value
      (rationalToReal bound) := by
    intro rational member
    exact (realAbs factor).value.lt_of_lower_of_not_lower
      member boundNotMember
  have boundNonzero : bound ≠ rationalOfInteger 0 := fun equal => by
    subst bound
    exact rationalLT_irrefl _ boundPositive
  obtain ⟨boundInverse, boundInverseLaw⟩ :=
    rational_nonzero_has_mul_inverse boundNonzero
  have boundInversePositive :
      rationalLT (rationalOfInteger 0) boundInverse := by
    apply rationalMul_positive_reflect_right boundPositive
    rw [boundInverseLaw]
    exact rational_zero_lt_one
  let outputRadius := rationalMul epsilon boundInverse
  have outputRadiusPositive :
      rationalLT (rationalOfInteger 0) outputRadius :=
    rationalMul_positive epsilonPositive boundInversePositive
  have boundOutputRadius : rationalMul bound outputRadius = epsilon := by
    calc
      _ = rationalMul epsilon (rationalMul bound boundInverse) := by
        rw [← rationalMul_assoc bound epsilon boundInverse,
          rationalMul_comm bound epsilon,
          rationalMul_assoc epsilon bound boundInverse]
      _ = rationalMul epsilon (rationalOfInteger 1) := by
        rw [boundInverseLaw]
      _ = epsilon := rationalMul_one_right epsilon
  obtain ⟨inputRadius, inputRadiusPositive, eventuallyClose⟩ :=
    converges outputRadius outputRadiusPositive
  let boundReal : NonnegativeReal :=
    { value := rationalToReal bound
      nonnegative := (rationalToReal_le_iff _ _).mpr boundPositive.1 }
  let outputRadiusReal : NonnegativeReal :=
    { value := rationalToReal outputRadius
      nonnegative :=
        (rationalToReal_le_iff _ _).mpr outputRadiusPositive.1 }
  refine ⟨inputRadius, inputRadiusPositive, ?_⟩
  intro input inputClose
  rw [realDist_mul_left]
  have productBound := nonnegativeRealMul_monotone
    (left := realAbs factor) (left' := boundReal)
    (right := realDist (function input) limit) (right' := outputRadiusReal)
    absoluteBound (eventuallyClose input inputClose)
  have principalProduct := nonnegativeRealMul_rationalToReal_positive
    boundPositive outputRadiusPositive
  rw [principalProduct, boundOutputRadius] at productBound
  exact productBound

theorem realFunctionLimitAt_mul_zero
    {left right : IncReal → IncReal} {point : IncReal}
    (leftConverges : RealFunctionLimitAt left point realZero)
    (rightConverges : RealFunctionLimitAt right point realZero) :
    RealFunctionLimitAt (fun value => realMul (left value) (right value))
      point realZero := by
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, deltaBelowOne, deltaBelowEpsilon⟩ :=
    rational_exists_positive_below_two rational_zero_lt_one epsilonPositive
  obtain ⟨leftRadius, leftRadiusPositive, leftClose⟩ :=
    leftConverges delta deltaPositive
  obtain ⟨rightRadius, rightRadiusPositive, rightClose⟩ :=
    rightConverges delta deltaPositive
  let deltaReal : NonnegativeReal :=
    { value := rationalToReal delta
      nonnegative := (rationalToReal_le_iff _ _).mpr deltaPositive.1 }
  rcases rationalLE_total leftRadius rightRadius with ordered | reverse
  · refine ⟨leftRadius, leftRadiusPositive, ?_⟩
    intro input inputClose
    have rightInputClose : realLE (realDist input point).value
        (rationalToReal rightRadius) :=
      realLE_trans inputClose ((rationalToReal_le_iff _ _).mpr ordered)
    rw [realDist_zero_right, realAbs_mul]
    have productBound := nonnegativeRealMul_monotone
      (left := realAbs (left input)) (left' := deltaReal)
      (right := realAbs (right input)) (right' := deltaReal)
      (by simpa [realDist_zero_right] using leftClose input inputClose)
      (by simpa [realDist_zero_right] using
        rightClose input rightInputClose)
    have principalProduct := nonnegativeRealMul_rationalToReal_positive
      deltaPositive deltaPositive
    rw [principalProduct] at productBound
    have deltaSquareBelowDelta : rationalLT (rationalMul delta delta) delta := by
      have multiplied := rationalLT_mul_left_of_positive deltaBelowOne deltaPositive
      simpa [rationalMul_one_right] using multiplied
    exact realLE_trans productBound ((rationalToReal_le_iff _ _).mpr
      (rationalLT_trans deltaSquareBelowDelta deltaBelowEpsilon).1)
  · refine ⟨rightRadius, rightRadiusPositive, ?_⟩
    intro input inputClose
    have leftInputClose : realLE (realDist input point).value
        (rationalToReal leftRadius) :=
      realLE_trans inputClose ((rationalToReal_le_iff _ _).mpr reverse)
    rw [realDist_zero_right, realAbs_mul]
    have productBound := nonnegativeRealMul_monotone
      (left := realAbs (left input)) (left' := deltaReal)
      (right := realAbs (right input)) (right' := deltaReal)
      (by simpa [realDist_zero_right] using
        leftClose input leftInputClose)
      (by simpa [realDist_zero_right] using rightClose input inputClose)
    have principalProduct := nonnegativeRealMul_rationalToReal_positive
      deltaPositive deltaPositive
    rw [principalProduct] at productBound
    have deltaSquareBelowDelta : rationalLT (rationalMul delta delta) delta := by
      have multiplied := rationalLT_mul_left_of_positive deltaBelowOne deltaPositive
      simpa [rationalMul_one_right] using multiplied
    exact realLE_trans productBound ((rationalToReal_le_iff _ _).mpr
      (rationalLT_trans deltaSquareBelowDelta deltaBelowEpsilon).1)

theorem realFunctionLimitAt_mul
    {left right : IncReal → IncReal}
    {point leftLimit rightLimit : IncReal}
    (leftConverges : RealFunctionLimitAt left point leftLimit)
    (rightConverges : RealFunctionLimitAt right point rightLimit) :
    RealFunctionLimitAt (fun value => realMul (left value) (right value))
      point (realMul leftLimit rightLimit) := by
  let leftError : IncReal → IncReal := fun value =>
    realAdd (left value) (realNeg leftLimit)
  let rightError : IncReal → IncReal := fun value =>
    realAdd (right value) (realNeg rightLimit)
  have leftErrorConverges : RealFunctionLimitAt leftError point realZero := by
    have result := realFunctionLimitAt_add leftConverges
      (realFunctionLimitAt_const (realNeg leftLimit) point)
    simpa [leftError, realAdd_neg] using result
  have rightErrorConverges : RealFunctionLimitAt rightError point realZero := by
    have result := realFunctionLimitAt_add rightConverges
      (realFunctionLimitAt_const (realNeg rightLimit) point)
    simpa [rightError, realAdd_neg] using result
  let quadratic : IncReal → IncReal := fun value =>
    realMul (leftError value) (rightError value)
  have quadraticConverges : RealFunctionLimitAt quadratic point realZero :=
    realFunctionLimitAt_mul_zero leftErrorConverges rightErrorConverges
  let leftLinear : IncReal → IncReal := fun value =>
    realMul (leftError value) rightLimit
  have leftLinearConverges : RealFunctionLimitAt leftLinear point realZero := by
    have result := realFunctionLimitAt_mul_const rightLimit leftErrorConverges
    simpa [leftLinear, realMul_comm, realMul_zero_right] using result
  let rightLinear : IncReal → IncReal := fun value =>
    realMul leftLimit (rightError value)
  have rightLinearConverges : RealFunctionLimitAt rightLinear point realZero := by
    simpa [rightLinear, realMul_zero_right] using
      (realFunctionLimitAt_mul_const leftLimit rightErrorConverges)
  let error : IncReal → IncReal := fun value =>
    realAdd (realAdd (quadratic value) (leftLinear value))
      (rightLinear value)
  have errorConverges : RealFunctionLimitAt error point realZero := by
    have firstSum := realFunctionLimitAt_add quadraticConverges
      leftLinearConverges
    have total := realFunctionLimitAt_add firstSum rightLinearConverges
    simpa [error, realAdd_zero_left] using total
  let assembled : IncReal → IncReal := fun value =>
    realAdd (error value) (realMul leftLimit rightLimit)
  have assembledConverges : RealFunctionLimitAt assembled point
      (realMul leftLimit rightLimit) := by
    have result := realFunctionLimitAt_add errorConverges
      (realFunctionLimitAt_const (realMul leftLimit rightLimit) point)
    simpa [assembled, realAdd_zero_left] using result
  have pointwise : ∀ value,
      realMul (left value) (right value) = assembled value := by
    intro value
    have leftRestore : realAdd (leftError value) leftLimit = left value := by
      simp only [leftError]
      rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
    have rightRestore : realAdd (rightError value) rightLimit = right value := by
      simp only [rightError]
      rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
    calc
      realMul (left value) (right value) =
          realMul (realAdd (leftError value) leftLimit)
            (realAdd (rightError value) rightLimit) := by
              rw [leftRestore, rightRestore]
      _ = realAdd
          (realAdd (realMul (leftError value) (rightError value))
            (realMul (leftError value) rightLimit))
          (realAdd (realMul leftLimit (rightError value))
            (realMul leftLimit rightLimit)) := by
              rw [realAdd_mul]
              congr 1 <;> rw [realMul_add]
      _ = assembled value := by
            dsimp only [assembled, error, quadratic, leftLinear, rightLinear]
            exact (realAdd_assoc
              (realAdd (realMul (leftError value) (rightError value))
                (realMul (leftError value) rightLimit))
              (realMul leftLimit (rightError value))
              (realMul leftLimit rightLimit)).symm
  intro epsilon epsilonPositive
  obtain ⟨radius, radiusPositive, eventuallyClose⟩ :=
    assembledConverges epsilon epsilonPositive
  refine ⟨radius, radiusPositive, ?_⟩
  intro input inputClose
  change realLE (realDist (realMul (left input) (right input))
    (realMul leftLimit rightLimit)).value (rationalToReal epsilon)
  rw [pointwise input]
  exact eventuallyClose input inputClose

theorem realFunctionLimitAt_eventually_inv_abs_upper
    {function : IncReal → IncReal} {point limit : IncReal}
    (limitNonzero : limit ≠ realZero)
    (converges : RealFunctionLimitAt function point limit) :
    ∃ bound : IncRational,
      rationalLT (rationalOfInteger 0) bound ∧
      ∃ radius : IncRational,
        rationalLT (rationalOfInteger 0) radius ∧
        ∀ input, realLE (realDist input point).value
            (rationalToReal radius) →
          ∃ inputNonzero : function input ≠ realZero,
            realLE (realAbs (realInv (function input) inputNonzero)).value
              (rationalToReal bound) := by
  have absoluteNonzero : (realAbs limit).value ≠ realZero := by
    intro absoluteZero
    exact limitNonzero ((realAbs_eq_zero_iff limit).mp absoluteZero)
  obtain ⟨inside, insideMember, insidePositive⟩ :=
    (realAbs limit).exists_positive_member absoluteNonzero
  obtain ⟨lower, lowerPositive, lowerAdd⟩ :=
    rational_exists_positive_half insidePositive
  obtain ⟨inputRadius, inputRadiusPositive, eventuallyClose⟩ :=
    converges lower lowerPositive
  have insideStrict :
      realLT (rationalToReal inside) (realAbs limit).value :=
    rationalToReal_lt_of_lower (realAbs limit).value insideMember
  have eventuallyLower : ∀ input,
      realLE (realDist input point).value (rationalToReal inputRadius) →
      realLE (rationalToReal lower) (realAbs (function input)).value := by
    intro input inputClose
    rcases realLE_total (rationalToReal lower)
        (realAbs (function input)).value with lowerBound | belowLower
    · exact lowerBound
    · exfalso
      have limitBound := realAbs_le_dist_add_abs limit (function input)
      have distanceBound : realLE (realDist limit (function input)).value
          (rationalToReal lower) := by
        rw [realDist_comm]
        exact eventuallyClose input inputClose
      have sumBound := realAdd_monotone distanceBound belowLower
      have limitBelowInside := realLE_trans limitBound sumBound
      rw [realAdd_rationalToReal, lowerAdd] at limitBelowInside
      exact insideStrict.2 (realLE_antisymm insideStrict.1 limitBelowInside)
  have lowerRealNonzero : rationalToReal lower ≠ realZero := by
    intro equal
    have injected := rationalToReal_injective equal
    rw [injected] at lowerPositive
    exact rationalLT_irrefl (rationalOfInteger 0) lowerPositive
  have lowerNonzero : lower ≠ rationalOfInteger 0 := by
    intro lowerZero
    rw [lowerZero] at lowerPositive
    exact rationalLT_irrefl (rationalOfInteger 0) lowerPositive
  obtain ⟨bound, inverseLaw⟩ :=
    rational_nonzero_has_mul_inverse lowerNonzero
  have boundPositive : rationalLT (rationalOfInteger 0) bound := by
    apply rationalMul_positive_reflect_right lowerPositive
    rw [inverseLaw]
    exact rational_zero_lt_one
  refine ⟨bound, boundPositive, inputRadius, inputRadiusPositive, ?_⟩
  intro input inputClose
  have lowerBound := eventuallyLower input inputClose
  have inputNonzero : function input ≠ realZero := by
    intro inputZero
    rw [inputZero, realAbs_zero] at lowerBound
    have lowerNonpositive := realLE_trans lowerBound nonnegativeZero.nonnegative
    have positiveOrder : realLT realZero (rationalToReal lower) :=
      ⟨(rationalToReal_le_iff _ _).mpr lowerPositive.1,
        fun equal => lowerRealNonzero equal.symm⟩
    exact positiveOrder.2
      (realLE_antisymm positiveOrder.1 lowerNonpositive)
  refine ⟨inputNonzero, ?_⟩
  rw [realAbs_inv_eq_nonnegativeRealInv]
  let lowerReal : NonnegativeReal :=
    { value := rationalToReal lower
      nonnegative := (rationalToReal_le_iff _ _).mpr lowerPositive.1 }
  have reversed := nonnegativeRealInv_order_reverse
    (left := lowerReal) (right := realAbs (function input))
    lowerRealNonzero
    (by
      intro absoluteZero
      exact inputNonzero
        ((realAbs_eq_zero_iff (function input)).mp absoluteZero)) lowerBound
  rw [nonnegativeRealInv_rationalToReal_positive
    lowerPositive lowerRealNonzero inverseLaw] at reversed
  exact reversed

theorem realFunctionLimitAt_invOrZero
    {function : IncReal → IncReal} {point limit : IncReal}
    (limitNonzero : limit ≠ realZero)
    (converges : RealFunctionLimitAt function point limit) :
    RealFunctionLimitAt (fun input => realInvOrZero (function input))
      point (realInvOrZero limit) := by
  obtain ⟨tailBound, tailBoundPositive, tailRadius, tailRadiusPositive,
      tailEventually⟩ :=
    realFunctionLimitAt_eventually_inv_abs_upper limitNonzero converges
  obtain ⟨limitBound, limitBoundNotMember, limitBoundPositive⟩ :=
    (realAbs (realInv limit limitNonzero)).positive_upper
  have limitAbsoluteBound :
      realLE (realAbs (realInv limit limitNonzero)).value
        (rationalToReal limitBound) := by
    intro rational member
    exact (realAbs (realInv limit limitNonzero)).value.lt_of_lower_of_not_lower
      member limitBoundNotMember
  let productBound := rationalMul tailBound limitBound
  have productBoundPositive :
      rationalLT (rationalOfInteger 0) productBound :=
    rationalMul_positive tailBoundPositive limitBoundPositive
  have productBoundNonzero : productBound ≠ rationalOfInteger 0 := by
    intro equal
    rw [equal] at productBoundPositive
    exact rationalLT_irrefl _ productBoundPositive
  obtain ⟨productBoundInverse, productBoundInverseLaw⟩ :=
    rational_nonzero_has_mul_inverse productBoundNonzero
  have productBoundInversePositive :
      rationalLT (rationalOfInteger 0) productBoundInverse := by
    apply rationalMul_positive_reflect_right productBoundPositive
    rw [productBoundInverseLaw]
    exact rational_zero_lt_one
  intro epsilon epsilonPositive
  let outputRadius := rationalMul epsilon productBoundInverse
  have outputRadiusPositive : rationalLT (rationalOfInteger 0) outputRadius :=
    rationalMul_positive epsilonPositive productBoundInversePositive
  have productOutputRadius :
      rationalMul productBound outputRadius = epsilon := by
    calc
      _ = rationalMul epsilon
          (rationalMul productBound productBoundInverse) := by
            rw [← rationalMul_assoc productBound epsilon productBoundInverse,
              rationalMul_comm productBound epsilon,
              rationalMul_assoc epsilon productBound productBoundInverse]
      _ = rationalMul epsilon (rationalOfInteger 1) := by
            rw [productBoundInverseLaw]
      _ = epsilon := rationalMul_one_right epsilon
  obtain ⟨closeRadius, closeRadiusPositive, eventuallyClose⟩ :=
    converges outputRadius outputRadiusPositive
  let tailBoundReal : NonnegativeReal :=
    { value := rationalToReal tailBound
      nonnegative := (rationalToReal_le_iff _ _).mpr tailBoundPositive.1 }
  let limitBoundReal : NonnegativeReal :=
    { value := rationalToReal limitBound
      nonnegative := (rationalToReal_le_iff _ _).mpr limitBoundPositive.1 }
  let outputRadiusReal : NonnegativeReal :=
    { value := rationalToReal outputRadius
      nonnegative :=
        (rationalToReal_le_iff _ _).mpr outputRadiusPositive.1 }
  let productBoundReal : NonnegativeReal :=
    { value := rationalToReal productBound
      nonnegative :=
        (rationalToReal_le_iff _ _).mpr productBoundPositive.1 }
  have finish : ∀ radius : IncRational,
      rationalLT (rationalOfInteger 0) radius →
      rationalLE radius tailRadius → rationalLE radius closeRadius →
      ∃ delta : IncRational,
        rationalLT (rationalOfInteger 0) delta ∧
        ∀ input, realLE (realDist input point).value
            (rationalToReal delta) →
          realLE
            (realDist (realInvOrZero (function input))
              (realInvOrZero limit)).value
            (rationalToReal epsilon) := by
    intro radius radiusPositive radiusTail radiusClose
    refine ⟨radius, radiusPositive, ?_⟩
    intro input inputClose
    have tailInputClose : realLE (realDist input point).value
        (rationalToReal tailRadius) :=
      realLE_trans inputClose ((rationalToReal_le_iff _ _).mpr radiusTail)
    have closeInputClose : realLE (realDist input point).value
        (rationalToReal closeRadius) :=
      realLE_trans inputClose ((rationalToReal_le_iff _ _).mpr radiusClose)
    obtain ⟨inputNonzero, inputInverseBound⟩ :=
      tailEventually input tailInputClose
    rw [realInvOrZero_of_ne (function input) inputNonzero,
      realInvOrZero_of_ne limit limitNonzero,
      realDist_inv (function input) limit inputNonzero limitNonzero]
    have inverseProductBound := nonnegativeRealMul_monotone
      (left := realAbs (realInv (function input) inputNonzero))
      (left' := tailBoundReal)
      (right := realAbs (realInv limit limitNonzero))
      (right' := limitBoundReal)
      inputInverseBound limitAbsoluteBound
    have totalBound := nonnegativeRealMul_monotone
      (left := nonnegativeRealMul
        (realAbs (realInv (function input) inputNonzero))
        (realAbs (realInv limit limitNonzero)))
      (left' := nonnegativeRealMul tailBoundReal limitBoundReal)
      (right := realDist (function input) limit)
      (right' := outputRadiusReal)
      inverseProductBound (eventuallyClose input closeInputClose)
    have firstPrincipal := nonnegativeRealMul_rationalToReal_positive
      tailBoundPositive limitBoundPositive
    have secondPrincipal := nonnegativeRealMul_rationalToReal_positive
      productBoundPositive outputRadiusPositive
    have firstBundle :
        nonnegativeRealMul tailBoundReal limitBoundReal =
          productBoundReal := by
      apply NonnegativeReal.ext
      exact firstPrincipal
    have secondBundle :
        nonnegativeRealMul productBoundReal outputRadiusReal =
          { value := rationalToReal
              (rationalMul productBound outputRadius)
            nonnegative := (rationalToReal_le_iff _ _).mpr
              (rationalMul_positive productBoundPositive
                outputRadiusPositive).1 } := by
      apply NonnegativeReal.ext
      exact secondPrincipal
    rw [firstBundle, secondBundle] at totalBound
    change realLE
      (nonnegativeRealMul
        (nonnegativeRealMul
          (realAbs (realInv (function input) inputNonzero))
          (realAbs (realInv limit limitNonzero)))
        (realDist (function input) limit)).value
      (rationalToReal (rationalMul productBound outputRadius)) at totalBound
    rw [productOutputRadius] at totalBound
    exact totalBound
  rcases rationalLE_total tailRadius closeRadius with ordered | reverse
  · exact finish tailRadius tailRadiusPositive (rationalLE_refl _)
      ordered
  · exact finish closeRadius closeRadiusPositive reverse
      (rationalLE_refl _)

theorem realFunctionLimitAt_div
    {numerator denominator : IncReal → IncReal}
    {point numeratorLimit denominatorLimit : IncReal}
    (denominatorLimitNonzero : denominatorLimit ≠ realZero)
    (numeratorConverges :
      RealFunctionLimitAt numerator point numeratorLimit)
    (denominatorConverges :
      RealFunctionLimitAt denominator point denominatorLimit) :
    RealFunctionLimitAt
      (fun input => realDiv (numerator input) (denominator input))
      point (realDiv numeratorLimit denominatorLimit) := by
  exact realFunctionLimitAt_mul numeratorConverges
    (realFunctionLimitAt_invOrZero denominatorLimitNonzero
      denominatorConverges)

noncomputable def realDifferenceQuotient
    (function : IncReal → IncReal) (point derivative increment : IncReal) : IncReal :=
  if increment = realZero then derivative
  else realDiv
    (realAdd (function (realAdd point increment)) (realNeg (function point)))
    increment

theorem realMul_differenceQuotient
    (function : IncReal → IncReal) (point derivative increment : IncReal) :
    realMul increment
        (realDifferenceQuotient function point derivative increment) =
      realAdd (function (realAdd point increment))
        (realNeg (function point)) := by
  classical
  by_cases incrementZero : increment = realZero
  · subst increment
    rw [realDifferenceQuotient, if_pos rfl, realMul_zero_left,
      realAdd_zero_right, realAdd_neg]
  · rw [realDifferenceQuotient, if_neg incrementZero, realDiv,
      realInvOrZero_of_ne increment incrementZero]
    calc
      realMul increment
          (realMul
            (realAdd (function (realAdd point increment))
              (realNeg (function point)))
            (realInv increment incrementZero)) =
        realMul
          (realAdd (function (realAdd point increment))
            (realNeg (function point)))
          (realMul increment (realInv increment incrementZero)) := by
            rw [← realMul_assoc,
              realMul_comm increment
                (realAdd (function (realAdd point increment))
                  (realNeg (function point))),
              realMul_assoc]
      _ = realAdd (function (realAdd point increment))
          (realNeg (function point)) := by
            rw [realMul_inv, realMul_one_right]

def RealHasDerivativeAt
    (function : IncReal → IncReal) (derivative point : IncReal) : Prop :=
  RealFunctionLimitAt
    (realDifferenceQuotient function point derivative) realZero derivative

theorem realHasDerivativeAt_unique
    {function : IncReal → IncReal}
    {firstDerivative secondDerivative point : IncReal}
    (first : RealHasDerivativeAt function firstDerivative point)
    (second : RealHasDerivativeAt function secondDerivative point) :
    firstDerivative = secondDerivative := by
  apply realFunctionLimitAt_unique_of_eq_ne_zero
    (firstConverges := first) (secondConverges := second)
  intro increment incrementNonzero
  simp only [realDifferenceQuotient, if_neg incrementNonzero]

def RealDifferentiableAt (function : IncReal → IncReal) (point : IncReal) : Prop :=
  ∃ derivative, RealHasDerivativeAt function derivative point

def RealDifferentiable (function : IncReal → IncReal) : Prop :=
  ∀ point, RealDifferentiableAt function point

noncomputable def realDerivativeAt
    (function : IncReal → IncReal) (point : IncReal)
    (differentiable : RealDifferentiableAt function point) : IncReal :=
  Classical.choose differentiable

theorem realDerivativeAt_spec
    (function : IncReal → IncReal) (point : IncReal)
    (differentiable : RealDifferentiableAt function point) :
    RealHasDerivativeAt function
      (realDerivativeAt function point differentiable) point :=
  Classical.choose_spec differentiable

theorem realDerivativeAt_eq
    {function : IncReal → IncReal} {point derivative : IncReal}
    (differentiable : RealDifferentiableAt function point)
    (hasDerivative : RealHasDerivativeAt function derivative point) :
    realDerivativeAt function point differentiable = derivative :=
  realHasDerivativeAt_unique
    (realDerivativeAt_spec function point differentiable) hasDerivative

noncomputable def realDerivative
    (function : IncReal → IncReal) (differentiable : RealDifferentiable function) :
    IncReal → IncReal :=
  fun point => realDerivativeAt function point (differentiable point)

theorem realDerivative_spec
    (function : IncReal → IncReal) (differentiable : RealDifferentiable function)
    (point : IncReal) :
    RealHasDerivativeAt function (realDerivative function differentiable point)
      point :=
  realDerivativeAt_spec function point (differentiable point)

theorem realDerivative_eq
    {function derivative : IncReal → IncReal}
    (differentiable : RealDifferentiable function)
    (hasDerivative : ∀ point,
      RealHasDerivativeAt function (derivative point) point) :
    realDerivative function differentiable = derivative := by
  funext point
  exact realHasDerivativeAt_unique
    (realDerivative_spec function differentiable point)
    (hasDerivative point)

theorem realHasDerivativeAt_continuousAt
    {function : IncReal → IncReal} {derivative point : IncReal}
    (differentiable : RealHasDerivativeAt function derivative point) :
    RealContinuousAt function point := by
  have incrementLimit : RealFunctionLimitAt (fun increment => increment)
      realZero realZero := realFunctionLimitAt_id realZero
  have productLimit : RealFunctionLimitAt
      (fun increment => realMul increment
        (realDifferenceQuotient function point derivative increment))
      realZero realZero :=
    by simpa [realMul_zero_left] using
      (realFunctionLimitAt_mul incrementLimit differentiable)
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    productLimit epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro input inputClose
  let increment := realAdd input (realNeg point)
  have incrementClose : realLE (realDist increment realZero).value
      (rationalToReal delta) := by
    rw [realDist_zero_right]
    change realLE (realAbs (realAdd input (realNeg point))).value
      (rationalToReal delta)
    simpa [realDist] using inputClose
  have productClose := eventuallyClose increment incrementClose
  have restore : realAdd point increment = input := by
    dsimp only [increment]
    calc
      realAdd point (realAdd input (realNeg point)) =
          realAdd input (realAdd point (realNeg point)) := by
            rw [← realAdd_assoc, realAdd_comm point input, realAdd_assoc]
      _ = input := by rw [realAdd_neg, realAdd_zero_right]
  change realLE (realDist (function input) (function point)).value
    (rationalToReal epsilon)
  rw [← restore]
  have reconstructed :=
    realMul_differenceQuotient function point derivative increment
  rw [realDist, ← reconstructed]
  simpa [realDist_zero_right] using productClose

theorem realContinuousAt_shift
    {function : IncReal → IncReal} {point : IncReal}
    (continuous : RealContinuousAt function point) :
    RealFunctionLimitAt (fun increment => function (realAdd point increment))
      realZero (function point) := by
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    continuous epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro increment incrementClose
  apply eventuallyClose
  have translated :
      realAdd (realAdd point increment) (realNeg point) = increment := by
    calc
      realAdd (realAdd point increment) (realNeg point) =
          realAdd increment (realAdd point (realNeg point)) := by
            rw [realAdd_comm point increment, realAdd_assoc]
      _ = increment := by rw [realAdd_neg, realAdd_zero_right]
  rw [realDist, translated]
  rw [realDist_zero_right] at incrementClose
  exact incrementClose

theorem realHasDerivativeAt_shift_limit
    {function : IncReal → IncReal} {derivative point : IncReal}
    (differentiable : RealHasDerivativeAt function derivative point) :
    RealFunctionLimitAt (fun increment => function (realAdd point increment))
      realZero (function point) :=
  realContinuousAt_shift (realHasDerivativeAt_continuousAt differentiable)

theorem realDifferenceQuotient_const
    (constant derivative point increment : IncReal)
    (derivativeZero : derivative = realZero) :
    realDifferenceQuotient (fun _ => constant) point derivative increment =
      realZero := by
  classical
  by_cases incrementZero : increment = realZero
  · rw [realDifferenceQuotient, if_pos incrementZero, derivativeZero]
  · rw [realDifferenceQuotient, if_neg incrementZero,
      realAdd_neg, realDiv, realMul_zero_left]

theorem realHasDerivativeAt_const (constant point : IncReal) :
    RealHasDerivativeAt (fun _ => constant) realZero point := by
  intro epsilon epsilonPositive
  refine ⟨epsilon, epsilonPositive, ?_⟩
  intro increment _
  rw [realDifferenceQuotient_const constant realZero point increment rfl,
    realDist_self]
  exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realDifferenceQuotient_id (point increment : IncReal) :
    realDifferenceQuotient (fun value => value) point realOne increment =
      realOne := by
  classical
  by_cases incrementZero : increment = realZero
  · rw [realDifferenceQuotient, if_pos incrementZero]
  · rw [realDifferenceQuotient, if_neg incrementZero]
    have numerator : realAdd (realAdd point increment) (realNeg point) =
        increment := by
      calc
        _ = realAdd increment (realAdd point (realNeg point)) := by
          rw [realAdd_comm point increment, realAdd_assoc]
        _ = increment := by rw [realAdd_neg, realAdd_zero_right]
    rw [numerator, realDiv, realInvOrZero_of_ne increment incrementZero,
      realMul_inv]

theorem realHasDerivativeAt_id (point : IncReal) :
    RealHasDerivativeAt (fun value => value) realOne point := by
  intro epsilon epsilonPositive
  refine ⟨epsilon, epsilonPositive, ?_⟩
  intro increment _
  rw [realDifferenceQuotient_id, realDist_self]
  exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realDifferenceQuotient_mul_left
    (factor point increment : IncReal) :
    realDifferenceQuotient (fun value => realMul factor value)
      point factor increment = factor := by
  classical
  by_cases incrementZero : increment = realZero
  · rw [realDifferenceQuotient, if_pos incrementZero]
  · rw [realDifferenceQuotient, if_neg incrementZero]
    have numerator : realAdd
        (realMul factor (realAdd point increment))
        (realNeg (realMul factor point)) = realMul factor increment := by
      rw [realMul_add]
      calc
        realAdd
            (realAdd (realMul factor point) (realMul factor increment))
            (realNeg (realMul factor point)) =
          realAdd (realMul factor increment)
            (realAdd (realMul factor point)
              (realNeg (realMul factor point))) := by
                rw [realAdd_comm (realMul factor point)
                  (realMul factor increment), realAdd_assoc]
        _ = realMul factor increment := by
              rw [realAdd_neg, realAdd_zero_right]
    rw [numerator, realDiv, realInvOrZero_of_ne increment incrementZero,
      realMul_assoc, realMul_inv, realMul_one_right]

theorem realHasDerivativeAt_mul_left (factor point : IncReal) :
    RealHasDerivativeAt (fun value => realMul factor value) factor point := by
  intro epsilon epsilonPositive
  refine ⟨epsilon, epsilonPositive, ?_⟩
  intro increment _
  rw [realDifferenceQuotient_mul_left, realDist_self]
  exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realAdd_sub_add_cancel_right
    (left right offset : IncReal) :
    realAdd (realAdd left offset) (realNeg (realAdd right offset)) =
      realAdd left (realNeg right) := by
  rw [realNeg_add]
  calc
    realAdd (realAdd left offset)
        (realAdd (realNeg right) (realNeg offset)) =
      realAdd left
        (realAdd offset (realAdd (realNeg right) (realNeg offset))) :=
          realAdd_assoc _ _ _
    _ = realAdd left
        (realAdd (realNeg right)
          (realAdd offset (realNeg offset))) := by
            apply congrArg (realAdd left)
            rw [← realAdd_assoc, realAdd_comm offset (realNeg right),
              realAdd_assoc]
    _ = realAdd left (realNeg right) := by
          rw [realAdd_neg, realAdd_zero_right]

theorem realDifferenceQuotient_affine
    (factor offset point increment : IncReal) :
    realDifferenceQuotient
      (fun value => realAdd (realMul factor value) offset)
      point factor increment = factor := by
  classical
  by_cases incrementZero : increment = realZero
  · rw [realDifferenceQuotient, if_pos incrementZero]
  · rw [realDifferenceQuotient, if_neg incrementZero,
      realAdd_sub_add_cancel_right]
    have scalarQuotient := realDifferenceQuotient_mul_left
      factor point increment
    rw [realDifferenceQuotient, if_neg incrementZero] at scalarQuotient
    exact scalarQuotient

theorem realHasDerivativeAt_affine
    (factor offset point : IncReal) :
    RealHasDerivativeAt
      (fun value => realAdd (realMul factor value) offset) factor point := by
  intro epsilon epsilonPositive
  refine ⟨epsilon, epsilonPositive, ?_⟩
  intro increment _
  rw [realDifferenceQuotient_affine, realDist_self]
  exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realAdd_sub_add_distribute
    (leftNow rightNow leftThen rightThen : IncReal) :
    realAdd (realAdd leftThen rightThen)
        (realNeg (realAdd leftNow rightNow)) =
      realAdd (realAdd leftThen (realNeg leftNow))
        (realAdd rightThen (realNeg rightNow)) := by
  rw [realNeg_add]
  calc
    realAdd (realAdd leftThen rightThen)
        (realAdd (realNeg leftNow) (realNeg rightNow)) =
      realAdd leftThen
        (realAdd rightThen
          (realAdd (realNeg leftNow) (realNeg rightNow))) :=
        realAdd_assoc _ _ _
    _ = realAdd leftThen
        (realAdd (realNeg leftNow)
          (realAdd rightThen (realNeg rightNow))) := by
            apply congrArg (realAdd leftThen)
            rw [← realAdd_assoc, realAdd_comm rightThen (realNeg leftNow),
              realAdd_assoc]
    _ = realAdd (realAdd leftThen (realNeg leftNow))
        (realAdd rightThen (realNeg rightNow)) :=
      (realAdd_assoc _ _ _).symm

theorem realDifferenceQuotient_add
    (left right : IncReal → IncReal)
    (leftDerivative rightDerivative point increment : IncReal) :
    realDifferenceQuotient (fun value => realAdd (left value) (right value))
        point (realAdd leftDerivative rightDerivative) increment =
      realAdd (realDifferenceQuotient left point leftDerivative increment)
        (realDifferenceQuotient right point rightDerivative increment) := by
  classical
  by_cases incrementZero : increment = realZero
  · simp only [realDifferenceQuotient, if_pos incrementZero]
  · simp only [realDifferenceQuotient, if_neg incrementZero]
    rw [realAdd_sub_add_distribute]
    rw [realDiv, realDiv, realDiv, realAdd_mul]

theorem realHasDerivativeAt_add
    {left right : IncReal → IncReal}
    {leftDerivative rightDerivative point : IncReal}
    (leftDifferentiable : RealHasDerivativeAt left leftDerivative point)
    (rightDifferentiable : RealHasDerivativeAt right rightDerivative point) :
    RealHasDerivativeAt (fun value => realAdd (left value) (right value))
      (realAdd leftDerivative rightDerivative) point := by
  have added := realFunctionLimitAt_add leftDifferentiable rightDifferentiable
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    added epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro increment incrementClose
  rw [realDifferenceQuotient_add]
  exact eventuallyClose increment incrementClose

theorem realDifferenceQuotient_neg
    (function : IncReal → IncReal) (derivative point increment : IncReal) :
    realDifferenceQuotient (fun value => realNeg (function value))
        point (realNeg derivative) increment =
      realNeg (realDifferenceQuotient function point derivative increment) := by
  classical
  by_cases incrementZero : increment = realZero
  · simp only [realDifferenceQuotient, if_pos incrementZero]
  · simp only [realDifferenceQuotient, if_neg incrementZero]
    have numeratorNeg : realAdd
        (realNeg (function (realAdd point increment)))
        (realNeg (realNeg (function point))) =
      realNeg (realAdd (function (realAdd point increment))
        (realNeg (function point))) := by
      rw [realNeg_neg, realNeg_add, realNeg_neg]
    rw [numeratorNeg, realDiv, realDiv, realMul_neg_left]

theorem realHasDerivativeAt_neg
    {function : IncReal → IncReal} {derivative point : IncReal}
    (differentiable : RealHasDerivativeAt function derivative point) :
    RealHasDerivativeAt (fun value => realNeg (function value))
      (realNeg derivative) point := by
  have negated := realFunctionLimitAt_neg differentiable
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    negated epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro increment incrementClose
  rw [realDifferenceQuotient_neg]
  exact eventuallyClose increment incrementClose

theorem realHasDerivativeAt_sub
    {left right : IncReal → IncReal}
    {leftDerivative rightDerivative point : IncReal}
    (leftDifferentiable : RealHasDerivativeAt left leftDerivative point)
    (rightDifferentiable : RealHasDerivativeAt right rightDerivative point) :
    RealHasDerivativeAt
      (fun value => realAdd (left value) (realNeg (right value)))
      (realAdd leftDerivative (realNeg rightDerivative)) point :=
  realHasDerivativeAt_add leftDifferentiable
    (realHasDerivativeAt_neg rightDifferentiable)

theorem realDifferenceQuotient_mul_const
    (factor : IncReal) (function : IncReal → IncReal)
    (derivative point increment : IncReal) :
    realDifferenceQuotient (fun value => realMul factor (function value))
        point (realMul factor derivative) increment =
      realMul factor (realDifferenceQuotient function point derivative increment) := by
  classical
  by_cases incrementZero : increment = realZero
  · simp only [realDifferenceQuotient, if_pos incrementZero]
  · simp only [realDifferenceQuotient, if_neg incrementZero]
    have numerator : realAdd
        (realMul factor (function (realAdd point increment)))
        (realNeg (realMul factor (function point))) =
      realMul factor
        (realAdd (function (realAdd point increment))
          (realNeg (function point))) := by
      rw [← realMul_neg_right, realMul_add]
    rw [numerator, realDiv, realDiv, realMul_assoc]

theorem realHasDerivativeAt_mul_const
    (factor : IncReal)
    {function : IncReal → IncReal} {derivative point : IncReal}
    (differentiable : RealHasDerivativeAt function derivative point) :
    RealHasDerivativeAt (fun value => realMul factor (function value))
      (realMul factor derivative) point := by
  have scaled := realFunctionLimitAt_mul_const factor differentiable
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    scaled epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro increment incrementClose
  rw [realDifferenceQuotient_mul_const]
  exact eventuallyClose increment incrementClose

theorem realMul_sub_mul_decompose
    (leftThen leftNow rightThen rightNow : IncReal) :
    realAdd (realMul leftThen rightThen)
        (realNeg (realMul leftNow rightNow)) =
      realAdd
        (realMul (realAdd leftThen (realNeg leftNow)) rightThen)
        (realMul leftNow (realAdd rightThen (realNeg rightNow))) := by
  rw [realAdd_mul, realMul_add, realMul_neg_left, realMul_neg_right]
  rw [realAdd_assoc
      (realMul leftThen rightThen)
      (realNeg (realMul leftNow rightThen))
      (realAdd (realMul leftNow rightThen)
        (realNeg (realMul leftNow rightNow))),
    ← realAdd_assoc
      (realNeg (realMul leftNow rightThen))
      (realMul leftNow rightThen)
      (realNeg (realMul leftNow rightNow)),
    realAdd_neg_left, realAdd_zero_left]

theorem realDifferenceQuotient_mul
    (left right : IncReal → IncReal)
    (leftDerivative rightDerivative point increment : IncReal) :
    realDifferenceQuotient (fun value => realMul (left value) (right value))
        point
        (realAdd (realMul leftDerivative (right point))
          (realMul (left point) rightDerivative)) increment =
      realAdd
        (realMul (realDifferenceQuotient left point leftDerivative increment)
          (right (realAdd point increment)))
        (realMul (left point)
          (realDifferenceQuotient right point rightDerivative increment)) := by
  classical
  by_cases incrementZero : increment = realZero
  · subst increment
    simp only [realDifferenceQuotient]
    simp only [if_true, realAdd_zero_right]
  · simp only [realDifferenceQuotient, if_neg incrementZero]
    rw [realMul_sub_mul_decompose]
    rw [realDiv, realDiv, realDiv, realAdd_mul,
      ← realMul_assoc]
    congr 1
    calc
      realMul
          (realMul
            (realAdd (left (realAdd point increment)) (realNeg (left point)))
            (right (realAdd point increment)))
          (realInvOrZero increment) =
        realMul
          (realAdd (left (realAdd point increment)) (realNeg (left point)))
          (realMul (right (realAdd point increment))
            (realInvOrZero increment)) := realMul_assoc _ _ _
      _ =
        realMul
          (realAdd (left (realAdd point increment)) (realNeg (left point)))
          (realMul (realInvOrZero increment)
            (right (realAdd point increment))) := by
              apply congrArg (realMul
                (realAdd (left (realAdd point increment))
                  (realNeg (left point))))
              exact realMul_comm _ _
      _ = realMul
          (realMul
            (realAdd (left (realAdd point increment)) (realNeg (left point)))
            (realInvOrZero increment))
          (right (realAdd point increment)) :=
            (realMul_assoc _ _ _).symm

theorem realHasDerivativeAt_mul
    {left right : IncReal → IncReal}
    {leftDerivative rightDerivative point : IncReal}
    (leftDifferentiable : RealHasDerivativeAt left leftDerivative point)
    (rightDifferentiable : RealHasDerivativeAt right rightDerivative point) :
    RealHasDerivativeAt (fun value => realMul (left value) (right value))
      (realAdd (realMul leftDerivative (right point))
        (realMul (left point) rightDerivative)) point := by
  have rightShiftLimit :=
    realHasDerivativeAt_shift_limit rightDifferentiable
  have firstTermLimit :=
    realFunctionLimitAt_mul leftDifferentiable rightShiftLimit
  have secondTermLimit :=
    realFunctionLimitAt_mul_const (left point) rightDifferentiable
  have sumLimit := realFunctionLimitAt_add firstTermLimit secondTermLimit
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    sumLimit epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro increment incrementClose
  rw [realDifferenceQuotient_mul]
  exact eventuallyClose increment incrementClose

theorem realDifferenceQuotient_comp
    (outer inner : IncReal → IncReal)
    (outerDerivative innerDerivative point increment : IncReal) :
    realDifferenceQuotient (fun value => outer (inner value)) point
        (realMul outerDerivative innerDerivative) increment =
      realMul
        (realDifferenceQuotient outer (inner point) outerDerivative
          (realAdd (inner (realAdd point increment))
            (realNeg (inner point))))
        (realDifferenceQuotient inner point innerDerivative increment) := by
  classical
  by_cases incrementZero : increment = realZero
  · subst increment
    simp only [realDifferenceQuotient, if_true, realAdd_zero_right]
    rw [realAdd_neg, if_pos rfl]
  · let innerIncrement := realAdd (inner (realAdd point increment))
      (realNeg (inner point))
    by_cases innerIncrementZero : innerIncrement = realZero
    · have innerValuesEqual : inner (realAdd point increment) = inner point :=
        real_eq_of_add_neg_eq_zero innerIncrementZero
      simp only [realDifferenceQuotient, if_neg incrementZero]
      rw [innerValuesEqual, realAdd_neg, realDiv, realMul_zero_left]
      rw [realAdd_neg, if_pos rfl, realDiv, realMul_zero_left,
        realMul_zero_right]
    · have innerRestore :
          realAdd (inner point) innerIncrement =
            inner (realAdd point increment) := by
        dsimp only [innerIncrement]
        calc
          realAdd (inner point)
              (realAdd (inner (realAdd point increment))
                (realNeg (inner point))) =
            realAdd (inner (realAdd point increment))
              (realAdd (inner point) (realNeg (inner point))) := by
                rw [← realAdd_assoc,
                  realAdd_comm (inner point)
                    (inner (realAdd point increment)),
                  realAdd_assoc]
          _ = inner (realAdd point increment) := by
                rw [realAdd_neg, realAdd_zero_right]
      simp only [realDifferenceQuotient, if_neg incrementZero]
      rw [show realAdd (inner (realAdd point increment))
          (realNeg (inner point)) = innerIncrement from rfl,
        if_neg innerIncrementZero, innerRestore]
      rw [realDiv, realDiv, realDiv]
      calc
        realMul
            (realAdd (outer (inner (realAdd point increment)))
              (realNeg (outer (inner point))))
            (realInvOrZero increment) =
          realMul
            (realMul
              (realAdd (outer (inner (realAdd point increment)))
                (realNeg (outer (inner point))))
              (realInvOrZero innerIncrement))
            (realMul innerIncrement (realInvOrZero increment)) := by
              rw [realInvOrZero_of_ne innerIncrement innerIncrementZero]
              rw [← realMul_assoc
                  (realMul
                    (realAdd (outer (inner (realAdd point increment)))
                      (realNeg (outer (inner point))))
                    (realInv innerIncrement innerIncrementZero))
                  innerIncrement (realInvOrZero increment),
                realMul_assoc
                  (realAdd (outer (inner (realAdd point increment)))
                    (realNeg (outer (inner point))))
                  (realInv innerIncrement innerIncrementZero)
                  innerIncrement,
                realInv_mul, realMul_one_right]
        _ = realMul
            (realDiv
              (realAdd (outer (inner (realAdd point increment)))
                (realNeg (outer (inner point)))) innerIncrement)
            (realDiv innerIncrement increment) := rfl

theorem realHasDerivativeAt_comp
    {outer inner : IncReal → IncReal}
    {outerDerivative innerDerivative point : IncReal}
    (innerDifferentiable :
      RealHasDerivativeAt inner innerDerivative point)
    (outerDifferentiable :
      RealHasDerivativeAt outer outerDerivative (inner point)) :
    RealHasDerivativeAt (fun value => outer (inner value))
      (realMul outerDerivative innerDerivative) point := by
  let innerIncrement : IncReal → IncReal := fun increment =>
    realAdd (inner (realAdd point increment)) (realNeg (inner point))
  have innerIncrementPointwise : ∀ increment,
      innerIncrement increment =
        realMul increment
          (realDifferenceQuotient inner point innerDerivative increment) := by
    intro increment
    exact (realMul_differenceQuotient inner point innerDerivative increment).symm
  have innerIncrementLimit :
      RealFunctionLimitAt innerIncrement realZero realZero := by
    have productLimit := realFunctionLimitAt_mul
      (realFunctionLimitAt_id realZero) innerDifferentiable
    intro epsilon epsilonPositive
    obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
      productLimit epsilon epsilonPositive
    refine ⟨delta, deltaPositive, ?_⟩
    intro increment incrementClose
    rw [innerIncrementPointwise]
    simpa [realMul_zero_left] using eventuallyClose increment incrementClose
  have outerQuotientLimit : RealFunctionLimitAt
      (fun increment => realDifferenceQuotient outer (inner point)
        outerDerivative (innerIncrement increment))
      realZero outerDerivative :=
    realFunctionLimitAt_comp innerIncrementLimit outerDifferentiable
  have productLimit :=
    realFunctionLimitAt_mul outerQuotientLimit innerDifferentiable
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, eventuallyClose⟩ :=
    productLimit epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro increment incrementClose
  rw [realDifferenceQuotient_comp]
  exact eventuallyClose increment incrementClose

theorem realDifferenceQuotient_invOrZero_of_ne
    (point increment : IncReal)
    (pointNonzero : point ≠ realZero)
    (shiftedNonzero : realAdd point increment ≠ realZero) :
    realDifferenceQuotient realInvOrZero point
        (realNeg (realMul (realInvOrZero point) (realInvOrZero point)))
        increment =
      realNeg (realMul (realInvOrZero (realAdd point increment))
        (realInvOrZero point)) := by
  classical
  by_cases incrementZero : increment = realZero
  · subst increment
    simp only [realDifferenceQuotient, if_true, realAdd_zero_right]
  · rw [realDifferenceQuotient, if_neg incrementZero,
      realInvOrZero_of_ne point pointNonzero,
      realInvOrZero_of_ne (realAdd point increment) shiftedNonzero,
      realInv_sub_realInv]
    have reversedIncrement :
        realAdd point (realNeg (realAdd point increment)) =
          realNeg increment := by
      rw [realNeg_add]
      calc
        realAdd point (realAdd (realNeg point) (realNeg increment)) =
          realAdd (realAdd point (realNeg point)) (realNeg increment) :=
            (realAdd_assoc _ _ _).symm
        _ = realNeg increment := by rw [realAdd_neg, realAdd_zero_left]
    rw [reversedIncrement, realDiv, realMul_neg_right]
    calc
      realMul
          (realNeg
            (realMul
              (realMul
                (realInv (realAdd point increment) shiftedNonzero)
                (realInv point pointNonzero))
              increment))
          (realInvOrZero increment) =
        realNeg
          (realMul
            (realMul
              (realMul
                (realInv (realAdd point increment) shiftedNonzero)
                (realInv point pointNonzero))
              increment)
            (realInvOrZero increment)) := by rw [realMul_neg_left]
      _ = realNeg
          (realMul
            (realInv (realAdd point increment) shiftedNonzero)
            (realInv point pointNonzero)) := by
              rw [realInvOrZero_of_ne increment incrementZero,
                realMul_assoc, realMul_inv, realMul_one_right]

theorem realHasDerivativeAt_invOrZero
    (point : IncReal) (pointNonzero : point ≠ realZero) :
    RealHasDerivativeAt realInvOrZero
      (realNeg (realMul (realInvOrZero point) (realInvOrZero point)))
      point := by
  have shiftedLimit : RealFunctionLimitAt
      (fun increment => realAdd point increment) realZero point := by
    have added := realFunctionLimitAt_add
      (realFunctionLimitAt_const point realZero)
      (realFunctionLimitAt_id realZero)
    simpa [realAdd_zero_right] using added
  have inverseShiftedLimit : RealFunctionLimitAt
      (fun increment => realInvOrZero (realAdd point increment))
      realZero (realInvOrZero point) :=
    realFunctionLimitAt_invOrZero pointNonzero shiftedLimit
  have scaledLimit := realFunctionLimitAt_mul_const
    (realInvOrZero point) inverseShiftedLimit
  have negatedLimit := realFunctionLimitAt_neg scaledLimit
  have targetLimit : RealFunctionLimitAt
      (fun increment => realNeg
        (realMul (realInvOrZero (realAdd point increment))
          (realInvOrZero point)))
      realZero
      (realNeg (realMul (realInvOrZero point) (realInvOrZero point))) := by
    simpa [realMul_comm] using negatedLimit
  obtain ⟨bound, boundPositive, nonzeroRadius, nonzeroRadiusPositive,
      eventuallyNonzero⟩ :=
    realFunctionLimitAt_eventually_inv_abs_upper pointNonzero shiftedLimit
  intro epsilon epsilonPositive
  obtain ⟨limitRadius, limitRadiusPositive, eventuallyClose⟩ :=
    targetLimit epsilon epsilonPositive
  rcases rationalLE_total nonzeroRadius limitRadius with ordered | reverse
  · refine ⟨nonzeroRadius, nonzeroRadiusPositive, ?_⟩
    intro increment incrementClose
    have limitClose : realLE (realDist increment realZero).value
        (rationalToReal limitRadius) :=
      realLE_trans incrementClose ((rationalToReal_le_iff _ _).mpr ordered)
    obtain ⟨shiftedNonzero, _⟩ :=
      eventuallyNonzero increment incrementClose
    rw [realDifferenceQuotient_invOrZero_of_ne point increment
      pointNonzero shiftedNonzero]
    exact eventuallyClose increment limitClose
  · refine ⟨limitRadius, limitRadiusPositive, ?_⟩
    intro increment incrementClose
    have nonzeroClose : realLE (realDist increment realZero).value
        (rationalToReal nonzeroRadius) :=
      realLE_trans incrementClose ((rationalToReal_le_iff _ _).mpr reverse)
    obtain ⟨shiftedNonzero, _⟩ :=
      eventuallyNonzero increment nonzeroClose
    rw [realDifferenceQuotient_invOrZero_of_ne point increment
      pointNonzero shiftedNonzero]
    exact eventuallyClose increment incrementClose

theorem realHasDerivativeAt_inv_comp
    {function : IncReal → IncReal} {derivative point : IncReal}
    (valueNonzero : function point ≠ realZero)
    (differentiable : RealHasDerivativeAt function derivative point) :
    RealHasDerivativeAt (fun value => realInvOrZero (function value))
      (realMul
        (realNeg (realMul (realInvOrZero (function point))
          (realInvOrZero (function point)))) derivative) point := by
  exact realHasDerivativeAt_comp differentiable
    (realHasDerivativeAt_invOrZero (function point) valueNonzero)

theorem realHasDerivativeAt_div
    {numerator denominator : IncReal → IncReal}
    {numeratorDerivative denominatorDerivative point : IncReal}
    (denominatorValueNonzero : denominator point ≠ realZero)
    (numeratorDifferentiable :
      RealHasDerivativeAt numerator numeratorDerivative point)
    (denominatorDifferentiable :
      RealHasDerivativeAt denominator denominatorDerivative point) :
    RealHasDerivativeAt
      (fun value => realDiv (numerator value) (denominator value))
      (realAdd
        (realMul numeratorDerivative (realInvOrZero (denominator point)))
        (realMul (numerator point)
          (realMul
            (realNeg (realMul (realInvOrZero (denominator point))
              (realInvOrZero (denominator point))))
            denominatorDerivative))) point := by
  simpa only [realDiv] using
    realHasDerivativeAt_mul numeratorDifferentiable
      (realHasDerivativeAt_inv_comp denominatorValueNonzero
        denominatorDifferentiable)

noncomputable def realPow (base : IncReal) : Nat → IncReal
  | 0 => realOne
  | Nat.succ exponent => realMul (realPow base exponent) base

@[simp] theorem realPow_zero (base : IncReal) :
    realPow base 0 = realOne := rfl

@[simp] theorem realPow_succ (base : IncReal) (exponent : Nat) :
    realPow base (Nat.succ exponent) =
      realMul (realPow base exponent) base := rfl

theorem realPow_one (base : IncReal) : realPow base 1 = base := by
  rw [realPow_succ, realPow_zero, realMul_one_left]

theorem realPow_one_base (exponent : Nat) :
    realPow realOne exponent = realOne := by
  induction exponent with
  | zero => rfl
  | succ exponent induction =>
      rw [realPow_succ, induction, realMul_one_right]

theorem realPow_ne_zero
    (base : IncReal) (baseNonzero : base ≠ realZero) (exponent : Nat) :
    realPow base exponent ≠ realZero := by
  induction exponent with
  | zero => exact real_zero_ne_one.symm
  | succ exponent induction =>
      rw [realPow_succ]
      exact realMul_ne_zero induction baseNonzero

theorem realPow_add (base : IncReal) (left right : Nat) :
    realPow base (left + right) =
      realMul (realPow base left) (realPow base right) := by
  induction right with
  | zero => rw [Nat.add_zero, realPow_zero, realMul_one_right]
  | succ right induction =>
      rw [Nat.add_succ, realPow_succ, realPow_succ, induction,
        realMul_assoc]

theorem realPow_mul (base : IncReal) (left right : Nat) :
    realPow base (left * right) = realPow (realPow base left) right := by
  induction right with
  | zero => rw [Nat.mul_zero, realPow_zero, realPow_zero]
  | succ right induction =>
      rw [Nat.mul_succ, realPow_add, realPow_succ, induction]

theorem realPow_mul_base (left right : IncReal) (exponent : Nat) :
    realPow (realMul left right) exponent =
      realMul (realPow left exponent) (realPow right exponent) := by
  induction exponent with
  | zero => rw [realPow_zero, realPow_zero, realPow_zero, realMul_one_left]
  | succ exponent induction =>
      rw [realPow_succ, realPow_succ, realPow_succ, induction]
      calc
        realMul (realMul (realPow left exponent) (realPow right exponent))
            (realMul left right) =
          realMul (realMul (realPow left exponent) left)
            (realMul (realPow right exponent) right) := by
              rw [realMul_assoc,
                ← realMul_assoc (realPow right exponent) left right,
                realMul_comm (realPow right exponent) left,
                realMul_assoc left (realPow right exponent) right,
                ← realMul_assoc]
        _ = _ := rfl

theorem realPow_mul_pow_inv
    (base : IncReal) (baseNonzero : base ≠ realZero) (exponent : Nat) :
    realMul (realPow base exponent)
        (realPow (realInv base baseNonzero) exponent) = realOne := by
  rw [← realPow_mul_base, realMul_inv, realPow_one_base]

theorem realPow_inv_eq_inv_pow
    (base : IncReal) (baseNonzero : base ≠ realZero) (exponent : Nat) :
    realPow (realInv base baseNonzero) exponent =
      realInv (realPow base exponent)
        (realPow_ne_zero base baseNonzero exponent) := by
  apply realMul_cancel_left
    (realPow_ne_zero base baseNonzero exponent)
  rw [realPow_mul_pow_inv, realMul_inv]

theorem nonnegativeRealInv_ne_zero
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero) :
    (nonnegativeRealInv value nonzero).value ≠ realZero := by
  intro inverseZero
  have lawBundle := congrArg NonnegativeReal.value
    (nonnegativeRealMul_inv value nonzero)
  have law : realMul value.value
      (nonnegativeRealInv value nonzero).value = realOne := by
    rw [realMul_of_nonnegative value.value
      (nonnegativeRealInv value nonzero).value value.nonnegative
      (nonnegativeRealInv value nonzero).nonnegative]
    exact lawBundle
  rw [inverseZero, realMul_zero_right] at law
  exact real_zero_ne_one law

theorem nonnegativeRealInv_involutive
    (value : NonnegativeReal) (nonzero : value.value ≠ realZero) :
    nonnegativeRealInv (nonnegativeRealInv value nonzero)
        (nonnegativeRealInv_ne_zero value nonzero) = value := by
  apply NonnegativeReal.ext
  apply realMul_cancel_left (nonnegativeRealInv_ne_zero value nonzero)
  rw [realMul_of_nonnegative
      (nonnegativeRealInv value nonzero).value
      (nonnegativeRealInv (nonnegativeRealInv value nonzero)
        (nonnegativeRealInv_ne_zero value nonzero)).value
      (nonnegativeRealInv value nonzero).nonnegative
      (nonnegativeRealInv (nonnegativeRealInv value nonzero)
        (nonnegativeRealInv_ne_zero value nonzero)).nonnegative,
    realMul_of_nonnegative
      (nonnegativeRealInv value nonzero).value value.value
      (nonnegativeRealInv value nonzero).nonnegative value.nonnegative]
  change
    (nonnegativeRealMul (nonnegativeRealInv value nonzero)
      (nonnegativeRealInv (nonnegativeRealInv value nonzero)
        (nonnegativeRealInv_ne_zero value nonzero))).value =
    (nonnegativeRealMul (nonnegativeRealInv value nonzero) value).value
  rw [nonnegativeRealMul_inv,
    nonnegativeRealMul_comm_bundle, nonnegativeRealMul_inv]

theorem nonnegativeRealInv_one :
    nonnegativeRealInv nonnegativeOne real_zero_ne_one.symm =
      nonnegativeOne := by
  have law := nonnegativeRealMul_inv nonnegativeOne real_zero_ne_one.symm
  rw [nonnegativeRealMul_one_left_bundle] at law
  exact law

noncomputable def nonnegativeRealPow
    (base : NonnegativeReal) : Nat → NonnegativeReal
  | 0 => nonnegativeOne
  | Nat.succ exponent => nonnegativeRealMul (nonnegativeRealPow base exponent) base

def nonnegativeRealNatScale
    (count : Nat) (value : NonnegativeReal) : NonnegativeReal :=
  Nat.rec nonnegativeZero
    (fun _ accumulated => nonnegativeRealAdd accumulated value) count

@[simp] theorem nonnegativeRealNatScale_zero (value : NonnegativeReal) :
    nonnegativeRealNatScale 0 value = nonnegativeZero := rfl

theorem nonnegativeRealNatScale_succ
    (count : Nat) (value : NonnegativeReal) :
    nonnegativeRealNatScale (Nat.succ count) value =
      nonnegativeRealAdd (nonnegativeRealNatScale count value) value := rfl

noncomputable def realNatCoefficient (count : Nat) : IncReal :=
  (nonnegativeRealNatScale count nonnegativeOne).value

@[simp] theorem realNatCoefficient_zero :
    realNatCoefficient 0 = realZero := rfl

theorem realNatCoefficient_succ (count : Nat) :
    realNatCoefficient (Nat.succ count) =
      realAdd (realNatCoefficient count) realOne := by
  rw [realNatCoefficient, realNatCoefficient,
    nonnegativeRealNatScale_succ]
  rfl

noncomputable def realPowFormalDerivative (base : IncReal) : Nat → IncReal
  | 0 => realZero
  | Nat.succ exponent =>
      realAdd (realMul (realPowFormalDerivative base exponent) base)
        (realPow base exponent)

@[simp] theorem realPowFormalDerivative_zero (base : IncReal) :
    realPowFormalDerivative base 0 = realZero := rfl

@[simp] theorem realPowFormalDerivative_succ
    (base : IncReal) (exponent : Nat) :
    realPowFormalDerivative base (Nat.succ exponent) =
      realAdd (realMul (realPowFormalDerivative base exponent) base)
        (realPow base exponent) := rfl

theorem realHasDerivativeAt_pow
    (exponent : Nat) (point : IncReal) :
    RealHasDerivativeAt (fun value => realPow value exponent)
      (realPowFormalDerivative point exponent) point := by
  induction exponent with
  | zero =>
      simpa only [realPow_zero, realPowFormalDerivative_zero] using
        realHasDerivativeAt_const realOne point
  | succ exponent induction =>
      simpa only [realPow_succ, realPowFormalDerivative_succ,
        realMul_one_right] using
        realHasDerivativeAt_mul induction (realHasDerivativeAt_id point)

theorem realPowFormalDerivative_closed_succ
    (base : IncReal) (previous : Nat) :
    realPowFormalDerivative base (Nat.succ previous) =
      realMul (realNatCoefficient (Nat.succ previous))
        (realPow base previous) := by
  induction previous with
  | zero =>
      rw [realPowFormalDerivative_succ,
        realPowFormalDerivative_zero, realMul_zero_left,
        realAdd_zero_left, realPow_zero,
        realNatCoefficient_succ, realNatCoefficient_zero,
        realAdd_zero_left, realMul_one_right]
  | succ previous induction =>
      rw [realPowFormalDerivative_succ, induction,
        realPow_succ, realMul_assoc,
        realNatCoefficient_succ (Nat.succ previous), realAdd_mul,
        realMul_one_left]

theorem realPowFormalDerivative_closed
    (base : IncReal) (exponent : Nat) :
    realPowFormalDerivative base exponent =
      match exponent with
      | 0 => realZero
      | Nat.succ previous =>
          realMul (realNatCoefficient (Nat.succ previous))
            (realPow base previous) := by
  cases exponent with
  | zero => rfl
  | succ previous => exact realPowFormalDerivative_closed_succ base previous

theorem realHasDerivativeAt_pow_closed
    (exponent : Nat) (point : IncReal) :
    RealHasDerivativeAt (fun value => realPow value exponent)
      (match exponent with
       | 0 => realZero
       | Nat.succ previous =>
           realMul (realNatCoefficient (Nat.succ previous))
             (realPow point previous)) point := by
  rw [← realPowFormalDerivative_closed]
  exact realHasDerivativeAt_pow exponent point

noncomputable def realPolynomialEval : List IncReal → IncReal → IncReal
  | [], _ => realZero
  | coefficient :: coefficients, value =>
      realAdd coefficient
        (realMul value (realPolynomialEval coefficients value))

noncomputable def realPolynomialDerivativeEval :
    List IncReal → IncReal → IncReal
  | [], _ => realZero
  | _ :: coefficients, value =>
      realAdd (realPolynomialEval coefficients value)
        (realMul value (realPolynomialDerivativeEval coefficients value))

@[simp] theorem realPolynomialEval_nil (value : IncReal) :
    realPolynomialEval [] value = realZero := rfl

@[simp] theorem realPolynomialEval_cons
    (coefficient : IncReal) (coefficients : List IncReal) (value : IncReal) :
    realPolynomialEval (coefficient :: coefficients) value =
      realAdd coefficient
        (realMul value (realPolynomialEval coefficients value)) := rfl

@[simp] theorem realPolynomialDerivativeEval_nil (value : IncReal) :
    realPolynomialDerivativeEval [] value = realZero := rfl

@[simp] theorem realPolynomialDerivativeEval_cons
    (coefficient : IncReal) (coefficients : List IncReal) (value : IncReal) :
    realPolynomialDerivativeEval (coefficient :: coefficients) value =
      realAdd (realPolynomialEval coefficients value)
        (realMul value (realPolynomialDerivativeEval coefficients value)) := rfl

theorem realHasDerivativeAt_polynomial
    (coefficients : List IncReal) (point : IncReal) :
    RealHasDerivativeAt (realPolynomialEval coefficients)
      (realPolynomialDerivativeEval coefficients point) point := by
  induction coefficients with
  | nil =>
      simpa only [realPolynomialEval_nil,
        realPolynomialDerivativeEval_nil] using
        realHasDerivativeAt_const realZero point
  | cons coefficient coefficients induction =>
      have productDerivative := realHasDerivativeAt_mul
        (realHasDerivativeAt_id point) induction
      have sumDerivative := realHasDerivativeAt_add
        (realHasDerivativeAt_const coefficient point) productDerivative
      simpa only [realPolynomialEval_cons,
        realPolynomialDerivativeEval_cons, realMul_one_left,
        realMul_zero_left, realAdd_zero_left] using sumDerivative

theorem realPolynomialEval_singleton
    (coefficient value : IncReal) :
    realPolynomialEval [coefficient] value = coefficient := by
  rw [realPolynomialEval_cons, realPolynomialEval_nil,
    realMul_zero_right, realAdd_zero_right]

theorem realPolynomialDerivativeEval_singleton
    (coefficient value : IncReal) :
    realPolynomialDerivativeEval [coefficient] value = realZero := by
  rw [realPolynomialDerivativeEval_cons, realPolynomialEval_nil,
    realPolynomialDerivativeEval_nil, realMul_zero_right,
    realAdd_zero_left]

theorem realPolynomialEval_pair
    (constant linear value : IncReal) :
    realPolynomialEval [constant, linear] value =
      realAdd constant (realMul value linear) := by
  rw [realPolynomialEval_cons, realPolynomialEval_cons,
    realPolynomialEval_nil, realMul_zero_right, realAdd_zero_right]

theorem realPolynomialDerivativeEval_pair
    (constant linear value : IncReal) :
    realPolynomialDerivativeEval [constant, linear] value = linear := by
  rw [realPolynomialDerivativeEval_cons, realPolynomialEval_singleton,
    realPolynomialDerivativeEval_singleton, realMul_zero_right,
    realAdd_zero_right]

theorem realHasDerivativeAt_polynomial_pair
    (constant linear point : IncReal) :
    RealHasDerivativeAt (realPolynomialEval [constant, linear]) linear point := by
  simpa only [realPolynomialDerivativeEval_pair] using
    realHasDerivativeAt_polynomial [constant, linear] point

noncomputable def realPolynomialScaleFrom :
    Nat → List IncReal → List IncReal
  | _, [] => []
  | weight, coefficient :: coefficients =>
      realMul (realNatCoefficient weight) coefficient ::
        realPolynomialScaleFrom (Nat.succ weight) coefficients

noncomputable def realPolynomialDerivativeCoefficients :
    List IncReal → List IncReal
  | [] => []
  | _ :: coefficients => realPolynomialScaleFrom 1 coefficients

@[simp] theorem realPolynomialScaleFrom_nil (weight : Nat) :
    realPolynomialScaleFrom weight [] = [] := rfl

@[simp] theorem realPolynomialScaleFrom_cons
    (weight : Nat) (coefficient : IncReal) (coefficients : List IncReal) :
    realPolynomialScaleFrom weight (coefficient :: coefficients) =
      realMul (realNatCoefficient weight) coefficient ::
        realPolynomialScaleFrom (Nat.succ weight) coefficients := rfl

@[simp] theorem realPolynomialDerivativeCoefficients_nil :
    realPolynomialDerivativeCoefficients [] = [] := rfl

@[simp] theorem realPolynomialDerivativeCoefficients_cons
    (coefficient : IncReal) (coefficients : List IncReal) :
    realPolynomialDerivativeCoefficients (coefficient :: coefficients) =
      realPolynomialScaleFrom 1 coefficients := rfl

theorem realPolynomialScaleFrom_eval
    (weight : Nat) (coefficients : List IncReal) (value : IncReal) :
    realPolynomialEval (realPolynomialScaleFrom weight coefficients) value =
      realAdd
        (realMul (realNatCoefficient weight)
          (realPolynomialEval coefficients value))
        (realMul value (realPolynomialDerivativeEval coefficients value)) := by
  induction coefficients generalizing weight with
  | nil =>
      rw [realPolynomialScaleFrom_nil, realPolynomialEval_nil,
        realPolynomialDerivativeEval_nil, realMul_zero_right,
        realAdd_zero_left, realMul_zero_right]
  | cons coefficient coefficients induction =>
      rw [realPolynomialScaleFrom_cons, realPolynomialEval_cons,
        realPolynomialEval_cons, realPolynomialDerivativeEval_cons,
        induction]
      simp only [realNatCoefficient_succ, realAdd_mul, realMul_add,
        realMul_one_left]
      have commuteScale :
          realMul value
              (realMul (realNatCoefficient weight)
                (realPolynomialEval coefficients value)) =
            realMul (realNatCoefficient weight)
              (realMul value (realPolynomialEval coefficients value)) := by
        rw [← realMul_assoc,
          realMul_comm value (realNatCoefficient weight), realMul_assoc]
      rw [commuteScale]
      rw [realAdd_assoc
          (realMul (realNatCoefficient weight)
            (realMul value (realPolynomialEval coefficients value)))
          (realMul value (realPolynomialEval coefficients value))
          (realMul value
            (realMul value
              (realPolynomialDerivativeEval coefficients value))),
        ← realAdd_assoc]

theorem realPolynomialDerivativeCoefficients_eval
    (coefficients : List IncReal) (value : IncReal) :
    realPolynomialEval (realPolynomialDerivativeCoefficients coefficients) value =
      realPolynomialDerivativeEval coefficients value := by
  cases coefficients with
  | nil => rfl
  | cons coefficient coefficients =>
      rw [realPolynomialDerivativeCoefficients_cons,
        realPolynomialScaleFrom_eval]
      rw [show realNatCoefficient 1 = realOne by
        rw [realNatCoefficient_succ, realNatCoefficient_zero,
          realAdd_zero_left], realMul_one_left]
      rfl

theorem realHasDerivativeAt_polynomial_coefficients
    (coefficients : List IncReal) (point : IncReal) :
    RealHasDerivativeAt (realPolynomialEval coefficients)
      (realPolynomialEval
        (realPolynomialDerivativeCoefficients coefficients) point) point := by
  rw [realPolynomialDerivativeCoefficients_eval]
  exact realHasDerivativeAt_polynomial coefficients point

noncomputable def realPolynomialIteratedDerivativeCoefficients
    (coefficients : List IncReal) : Nat → List IncReal
  | 0 => coefficients
  | Nat.succ order =>
      realPolynomialDerivativeCoefficients
        (realPolynomialIteratedDerivativeCoefficients coefficients order)

@[simp] theorem realPolynomialIteratedDerivativeCoefficients_zero
    (coefficients : List IncReal) :
    realPolynomialIteratedDerivativeCoefficients coefficients 0 =
      coefficients := rfl

@[simp] theorem realPolynomialIteratedDerivativeCoefficients_succ
    (coefficients : List IncReal) (order : Nat) :
    realPolynomialIteratedDerivativeCoefficients coefficients
        (Nat.succ order) =
      realPolynomialDerivativeCoefficients
        (realPolynomialIteratedDerivativeCoefficients coefficients order) := rfl

noncomputable def realPolynomialIteratedDerivativeEval
    (coefficients : List IncReal) (order : Nat) (value : IncReal) : IncReal :=
  realPolynomialEval
    (realPolynomialIteratedDerivativeCoefficients coefficients order) value

theorem realHasDerivativeAt_polynomial_iterated
    (coefficients : List IncReal) (order : Nat) (point : IncReal) :
    RealHasDerivativeAt
      (realPolynomialIteratedDerivativeEval coefficients order)
      (realPolynomialIteratedDerivativeEval coefficients
        (Nat.succ order) point) point := by
  change RealHasDerivativeAt
    (realPolynomialEval
      (realPolynomialIteratedDerivativeCoefficients coefficients order))
    (realPolynomialEval
      (realPolynomialDerivativeCoefficients
        (realPolynomialIteratedDerivativeCoefficients coefficients order))
      point) point
  exact realHasDerivativeAt_polynomial_coefficients
    (realPolynomialIteratedDerivativeCoefficients coefficients order) point

theorem realPolynomialScaleFrom_length
    (weight : Nat) (coefficients : List IncReal) :
    (realPolynomialScaleFrom weight coefficients).length = coefficients.length := by
  induction coefficients generalizing weight with
  | nil => rfl
  | cons coefficient coefficients induction =>
      simp only [realPolynomialScaleFrom_cons, List.length_cons]
      rw [induction]

theorem realPolynomialDerivativeCoefficients_length
    (coefficients : List IncReal) :
    (realPolynomialDerivativeCoefficients coefficients).length =
      coefficients.length - 1 := by
  cases coefficients with
  | nil => rfl
  | cons coefficient coefficients =>
      rw [realPolynomialDerivativeCoefficients_cons,
        realPolynomialScaleFrom_length]
      simp

theorem realPolynomialIteratedDerivativeCoefficients_length
    (coefficients : List IncReal) (order : Nat) :
    (realPolynomialIteratedDerivativeCoefficients coefficients order).length =
      coefficients.length - order := by
  induction order with
  | zero => simp
  | succ order induction =>
      rw [realPolynomialIteratedDerivativeCoefficients_succ,
        realPolynomialDerivativeCoefficients_length, induction]
      omega

theorem realPolynomialIteratedDerivativeCoefficients_at_length
    (coefficients : List IncReal) :
    realPolynomialIteratedDerivativeCoefficients coefficients
      coefficients.length = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [realPolynomialIteratedDerivativeCoefficients_length]
  omega

theorem realPolynomialIteratedDerivativeEval_at_length
    (coefficients : List IncReal) (value : IncReal) :
    realPolynomialIteratedDerivativeEval coefficients coefficients.length value =
      realZero := by
  rw [realPolynomialIteratedDerivativeEval,
    realPolynomialIteratedDerivativeCoefficients_at_length,
    realPolynomialEval_nil]

theorem nonnegativeRealNatScale_rationalToReal
    (count : Nat) {value : IncRational}
    (nonnegative : rationalLE (rationalOfInteger 0) value) :
    (nonnegativeRealNatScale count
      { value := rationalToReal value
        nonnegative := (rationalToReal_le_iff _ _).mpr nonnegative }).value =
      rationalToReal (rationalNatScale count value) := by
  induction count with
  | zero =>
      rw [nonnegativeRealNatScale_zero, rationalNatScale_zero]
      rfl
  | succ count induction =>
      rw [nonnegativeRealNatScale_succ]
      change realAdd
        (nonnegativeRealNatScale count
          { value := rationalToReal value
            nonnegative := (rationalToReal_le_iff _ _).mpr nonnegative }).value
        (rationalToReal value) =
        rationalToReal (rationalNatScale (Nat.succ count) value)
      rw [induction, realAdd_rationalToReal]
      simpa [Nat.succ_eq_add_one] using
        congrArg rationalToReal (rationalNatScale_succ count value).symm

theorem nonnegativeRealNatScale_monotone
    (count : Nat) {left right : NonnegativeReal}
    (ordered : realLE left.value right.value) :
    realLE (nonnegativeRealNatScale count left).value
      (nonnegativeRealNatScale count right).value := by
  induction count with
  | zero => exact realLE_refl _
  | succ count induction =>
      rw [nonnegativeRealNatScale_succ, nonnegativeRealNatScale_succ]
      exact realAdd_monotone induction ordered

theorem nonnegativeReal_bernoulli
    (value : NonnegativeReal) (exponent : Nat) :
    realLE
      (nonnegativeRealAdd nonnegativeOne
        (nonnegativeRealNatScale exponent value)).value
      (nonnegativeRealPow
        (nonnegativeRealAdd nonnegativeOne value) exponent).value := by
  induction exponent with
  | zero =>
      rw [nonnegativeRealNatScale_zero, nonnegativeRealAdd_zero_right,
        nonnegativeRealPow]
      exact realLE_refl _
  | succ exponent induction =>
      let linear := nonnegativeRealAdd nonnegativeOne
        (nonnegativeRealNatScale exponent value)
      let factor := nonnegativeRealAdd nonnegativeOne value
      let extra := nonnegativeRealMul
        (nonnegativeRealNatScale exponent value) value
      let nextLinear := nonnegativeRealAdd nonnegativeOne
        (nonnegativeRealNatScale (Nat.succ exponent) value)
      have expansion : nonnegativeRealMul linear factor =
          nonnegativeRealAdd nextLinear extra := by
        dsimp [linear, factor, extra, nextLinear]
        rw [nonnegativeRealAdd_mul,
          nonnegativeRealMul_one_left_bundle,
          nonnegativeRealMul_add,
          nonnegativeRealMul_one_right_bundle,
          nonnegativeRealNatScale_succ]
        rw [nonnegativeRealAdd_assoc]
        rw [nonnegativeRealAdd_assoc nonnegativeOne
          (nonnegativeRealAdd (nonnegativeRealNatScale exponent value) value)
          (nonnegativeRealMul (nonnegativeRealNatScale exponent value) value)]
        apply congrArg (nonnegativeRealAdd nonnegativeOne)
        rw [← nonnegativeRealAdd_assoc,
          nonnegativeRealAdd_comm value
            (nonnegativeRealNatScale exponent value)]
      have nextBelowExpansion : realLE nextLinear.value
          (nonnegativeRealMul linear factor).value := by
        rw [expansion]
        have added := realAdd_monotone_right
          (left := nextLinear.value) extra.nonnegative
        simpa [realAdd_zero_right] using added
      have multiplied := nonnegativeRealMul_monotone_left
        (right := factor) induction
      have powerStep : nonnegativeRealMul
          (nonnegativeRealPow factor exponent) factor =
          nonnegativeRealPow factor (Nat.succ exponent) := rfl
      rw [powerStep] at multiplied
      exact realLE_trans nextBelowExpansion multiplied

theorem nonnegativeReal_one_add_pow_unbounded
    (value : NonnegativeReal) (valueNonzero : value.value ≠ realZero)
    (target : IncReal) :
    ∃ exponent : Nat,
      realLT target
        (nonnegativeRealPow
          (nonnegativeRealAdd nonnegativeOne value) exponent).value := by
  obtain ⟨step, stepMember, stepPositive⟩ :=
    value.exists_positive_member valueNonzero
  obtain ⟨targetRational, targetBelow⟩ := real_exists_rational_above target
  obtain ⟨exponent, rationalGrowthRaw⟩ := rational_archimedean_steps
    (start := rationalOfInteger 1) (target := targetRational)
    (step := step) stepPositive
  let stepReal : NonnegativeReal :=
    { value := rationalToReal step
      nonnegative := (rationalToReal_le_iff _ _).mpr stepPositive.1 }
  have stepBelow : realLE stepReal.value value.value :=
    (rationalToReal_lt_of_lower value.value stepMember).1
  have scaledBelow := nonnegativeRealNatScale_monotone
    exponent stepBelow
  have rationalGrowth : realLT (rationalToReal targetRational)
      (nonnegativeRealAdd nonnegativeOne
        (nonnegativeRealNatScale exponent stepReal)).value := by
    have principalGrowth : rationalLT targetRational
        (rationalAdd (rationalOfInteger 1)
          (rationalNatScale exponent step)) := by
      simpa [rationalStepValue] using rationalGrowthRaw
    have embedded := rationalToReal_lt_preserves principalGrowth
    change realLT (rationalToReal targetRational)
      (realAdd realOne (nonnegativeRealNatScale exponent stepReal).value)
    rw [nonnegativeRealNatScale_rationalToReal exponent stepPositive.1]
    change realLT (rationalToReal targetRational)
      (realAdd (rationalToReal (rationalOfInteger 1))
        (rationalToReal (rationalNatScale exponent step)))
    rw [realAdd_rationalToReal]
    exact embedded
  have rationalToPower := realLT_of_lt_of_le rationalGrowth
    (realLE_trans
      (realAdd_monotone_right (left := nonnegativeOne.value) scaledBelow)
      (nonnegativeReal_bernoulli value exponent))
  exact ⟨exponent, realLT_trans targetBelow rationalToPower⟩

theorem nonnegativeRealPow_value (base : NonnegativeReal) (exponent : Nat) :
    (nonnegativeRealPow base exponent).value = realPow base.value exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent induction =>
      rw [nonnegativeRealPow, realPow_succ, ← induction]
      rw [realMul_of_nonnegative
        (nonnegativeRealPow base exponent).value base.value
        (nonnegativeRealPow base exponent).nonnegative base.nonnegative]

theorem nonnegativeRealPow_one (exponent : Nat) :
    nonnegativeRealPow nonnegativeOne exponent = nonnegativeOne := by
  induction exponent with
  | zero => rfl
  | succ exponent induction =>
      rw [nonnegativeRealPow, induction,
        nonnegativeRealMul_one_right_bundle]

theorem nonnegativeRealPow_add
    (base : NonnegativeReal) (left right : Nat) :
    nonnegativeRealPow base (left + right) =
      nonnegativeRealMul (nonnegativeRealPow base left)
        (nonnegativeRealPow base right) := by
  apply NonnegativeReal.ext
  rw [nonnegativeRealPow_value, realPow_add]
  rw [← nonnegativeRealPow_value base left,
    ← nonnegativeRealPow_value base right]
  rw [realMul_of_nonnegative
    (nonnegativeRealPow base left).value
    (nonnegativeRealPow base right).value
    (nonnegativeRealPow base left).nonnegative
    (nonnegativeRealPow base right).nonnegative]

theorem nonnegativeRealPow_monotone_base
    {left right : NonnegativeReal}
    (ordered : realLE left.value right.value) (exponent : Nat) :
    realLE (nonnegativeRealPow left exponent).value
      (nonnegativeRealPow right exponent).value := by
  induction exponent with
  | zero => exact realLE_refl _
  | succ exponent induction =>
      rw [nonnegativeRealPow, nonnegativeRealPow]
      exact nonnegativeRealMul_monotone induction ordered

theorem nonnegativeRealPow_one_le
    {base : NonnegativeReal} (oneBelow : realLE nonnegativeOne.value base.value)
    (exponent : Nat) :
    realLE nonnegativeOne.value (nonnegativeRealPow base exponent).value := by
  have powered := nonnegativeRealPow_monotone_base oneBelow exponent
  rw [nonnegativeRealPow_one] at powered
  exact powered

theorem nonnegativeRealPow_monotone_exponent
    {base : NonnegativeReal} (oneBelow : realLE nonnegativeOne.value base.value)
    {first second : Nat} (ordered : first ≤ second) :
    realLE (nonnegativeRealPow base first).value
      (nonnegativeRealPow base second).value := by
  obtain ⟨difference, equal⟩ := Nat.le.dest ordered
  subst second
  rw [nonnegativeRealPow_add]
  have extraOne := nonnegativeRealPow_one_le oneBelow difference
  have multiplied := nonnegativeRealMul_monotone_right
    (left := nonnegativeRealPow base first) extraOne
  rw [nonnegativeRealMul_one_right_bundle] at multiplied
  exact multiplied

theorem nonnegativeReal_one_add_pow_eventually_above
    (value : NonnegativeReal) (valueNonzero : value.value ≠ realZero)
    (target : IncReal) :
    ∃ threshold : Nat, ∀ exponent, threshold ≤ exponent →
      realLT target
        (nonnegativeRealPow
          (nonnegativeRealAdd nonnegativeOne value) exponent).value := by
  obtain ⟨threshold, thresholdAbove⟩ :=
    nonnegativeReal_one_add_pow_unbounded value valueNonzero target
  let base := nonnegativeRealAdd nonnegativeOne value
  have oneBelowBase : realLE nonnegativeOne.value base.value := by
    have added := realAdd_monotone_right
      (left := nonnegativeOne.value) value.nonnegative
    simpa [realAdd_zero_right] using added
  refine ⟨threshold, ?_⟩
  intro exponent exponentLarge
  exact realLT_of_lt_of_le thresholdAbove
    (nonnegativeRealPow_monotone_exponent oneBelowBase exponentLarge)

theorem nonnegativeReal_inv_one_add_pow_converges_zero
    (value : NonnegativeReal) (valueNonzero : value.value ≠ realZero) :
    RealSequenceConverges
      (fun exponent =>
        (nonnegativeRealPow
          (nonnegativeRealInv (nonnegativeRealAdd nonnegativeOne value)
            (by
              intro baseZero
              have oneBelow : realLE nonnegativeOne.value
                  (nonnegativeRealAdd nonnegativeOne value).value := by
                have added := realAdd_monotone_right
                  (left := nonnegativeOne.value) value.nonnegative
                simpa [realAdd_zero_right] using added
              rw [baseZero] at oneBelow
              exact real_zero_ne_one
                (realLE_antisymm oneBelow nonnegativeOne.nonnegative).symm))
          exponent).value)
      realZero := by
  let base := nonnegativeRealAdd nonnegativeOne value
  have baseNonzero : base.value ≠ realZero := by
    intro baseZero
    have oneBelow : realLE nonnegativeOne.value base.value := by
      have added := realAdd_monotone_right
        (left := nonnegativeOne.value) value.nonnegative
      simpa [base, realAdd_zero_right] using added
    rw [baseZero] at oneBelow
    exact real_zero_ne_one
      (realLE_antisymm oneBelow nonnegativeOne.nonnegative).symm
  let inverseBase := nonnegativeRealInv base baseNonzero
  intro epsilon epsilonPositive
  let epsilonReal : NonnegativeReal :=
    { value := rationalToReal epsilon
      nonnegative := (rationalToReal_le_iff _ _).mpr epsilonPositive.1 }
  have epsilonNonzero : epsilonReal.value ≠ realZero := by
    intro epsilonZero
    have injected := rationalToReal_injective epsilonZero
    rw [injected] at epsilonPositive
    exact rationalLT_irrefl _ epsilonPositive
  let target := nonnegativeRealInv epsilonReal epsilonNonzero
  obtain ⟨threshold, eventuallyAbove⟩ :=
    nonnegativeReal_one_add_pow_eventually_above value valueNonzero target.value
  refine ⟨threshold, ?_⟩
  intro exponent exponentLarge
  have above := eventuallyAbove exponent exponentLarge
  let basePower := nonnegativeRealPow base exponent
  have basePowerNonzero : basePower.value ≠ realZero := by
    rw [nonnegativeRealPow_value]
    exact realPow_ne_zero base.value baseNonzero exponent
  have reversed := nonnegativeRealInv_order_reverse
    (left := target) (right := basePower)
    (nonnegativeRealInv_ne_zero epsilonReal epsilonNonzero)
    basePowerNonzero above.1
  have inverseTarget : nonnegativeRealInv target
      (nonnegativeRealInv_ne_zero epsilonReal epsilonNonzero) = epsilonReal :=
    nonnegativeRealInv_involutive epsilonReal epsilonNonzero
  rw [inverseTarget] at reversed
  have powerInverse :
      (nonnegativeRealPow inverseBase exponent).value =
        (nonnegativeRealInv basePower basePowerNonzero).value := by
    apply realMul_cancel_left basePowerNonzero
    have leftLaw : realMul basePower.value
        (nonnegativeRealPow inverseBase exponent).value = realOne := by
      calc
        _ = realMul (realPow base.value exponent)
            (realPow (realInv base.value baseNonzero) exponent) := by
              dsimp [basePower]
              rw [nonnegativeRealPow_value, nonnegativeRealPow_value,
                ← realInv_of_nonnegative base baseNonzero]
        _ = realOne := realPow_mul_pow_inv base.value baseNonzero exponent
    have rightLaw : realMul basePower.value
        (nonnegativeRealInv basePower basePowerNonzero).value = realOne := by
      rw [← realInv_of_nonnegative basePower basePowerNonzero,
        realMul_inv]
    rw [leftLaw, rightLaw]
  change realLE
    (realDist (nonnegativeRealPow inverseBase exponent).value realZero).value
    (rationalToReal epsilon)
  rw [realDist_zero_right,
    realAbs_of_nonnegative _ (nonnegativeRealPow inverseBase exponent).nonnegative,
    powerInverse]
  exact reversed

theorem nonnegativeReal_pow_converges_zero_of_lt_one
    (magnitude : NonnegativeReal)
    (belowOne : realLT magnitude.value nonnegativeOne.value) :
    RealSequenceConverges
      (fun exponent => (nonnegativeRealPow magnitude exponent).value)
      realZero := by
  by_cases magnitudeZero : magnitude.value = realZero
  · have magnitudeEq : magnitude = nonnegativeZero := by
      apply NonnegativeReal.ext
      exact magnitudeZero
    subst magnitude
    intro epsilon epsilonPositive
    refine ⟨1, ?_⟩
    intro exponent exponentLarge
    cases exponent with
    | zero => omega
    | succ exponent =>
        change realLE
          (realDist (nonnegativeRealPow nonnegativeZero
            (Nat.succ exponent)).value realZero).value
          (rationalToReal epsilon)
        rw [nonnegativeRealPow, nonnegativeRealMul_zero_right_bundle]
        change realLE (realDist realZero realZero).value
          (rationalToReal epsilon)
        rw [realDist_self]
        exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1
  · let inverseMagnitude := nonnegativeRealInv magnitude magnitudeZero
    have oneBelowInverse :
        realLE nonnegativeOne.value inverseMagnitude.value := by
      have reversed := nonnegativeRealInv_order_reverse
        (left := magnitude) (right := nonnegativeOne)
        magnitudeZero real_zero_ne_one.symm belowOne.1
      rw [nonnegativeRealInv_one] at reversed
      exact reversed
    have inverseNeOne : inverseMagnitude ≠ nonnegativeOne := by
      intro equal
      have law := nonnegativeRealMul_inv magnitude magnitudeZero
      change nonnegativeRealMul magnitude inverseMagnitude = nonnegativeOne at law
      rw [equal, nonnegativeRealMul_one_right_bundle] at law
      exact belowOne.2 (congrArg NonnegativeReal.value law)
    let increment : NonnegativeReal :=
      { value := realAdd inverseMagnitude.value
          (realNeg nonnegativeOne.value)
        nonnegative := by
          have shifted := realAdd_monotone_left
            (right := realNeg nonnegativeOne.value) oneBelowInverse
          rw [realAdd_neg] at shifted
          exact shifted }
    have incrementNonzero : increment.value ≠ realZero := by
      intro incrementZero
      have inverseValueEq := real_eq_of_add_neg_eq_zero incrementZero
      exact inverseNeOne (NonnegativeReal.ext inverseValueEq)
    have baseEq : nonnegativeRealAdd nonnegativeOne increment =
        inverseMagnitude := by
      apply NonnegativeReal.ext
      dsimp [increment]
      change realAdd nonnegativeOne.value
        (realAdd inverseMagnitude.value (realNeg nonnegativeOne.value)) =
        inverseMagnitude.value
      calc
        _ = realAdd inverseMagnitude.value
            (realAdd nonnegativeOne.value (realNeg nonnegativeOne.value)) := by
              rw [← realAdd_assoc,
                realAdd_comm nonnegativeOne.value inverseMagnitude.value,
                realAdd_assoc]
        _ = inverseMagnitude.value := by
              rw [realAdd_neg, realAdd_zero_right]
    have constructedBaseNonzero :
        (nonnegativeRealAdd nonnegativeOne increment).value ≠ realZero := by
      rw [baseEq]
      exact nonnegativeRealInv_ne_zero magnitude magnitudeZero
    have inverseConverges :=
      nonnegativeReal_inv_one_add_pow_converges_zero increment incrementNonzero
    have inverseInverse := nonnegativeRealInv_involutive magnitude magnitudeZero
    intro epsilon epsilonPositive
    obtain ⟨threshold, eventuallyClose⟩ :=
      inverseConverges epsilon epsilonPositive
    refine ⟨threshold, ?_⟩
    intro exponent exponentLarge
    have close := eventuallyClose exponent exponentLarge
    change realLE
      (realDist (nonnegativeRealPow magnitude exponent).value realZero).value
      (rationalToReal epsilon)
    have inverseBaseEq :
        nonnegativeRealInv (nonnegativeRealAdd nonnegativeOne increment)
            constructedBaseNonzero =
          magnitude := by
      simpa only [baseEq] using inverseInverse
    rw [inverseBaseEq] at close
    exact close

theorem realAbs_pow (base : IncReal) (exponent : Nat) :
    realAbs (realPow base exponent) = nonnegativeRealPow (realAbs base) exponent := by
  induction exponent with
  | zero =>
      rw [realPow_zero, nonnegativeRealPow]
      exact realAbs_of_nonnegative realOne nonnegativeOne.nonnegative
  | succ exponent induction =>
      rw [realPow_succ, nonnegativeRealPow, realAbs_mul, induction]

theorem realPow_converges_zero_of_abs_lt_one
    (ratio : IncReal)
    (belowOne : realLT (realAbs ratio).value realOne) :
    RealSequenceConverges (realPow ratio) realZero := by
  have magnitudeConverges :=
    nonnegativeReal_pow_converges_zero_of_lt_one (realAbs ratio) belowOne
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    magnitudeConverges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro exponent exponentLarge
  have close := eventuallyClose exponent exponentLarge
  change realLE (realDist (realPow ratio exponent) realZero).value
    (rationalToReal epsilon)
  rw [realDist_zero_right, realAbs_pow]
  change realLE
    (realDist (nonnegativeRealPow (realAbs ratio) exponent).value realZero).value
    (rationalToReal epsilon) at close
  rw [realDist_zero_right,
    realAbs_of_nonnegative _
      (nonnegativeRealPow (realAbs ratio) exponent).nonnegative] at close
  exact close

def realPartialSum (terms : RealSequence) : RealSequence
  | 0 => realZero
  | Nat.succ count => realAdd (realPartialSum terms count) (terms count)

@[simp] theorem realPartialSum_zero (terms : RealSequence) :
    realPartialSum terms 0 = realZero := rfl

@[simp] theorem realPartialSum_succ (terms : RealSequence) (count : Nat) :
    realPartialSum terms (Nat.succ count) =
      realAdd (realPartialSum terms count) (terms count) := rfl

noncomputable def realAbsPartialSum
    (terms : RealSequence) : Nat → NonnegativeReal
  | 0 => nonnegativeZero
  | Nat.succ count =>
      nonnegativeRealAdd (realAbsPartialSum terms count) (realAbs (terms count))

@[simp] theorem realAbsPartialSum_zero (terms : RealSequence) :
    realAbsPartialSum terms 0 = nonnegativeZero := rfl

theorem realAbsPartialSum_succ (terms : RealSequence) (count : Nat) :
    realAbsPartialSum terms (Nat.succ count) =
      nonnegativeRealAdd (realAbsPartialSum terms count)
        (realAbs (terms count)) := rfl

theorem realAbsPartialSum_value (terms : RealSequence) (count : Nat) :
    (realAbsPartialSum terms count).value =
      realPartialSum (fun index => (realAbs (terms index)).value) count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [realAbsPartialSum_succ, realPartialSum_succ]
      exact congrArg (fun value => realAdd value (realAbs (terms count)).value)
        induction

theorem realAbs_partialSum_le_absPartialSum
    (terms : RealSequence) (count : Nat) :
    realLE (realAbs (realPartialSum terms count)).value
      (realAbsPartialSum terms count).value := by
  induction count with
  | zero =>
      rw [realPartialSum_zero, realAbs_zero, realAbsPartialSum_zero]
      exact realLE_refl _
  | succ count induction =>
      rw [realPartialSum_succ, realAbsPartialSum_succ]
      exact realLE_trans (realAbs_add_le _ _)
        (realAdd_monotone induction (realLE_refl _))

def realIntervalSum
    (terms : RealSequence) (start : Nat) : Nat → IncReal
  | 0 => realZero
  | Nat.succ length =>
      realAdd (realIntervalSum terms start length) (terms (start + length))

noncomputable def realAbsIntervalSum
    (terms : RealSequence) (start : Nat) : Nat → NonnegativeReal
  | 0 => nonnegativeZero
  | Nat.succ length =>
      nonnegativeRealAdd (realAbsIntervalSum terms start length)
        (realAbs (terms (start + length)))

theorem realPartialSum_add_interval
    (terms : RealSequence) (start length : Nat) :
    realPartialSum terms (start + length) =
      realAdd (realPartialSum terms start)
        (realIntervalSum terms start length) := by
  induction length with
  | zero => rw [Nat.add_zero, realIntervalSum, realAdd_zero_right]
  | succ length induction =>
      rw [Nat.add_succ, realPartialSum_succ, realIntervalSum, induction,
        realAdd_assoc]

theorem realAbsPartialSum_add_interval
    (terms : RealSequence) (start length : Nat) :
    realAbsPartialSum terms (start + length) =
      nonnegativeRealAdd (realAbsPartialSum terms start)
        (realAbsIntervalSum terms start length) := by
  induction length with
  | zero =>
      rw [Nat.add_zero, realAbsIntervalSum, nonnegativeRealAdd_zero_right]
  | succ length induction =>
      rw [Nat.add_succ, realAbsPartialSum_succ, realAbsIntervalSum,
        induction, nonnegativeRealAdd_assoc]

theorem realAbs_intervalSum_le_absIntervalSum
    (terms : RealSequence) (start length : Nat) :
    realLE (realAbs (realIntervalSum terms start length)).value
      (realAbsIntervalSum terms start length).value := by
  induction length with
  | zero =>
      rw [realIntervalSum, realAbs_zero, realAbsIntervalSum]
      exact realLE_refl _
  | succ length induction =>
      rw [realIntervalSum, realAbsIntervalSum]
      exact realLE_trans (realAbs_add_le _ _)
        (realAdd_monotone induction (realLE_refl _))

theorem realIntervalSum_nonnegative
    {terms : RealSequence}
    (termsNonnegative : ∀ index, realLE realZero (terms index))
    (start length : Nat) :
    realLE realZero (realIntervalSum terms start length) := by
  induction length with
  | zero => exact realLE_refl _
  | succ length induction =>
      rw [realIntervalSum]
      have added := realAdd_monotone induction (termsNonnegative (start + length))
      simpa [realAdd_zero_left] using added

theorem realIntervalSum_monotone
    {smaller larger : RealSequence}
    (ordered : ∀ index, realLE (smaller index) (larger index))
    (start length : Nat) :
    realLE (realIntervalSum smaller start length)
      (realIntervalSum larger start length) := by
  induction length with
  | zero => exact realLE_refl _
  | succ length induction =>
      rw [realIntervalSum, realIntervalSum]
      exact realAdd_monotone induction (ordered (start + length))

theorem realDist_base_add (base increment : IncReal) :
    realDist base (realAdd base increment) = realAbs increment := by
  rw [realDist]
  have difference : realAdd base (realNeg (realAdd base increment)) =
      realNeg increment := by
    rw [realNeg_add]
    calc
      realAdd base (realAdd (realNeg base) (realNeg increment)) =
        realAdd (realAdd base (realNeg base)) (realNeg increment) :=
          (realAdd_assoc _ _ _).symm
      _ = realNeg increment := by rw [realAdd_neg, realAdd_zero_left]
  rw [difference, realAbs_neg]

theorem realDist_partialSum_le_absPartialSum_dist_ordered
    (terms : RealSequence) {first second : Nat} (ordered : first ≤ second) :
    realLE
      (realDist (realPartialSum terms first)
        (realPartialSum terms second)).value
      (realDist (realAbsPartialSum terms first).value
        (realAbsPartialSum terms second).value).value := by
  obtain ⟨length, equal⟩ := Nat.le.dest ordered
  subst second
  rw [realPartialSum_add_interval, realAbsPartialSum_add_interval,
    realDist_base_add]
  change realLE (realAbs (realIntervalSum terms first length)).value
    (realDist (realAbsPartialSum terms first).value
      (realAdd (realAbsPartialSum terms first).value
        (realAbsIntervalSum terms first length).value)).value
  rw [realDist_base_add]
  rw [realAbs_of_nonnegative _ (realAbsIntervalSum terms first length).nonnegative]
  exact realAbs_intervalSum_le_absIntervalSum terms first length

theorem realDist_partialSum_le_absPartialSum_dist
    (terms : RealSequence) (first second : Nat) :
    realLE
      (realDist (realPartialSum terms first)
        (realPartialSum terms second)).value
      (realDist (realAbsPartialSum terms first).value
        (realAbsPartialSum terms second).value).value := by
  rcases Nat.le_total first second with ordered | reverse
  · exact realDist_partialSum_le_absPartialSum_dist_ordered terms ordered
  · rw [realDist_comm (realPartialSum terms first),
      realDist_comm (realAbsPartialSum terms first).value]
    exact realDist_partialSum_le_absPartialSum_dist_ordered terms reverse

theorem realDist_partialSum_le_dominating_ordered
    {smaller larger : RealSequence}
    (smallerNonnegative : ∀ index, realLE realZero (smaller index))
    (largerNonnegative : ∀ index, realLE realZero (larger index))
    (dominated : ∀ index, realLE (smaller index) (larger index))
    {first second : Nat} (indicesOrdered : first ≤ second) :
    realLE
      (realDist (realPartialSum smaller first)
        (realPartialSum smaller second)).value
      (realDist (realPartialSum larger first)
        (realPartialSum larger second)).value := by
  obtain ⟨length, equal⟩ := Nat.le.dest indicesOrdered
  subst second
  rw [realPartialSum_add_interval, realPartialSum_add_interval,
    realDist_base_add, realDist_base_add]
  rw [realAbs_of_nonnegative _
      (realIntervalSum_nonnegative smallerNonnegative first length),
    realAbs_of_nonnegative _
      (realIntervalSum_nonnegative largerNonnegative first length)]
  exact realIntervalSum_monotone dominated first length

theorem realDist_partialSum_le_dominating
    {smaller larger : RealSequence}
    (smallerNonnegative : ∀ index, realLE realZero (smaller index))
    (largerNonnegative : ∀ index, realLE realZero (larger index))
    (dominated : ∀ index, realLE (smaller index) (larger index))
    (first second : Nat) :
    realLE
      (realDist (realPartialSum smaller first)
        (realPartialSum smaller second)).value
      (realDist (realPartialSum larger first)
        (realPartialSum larger second)).value := by
  rcases Nat.le_total first second with ordered | reverse
  · exact realDist_partialSum_le_dominating_ordered
      smallerNonnegative largerNonnegative dominated ordered
  · rw [realDist_comm (realPartialSum smaller first),
      realDist_comm (realPartialSum larger first)]
    exact realDist_partialSum_le_dominating_ordered
      smallerNonnegative largerNonnegative dominated reverse

noncomputable def realGeometricPartialSum
    (ratio : IncReal) (count : Nat) : IncReal :=
  realPartialSum (realPow ratio) count

@[simp] theorem realGeometricPartialSum_zero (ratio : IncReal) :
    realGeometricPartialSum ratio 0 = realZero := rfl

theorem realGeometricPartialSum_succ (ratio : IncReal) (count : Nat) :
    realGeometricPartialSum ratio (Nat.succ count) =
      realAdd (realGeometricPartialSum ratio count) (realPow ratio count) := rfl

theorem realGeometric_factor_term (ratio : IncReal) (exponent : Nat) :
    realMul (realAdd realOne (realNeg ratio)) (realPow ratio exponent) =
      realAdd (realPow ratio exponent)
        (realNeg (realPow ratio (Nat.succ exponent))) := by
  rw [realAdd_mul, realMul_one_left, realPow_succ,
    realMul_neg_left, realMul_comm ratio (realPow ratio exponent)]

theorem realGeometricPartialSum_mul_one_sub
    (ratio : IncReal) (count : Nat) :
    realMul (realAdd realOne (realNeg ratio))
        (realGeometricPartialSum ratio count) =
      realAdd realOne (realNeg (realPow ratio count)) := by
  induction count with
  | zero =>
      rw [realGeometricPartialSum_zero, realMul_zero_right,
        realPow_zero, realAdd_neg]
  | succ count induction =>
      rw [realGeometricPartialSum_succ, realMul_add, induction,
        realGeometric_factor_term]
      calc
        realAdd
            (realAdd realOne (realNeg (realPow ratio count)))
            (realAdd (realPow ratio count)
              (realNeg (realPow ratio (Nat.succ count)))) =
          realAdd realOne
            (realAdd (realNeg (realPow ratio count))
              (realAdd (realPow ratio count)
                (realNeg (realPow ratio (Nat.succ count))))) :=
            realAdd_assoc _ _ _
        _ = realAdd realOne
            (realAdd
              (realAdd (realNeg (realPow ratio count))
                (realPow ratio count))
              (realNeg (realPow ratio (Nat.succ count)))) := by
                apply congrArg (realAdd realOne)
                exact (realAdd_assoc _ _ _).symm
        _ = realAdd realOne (realNeg (realPow ratio (Nat.succ count))) := by
              rw [realAdd_neg_left, realAdd_zero_left]

theorem realGeometricPartialSum_closed
    (ratio : IncReal) (ratioNeOne : ratio ≠ realOne) (count : Nat) :
    realGeometricPartialSum ratio count =
      realDiv (realAdd realOne (realNeg (realPow ratio count)))
        (realAdd realOne (realNeg ratio)) := by
  let denominator := realAdd realOne (realNeg ratio)
  have denominatorNonzero : denominator ≠ realZero := by
    intro denominatorZero
    have oneEqRatio := real_eq_of_add_neg_eq_zero denominatorZero
    exact ratioNeOne oneEqRatio.symm
  have finiteIdentity := realGeometricPartialSum_mul_one_sub ratio count
  change realMul denominator (realGeometricPartialSum ratio count) =
    realAdd realOne (realNeg (realPow ratio count)) at finiteIdentity
  change realGeometricPartialSum ratio count =
    realMul (realAdd realOne (realNeg (realPow ratio count)))
      (realInvOrZero denominator)
  rw [realInvOrZero_of_ne denominator denominatorNonzero,
    ← finiteIdentity]
  symm
  calc
    realMul (realMul denominator (realGeometricPartialSum ratio count))
        (realInv denominator denominatorNonzero) =
      realMul (realGeometricPartialSum ratio count)
        (realMul denominator (realInv denominator denominatorNonzero)) := by
          rw [realMul_comm denominator (realGeometricPartialSum ratio count),
            realMul_assoc]
    _ = realGeometricPartialSum ratio count := by
          rw [realMul_inv, realMul_one_right]

def RealSeriesConverges (terms : RealSequence) (sum : IncReal) : Prop :=
  RealSequenceConverges (realPartialSum terms) sum

def RealSeriesSummable (terms : RealSequence) : Prop :=
  ∃ sum, RealSeriesConverges terms sum

def RealSeriesAbsolutelyConverges
    (terms : RealSequence) (absoluteSum : IncReal) : Prop :=
  RealSeriesConverges (fun index => (realAbs (terms index)).value) absoluteSum

def RealSeriesAbsolutelySummable (terms : RealSequence) : Prop :=
  ∃ absoluteSum, RealSeriesAbsolutelyConverges terms absoluteSum

theorem realGeometricSeriesConverges_of_pow_zero
    (ratio : IncReal) (ratioNeOne : ratio ≠ realOne)
    (powersConverge :
      RealSequenceConverges (realPow ratio) realZero) :
    RealSeriesConverges (realPow ratio)
      (realDiv realOne (realAdd realOne (realNeg ratio))) := by
  let denominator := realAdd realOne (realNeg ratio)
  have denominatorNonzero : denominator ≠ realZero := by
    intro denominatorZero
    have oneEqRatio := real_eq_of_add_neg_eq_zero denominatorZero
    exact ratioNeOne oneEqRatio.symm
  have numeratorConverges :
      RealSequenceConverges
        (fun index => realAdd realOne (realNeg (realPow ratio index)))
        realOne := by
    have combined := realSequenceConverges_add
      (realSequenceConverges_const realOne)
      (realSequenceConverges_neg powersConverge)
    simpa [realNeg_zero, realAdd_zero_right] using combined
  have quotientConverges := realSequenceConverges_div denominatorNonzero
    numeratorConverges (realSequenceConverges_const denominator)
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    quotientConverges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  change realLE
    (realDist (realGeometricPartialSum ratio index)
      (realDiv realOne denominator)).value
    (rationalToReal epsilon)
  rw [realGeometricPartialSum_closed ratio ratioNeOne index]
  exact eventuallyClose index indexLarge

theorem realGeometricSeriesConverges_of_abs_lt_one
    (ratio : IncReal)
    (belowOne : realLT (realAbs ratio).value realOne) :
    RealSeriesConverges (realPow ratio)
      (realDiv realOne (realAdd realOne (realNeg ratio))) := by
  have ratioNeOne : ratio ≠ realOne := by
    intro ratioOne
    subst ratio
    have absoluteOne := realAbs_of_nonnegative realOne nonnegativeOne.nonnegative
    exact belowOne.2 (congrArg NonnegativeReal.value absoluteOne)
  exact realGeometricSeriesConverges_of_pow_zero ratio ratioNeOne
    (realPow_converges_zero_of_abs_lt_one ratio belowOne)

theorem realPow_zero_succ (exponent : Nat) :
    realPow realZero (Nat.succ exponent) = realZero := by
  rw [realPow_succ, realMul_zero_right]

theorem realPow_zero_converges :
    RealSequenceConverges (realPow realZero) realZero := by
  intro epsilon epsilonPositive
  refine ⟨1, ?_⟩
  intro index indexLarge
  cases index with
  | zero => omega
  | succ exponent =>
      rw [realPow_zero_succ, realDist_self]
      exact (rationalToReal_le_iff _ _).mpr epsilonPositive.1

theorem realGeometricSeries_zero :
    RealSeriesConverges (realPow realZero) realOne := by
  have oneNonzero : realOne ≠ realZero := real_zero_ne_one.symm
  have inverseOne : realInv realOne oneNonzero = realOne := by
    have law := realMul_inv realOne oneNonzero
    rw [realMul_one_left] at law
    exact law
  have converges := realGeometricSeriesConverges_of_pow_zero
    realZero real_zero_ne_one realPow_zero_converges
  simpa [realNeg_zero, realAdd_zero_right, realDiv,
    realInvOrZero_of_ne realOne oneNonzero, inverseOne,
    realMul_one_left] using converges

theorem realSequenceConverges_shift
    {sequence : RealSequence} {limit : IncReal}
    (converges : RealSequenceConverges sequence limit) :
    RealSequenceConverges (fun index => sequence (Nat.succ index)) limit := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := converges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  exact eventuallyClose (Nat.succ index)
    (Nat.le_trans indexLarge (Nat.le_succ index))

theorem realPartialSum_increment (terms : RealSequence) (index : Nat) :
    realAdd (realPartialSum terms (Nat.succ index))
        (realNeg (realPartialSum terms index)) = terms index := by
  rw [realPartialSum_succ]
  calc
    realAdd (realAdd (realPartialSum terms index) (terms index))
        (realNeg (realPartialSum terms index)) =
      realAdd (terms index)
        (realAdd (realPartialSum terms index)
          (realNeg (realPartialSum terms index))) := by
            rw [realAdd_comm (realPartialSum terms index) (terms index),
              realAdd_assoc]
    _ = terms index := by rw [realAdd_neg, realAdd_zero_right]

theorem realSeriesConverges_terms_zero
    {terms : RealSequence} {sum : IncReal}
    (converges : RealSeriesConverges terms sum) :
    RealSequenceConverges terms realZero := by
  have shifted : RealSequenceConverges
      (fun index => realPartialSum terms (Nat.succ index)) sum :=
    realSequenceConverges_shift converges
  have differences := realSequenceConverges_sub shifted converges
  have differenceLimit : realAdd sum (realNeg sum) = realZero :=
    realAdd_neg sum
  rw [differenceLimit] at differences
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    differences epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  change realLE (realDist (terms index) realZero).value
    (rationalToReal epsilon)
  rw [← realPartialSum_increment terms index]
  exact eventuallyClose index indexLarge

theorem realSeriesSummable_terms_zero
    {terms : RealSequence} (summable : RealSeriesSummable terms) :
    RealSequenceConverges terms realZero := by
  obtain ⟨sum, converges⟩ := summable
  exact realSeriesConverges_terms_zero converges

theorem realSeriesAbsolutelyConverges_abs_terms_zero
    {terms : RealSequence} {absoluteSum : IncReal}
    (converges : RealSeriesAbsolutelyConverges terms absoluteSum) :
    RealSequenceConverges
      (fun index => (realAbs (terms index)).value) realZero :=
  realSeriesConverges_terms_zero converges

theorem realSeriesAbsolutelyConverges_terms_zero
    {terms : RealSequence} {absoluteSum : IncReal}
    (converges : RealSeriesAbsolutelyConverges terms absoluteSum) :
    RealSequenceConverges terms realZero := by
  have absoluteTerms :=
    realSeriesAbsolutelyConverges_abs_terms_zero converges
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    absoluteTerms epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  have close := eventuallyClose index indexLarge
  change realLE (realDist (terms index) realZero).value
    (rationalToReal epsilon)
  rw [realDist_zero_right]
  change realLE
    (realDist (realAbs (terms index)).value realZero).value
    (rationalToReal epsilon) at close
  rw [realDist_zero_right,
    realAbs_of_nonnegative _ (realAbs (terms index)).nonnegative] at close
  exact close

theorem realPartialSum_add
    (left right : RealSequence) (count : Nat) :
    realPartialSum (fun index => realAdd (left index) (right index)) count =
      realAdd (realPartialSum left count) (realPartialSum right count) := by
  induction count with
  | zero => rw [realPartialSum_zero, realPartialSum_zero,
      realPartialSum_zero, realAdd_zero_left]
  | succ count induction =>
      rw [realPartialSum_succ, realPartialSum_succ, realPartialSum_succ,
        induction]
      calc
        realAdd
            (realAdd (realPartialSum left count) (realPartialSum right count))
            (realAdd (left count) (right count)) =
          realAdd (realPartialSum left count)
            (realAdd (realPartialSum right count)
              (realAdd (left count) (right count))) :=
            realAdd_assoc _ _ _
        _ = realAdd (realPartialSum left count)
            (realAdd (left count)
              (realAdd (realPartialSum right count) (right count))) := by
              apply congrArg (realAdd (realPartialSum left count))
              rw [← realAdd_assoc,
                realAdd_comm (realPartialSum right count) (left count),
                realAdd_assoc]
        _ = realAdd
            (realAdd (realPartialSum left count) (left count))
            (realAdd (realPartialSum right count) (right count)) :=
              (realAdd_assoc _ _ _).symm

theorem realPartialSum_neg (terms : RealSequence) (count : Nat) :
    realPartialSum (fun index => realNeg (terms index)) count =
      realNeg (realPartialSum terms count) := by
  induction count with
  | zero => rw [realPartialSum_zero, realPartialSum_zero, realNeg_zero]
  | succ count induction =>
      rw [realPartialSum_succ, realPartialSum_succ, induction, realNeg_add]

theorem realPartialSum_mul_const
    (factor : IncReal) (terms : RealSequence) (count : Nat) :
    realPartialSum (fun index => realMul factor (terms index)) count =
      realMul factor (realPartialSum terms count) := by
  induction count with
  | zero => rw [realPartialSum_zero, realPartialSum_zero, realMul_zero_right]
  | succ count induction =>
      rw [realPartialSum_succ, realPartialSum_succ, induction, realMul_add]

theorem realSeriesConverges_add
    {left right : RealSequence} {leftSum rightSum : IncReal}
    (leftConverges : RealSeriesConverges left leftSum)
    (rightConverges : RealSeriesConverges right rightSum) :
    RealSeriesConverges (fun index => realAdd (left index) (right index))
      (realAdd leftSum rightSum) := by
  have combined := realSequenceConverges_add leftConverges rightConverges
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    combined epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  rw [realPartialSum_add]
  exact eventuallyClose index indexLarge

theorem realSeriesConverges_neg
    {terms : RealSequence} {sum : IncReal}
    (converges : RealSeriesConverges terms sum) :
    RealSeriesConverges (fun index => realNeg (terms index)) (realNeg sum) := by
  have negated := realSequenceConverges_neg converges
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := negated epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  rw [realPartialSum_neg]
  exact eventuallyClose index indexLarge

theorem realSeriesConverges_mul_const
    (factor : IncReal) {terms : RealSequence} {sum : IncReal}
    (converges : RealSeriesConverges terms sum) :
    RealSeriesConverges (fun index => realMul factor (terms index))
      (realMul factor sum) := by
  have scaled := realSequenceConverges_mul_const (factor := factor) converges
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := scaled epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  rw [realPartialSum_mul_const]
  exact eventuallyClose index indexLarge

theorem realSeriesConverges_sum_unique
    {terms : RealSequence} {firstSum secondSum : IncReal}
    (first : RealSeriesConverges terms firstSum)
    (second : RealSeriesConverges terms secondSum) :
    firstSum = secondSum :=
  realSequence_limit_unique first second

theorem real_finite_sequence_upper_bound
    (sequence : RealSequence) (count : Nat) :
    ∃ upper : IncReal, ∀ index, index < count →
      realLE (sequence index) upper := by
  induction count with
  | zero =>
      exact ⟨realZero, fun index impossible => False.elim (Nat.not_lt_zero _ impossible)⟩
  | succ count induction =>
      obtain ⟨previousUpper, previousBound⟩ := induction
      rcases realLE_total previousUpper (sequence count) with ordered | reverse
      · refine ⟨sequence count, ?_⟩
        intro index indexBelow
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ indexBelow) with earlier | equal
        · exact realLE_trans (previousBound index earlier) ordered
        · subst index
          exact realLE_refl _
      · refine ⟨previousUpper, ?_⟩
        intro index indexBelow
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ indexBelow) with earlier | equal
        · exact previousBound index earlier
        · subst index
          exact reverse

def RealSequenceUpperBound (sequence : RealSequence) (upper : IncReal) : Prop :=
  ∀ index, realLE (sequence index) upper

theorem realSequenceCauchy_bounded_above
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence) :
    ∃ upper, RealSequenceUpperBound sequence upper := by
  have onePositive :
      rationalLT (rationalOfInteger 0) (rationalOfInteger 1) :=
    rational_zero_lt_one
  obtain ⟨threshold, tailCauchy⟩ :=
    cauchy (rationalOfInteger 1) onePositive
  obtain ⟨prefixUpper, prefixBound⟩ :=
    real_finite_sequence_upper_bound sequence threshold
  let tailUpper := realAdd (sequence threshold) realOne
  rcases realLE_total prefixUpper tailUpper with prefixTail | tailPrefix
  · refine ⟨tailUpper, ?_⟩
    intro index
    by_cases indexLarge : threshold ≤ index
    · have distanceBound := tailCauchy index threshold indexLarge
        (Nat.le_refl threshold)
      have ordered := real_le_add_of_dist_le distanceBound
      simpa [realOne] using ordered
    · have indexBelow : index < threshold := Nat.lt_of_not_ge indexLarge
      exact realLE_trans (prefixBound index indexBelow) prefixTail
  · refine ⟨prefixUpper, ?_⟩
    intro index
    by_cases indexLarge : threshold ≤ index
    · have distanceBound := tailCauchy index threshold indexLarge
        (Nat.le_refl threshold)
      have ordered := real_le_add_of_dist_le distanceBound
      exact realLE_trans (by simpa [realOne] using ordered) tailPrefix
    · exact prefixBound index (Nat.lt_of_not_ge indexLarge)

theorem realSequenceCauchy_neg {sequence : RealSequence}
    (cauchy : RealSequenceCauchy sequence) :
    RealSequenceCauchy (fun index => realNeg (sequence index)) := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := cauchy epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro left right leftLarge rightLarge
  rw [realDist_neg]
  exact eventuallyClose left right leftLarge rightLarge

def RealSequenceLowerBound (sequence : RealSequence) (lower : IncReal) : Prop :=
  ∀ index, realLE lower (sequence index)

theorem realSequenceCauchy_bounded_below
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence) :
    ∃ lower, RealSequenceLowerBound sequence lower := by
  obtain ⟨negUpper, negBound⟩ :=
    realSequenceCauchy_bounded_above (realSequenceCauchy_neg cauchy)
  refine ⟨realNeg negUpper, ?_⟩
  intro index
  have reversed := realNeg_order_reverse (negBound index)
  simpa [realNeg_neg] using reversed

theorem realSequenceCauchy_bounded
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence) :
    (∃ lower, RealSequenceLowerBound sequence lower) ∧
      ∃ upper, RealSequenceUpperBound sequence upper :=
  ⟨realSequenceCauchy_bounded_below cauchy,
    realSequenceCauchy_bounded_above cauchy⟩

def RealSequenceTail (sequence : RealSequence) (start : Nat)
    (value : IncReal) : Prop :=
  ∃ index, start ≤ index ∧ sequence index = value

theorem realSequenceTail_nonempty (sequence : RealSequence) (start : Nat) :
    ∃ value, RealSequenceTail sequence start value :=
  ⟨sequence start, start, Nat.le_refl start, rfl⟩

theorem realSequenceTail_bounded
    {sequence : RealSequence}
    (bounded : ∃ upper, RealSequenceUpperBound sequence upper)
    (start : Nat) :
    ∃ upper, RealUpperBound (RealSequenceTail sequence start) upper := by
  obtain ⟨upper, isUpper⟩ := bounded
  refine ⟨upper, ?_⟩
  intro value member
  obtain ⟨index, _, equal⟩ := member
  subst value
  exact isUpper index

noncomputable def realSequenceTailSup
    (sequence : RealSequence) (start : Nat)
    (bounded : ∃ upper, RealSequenceUpperBound sequence upper) : IncReal :=
  realSup (RealSequenceTail sequence start)
    (realSequenceTail_nonempty sequence start)
    (realSequenceTail_bounded bounded start)

theorem realSequence_le_tailSup
    {sequence : RealSequence}
    (bounded : ∃ upper, RealSequenceUpperBound sequence upper)
    {start index : Nat} (indexLarge : start ≤ index) :
    realLE (sequence index) (realSequenceTailSup sequence start bounded) := by
  apply realSup_is_upper_bound
    (RealSequenceTail sequence start)
    (realSequenceTail_nonempty sequence start)
    (realSequenceTail_bounded bounded start)
  exact ⟨index, indexLarge, rfl⟩

theorem realSequenceTailSup_monotone
    {sequence : RealSequence}
    (bounded : ∃ upper, RealSequenceUpperBound sequence upper)
    {start later : Nat} (ordered : start ≤ later) :
    realLE (realSequenceTailSup sequence later bounded)
      (realSequenceTailSup sequence start bounded) := by
  apply realSup_is_least
    (RealSequenceTail sequence later)
    (realSequenceTail_nonempty sequence later)
    (realSequenceTail_bounded bounded later)
  intro value member
  obtain ⟨index, laterIndex, equal⟩ := member
  subst value
  exact realSequence_le_tailSup bounded
    (Nat.le_trans ordered laterIndex)

noncomputable def realCauchyTailSup
    (sequence : RealSequence) (cauchy : RealSequenceCauchy sequence)
    (start : Nat) : IncReal :=
  realSequenceTailSup sequence start
    (realSequenceCauchy_bounded_above cauchy)

theorem realCauchyTailSup_monotone
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence)
    {start later : Nat} (ordered : start ≤ later) :
    realLE (realCauchyTailSup sequence cauchy later)
      (realCauchyTailSup sequence cauchy start) :=
  realSequenceTailSup_monotone
    (realSequenceCauchy_bounded_above cauchy) ordered

theorem realCauchy_tailSup_close
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence)
    {epsilon : IncRational}
    (epsilonPositive : rationalLT (rationalOfInteger 0) epsilon) :
    ∃ threshold, realLE
      (realDist (sequence threshold)
        (realCauchyTailSup sequence cauchy threshold)).value
      (rationalToReal epsilon) := by
  obtain ⟨threshold, tailClose⟩ := cauchy epsilon epsilonPositive
  have bounded := realSequenceCauchy_bounded_above cauchy
  have sequenceBelowSup : realLE (sequence threshold)
      (realCauchyTailSup sequence cauchy threshold) :=
    realSequence_le_tailSup bounded (Nat.le_refl threshold)
  have supBelow : realLE (realCauchyTailSup sequence cauchy threshold)
      (realAdd (sequence threshold) (rationalToReal epsilon)) := by
    apply realSup_is_least
      (RealSequenceTail sequence threshold)
      (realSequenceTail_nonempty sequence threshold)
      (realSequenceTail_bounded bounded threshold)
    intro value member
    obtain ⟨index, indexLarge, equal⟩ := member
    subst value
    exact real_le_add_of_dist_le
      (tailClose index threshold indexLarge (Nat.le_refl threshold))
  let radius : NonnegativeReal :=
    { value := rationalToReal epsilon
      nonnegative := (rationalToReal_le_iff _ _).mpr epsilonPositive.1 }
  refine ⟨threshold, ?_⟩
  exact realDist_le_of_le_of_le_add radius sequenceBelowSup supBelow

def RealLowerBound (family : IncReal → Prop) (lower : IncReal) : Prop :=
  ∀ value, family value → realLE lower value

def RealNegFamily (family : IncReal → Prop) (value : IncReal) : Prop :=
  ∃ original, family original ∧ value = realNeg original

theorem realNegFamily_nonempty {family : IncReal → Prop}
    (nonempty : ∃ value, family value) :
    ∃ value, RealNegFamily family value := by
  obtain ⟨value, member⟩ := nonempty
  exact ⟨realNeg value, value, member, rfl⟩

theorem realNegFamily_bounded {family : IncReal → Prop}
    (bounded : ∃ lower, RealLowerBound family lower) :
    ∃ upper, RealUpperBound (RealNegFamily family) upper := by
  obtain ⟨lower, isLower⟩ := bounded
  refine ⟨realNeg lower, ?_⟩
  intro value member
  obtain ⟨original, originalMember, equal⟩ := member
  subst value
  exact realNeg_order_reverse (isLower original originalMember)

/-- Infimum derived from the already checked Dedekind supremum by order
duality through real negation. -/
noncomputable def realInf (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ lower, RealLowerBound family lower) : IncReal :=
  realNeg (realSup (RealNegFamily family)
    (realNegFamily_nonempty nonempty) (realNegFamily_bounded bounded))

theorem realInf_is_lower_bound (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ lower, RealLowerBound family lower) :
    RealLowerBound family (realInf family nonempty bounded) := by
  intro value member
  have negBelowSup := realSup_is_upper_bound (RealNegFamily family)
    (realNegFamily_nonempty nonempty) (realNegFamily_bounded bounded)
    (realNeg value) ⟨value, member, rfl⟩
  have reversed := realNeg_order_reverse negBelowSup
  simpa [realInf, realNeg_neg] using reversed

theorem realInf_is_greatest (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ lower, RealLowerBound family lower)
    {lower : IncReal} (isLower : RealLowerBound family lower) :
    realLE lower (realInf family nonempty bounded) := by
  have supBelow : realLE
      (realSup (RealNegFamily family)
        (realNegFamily_nonempty nonempty) (realNegFamily_bounded bounded))
      (realNeg lower) := by
    apply realSup_is_least (RealNegFamily family)
      (realNegFamily_nonempty nonempty) (realNegFamily_bounded bounded)
    intro value member
    obtain ⟨original, originalMember, equal⟩ := member
    subst value
    exact realNeg_order_reverse (isLower original originalMember)
  have reversed := realNeg_order_reverse supBelow
  simpa [realInf, realNeg_neg] using reversed

def RealCauchyTailSupFamily (sequence : RealSequence)
    (cauchy : RealSequenceCauchy sequence) (value : IncReal) : Prop :=
  ∃ start, realCauchyTailSup sequence cauchy start = value

theorem realCauchyTailSupFamily_nonempty
    (sequence : RealSequence) (cauchy : RealSequenceCauchy sequence) :
    ∃ value, RealCauchyTailSupFamily sequence cauchy value :=
  ⟨realCauchyTailSup sequence cauchy 0, 0, rfl⟩

theorem realCauchyTailSupFamily_bounded_below
    (sequence : RealSequence) (cauchy : RealSequenceCauchy sequence) :
    ∃ lower, RealLowerBound (RealCauchyTailSupFamily sequence cauchy) lower := by
  obtain ⟨lower, sequenceLower⟩ := realSequenceCauchy_bounded_below cauchy
  refine ⟨lower, ?_⟩
  intro value member
  obtain ⟨start, equal⟩ := member
  subst value
  exact realLE_trans (sequenceLower start)
    (realSequence_le_tailSup (realSequenceCauchy_bounded_above cauchy)
      (Nat.le_refl start))

noncomputable def realCauchyLimitCandidate
    (sequence : RealSequence) (cauchy : RealSequenceCauchy sequence) : IncReal :=
  realInf (RealCauchyTailSupFamily sequence cauchy)
    (realCauchyTailSupFamily_nonempty sequence cauchy)
    (realCauchyTailSupFamily_bounded_below sequence cauchy)

theorem realCauchyLimitCandidate_le_tailSup
    (sequence : RealSequence) (cauchy : RealSequenceCauchy sequence)
    (start : Nat) :
    realLE (realCauchyLimitCandidate sequence cauchy)
      (realCauchyTailSup sequence cauchy start) := by
  apply realInf_is_lower_bound (RealCauchyTailSupFamily sequence cauchy)
    (realCauchyTailSupFamily_nonempty sequence cauchy)
    (realCauchyTailSupFamily_bounded_below sequence cauchy)
  exact ⟨start, rfl⟩

theorem realCauchy_candidate_close
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence)
    {epsilon : IncRational}
    (epsilonPositive : rationalLT (rationalOfInteger 0) epsilon) :
    ∃ threshold,
      (∀ index, threshold ≤ index →
        realLE (realDist (sequence index) (sequence threshold)).value
          (rationalToReal epsilon)) ∧
      realLE (realDist (sequence threshold)
          (realCauchyLimitCandidate sequence cauchy)).value
        (rationalToReal epsilon) := by
  obtain ⟨threshold, tailClose⟩ := cauchy epsilon epsilonPositive
  have bounded := realSequenceCauchy_bounded_above cauchy
  let radius : NonnegativeReal :=
    { value := rationalToReal epsilon
      nonnegative := (rationalToReal_le_iff _ _).mpr epsilonPositive.1 }
  let lower := realAdd (sequence threshold) (realNeg radius.value)
  have lowerBelowThreshold : realLE lower (sequence threshold) := by
    apply realAdd_neg_le_of_le_add
    simpa [realAdd_zero_right] using
      (realAdd_monotone_right (left := sequence threshold) radius.nonnegative)
  have lowerIsFamilyBound :
      RealLowerBound (RealCauchyTailSupFamily sequence cauchy) lower := by
    intro value member
    obtain ⟨start, equal⟩ := member
    subst value
    by_cases startLarge : threshold ≤ start
    · have distanceBound := tailClose threshold start
        (Nat.le_refl threshold) startLarge
      have thresholdBelowStartRadius := real_le_add_of_dist_le distanceBound
      have lowerBelowStart :=
        realAdd_neg_le_of_le_add thresholdBelowStartRadius
      exact realLE_trans lowerBelowStart
        (realSequence_le_tailSup bounded (Nat.le_refl start))
    · have startThreshold : start ≤ threshold :=
        Nat.le_of_lt (Nat.lt_of_not_ge startLarge)
      exact realLE_trans lowerBelowThreshold
        (realLE_trans
          (realSequence_le_tailSup bounded (Nat.le_refl threshold))
          (realCauchyTailSup_monotone cauchy startThreshold))
  have lowerBelowCandidate :
      realLE lower (realCauchyLimitCandidate sequence cauchy) := by
    apply realInf_is_greatest (RealCauchyTailSupFamily sequence cauchy)
      (realCauchyTailSupFamily_nonempty sequence cauchy)
      (realCauchyTailSupFamily_bounded_below sequence cauchy)
    exact lowerIsFamilyBound
  have candidateBelowTail :=
    realCauchyLimitCandidate_le_tailSup sequence cauchy threshold
  have tailBelow : realLE (realCauchyTailSup sequence cauchy threshold)
      (realAdd (sequence threshold) radius.value) := by
    apply realSup_is_least
      (RealSequenceTail sequence threshold)
      (realSequenceTail_nonempty sequence threshold)
      (realSequenceTail_bounded bounded threshold)
    intro value member
    obtain ⟨index, indexLarge, equal⟩ := member
    subst value
    exact real_le_add_of_dist_le
      (tailClose index threshold indexLarge (Nat.le_refl threshold))
  have candidateUpper := realLE_trans candidateBelowTail tailBelow
  have sequenceUpper : realLE (sequence threshold)
      (realAdd (realCauchyLimitCandidate sequence cauchy) radius.value) :=
    realLE_add_of_add_neg_le lowerBelowCandidate
  refine ⟨threshold, ?_, ?_⟩
  · intro index indexLarge
    exact tailClose index threshold indexLarge (Nat.le_refl threshold)
  · exact realDist_le_of_le_add_both radius sequenceUpper candidateUpper

theorem realSequenceCauchy_converges
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence) :
    RealSequenceConverges sequence
      (realCauchyLimitCandidate sequence cauchy) := by
  intro epsilon epsilonPositive
  obtain ⟨half, halfPositive, halfAdd⟩ :=
    rational_exists_positive_half epsilonPositive
  obtain ⟨threshold, tailClose, candidateClose⟩ :=
    realCauchy_candidate_close cauchy halfPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  have triangle := realDist_triangle (sequence index) (sequence threshold)
    (realCauchyLimitCandidate sequence cauchy)
  have summed := realAdd_monotone (tailClose index indexLarge) candidateClose
  have result := realLE_trans triangle summed
  rw [realAdd_rationalToReal, halfAdd] at result
  exact result

theorem real_metric_complete (sequence : RealSequence) :
    RealSequenceCauchy sequence →
      ∃ limit, RealSequenceConverges sequence limit := by
  intro cauchy
  exact ⟨realCauchyLimitCandidate sequence cauchy,
    realSequenceCauchy_converges cauchy⟩

theorem realSeriesSummable_iff_partialSum_cauchy (terms : RealSequence) :
    RealSeriesSummable terms ↔ RealSequenceCauchy (realPartialSum terms) := by
  constructor
  · intro summable
    obtain ⟨sum, converges⟩ := summable
    exact realSequenceConverges_cauchy converges
  · intro cauchy
    obtain ⟨sum, converges⟩ := real_metric_complete (realPartialSum terms) cauchy
    exact ⟨sum, converges⟩

theorem realSeriesAbsolutelySummable_implies_summable
    {terms : RealSequence}
    (absoluteSummable : RealSeriesAbsolutelySummable terms) :
    RealSeriesSummable terms := by
  obtain ⟨absoluteSum, absoluteConverges⟩ := absoluteSummable
  have absolutePartialCauchy :=
    realSequenceConverges_cauchy absoluteConverges
  have bundledAbsoluteCauchy :
      RealSequenceCauchy (fun index => (realAbsPartialSum terms index).value) := by
    intro epsilon epsilonPositive
    obtain ⟨threshold, eventuallyClose⟩ :=
      absolutePartialCauchy epsilon epsilonPositive
    refine ⟨threshold, ?_⟩
    intro first second firstLarge secondLarge
    change realLE
      (realDist (realAbsPartialSum terms first).value
        (realAbsPartialSum terms second).value).value
      (rationalToReal epsilon)
    rw [realAbsPartialSum_value, realAbsPartialSum_value]
    exact eventuallyClose first second firstLarge secondLarge
  have partialCauchy : RealSequenceCauchy (realPartialSum terms) := by
    intro epsilon epsilonPositive
    obtain ⟨threshold, eventuallyClose⟩ :=
      bundledAbsoluteCauchy epsilon epsilonPositive
    refine ⟨threshold, ?_⟩
    intro first second firstLarge secondLarge
    exact realLE_trans
      (realDist_partialSum_le_absPartialSum_dist terms first second)
      (eventuallyClose first second firstLarge secondLarge)
  exact (realSeriesSummable_iff_partialSum_cauchy terms).mpr partialCauchy

theorem realSeriesAbsolutelyConverges_has_sum
    {terms : RealSequence} {absoluteSum : IncReal}
    (absoluteConverges : RealSeriesAbsolutelyConverges terms absoluteSum) :
    ∃ sum, RealSeriesConverges terms sum :=
  realSeriesAbsolutelySummable_implies_summable
    ⟨absoluteSum, absoluteConverges⟩

theorem realSeries_comparison
    {smaller larger : RealSequence}
    (smallerNonnegative : ∀ index, realLE realZero (smaller index))
    (largerNonnegative : ∀ index, realLE realZero (larger index))
    (dominated : ∀ index, realLE (smaller index) (larger index))
    (largerSummable : RealSeriesSummable larger) :
    RealSeriesSummable smaller := by
  have largerCauchy :=
    (realSeriesSummable_iff_partialSum_cauchy larger).mp largerSummable
  have smallerCauchy : RealSequenceCauchy (realPartialSum smaller) := by
    intro epsilon epsilonPositive
    obtain ⟨threshold, eventuallyClose⟩ := largerCauchy epsilon epsilonPositive
    refine ⟨threshold, ?_⟩
    intro first second firstLarge secondLarge
    exact realLE_trans
      (realDist_partialSum_le_dominating
        smallerNonnegative largerNonnegative dominated first second)
      (eventuallyClose first second firstLarge secondLarge)
  exact (realSeriesSummable_iff_partialSum_cauchy smaller).mpr smallerCauchy

theorem realSeries_absolute_comparison
    {terms majorant : RealSequence}
    (majorantNonnegative : ∀ index, realLE realZero (majorant index))
    (dominated : ∀ index,
      realLE (realAbs (terms index)).value (majorant index))
    (majorantSummable : RealSeriesSummable majorant) :
    RealSeriesAbsolutelySummable terms := by
  have absoluteSummable := realSeries_comparison
    (smaller := fun index => (realAbs (terms index)).value)
    (larger := majorant)
    (fun index => (realAbs (terms index)).nonnegative)
    majorantNonnegative dominated majorantSummable
  exact absoluteSummable

theorem realSeries_absolute_comparison_converges
    {terms majorant : RealSequence}
    (majorantNonnegative : ∀ index, realLE realZero (majorant index))
    (dominated : ∀ index,
      realLE (realAbs (terms index)).value (majorant index))
    (majorantSummable : RealSeriesSummable majorant) :
    RealSeriesSummable terms :=
  realSeriesAbsolutelySummable_implies_summable
    (realSeries_absolute_comparison majorantNonnegative dominated majorantSummable)

theorem realSeries_absolute_comparison_of_absolute
    {smaller larger : RealSequence}
    (dominated : ∀ index,
      realLE (realAbs (smaller index)).value (realAbs (larger index)).value)
    (largerAbsolutelySummable : RealSeriesAbsolutelySummable larger) :
    RealSeriesAbsolutelySummable smaller := by
  exact realSeries_absolute_comparison
    (majorant := fun index => (realAbs (larger index)).value)
    (fun index => (realAbs (larger index)).nonnegative)
    dominated largerAbsolutelySummable

theorem realSeries_ratio_bound
    (terms : RealSequence) (ratio : NonnegativeReal)
    (stepBound : ∀ index,
      realLE (realAbs (terms (Nat.succ index))).value
        (nonnegativeRealMul ratio (realAbs (terms index))).value)
    (index : Nat) :
    realLE (realAbs (terms index)).value
      (nonnegativeRealMul (realAbs (terms 0))
        (nonnegativeRealPow ratio index)).value := by
  induction index with
  | zero =>
      rw [nonnegativeRealPow, nonnegativeRealMul_one_right_bundle]
      exact realLE_refl _
  | succ index induction =>
      have multiplied := nonnegativeRealMul_monotone_right
        (left := ratio) induction
      have chained := realLE_trans (stepBound index) multiplied
      rw [nonnegativeRealPow]
      change realLE (realAbs (terms (Nat.succ index))).value
        (nonnegativeRealMul (realAbs (terms 0))
          (nonnegativeRealMul (nonnegativeRealPow ratio index) ratio)).value
      exact realLE_trans chained (by
        rw [← nonnegativeRealMul_assoc,
          nonnegativeRealMul_comm_bundle ratio (realAbs (terms 0)),
          nonnegativeRealMul_assoc,
          nonnegativeRealMul_comm_bundle ratio
            (nonnegativeRealPow ratio index)]
        exact realLE_refl _)

theorem realSeries_ratio_test
    (terms : RealSequence) (ratio : NonnegativeReal)
    (ratioBelowOne : realLT ratio.value nonnegativeOne.value)
    (stepBound : ∀ index,
      realLE (realAbs (terms (Nat.succ index))).value
        (nonnegativeRealMul ratio (realAbs (terms index))).value) :
    RealSeriesAbsolutelySummable terms := by
  let majorant : RealSequence := fun index =>
    realMul (realAbs (terms 0)).value (realPow ratio.value index)
  have ratioAbs : realAbs ratio.value = ratio :=
    realAbs_of_nonnegative ratio.value ratio.nonnegative
  have ratioPowers := realGeometricSeriesConverges_of_abs_lt_one
    ratio.value (by simpa [ratioAbs] using ratioBelowOne)
  have majorantConverges := realSeriesConverges_mul_const
    (realAbs (terms 0)).value ratioPowers
  have majorantSummable : RealSeriesSummable majorant :=
    ⟨_, majorantConverges⟩
  have majorantNonnegative : ∀ index, realLE realZero (majorant index) := by
    intro index
    dsimp [majorant]
    rw [← nonnegativeRealPow_value ratio index]
    rw [realMul_of_nonnegative
      (realAbs (terms 0)).value (nonnegativeRealPow ratio index).value
      (realAbs (terms 0)).nonnegative
      (nonnegativeRealPow ratio index).nonnegative]
    exact (nonnegativeRealMul
      (realAbs (terms 0)) (nonnegativeRealPow ratio index)).nonnegative
  have dominated : ∀ index,
      realLE (realAbs (terms index)).value (majorant index) := by
    intro index
    have bound := realSeries_ratio_bound terms ratio stepBound index
    dsimp [majorant]
    rw [← nonnegativeRealPow_value ratio index]
    rw [realMul_of_nonnegative
      (realAbs (terms 0)).value (nonnegativeRealPow ratio index).value
      (realAbs (terms 0)).nonnegative
      (nonnegativeRealPow ratio index).nonnegative]
    exact bound
  exact realSeries_absolute_comparison
    majorantNonnegative dominated majorantSummable

def RealClosedInterval (lower upper value : IncReal) : Prop :=
  realLE lower value ∧ realLE value upper

theorem realClosedInterval_nonempty
    {lower upper : IncReal} (ordered : realLE lower upper) :
    ∃ value, RealClosedInterval lower upper value :=
  ⟨lower, realLE_refl lower, ordered⟩

theorem realClosedInterval_contains_lower
    {lower upper : IncReal} (ordered : realLE lower upper) :
    RealClosedInterval lower upper lower :=
  ⟨realLE_refl lower, ordered⟩

theorem realClosedInterval_contains_upper
    {lower upper : IncReal} (ordered : realLE lower upper) :
    RealClosedInterval lower upper upper :=
  ⟨ordered, realLE_refl upper⟩

theorem realClosedInterval_bounded_above
    (lower upper : IncReal) :
    ∃ bound, RealUpperBound (RealClosedInterval lower upper) bound := by
  refine ⟨upper, ?_⟩
  intro value member
  exact member.2

theorem realClosedInterval_bounded_below
    (lower upper : IncReal) :
    ∃ bound, RealLowerBound (RealClosedInterval lower upper) bound := by
  refine ⟨lower, ?_⟩
  intro value member
  exact member.1

noncomputable def realClosedIntervalSup
    (lower upper : IncReal) (ordered : realLE lower upper) : IncReal :=
  realSup (RealClosedInterval lower upper)
    (realClosedInterval_nonempty ordered)
    (realClosedInterval_bounded_above lower upper)

noncomputable def realClosedIntervalInf
    (lower upper : IncReal) (ordered : realLE lower upper) : IncReal :=
  realInf (RealClosedInterval lower upper)
    (realClosedInterval_nonempty ordered)
    (realClosedInterval_bounded_below lower upper)

theorem realClosedIntervalSup_eq_upper
    (lower upper : IncReal) (ordered : realLE lower upper) :
    realClosedIntervalSup lower upper ordered = upper := by
  apply realLE_antisymm
  · apply realSup_is_least
    intro value member
    exact member.2
  · apply realSup_is_upper_bound
    exact realClosedInterval_contains_upper ordered

theorem realClosedIntervalInf_eq_lower
    (lower upper : IncReal) (ordered : realLE lower upper) :
    realClosedIntervalInf lower upper ordered = lower := by
  apply realLE_antisymm
  · apply realInf_is_lower_bound
    exact realClosedInterval_contains_lower ordered
  · apply realInf_is_greatest
    intro value member
    exact member.1

theorem realClosedInterval_nested
    {outerLower innerLower innerUpper outerUpper value : IncReal}
    (lowerOrdered : realLE outerLower innerLower)
    (upperOrdered : realLE innerUpper outerUpper)
    (member : RealClosedInterval innerLower innerUpper value) :
    RealClosedInterval outerLower outerUpper value :=
  ⟨realLE_trans lowerOrdered member.1,
    realLE_trans member.2 upperOrdered⟩

theorem realClosedInterval_antisymm
    {lower upper : IncReal} (ordered : realLE lower upper)
    {value : IncReal}
    (member : RealClosedInterval upper lower value) :
    lower = upper := by
  exact realLE_antisymm ordered (realLE_trans member.1 member.2)

def RealContinuousOn
    (function : IncReal → IncReal) (domain : IncReal → Prop) : Prop :=
  ∀ point, domain point → RealContinuousAt function point

def RealDifferentiableOn
    (function : IncReal → IncReal) (domain : IncReal → Prop) : Prop :=
  ∀ point, domain point → RealDifferentiableAt function point

theorem realDifferentiableOn_continuousOn
    {function : IncReal → IncReal} {domain : IncReal → Prop}
    (differentiable : RealDifferentiableOn function domain) :
    RealContinuousOn function domain := by
  intro point member
  obtain ⟨derivative, hasDerivative⟩ := differentiable point member
  exact realHasDerivativeAt_continuousAt hasDerivative

theorem realPolynomial_differentiable
    (coefficients : List IncReal) :
    RealDifferentiable (realPolynomialEval coefficients) := by
  intro point
  exact ⟨realPolynomialDerivativeEval coefficients point,
    realHasDerivativeAt_polynomial coefficients point⟩

theorem realPolynomial_differentiableOn
    (coefficients : List IncReal) (domain : IncReal → Prop) :
    RealDifferentiableOn (realPolynomialEval coefficients) domain := by
  intro point _
  exact realPolynomial_differentiable coefficients point

theorem realPolynomial_continuousOn
    (coefficients : List IncReal) (domain : IncReal → Prop) :
    RealContinuousOn (realPolynomialEval coefficients) domain :=
  realDifferentiableOn_continuousOn
    (realPolynomial_differentiableOn coefficients domain)

theorem realPolynomial_continuousOn_closedInterval
    (coefficients : List IncReal) (lower upper : IncReal) :
    RealContinuousOn (realPolynomialEval coefficients)
      (RealClosedInterval lower upper) :=
  realPolynomial_continuousOn coefficients
    (RealClosedInterval lower upper)

def RealSubsequence (indices : Nat → Nat) : Prop :=
  ∀ {left right}, left < right → indices left < indices right

theorem realSubsequence_index_large
    {indices : Nat → Nat} (subsequence : RealSubsequence indices) :
    ∀ index, index ≤ indices index := by
  intro index
  induction index with
  | zero => exact Nat.zero_le _
  | succ index induction =>
      have step := subsequence (Nat.lt_succ_self index)
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt induction step)

theorem realSubsequence_monotone
    {indices : Nat → Nat} (subsequence : RealSubsequence indices)
    {left right : Nat} (ordered : left ≤ right) :
    indices left ≤ indices right := by
  rcases Nat.lt_or_eq_of_le ordered with strict | equal
  · exact Nat.le_of_lt (subsequence strict)
  · subst right
    exact Nat.le_refl _

theorem realSequenceConverges_subsequence
    {sequence : RealSequence} {limit : IncReal}
    (converges : RealSequenceConverges sequence limit)
    {indices : Nat → Nat} (subsequence : RealSubsequence indices) :
    RealSequenceConverges (fun index => sequence (indices index)) limit := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := converges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  apply eventuallyClose
  exact Nat.le_trans (realSubsequence_index_large subsequence threshold)
    (realSubsequence_monotone subsequence indexLarge)

theorem realSequenceCauchy_subsequence
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence)
    {indices : Nat → Nat} (subsequence : RealSubsequence indices) :
    RealSequenceCauchy (fun index => sequence (indices index)) := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ := cauchy epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro left right leftLarge rightLarge
  apply eventuallyClose
  · exact Nat.le_trans (realSubsequence_index_large subsequence threshold)
      (realSubsequence_monotone subsequence leftLarge)
  · exact Nat.le_trans (realSubsequence_index_large subsequence threshold)
      (realSubsequence_monotone subsequence rightLarge)

theorem realSubsequence_id : RealSubsequence (fun index => index) := by
  intro left right strict
  exact strict

theorem realSubsequence_comp
    {first second : Nat → Nat}
    (firstSubsequence : RealSubsequence first)
    (secondSubsequence : RealSubsequence second) :
    RealSubsequence (fun index => first (second index)) := by
  intro left right strict
  exact firstSubsequence (secondSubsequence strict)

theorem realSequenceConverges_hasConvergentSubsequence
    {sequence : RealSequence} {limit : IncReal}
    (converges : RealSequenceConverges sequence limit) :
    ∃ indices : Nat → Nat, RealSubsequence indices ∧
      ∃ subsequentialLimit, RealSequenceConverges
        (fun index => sequence (indices index)) subsequentialLimit := by
  exact ⟨fun index => index, realSubsequence_id, limit, converges⟩

theorem realSequenceCauchy_subsequence_converges
    {sequence : RealSequence} (cauchy : RealSequenceCauchy sequence)
    {indices : Nat → Nat} (subsequence : RealSubsequence indices) :
    ∃ limit, RealSequenceConverges
      (fun index => sequence (indices index)) limit :=
  real_metric_complete (fun index => sequence (indices index))
    (realSequenceCauchy_subsequence cauchy subsequence)

def RealHasConvergentSubsequence (sequence : RealSequence) : Prop :=
  ∃ indices : Nat → Nat, RealSubsequence indices ∧
    ∃ limit, RealSequenceConverges
      (fun index => sequence (indices index)) limit

def RealSequentiallyCompact (domain : IncReal → Prop) : Prop :=
  ∀ sequence : RealSequence,
    (∀ index, domain (sequence index)) →
    ∃ indices : Nat → Nat, RealSubsequence indices ∧
      ∃ limit, domain limit ∧
        RealSequenceConverges (fun index => sequence (indices index)) limit

def RealSequenceNondecreasing (sequence : RealSequence) : Prop :=
  ∀ {left right}, left ≤ right → realLE (sequence left) (sequence right)

def RealSequenceNonincreasing (sequence : RealSequence) : Prop :=
  ∀ {left right}, left ≤ right → realLE (sequence right) (sequence left)

theorem realSequenceNondecreasing_converges
    {sequence : RealSequence}
    (monotone : RealSequenceNondecreasing sequence)
    (bounded : ∃ upper, RealSequenceUpperBound sequence upper) :
    RealSequenceConverges sequence
      (realSequenceTailSup sequence 0 bounded) := by
  intro epsilon epsilonPositive
  let supremum := realSequenceTailSup sequence 0 bounded
  obtain ⟨inside, outside, insideMember, outsideNotMember, outsideStep⟩ :=
    supremum.boundary_approximation epsilonPositive
  change ∃ value, RealSequenceTail sequence 0 value ∧
      value.lower inside at insideMember
  obtain ⟨value, valueInTail, insideBelowValue⟩ := insideMember
  obtain ⟨threshold, _, valueEqual⟩ := valueInTail
  subst value
  have supremumBelowOutside :
      realLE supremum (rationalToReal outside) := by
    intro rational member
    exact supremum.lt_of_lower_of_not_lower member outsideNotMember
  have insideBelowSequence :
      realLE (rationalToReal inside) (sequence threshold) :=
    (rationalToReal_lt_of_lower (sequence threshold) insideBelowValue).1
  have outsideBelowSequencePlus :
      realLE (rationalToReal outside)
        (realAdd (sequence threshold) (rationalToReal epsilon)) := by
    rw [outsideStep, ← realAdd_rationalToReal]
    exact realAdd_monotone insideBelowSequence (realLE_refl _)
  have supremumBelowThresholdPlus :
      realLE supremum
        (realAdd (sequence threshold) (rationalToReal epsilon)) :=
    realLE_trans supremumBelowOutside outsideBelowSequencePlus
  let radius : NonnegativeReal :=
    { value := rationalToReal epsilon
      nonnegative := (rationalToReal_le_iff _ _).mpr epsilonPositive.1 }
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  have sequenceOrdered := monotone indexLarge
  have sequenceBelowSupremum : realLE (sequence index) supremum :=
    realSequence_le_tailSup bounded (Nat.zero_le index)
  have supremumBelowIndexPlus :
      realLE supremum
        (realAdd (sequence index) radius.value) := by
    have plusOrdered := realAdd_monotone_left
      (right := rationalToReal epsilon) sequenceOrdered
    exact realLE_trans supremumBelowThresholdPlus (by
      simpa only [radius] using plusOrdered)
  exact realDist_le_of_le_of_le_add radius
    sequenceBelowSupremum supremumBelowIndexPlus

theorem realSequenceNonincreasing_converges
    {sequence : RealSequence}
    (monotone : RealSequenceNonincreasing sequence)
    (bounded : ∃ lower, RealSequenceLowerBound sequence lower) :
    ∃ limit, RealSequenceConverges sequence limit := by
  let negated : RealSequence := fun index => realNeg (sequence index)
  have negatedMonotone : RealSequenceNondecreasing negated := by
    intro left right ordered
    exact realNeg_order_reverse (monotone ordered)
  have negatedBounded : ∃ upper, RealSequenceUpperBound negated upper := by
    obtain ⟨lower, isLower⟩ := bounded
    refine ⟨realNeg lower, ?_⟩
    intro index
    exact realNeg_order_reverse (isLower index)
  have negatedConverges := realSequenceNondecreasing_converges
    negatedMonotone negatedBounded
  have restoredConverges := realSequenceConverges_neg negatedConverges
  refine ⟨realNeg (realSequenceTailSup negated 0 negatedBounded), ?_⟩
  simpa only [negated, realNeg_neg] using restoredConverges

theorem realSequenceNonincreasing_converges_to_neg_tailSup
    {sequence : RealSequence}
    (monotone : RealSequenceNonincreasing sequence)
    (bounded : ∃ lower, RealSequenceLowerBound sequence lower) :
    let negated : RealSequence := fun index => realNeg (sequence index)
    let negatedBounded : ∃ upper, RealSequenceUpperBound negated upper := by
      obtain ⟨lower, isLower⟩ := bounded
      exact ⟨realNeg lower, fun index =>
        realNeg_order_reverse (isLower index)⟩
    RealSequenceConverges sequence
      (realNeg (realSequenceTailSup negated 0 negatedBounded)) := by
  dsimp only
  let negated : RealSequence := fun index => realNeg (sequence index)
  have negatedMonotone : RealSequenceNondecreasing negated := by
    intro left right ordered
    exact realNeg_order_reverse (monotone ordered)
  let negatedBounded : ∃ upper, RealSequenceUpperBound negated upper := by
    obtain ⟨lower, isLower⟩ := bounded
    exact ⟨realNeg lower, fun index =>
      realNeg_order_reverse (isLower index)⟩
  have negatedConverges := realSequenceNondecreasing_converges
    negatedMonotone negatedBounded
  have restored := realSequenceConverges_neg negatedConverges
  simpa only [negated, realNeg_neg] using restored

theorem realSequenceMonotone_bounded_converges
    {sequence : RealSequence}
    (monotone : RealSequenceNondecreasing sequence ∨
      RealSequenceNonincreasing sequence)
    (boundedBelow : ∃ lower, RealSequenceLowerBound sequence lower)
    (boundedAbove : ∃ upper, RealSequenceUpperBound sequence upper) :
    ∃ limit, RealSequenceConverges sequence limit := by
  rcases monotone with increasing | decreasing
  · exact ⟨realSequenceTailSup sequence 0 boundedAbove,
      realSequenceNondecreasing_converges increasing boundedAbove⟩
  · exact realSequenceNonincreasing_converges decreasing boundedBelow

def RealSequencePeak (sequence : RealSequence) (index : Nat) : Prop :=
  ∀ later, index < later → realLE (sequence later) (sequence index)

noncomputable def realPeakSubsequenceIndices
    (sequence : RealSequence)
    (abundant : ∀ start, ∃ index, start ≤ index ∧
      RealSequencePeak sequence index) : Nat → Nat
  | 0 => Classical.choose (abundant 0)
  | Nat.succ order =>
      Classical.choose
        (abundant (Nat.succ
          (realPeakSubsequenceIndices sequence abundant order)))

theorem realPeakSubsequenceIndices_spec
    (sequence : RealSequence)
    (abundant : ∀ start, ∃ index, start ≤ index ∧
      RealSequencePeak sequence index) (order : Nat) :
    (match order with
      | 0 => 0
      | Nat.succ previous => Nat.succ
          (realPeakSubsequenceIndices sequence abundant previous)) ≤
        realPeakSubsequenceIndices sequence abundant order ∧
      RealSequencePeak sequence
        (realPeakSubsequenceIndices sequence abundant order) := by
  cases order with
  | zero => exact Classical.choose_spec (abundant 0)
  | succ previous =>
      exact Classical.choose_spec
        (abundant (Nat.succ
          (realPeakSubsequenceIndices sequence abundant previous)))

theorem realPeakSubsequence_isSubsequence
    (sequence : RealSequence)
    (abundant : ∀ start, ∃ index, start ≤ index ∧
      RealSequencePeak sequence index) :
    RealSubsequence (realPeakSubsequenceIndices sequence abundant) := by
  intro left right strict
  induction right with
  | zero => exact False.elim (Nat.not_lt_zero _ strict)
  | succ right induction =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ strict) with before | equal
      · exact Nat.lt_trans (induction before)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
            (realPeakSubsequenceIndices_spec sequence abundant
              (Nat.succ right)).1)
      · subst left
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
          (realPeakSubsequenceIndices_spec sequence abundant
            (Nat.succ right)).1

theorem realPeakSubsequence_nonincreasing
    (sequence : RealSequence)
    (abundant : ∀ start, ∃ index, start ≤ index ∧
      RealSequencePeak sequence index) :
    RealSequenceNonincreasing
      (fun order => sequence
        (realPeakSubsequenceIndices sequence abundant order)) := by
  intro left right ordered
  rcases Nat.lt_or_eq_of_le ordered with strict | equal
  · exact (realPeakSubsequenceIndices_spec sequence abundant left).2 _
      (realPeakSubsequence_isSubsequence sequence abundant strict)
  · subst right
    exact realLE_refl _

noncomputable def realRisingNext
    (sequence : RealSequence) (start : Nat)
    (noPeak : ∀ index, start ≤ index →
      ¬ RealSequencePeak sequence index) (index : Nat) : Nat :=
  if indexLarge : start ≤ index then
    Classical.choose (show ∃ later, index < later ∧
        ¬ realLE (sequence later) (sequence index) from by
      have notPeak := noPeak index indexLarge
      apply Classical.byContradiction
      intro none
      apply notPeak
      intro later laterLarge
      by_cases ordered : realLE (sequence later) (sequence index)
      · exact ordered
      · exact False.elim (none ⟨later, laterLarge, ordered⟩))
  else Nat.succ index

theorem realRisingNext_spec
    (sequence : RealSequence) (start : Nat)
    (noPeak : ∀ index, start ≤ index →
      ¬ RealSequencePeak sequence index)
    {index : Nat} (indexLarge : start ≤ index) :
    index < realRisingNext sequence start noPeak index ∧
      realLE (sequence index)
        (sequence (realRisingNext sequence start noPeak index)) := by
  rw [realRisingNext, dif_pos indexLarge]
  have chosen := Classical.choose_spec (show ∃ later, index < later ∧
      ¬ realLE (sequence later) (sequence index) from by
    have notPeak := noPeak index indexLarge
    apply Classical.byContradiction
    intro none
    apply notPeak
    intro later laterLarge
    by_cases ordered : realLE (sequence later) (sequence index)
    · exact ordered
    · exact False.elim (none ⟨later, laterLarge, ordered⟩))
  refine ⟨chosen.1, ?_⟩
  rcases realLE_total (sequence index)
      (sequence (Classical.choose _)) with ordered | reverse
  · exact ordered
  · exact False.elim (chosen.2 reverse)

noncomputable def realRisingSubsequenceIndices
    (sequence : RealSequence) (start : Nat)
    (noPeak : ∀ index, start ≤ index →
      ¬ RealSequencePeak sequence index) : Nat → Nat
  | 0 => start
  | Nat.succ order => realRisingNext sequence start noPeak
      (realRisingSubsequenceIndices sequence start noPeak order)

theorem realRisingSubsequenceIndices_large
    (sequence : RealSequence) (start : Nat)
    (noPeak : ∀ index, start ≤ index →
      ¬ RealSequencePeak sequence index) :
    ∀ order, start ≤
      realRisingSubsequenceIndices sequence start noPeak order := by
  intro order
  induction order with
  | zero => exact Nat.le_refl _
  | succ order induction =>
      exact Nat.le_trans induction (Nat.le_of_lt
        (realRisingNext_spec sequence start noPeak induction).1)

theorem realRisingSubsequence_step
    (sequence : RealSequence) (start : Nat)
    (noPeak : ∀ index, start ≤ index →
      ¬ RealSequencePeak sequence index) (order : Nat) :
    realRisingSubsequenceIndices sequence start noPeak order <
      realRisingSubsequenceIndices sequence start noPeak (Nat.succ order) ∧
    realLE
      (sequence (realRisingSubsequenceIndices sequence start noPeak order))
      (sequence (realRisingSubsequenceIndices sequence start noPeak
        (Nat.succ order))) := by
  exact realRisingNext_spec sequence start noPeak
    (realRisingSubsequenceIndices_large sequence start noPeak order)

theorem realRisingSubsequence_isSubsequence
    (sequence : RealSequence) (start : Nat)
    (noPeak : ∀ index, start ≤ index →
      ¬ RealSequencePeak sequence index) :
    RealSubsequence
      (realRisingSubsequenceIndices sequence start noPeak) := by
  intro left right strict
  induction right with
  | zero => exact False.elim (Nat.not_lt_zero _ strict)
  | succ right induction =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ strict) with before | equal
      · exact Nat.lt_trans (induction before)
          (realRisingSubsequence_step sequence start noPeak right).1
      · subst left
        exact (realRisingSubsequence_step sequence start noPeak right).1

theorem realRisingSubsequence_nondecreasing
    (sequence : RealSequence) (start : Nat)
    (noPeak : ∀ index, start ≤ index →
      ¬ RealSequencePeak sequence index) :
    RealSequenceNondecreasing
      (fun order => sequence
        (realRisingSubsequenceIndices sequence start noPeak order)) := by
  intro left right ordered
  induction right with
  | zero =>
      have equal : left = 0 := Nat.eq_zero_of_le_zero ordered
      subst left
      exact realLE_refl _
  | succ right induction =>
      rcases Nat.lt_or_eq_of_le ordered with strict | equal
      · have leftBefore : left ≤ right := Nat.le_of_lt_succ strict
        exact realLE_trans (induction leftBefore)
          (realRisingSubsequence_step sequence start noPeak right).2
      · subst left
        exact realLE_refl _

theorem realSequence_has_monotone_subsequence (sequence : RealSequence) :
    ∃ indices : Nat → Nat, RealSubsequence indices ∧
      (RealSequenceNondecreasing (fun order => sequence (indices order)) ∨
       RealSequenceNonincreasing (fun order => sequence (indices order))) := by
  classical
  by_cases abundant : ∀ start, ∃ index, start ≤ index ∧
      RealSequencePeak sequence index
  · exact ⟨realPeakSubsequenceIndices sequence abundant,
      realPeakSubsequence_isSubsequence sequence abundant,
      Or.inr (realPeakSubsequence_nonincreasing sequence abundant)⟩
  · have eventuallyNoPeak : ∃ start, ∀ index, start ≤ index →
        ¬ RealSequencePeak sequence index := by
      apply Classical.byContradiction
      intro none
      apply abundant
      intro start
      apply Classical.byContradiction
      intro noIndex
      apply none
      refine ⟨start, ?_⟩
      intro index indexLarge peak
      exact noIndex ⟨index, indexLarge, peak⟩
    obtain ⟨start, noPeak⟩ := eventuallyNoPeak
    exact ⟨realRisingSubsequenceIndices sequence start noPeak,
      realRisingSubsequence_isSubsequence sequence start noPeak,
      Or.inl (realRisingSubsequence_nondecreasing sequence start noPeak)⟩

theorem realSequence_bounded_has_convergent_subsequence
    (sequence : RealSequence)
    (boundedBelow : ∃ lower, RealSequenceLowerBound sequence lower)
    (boundedAbove : ∃ upper, RealSequenceUpperBound sequence upper) :
    RealHasConvergentSubsequence sequence := by
  obtain ⟨indices, subsequence, monotone⟩ :=
    realSequence_has_monotone_subsequence sequence
  have subsequenceBoundedBelow : ∃ lower,
      RealSequenceLowerBound (fun order => sequence (indices order)) lower := by
    obtain ⟨lower, isLower⟩ := boundedBelow
    exact ⟨lower, fun order => isLower (indices order)⟩
  have subsequenceBoundedAbove : ∃ upper,
      RealSequenceUpperBound (fun order => sequence (indices order)) upper := by
    obtain ⟨upper, isUpper⟩ := boundedAbove
    exact ⟨upper, fun order => isUpper (indices order)⟩
  obtain ⟨limit, converges⟩ := realSequenceMonotone_bounded_converges
    monotone subsequenceBoundedBelow subsequenceBoundedAbove
  exact ⟨indices, subsequence, limit, converges⟩

theorem realClosedInterval_sequence_has_convergent_subsequence
    {lower upper : IncReal} {sequence : RealSequence}
    (inInterval : ∀ index,
      RealClosedInterval lower upper (sequence index)) :
    RealHasConvergentSubsequence sequence := by
  apply realSequence_bounded_has_convergent_subsequence sequence
  · exact ⟨lower, fun index => (inInterval index).1⟩
  · exact ⟨upper, fun index => (inInterval index).2⟩

theorem realClosedInterval_sequentiallyCompact
    (lower upper : IncReal) :
    RealSequentiallyCompact (RealClosedInterval lower upper) := by
  intro sequence inInterval
  obtain ⟨indices, subsequence, monotone⟩ :=
    realSequence_has_monotone_subsequence sequence
  let extracted : RealSequence := fun order => sequence (indices order)
  have extractedBoundedBelow : ∃ bound,
      RealSequenceLowerBound extracted bound :=
    ⟨lower, fun order => (inInterval (indices order)).1⟩
  have extractedBoundedAbove : ∃ bound,
      RealSequenceUpperBound extracted bound :=
    ⟨upper, fun order => (inInterval (indices order)).2⟩
  rcases monotone with increasing | decreasing
  · let limit := realSequenceTailSup extracted 0 extractedBoundedAbove
    have converges : RealSequenceConverges extracted limit :=
      realSequenceNondecreasing_converges increasing extractedBoundedAbove
    have lowerBound : realLE lower limit := by
      exact realLE_trans (inInterval (indices 0)).1
        (realSequence_le_tailSup extractedBoundedAbove (Nat.zero_le 0))
    have upperBound : realLE limit upper := by
      apply realSup_is_least
      intro value member
      obtain ⟨index, _, equal⟩ := member
      subst value
      exact (inInterval (indices index)).2
    exact ⟨indices, subsequence, limit, ⟨lowerBound, upperBound⟩,
      converges⟩
  · let negated : RealSequence := fun order => realNeg (extracted order)
    let negatedBounded : ∃ bound,
        RealSequenceUpperBound negated bound := by
      exact ⟨realNeg lower, fun order =>
        realNeg_order_reverse (inInterval (indices order)).1⟩
    let limit := realNeg
      (realSequenceTailSup negated 0 negatedBounded)
    have converges : RealSequenceConverges extracted limit := by
      simpa only [limit, negated, extracted] using
        (realSequenceNonincreasing_converges_to_neg_tailSup
          decreasing extractedBoundedBelow)
    have supremumBelowNegLower :
        realLE (realSequenceTailSup negated 0 negatedBounded)
          (realNeg lower) := by
      apply realSup_is_least
      intro value member
      obtain ⟨index, _, equal⟩ := member
      subst value
      exact realNeg_order_reverse (inInterval (indices index)).1
    have lowerBound : realLE lower limit := by
      have reversed := realNeg_order_reverse supremumBelowNegLower
      simpa only [limit, realNeg_neg] using reversed
    have negUpperBelowSupremum :
        realLE (realNeg upper)
          (realSequenceTailSup negated 0 negatedBounded) := by
      exact realLE_trans
        (realNeg_order_reverse (inInterval (indices 0)).2)
        (realSequence_le_tailSup negatedBounded (Nat.zero_le 0))
    have upperBound : realLE limit upper := by
      have reversed := realNeg_order_reverse negUpperBelowSupremum
      simpa only [limit, realNeg_neg] using reversed
    exact ⟨indices, subsequence, limit, ⟨lowerBound, upperBound⟩,
      converges⟩

theorem realContinuousAt_sequentiallyContinuousAt
    {function : IncReal → IncReal} {point : IncReal}
    (continuous : RealContinuousAt function point) :
    RealSequentiallyContinuousAt function point := by
  intro sequence converges
  intro epsilon epsilonPositive
  obtain ⟨inputRadius, inputRadiusPositive, eventuallyMapped⟩ :=
    continuous epsilon epsilonPositive
  obtain ⟨threshold, eventuallyInput⟩ :=
    converges inputRadius inputRadiusPositive
  refine ⟨threshold, ?_⟩
  intro index indexLarge
  exact eventuallyMapped (sequence index)
    (eventuallyInput index indexLarge)

def RealImage
    (function : IncReal → IncReal) (domain : IncReal → Prop)
    (value : IncReal) : Prop :=
  ∃ source, domain source ∧ function source = value

theorem realSequentiallyCompact_continuous_image
    {function : IncReal → IncReal} {domain : IncReal → Prop}
    (compact : RealSequentiallyCompact domain)
    (continuous : RealContinuousOn function domain) :
    RealSequentiallyCompact (RealImage function domain) := by
  classical
  intro imageSequence inImage
  let sourceSequence : RealSequence := fun index =>
    Classical.choose (inImage index)
  have sourceInDomain : ∀ index, domain (sourceSequence index) := by
    intro index
    exact (Classical.choose_spec (inImage index)).1
  have sourceMaps : ∀ index,
      function (sourceSequence index) = imageSequence index := by
    intro index
    exact (Classical.choose_spec (inImage index)).2
  obtain ⟨indices, subsequence, limit, limitInDomain, sourceConverges⟩ :=
    compact sourceSequence sourceInDomain
  have mappedConverges : RealSequenceConverges
      (fun order => function (sourceSequence (indices order)))
      (function limit) :=
    (realContinuousAt_sequentiallyContinuousAt
      (continuous limit limitInDomain)) _ sourceConverges
  refine ⟨indices, subsequence, function limit,
    ⟨limit, limitInDomain, rfl⟩, ?_⟩
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyClose⟩ :=
    mappedConverges epsilon epsilonPositive
  refine ⟨threshold, ?_⟩
  intro order orderLarge
  change realLE
    (realDist (imageSequence (indices order)) (function limit)).value
    (rationalToReal epsilon)
  rw [← sourceMaps (indices order)]
  exact eventuallyClose order orderLarge

/-! ### Extreme value theorem (cycle 42)

The remaining roadmap step towards the extreme value theorem: any nonempty
sequentially compact set of reals is bounded above and below, and achieves
its supremum and infimum; specialised to a continuous image of a closed
interval this gives that a continuous function on a closed interval attains
a maximum and a minimum. -/

theorem realSup_approx (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper)
    {epsilon : IncRational} (epsilonPositive : rationalLT (rationalOfInteger 0) epsilon) :
    ∃ value, family value ∧
      realLE (realDist value (realSup family nonempty bounded)).value
        (rationalToReal epsilon) := by
  let supremum := realSup family nonempty bounded
  obtain ⟨inside, outside, insideMember, outsideNotMember, outsideStep⟩ :=
    supremum.boundary_approximation epsilonPositive
  obtain ⟨value, valueMember, insideBelowValue⟩ := insideMember
  refine ⟨value, valueMember, ?_⟩
  have valueBelowSup : realLE value supremum :=
    realSup_is_upper_bound family nonempty bounded value valueMember
  have supBelowOutside : realLE supremum (rationalToReal outside) := by
    intro rational member
    exact supremum.lt_of_lower_of_not_lower member outsideNotMember
  have insideBelowValue' : realLE (rationalToReal inside) value :=
    (rationalToReal_lt_of_lower value insideBelowValue).1
  have outsideBelowValuePlus : realLE (rationalToReal outside)
      (realAdd value (rationalToReal epsilon)) := by
    rw [outsideStep, ← realAdd_rationalToReal]
    exact realAdd_monotone insideBelowValue' (realLE_refl _)
  have supBelowValuePlus :
      realLE supremum (realAdd value (rationalToReal epsilon)) :=
    realLE_trans supBelowOutside outsideBelowValuePlus
  exact realDist_le_of_le_of_le_add
    ⟨rationalToReal epsilon, (rationalToReal_le_iff _ _).mpr epsilonPositive.1⟩
    valueBelowSup supBelowValuePlus

/-- An explicit sequence of `family` members approximating the supremum to
within `1 / (n + 1)`, built from `realSup_approx` indexed by the rational
null sequence `rationalNatSuccInv`. -/
noncomputable def realSupApproxSequence (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper) : RealSequence :=
  fun n => Classical.choose
    (realSup_approx family nonempty bounded (rationalNatSuccInv_pos n))

theorem realSupApproxSequence_mem (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper) (n : Nat) :
    family (realSupApproxSequence family nonempty bounded n) :=
  (Classical.choose_spec
    (realSup_approx family nonempty bounded (rationalNatSuccInv_pos n))).1

theorem realSupApproxSequence_dist (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper) (n : Nat) :
    realLE (realDist (realSupApproxSequence family nonempty bounded n)
        (realSup family nonempty bounded)).value
      (rationalToReal (rationalNatSuccInv n)) :=
  (Classical.choose_spec
    (realSup_approx family nonempty bounded (rationalNatSuccInv_pos n))).2

theorem realSupApproxSequence_converges (family : IncReal → Prop)
    (nonempty : ∃ value, family value)
    (bounded : ∃ upper, RealUpperBound family upper) :
    RealSequenceConverges (realSupApproxSequence family nonempty bounded)
      (realSup family nonempty bounded) := by
  intro epsilon epsilonPositive
  obtain ⟨threshold, eventuallyLe⟩ := rationalNatSuccInv_eventually_le epsilonPositive
  refine ⟨threshold, ?_⟩
  intro n thresholdLe
  have distBound := realSupApproxSequence_dist family nonempty bounded n
  have radiusBound : realLE (rationalToReal (rationalNatSuccInv n))
      (rationalToReal epsilon) :=
    (rationalToReal_le_iff _ _).mpr (eventuallyLe n thresholdLe)
  exact realLE_trans distBound radiusBound

/-- A nonempty sequentially compact set of reals is bounded above. If it were
not, the Archimedean embedding of the naturals would witness an unbounded
sequence inside the set, but every convergent subsequence a compactness
witness extracts is Cauchy, hence bounded -- contradiction. -/
theorem realSequentiallyCompact_bounded_above
    {domain : IncReal → Prop}
    (nonempty : ∃ value, domain value)
    (compact : RealSequentiallyCompact domain) :
    ∃ upper, RealUpperBound domain upper := by
  classical
  apply Classical.byContradiction
  intro notExists
  have notBounded : ∀ upper, ¬ RealUpperBound domain upper := by
    intro upper isUpper
    exact notExists ⟨upper, isUpper⟩
  have witness : ∀ candidate : IncReal,
      ∃ value, domain value ∧ realLE candidate value := by
    intro candidate
    have notUpper := notBounded candidate
    have witnessExists :
        ∃ value, domain value ∧ ¬ realLE value candidate := by
      apply Classical.byContradiction
      intro noWitness
      apply notUpper
      intro value valueMem
      apply Classical.byContradiction
      intro notLe
      exact noWitness ⟨value, valueMem, notLe⟩
    obtain ⟨value, valueMem, notLe⟩ := witnessExists
    refine ⟨value, valueMem, ?_⟩
    rcases realLE_total value candidate with le | ge
    · exact absurd le notLe
    · exact ge
  let sequence : RealSequence := fun n =>
    Classical.choose (witness (rationalToReal (rationalOfInteger (Int.ofNat n))))
  have sequenceMem : ∀ n, domain (sequence n) := fun n =>
    (Classical.choose_spec
      (witness (rationalToReal (rationalOfInteger (Int.ofNat n))))).1
  have sequenceAbove : ∀ n, realLE
      (rationalToReal (rationalOfInteger (Int.ofNat n))) (sequence n) := fun n =>
    (Classical.choose_spec
      (witness (rationalToReal (rationalOfInteger (Int.ofNat n))))).2
  obtain ⟨indices, subsequence, limit, limitInDomain, converges⟩ :=
    compact sequence sequenceMem
  have cauchy := realSequenceConverges_cauchy converges
  obtain ⟨upper, isUpper⟩ := realSequenceCauchy_bounded_above cauchy
  obtain ⟨count, countAbove⟩ := real_archimedean_nat_upper upper
  have indicesLarge : count ≤ indices count :=
    realSubsequence_index_large subsequence count
  have embedMono : realLE (rationalToReal (rationalOfInteger (Int.ofNat count)))
      (rationalToReal (rationalOfInteger (Int.ofNat (indices count)))) :=
    (rationalToReal_le_iff _ _).mpr
      ((rationalOfInteger_le_iff _ _).mpr (Int.ofNat_le.mpr indicesLarge))
  have upperBelowEmbed : realLT upper
      (rationalToReal (rationalOfInteger (Int.ofNat (indices count)))) :=
    realLT_of_lt_of_le countAbove embedMono
  have embedBelowExtracted : realLE
      (rationalToReal (rationalOfInteger (Int.ofNat (indices count))))
      (sequence (indices count)) :=
    sequenceAbove (indices count)
  have upperBelowExtracted : realLT upper (sequence (indices count)) :=
    realLT_of_lt_of_le upperBelowEmbed embedBelowExtracted
  exact realLT_irrefl upper
    (realLT_of_lt_of_le upperBelowExtracted (isUpper count))

/-- A nonempty sequentially compact set of reals contains its own supremum:
the sup-approximating sequence converges to the supremum by construction, so
any convergent subsequence a compactness witness extracts must (by
uniqueness of limits) converge to that same supremum -- and compactness
requires that subsequence's limit to lie in the set. -/
theorem realSequentiallyCompact_sup_mem
    {domain : IncReal → Prop}
    (compact : RealSequentiallyCompact domain)
    (nonempty : ∃ value, domain value)
    (bounded : ∃ upper, RealUpperBound domain upper) :
    domain (realSup domain nonempty bounded) := by
  obtain ⟨indices, subsequence, limit, limitInDomain, converges⟩ :=
    compact (realSupApproxSequence domain nonempty bounded)
      (realSupApproxSequence_mem domain nonempty bounded)
  have alsoConverges : RealSequenceConverges
      (fun order => realSupApproxSequence domain nonempty bounded (indices order))
      (realSup domain nonempty bounded) :=
    realSequenceConverges_subsequence
      (realSupApproxSequence_converges domain nonempty bounded) subsequence
  have limitEq : limit = realSup domain nonempty bounded :=
    realSequence_limit_unique converges alsoConverges
  rw [limitEq] at limitInDomain
  exact limitInDomain

theorem realContinuousAt_neg (point : IncReal) :
    RealContinuousAt realNeg point :=
  realFunctionLimitAt_neg (realFunctionLimitAt_id point)

theorem realContinuousOn_neg (domain : IncReal → Prop) :
    RealContinuousOn realNeg domain :=
  fun point _ => realContinuousAt_neg point

/-- Sequential compactness transports across the (everywhere continuous)
negation map, so it holds for the pointwise negation of a compact set too. -/
theorem realSequentiallyCompact_negFamily
    {domain : IncReal → Prop} (compact : RealSequentiallyCompact domain) :
    RealSequentiallyCompact (RealNegFamily domain) := by
  have imageCompact := realSequentiallyCompact_continuous_image compact
    (realContinuousOn_neg domain)
  intro sequence inNegFamily
  have inImage : ∀ index, RealImage realNeg domain (sequence index) := by
    intro index
    obtain ⟨original, originalMem, eq⟩ := inNegFamily index
    exact ⟨original, originalMem, eq.symm⟩
  obtain ⟨indices, subsequence, limit, limitInImage, converges⟩ :=
    imageCompact sequence inImage
  obtain ⟨originalLimit, originalLimitMem, limitEq⟩ := limitInImage
  exact ⟨indices, subsequence, limit,
    ⟨originalLimit, originalLimitMem, limitEq.symm⟩, converges⟩

/-- A nonempty sequentially compact set of reals is bounded below, by
transporting boundedness-above through negation. -/
theorem realSequentiallyCompact_bounded_below
    {domain : IncReal → Prop}
    (nonempty : ∃ value, domain value)
    (compact : RealSequentiallyCompact domain) :
    ∃ lower, RealLowerBound domain lower := by
  have negCompact := realSequentiallyCompact_negFamily compact
  have negNonempty := realNegFamily_nonempty nonempty
  obtain ⟨upper, isUpper⟩ :=
    realSequentiallyCompact_bounded_above negNonempty negCompact
  refine ⟨realNeg upper, ?_⟩
  intro value member
  have negValueMem : RealNegFamily domain (realNeg value) := ⟨value, member, rfl⟩
  have negValueBound := isUpper (realNeg value) negValueMem
  have reversed := realNeg_order_reverse negValueBound
  simpa [realNeg_neg] using reversed

/-- A nonempty sequentially compact set of reals contains its own infimum,
by transporting `realSequentiallyCompact_sup_mem` through negation. -/
theorem realSequentiallyCompact_inf_mem
    {domain : IncReal → Prop}
    (compact : RealSequentiallyCompact domain)
    (nonempty : ∃ value, domain value)
    (bounded : ∃ lower, RealLowerBound domain lower) :
    domain (realInf domain nonempty bounded) := by
  have negCompact := realSequentiallyCompact_negFamily compact
  have negNonempty := realNegFamily_nonempty nonempty
  have negBounded := realNegFamily_bounded bounded
  have negSupMem := realSequentiallyCompact_sup_mem negCompact negNonempty negBounded
  obtain ⟨original, originalMem, eq⟩ := negSupMem
  show domain (realNeg (realSup (RealNegFamily domain) negNonempty negBounded))
  rw [eq, realNeg_neg]
  exact originalMem

/-- Extreme value theorem, maximum case: a function continuous on a closed
interval attains a maximum on that interval. -/
theorem realContinuousOn_closedInterval_attains_max
    {function : IncReal → IncReal} {lower upper : IncReal}
    (ordered : realLE lower upper)
    (continuous : RealContinuousOn function (RealClosedInterval lower upper)) :
    ∃ maximizer, RealClosedInterval lower upper maximizer ∧
      ∀ point, RealClosedInterval lower upper point →
        realLE (function point) (function maximizer) := by
  have domainCompact := realClosedInterval_sequentiallyCompact lower upper
  have imageCompact :=
    realSequentiallyCompact_continuous_image domainCompact continuous
  have imageNonempty :
      ∃ value, RealImage function (RealClosedInterval lower upper) value :=
    ⟨function lower, lower, realClosedInterval_contains_lower ordered, rfl⟩
  have imageBounded := realSequentiallyCompact_bounded_above imageNonempty imageCompact
  have imageSupMem :=
    realSequentiallyCompact_sup_mem imageCompact imageNonempty imageBounded
  obtain ⟨maximizer, maximizerMem, maximizerEq⟩ := imageSupMem
  refine ⟨maximizer, maximizerMem, ?_⟩
  intro point pointMem
  have pointImage : RealImage function (RealClosedInterval lower upper)
      (function point) :=
    ⟨point, pointMem, rfl⟩
  have pointBelowSup := realSup_is_upper_bound
    (RealImage function (RealClosedInterval lower upper)) imageNonempty imageBounded
    (function point) pointImage
  rw [← maximizerEq] at pointBelowSup
  exact pointBelowSup

/-- Extreme value theorem, minimum case: a function continuous on a closed
interval attains a minimum on that interval. -/
theorem realContinuousOn_closedInterval_attains_min
    {function : IncReal → IncReal} {lower upper : IncReal}
    (ordered : realLE lower upper)
    (continuous : RealContinuousOn function (RealClosedInterval lower upper)) :
    ∃ minimizer, RealClosedInterval lower upper minimizer ∧
      ∀ point, RealClosedInterval lower upper point →
        realLE (function minimizer) (function point) := by
  have domainCompact := realClosedInterval_sequentiallyCompact lower upper
  have imageCompact :=
    realSequentiallyCompact_continuous_image domainCompact continuous
  have imageNonempty :
      ∃ value, RealImage function (RealClosedInterval lower upper) value :=
    ⟨function lower, lower, realClosedInterval_contains_lower ordered, rfl⟩
  have imageBoundedBelow :=
    realSequentiallyCompact_bounded_below imageNonempty imageCompact
  have imageInfMem :=
    realSequentiallyCompact_inf_mem imageCompact imageNonempty imageBoundedBelow
  obtain ⟨minimizer, minimizerMem, minimizerEq⟩ := imageInfMem
  refine ⟨minimizer, minimizerMem, ?_⟩
  intro point pointMem
  have pointImage : RealImage function (RealClosedInterval lower upper)
      (function point) :=
    ⟨point, pointMem, rfl⟩
  have infBelowPoint := realInf_is_lower_bound
    (RealImage function (RealClosedInterval lower upper)) imageNonempty
    imageBoundedBelow (function point) pointImage
  rw [← minimizerEq] at infBelowPoint
  exact infBelowPoint

/-! ### Order/sign lemmas needed for Fermat's interior extremum theorem

The extreme value theorem above locates a maximizer/minimizer; to show the
derivative vanishes there we need a handful of sign-manipulation facts about
`realLE`/`realLT`/`realMul` that no earlier cycle needed (limits, sequences
and the field structure never required reasoning about the *sign* of a
product or a difference in this generality). -/

theorem realLT_of_not_le {left right : IncReal} (notLE : ¬ realLE left right) :
    realLT right left := by
  rcases realLE_total left right with le | ge
  · exact absurd le notLE
  · refine ⟨ge, ?_⟩
    intro equal
    apply notLE
    subst equal
    exact realLE_refl _

/-- If `left < right` then `right - left` is (strictly) positive. -/
theorem realAdd_neg_pos_of_lt {left right : IncReal} (strict : realLT left right) :
    realLT realZero (realAdd right (realNeg left)) := by
  refine ⟨?_, ?_⟩
  · have monotone := realAdd_monotone_left (right := realNeg left) strict.1
    rwa [realAdd_neg] at monotone
  · intro equal
    apply strict.2
    have shifted : realAdd realZero left =
        realAdd (realAdd right (realNeg left)) left := by rw [equal]
    rw [realAdd_zero_left, realAdd_assoc, realAdd_neg_left,
      realAdd_zero_right] at shifted
    exact shifted

/-- If `bound < -left` then `left + bound < 0`. -/
theorem realAdd_lt_zero_of_lt_neg {left bound : IncReal}
    (strict : realLT bound (realNeg left)) :
    realLT (realAdd left bound) realZero := by
  refine ⟨?_, ?_⟩
  · have monotone := realAdd_monotone_right (left := left) strict.1
    rwa [realAdd_neg] at monotone
  · intro equal
    apply strict.2
    have shifted : realAdd (realNeg left) (realAdd left bound) =
        realAdd (realNeg left) realZero := by rw [equal]
    rw [← realAdd_assoc, realAdd_neg_left, realAdd_zero_left,
      realAdd_zero_right] at shifted
    exact shifted

theorem realLT_neg_of_pos {value : IncReal} (positive : realLT realZero value) :
    realLT (realNeg value) realZero := by
  have monotone := realNeg_order_reverse positive.1
  rw [realNeg_zero] at monotone
  refine ⟨monotone, ?_⟩
  intro equal
  have shifted := congrArg realNeg equal
  rw [realNeg_neg, realNeg_zero] at shifted
  exact positive.2 shifted.symm

theorem realLT_pos_of_neg {value : IncReal} (negative : realLT value realZero) :
    realLT realZero (realNeg value) := by
  have monotone := realNeg_order_reverse negative.1
  rw [realNeg_zero] at monotone
  refine ⟨monotone, ?_⟩
  intro equal
  have shifted := congrArg realNeg equal
  rw [realNeg_neg, realNeg_zero] at shifted
  exact negative.2 shifted.symm

/-- Product of two (strictly) positive reals is (strictly) positive. -/
theorem realMul_pos_of_pos_pos {left right : IncReal}
    (leftPositive : realLT realZero left) (rightPositive : realLT realZero right) :
    realLT realZero (realMul left right) := by
  let leftPart : NonnegativeReal := ⟨left, leftPositive.1⟩
  let rightPart : NonnegativeReal := ⟨right, rightPositive.1⟩
  have eq : realMul left right = (nonnegativeRealMul leftPart rightPart).value :=
    realMul_of_nonnegative left right leftPositive.1 rightPositive.1
  rw [eq]
  refine ⟨(nonnegativeRealMul leftPart rightPart).nonnegative, ?_⟩
  intro zeroEq
  exact (nonnegativeRealMul_ne_zero leftPart rightPart
    (fun h => leftPositive.2 h.symm) (fun h => rightPositive.2 h.symm)) zeroEq.symm

/-- If a product with a positive factor is `≤ 0`, the other factor is `≤ 0`. -/
theorem realLE_zero_of_mul_le_zero_of_pos {factor value : IncReal}
    (factorPositive : realLT realZero factor)
    (productNonpos : realLE (realMul factor value) realZero) :
    realLE value realZero := by
  apply Classical.byContradiction
  intro notNonpos
  have valuePositive : realLT realZero value := realLT_of_not_le notNonpos
  have productPositive := realMul_pos_of_pos_pos factorPositive valuePositive
  exact productPositive.2 (realLE_antisymm productNonpos productPositive.1).symm

/-- If a product with a positive factor is `≥ 0`, the other factor is `≥ 0`. -/
theorem realLE_zero_of_zero_le_mul_of_pos {factor value : IncReal}
    (factorPositive : realLT realZero factor)
    (productNonneg : realLE realZero (realMul factor value)) :
    realLE realZero value := by
  apply Classical.byContradiction
  intro notNonneg
  have valueNegative : realLT value realZero := realLT_of_not_le notNonneg
  have negValuePositive := realLT_pos_of_neg valueNegative
  have productPositive := realMul_pos_of_pos_pos factorPositive negValuePositive
  rw [realMul_neg_right] at productPositive
  have productNegative := realLT_neg_of_pos productPositive
  rw [realNeg_neg] at productNegative
  exact productNegative.2 (realLE_antisymm productNegative.1 productNonneg)

/-- Given a positive rational radius and a positive real gap, produces a
positive rational `step` that is both `≤ radius` (as rationals) and whose
real image is `< gap`. Used to pick an increment simultaneously small enough
for an epsilon-delta bound and small enough to stay inside a domain. -/
theorem real_exists_rational_step_le_lt
    {radius : IncRational} (radiusPositive : rationalLT (rationalOfInteger 0) radius)
    {gap : IncReal} (gapPositive : realLT realZero gap) :
    ∃ step : IncRational, rationalLT (rationalOfInteger 0) step ∧
      rationalLE step radius ∧ realLT (rationalToReal step) gap := by
  let gapPart : NonnegativeReal := ⟨gap, gapPositive.1⟩
  obtain ⟨gapRational, gapMember, gapRationalPositive⟩ :=
    gapPart.exists_positive_member (fun h => gapPositive.2 h.symm)
  rcases rationalLE_total radius gapRational with ordered | reverse
  · refine ⟨radius, radiusPositive, rationalLE_refl radius, ?_⟩
    exact realLT_of_le_of_lt ((rationalToReal_le_iff radius gapRational).mpr ordered)
      (rationalToReal_lt_of_lower gap gapMember)
  · exact ⟨gapRational, gapRationalPositive, reverse,
      rationalToReal_lt_of_lower gap gapMember⟩

/-! ### Fermat's interior extremum theorem -/

/-- Fermat's interior extremum theorem, maximum case: if `function` attains a
global maximum over `[lower, upper]` at an interior point, and has a
derivative there, that derivative is zero. -/
theorem realHasDerivativeAt_zero_of_interior_max
    {function : IncReal → IncReal} {lower upper point derivative : IncReal}
    (lowerPoint : realLT lower point) (pointUpper : realLT point upper)
    (isMax : ∀ x, RealClosedInterval lower upper x →
      realLE (function x) (function point))
    (hasDerivative : RealHasDerivativeAt function derivative point) :
    derivative = realZero := by
  have nonpos : realLE derivative realZero := by
    apply Classical.byContradiction
    intro notNonpos
    have derivativePositive : realLT realZero derivative :=
      realLT_of_not_le notNonpos
    let derivativePart : NonnegativeReal := ⟨derivative, derivativePositive.1⟩
    obtain ⟨epsilon0, epsilon0Member, epsilon0Positive⟩ :=
      derivativePart.exists_positive_member (fun h => derivativePositive.2 h.symm)
    have epsilon0Below : realLT (rationalToReal epsilon0) derivative :=
      rationalToReal_lt_of_lower derivative epsilon0Member
    obtain ⟨radius1, radius1Positive, eventuallyClose⟩ :=
      hasDerivative epsilon0 epsilon0Positive
    have gapPositive := realAdd_neg_pos_of_lt pointUpper
    obtain ⟨step, stepPositive, stepBelowRadius, stepBelowGap⟩ :=
      real_exists_rational_step_le_lt radius1Positive gapPositive
    have incrementPositive : realLT realZero (rationalToReal step) :=
      rationalToReal_lt_preserves stepPositive
    have incrementCloseToPoint : realLE
        (realDist (rationalToReal step) realZero).value (rationalToReal radius1) := by
      rw [realDist_zero_right,
        realAbs_of_nonnegative (rationalToReal step) incrementPositive.1]
      exact (rationalToReal_le_iff step radius1).mpr stepBelowRadius
    have quotientClose := eventuallyClose (rationalToReal step) incrementCloseToPoint
    have flipped : realLE (realDist derivative
        (realDifferenceQuotient function point derivative
          (rationalToReal step))).value (rationalToReal epsilon0) := by
      rw [realDist_comm]
      exact quotientClose
    have lowerBoundOnQuotient : realLE
        (realAdd derivative (realNeg (rationalToReal epsilon0)))
        (realDifferenceQuotient function point derivative (rationalToReal step)) :=
      realAdd_neg_le_of_le_add (real_le_add_of_dist_le flipped)
    have quotientPositive : realLT realZero
        (realDifferenceQuotient function point derivative (rationalToReal step)) :=
      realLT_of_lt_of_le (realAdd_neg_pos_of_lt epsilon0Below) lowerBoundOnQuotient
    have memberInterval : RealClosedInterval lower upper
        (realAdd point (rationalToReal step)) := by
      refine ⟨?_, ?_⟩
      · have base : realLE point (realAdd point (rationalToReal step)) := by
          have monotone := realAdd_monotone_right
            (left := point) incrementPositive.1
          rwa [realAdd_zero_right] at monotone
        exact realLE_trans lowerPoint.1 base
      · have le1 : realLE (realAdd point (rationalToReal step))
            (realAdd point (realAdd upper (realNeg point))) :=
          realAdd_monotone_right stepBelowGap.1
        have restore : realAdd point (realAdd upper (realNeg point)) = upper := by
          rw [← realAdd_assoc, realAdd_comm point upper, realAdd_assoc,
            realAdd_neg, realAdd_zero_right]
        rwa [restore] at le1
    have maxProp := isMax (realAdd point (rationalToReal step)) memberInterval
    have diffNonpos : realLE (realAdd
        (function (realAdd point (rationalToReal step)))
        (realNeg (function point))) realZero := by
      have m := realAdd_monotone_left (right := realNeg (function point)) maxProp
      rwa [realAdd_neg] at m
    have quotientEqDiff :=
      realMul_differenceQuotient function point derivative (rationalToReal step)
    have quotientNonpos : realLE
        (realDifferenceQuotient function point derivative (rationalToReal step))
        realZero := by
      apply realLE_zero_of_mul_le_zero_of_pos incrementPositive
      rw [quotientEqDiff]
      exact diffNonpos
    exact quotientPositive.2
      (realLE_antisymm quotientNonpos quotientPositive.1).symm
  have nonneg : realLE realZero derivative := by
    apply Classical.byContradiction
    intro notNonneg
    have derivativeNegative : realLT derivative realZero :=
      realLT_of_not_le notNonneg
    have negDerivativePositive := realLT_pos_of_neg derivativeNegative
    let negDerivativePart : NonnegativeReal :=
      ⟨realNeg derivative, negDerivativePositive.1⟩
    obtain ⟨epsilon1, epsilon1Member, epsilon1Positive⟩ :=
      negDerivativePart.exists_positive_member
        (fun h => negDerivativePositive.2 h.symm)
    have epsilon1Below : realLT (rationalToReal epsilon1) (realNeg derivative) :=
      rationalToReal_lt_of_lower (realNeg derivative) epsilon1Member
    obtain ⟨radius2, radius2Positive, eventuallyClose⟩ :=
      hasDerivative epsilon1 epsilon1Positive
    have gapPositive := realAdd_neg_pos_of_lt lowerPoint
    obtain ⟨step, stepPositive, stepBelowRadius, stepBelowGap⟩ :=
      real_exists_rational_step_le_lt radius2Positive gapPositive
    have stepRealPositive : realLT realZero (rationalToReal step) :=
      rationalToReal_lt_preserves stepPositive
    have incrementCloseToPoint : realLE
        (realDist (realNeg (rationalToReal step)) realZero).value
        (rationalToReal radius2) := by
      rw [realDist_zero_right, realAbs_neg (rationalToReal step),
        realAbs_of_nonnegative (rationalToReal step) stepRealPositive.1]
      exact (rationalToReal_le_iff step radius2).mpr stepBelowRadius
    have quotientClose :=
      eventuallyClose (realNeg (rationalToReal step)) incrementCloseToPoint
    have upperBoundOnQuotient : realLE
        (realDifferenceQuotient function point derivative
          (realNeg (rationalToReal step)))
        (realAdd derivative (rationalToReal epsilon1)) :=
      real_le_add_of_dist_le quotientClose
    have epsilonSumNegative : realLT
        (realAdd derivative (rationalToReal epsilon1)) realZero :=
      realAdd_lt_zero_of_lt_neg epsilon1Below
    have quotientNegative : realLT
        (realDifferenceQuotient function point derivative
          (realNeg (rationalToReal step))) realZero :=
      realLT_of_le_of_lt upperBoundOnQuotient epsilonSumNegative
    have lowerBound : realLE lower
        (realAdd point (realNeg (rationalToReal step))) := by
      have stepPlusLowerLEPoint :
          realLE (realAdd (rationalToReal step) lower) point := by
        have m := realAdd_monotone_left (right := lower) stepBelowGap.1
        have restore :
            realAdd (realAdd point (realNeg lower)) lower = point := by
          rw [realAdd_assoc, realAdd_neg_left, realAdd_zero_right]
        rwa [restore] at m
      have m := realAdd_monotone_left
        (right := realNeg (rationalToReal step)) stepPlusLowerLEPoint
      have restore : realAdd (realAdd (rationalToReal step) lower)
          (realNeg (rationalToReal step)) = lower := by
        rw [realAdd_comm (rationalToReal step) lower, realAdd_assoc,
          realAdd_neg, realAdd_zero_right]
      rw [restore] at m
      exact m
    have upperBound : realLE (realAdd point (realNeg (rationalToReal step)))
        upper := by
      have incrementNonpos : realLE (realNeg (rationalToReal step)) realZero := by
        have m := realNeg_order_reverse stepRealPositive.1
        rwa [realNeg_zero] at m
      have m := realAdd_monotone_right (left := point) incrementNonpos
      rw [realAdd_zero_right] at m
      exact realLE_trans m pointUpper.1
    have memberInterval : RealClosedInterval lower upper
        (realAdd point (realNeg (rationalToReal step))) :=
      ⟨lowerBound, upperBound⟩
    have maxProp :=
      isMax (realAdd point (realNeg (rationalToReal step))) memberInterval
    have diffNonpos : realLE (realAdd
        (function (realAdd point (realNeg (rationalToReal step))))
        (realNeg (function point))) realZero := by
      have m := realAdd_monotone_left
        (right := realNeg (function point)) maxProp
      rwa [realAdd_neg] at m
    have quotientEqDiff := realMul_differenceQuotient function point derivative
      (realNeg (rationalToReal step))
    rw [realMul_neg_left] at quotientEqDiff
    have stepQuotientEq : realMul (rationalToReal step)
        (realDifferenceQuotient function point derivative
          (realNeg (rationalToReal step))) =
        realNeg (realAdd
          (function (realAdd point (realNeg (rationalToReal step))))
          (realNeg (function point))) := by
      have shifted := congrArg realNeg quotientEqDiff
      rwa [realNeg_neg] at shifted
    have negDiffNonneg : realLE realZero (realNeg (realAdd
        (function (realAdd point (realNeg (rationalToReal step))))
        (realNeg (function point)))) := by
      have m := realNeg_order_reverse diffNonpos
      rwa [realNeg_zero] at m
    have productNonneg : realLE realZero
        (realMul (rationalToReal step)
          (realDifferenceQuotient function point derivative
            (realNeg (rationalToReal step)))) := by
      rw [stepQuotientEq]
      exact negDiffNonneg
    have quotientNonneg : realLE realZero
        (realDifferenceQuotient function point derivative
          (realNeg (rationalToReal step))) :=
      realLE_zero_of_zero_le_mul_of_pos stepRealPositive productNonneg
    exact quotientNegative.2
      (realLE_antisymm quotientNegative.1 quotientNonneg)
  exact realLE_antisymm nonpos nonneg

/-- Fermat's interior extremum theorem, minimum case: derived from the
maximum case by negation (minimizing `function` is maximizing `-function`). -/
theorem realHasDerivativeAt_zero_of_interior_min
    {function : IncReal → IncReal} {lower upper point derivative : IncReal}
    (lowerPoint : realLT lower point) (pointUpper : realLT point upper)
    (isMin : ∀ x, RealClosedInterval lower upper x →
      realLE (function point) (function x))
    (hasDerivative : RealHasDerivativeAt function derivative point) :
    derivative = realZero := by
  have negHasDerivative : RealHasDerivativeAt
      (fun value => realNeg (function value)) (realNeg derivative) point :=
    realHasDerivativeAt_neg hasDerivative
  have negIsMax : ∀ x, RealClosedInterval lower upper x →
      realLE (realNeg (function x)) (realNeg (function point)) := by
    intro x member
    exact realNeg_order_reverse (isMin x member)
  have negZero := realHasDerivativeAt_zero_of_interior_max
    lowerPoint pointUpper negIsMax negHasDerivative
  have restored := congrArg realNeg negZero
  rwa [realNeg_neg, realNeg_zero] at restored

/-! ### Rolle's theorem -/

/-- Adding a fixed positive offset to a base value strictly increases it. -/
theorem realLT_add_right_of_pos {base offset : IncReal}
    (positive : realLT realZero offset) :
    realLT base (realAdd base offset) := by
  refine ⟨?_, ?_⟩
  · have m := realAdd_monotone_right (left := base) positive.1
    rwa [realAdd_zero_right] at m
  · intro equal
    have shifted := congrArg (realAdd (realNeg base)) equal
    rw [realAdd_neg_left, ← realAdd_assoc, realAdd_neg_left,
      realAdd_zero_left] at shifted
    exact positive.2 shifted

/-- Adding a fixed real to both sides of a strict inequality preserves it. -/
theorem realAdd_lt_monotone_left (offset : IncReal) {left right : IncReal}
    (strict : realLT left right) :
    realLT (realAdd offset left) (realAdd offset right) := by
  refine ⟨realAdd_monotone_right strict.1, ?_⟩
  intro equal
  apply strict.2
  have shifted := congrArg (realAdd (realNeg offset)) equal
  rw [← realAdd_assoc, realAdd_neg_left, realAdd_zero_left,
    ← realAdd_assoc, realAdd_neg_left, realAdd_zero_left] at shifted
  exact shifted

/-- Rolle's theorem: a function continuous on `[lower, upper]`, differentiable
everywhere on that closed interval (a slightly stronger hypothesis than the
textbook "differentiable on the open interval", adopted since this codebase
has no separate open-interval domain predicate), and agreeing at the two
endpoints, has a derivative of zero at some interior point. The extreme value
theorem locates a maximizer and a minimizer; if either is interior, Fermat's
theorem finishes it directly. If both coincide with the shared endpoint
value, the function is constant on the whole interval and any freshly
manufactured interior point works (it is trivially its own local extremum). -/
theorem real_rolle
    {function : IncReal → IncReal} {lower upper : IncReal}
    (ordered : realLT lower upper)
    (continuous : RealContinuousOn function (RealClosedInterval lower upper))
    (differentiable : RealDifferentiableOn function (RealClosedInterval lower upper))
    (equalEndpoints : function lower = function upper) :
    ∃ point, realLT lower point ∧ realLT point upper ∧
      RealHasDerivativeAt function realZero point := by
  obtain ⟨maximizer, maximizerMem, maximizerMax⟩ :=
    realContinuousOn_closedInterval_attains_max ordered.1 continuous
  obtain ⟨minimizer, minimizerMem, minimizerMin⟩ :=
    realContinuousOn_closedInterval_attains_min ordered.1 continuous
  by_cases maxEqLower : function maximizer = function lower
  · by_cases minEqLower : function minimizer = function lower
    · -- Constant case: manufacture a genuine interior point and use it.
      have constantOnDomain : ∀ x, RealClosedInterval lower upper x →
          function x = function lower := by
        intro x member
        have upperBound := maximizerMax x member
        have lowerBound := minimizerMin x member
        rw [maxEqLower] at upperBound
        rw [minEqLower] at lowerBound
        exact realLE_antisymm upperBound lowerBound
      have gapPositive := realAdd_neg_pos_of_lt ordered
      let gapPart : NonnegativeReal := ⟨realAdd upper (realNeg lower), gapPositive.1⟩
      obtain ⟨step, gapMember, stepPositive⟩ :=
        gapPart.exists_positive_member (fun h => gapPositive.2 h.symm)
      have stepBelowGap : realLT (rationalToReal step) (realAdd upper (realNeg lower)) :=
        rationalToReal_lt_of_lower (realAdd upper (realNeg lower)) gapMember
      have stepRealPositive : realLT realZero (rationalToReal step) :=
        rationalToReal_lt_preserves stepPositive
      have lowerLtPoint0 : realLT lower (realAdd lower (rationalToReal step)) :=
        realLT_add_right_of_pos stepRealPositive
      have pointLtUpper : realLT (realAdd lower (rationalToReal step)) upper := by
        have m := realAdd_lt_monotone_left lower stepBelowGap
        have restore : realAdd lower (realAdd upper (realNeg lower)) = upper := by
          rw [← realAdd_assoc, realAdd_comm lower upper, realAdd_assoc,
            realAdd_neg, realAdd_zero_right]
        rwa [restore] at m
      have memberPoint0 : RealClosedInterval lower upper
          (realAdd lower (rationalToReal step)) :=
        ⟨lowerLtPoint0.1, pointLtUpper.1⟩
      have isMaxAtPoint0 : ∀ x, RealClosedInterval lower upper x →
          realLE (function x)
            (function (realAdd lower (rationalToReal step))) := by
        intro x member
        rw [constantOnDomain x member, constantOnDomain _ memberPoint0]
        exact realLE_refl _
      obtain ⟨d, hasD⟩ :=
        differentiable (realAdd lower (rationalToReal step)) memberPoint0
      have dZero := realHasDerivativeAt_zero_of_interior_max
        lowerLtPoint0 pointLtUpper isMaxAtPoint0 hasD
      rw [dZero] at hasD
      exact ⟨realAdd lower (rationalToReal step), lowerLtPoint0, pointLtUpper, hasD⟩
    · -- The minimizer differs from the shared endpoint value, so it is interior.
      have minimizerNeLower : minimizer ≠ lower := by
        intro h
        exact minEqLower (congrArg function h)
      have minimizerNeUpper : minimizer ≠ upper := by
        intro h
        apply minEqLower
        rw [congrArg function h, equalEndpoints]
      have interiorLower : realLT lower minimizer :=
        ⟨minimizerMem.1, fun h => minimizerNeLower h.symm⟩
      have interiorUpper : realLT minimizer upper :=
        ⟨minimizerMem.2, minimizerNeUpper⟩
      obtain ⟨d, hasD⟩ := differentiable minimizer minimizerMem
      have dZero := realHasDerivativeAt_zero_of_interior_min
        interiorLower interiorUpper minimizerMin hasD
      rw [dZero] at hasD
      exact ⟨minimizer, interiorLower, interiorUpper, hasD⟩
  · -- The maximizer differs from the shared endpoint value, so it is interior.
    have maximizerNeLower : maximizer ≠ lower := by
      intro h
      exact maxEqLower (congrArg function h)
    have maximizerNeUpper : maximizer ≠ upper := by
      intro h
      apply maxEqLower
      rw [congrArg function h, equalEndpoints]
    have interiorLower : realLT lower maximizer :=
      ⟨maximizerMem.1, fun h => maximizerNeLower h.symm⟩
    have interiorUpper : realLT maximizer upper :=
      ⟨maximizerMem.2, maximizerNeUpper⟩
    obtain ⟨d, hasD⟩ := differentiable maximizer maximizerMem
    have dZero := realHasDerivativeAt_zero_of_interior_max
      interiorLower interiorUpper maximizerMax hasD
    rw [dZero] at hasD
    exact ⟨maximizer, interiorLower, interiorUpper, hasD⟩

end IncidenceCore
