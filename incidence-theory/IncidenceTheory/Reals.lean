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

def RealSequentiallyContinuousAt
    (function : IncReal → IncReal) (point : IncReal) : Prop :=
  ∀ sequence : RealSequence,
    RealSequenceConverges sequence point →
      RealSequenceConverges (fun index => function (sequence index))
        (function point)

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

end IncidenceCore
