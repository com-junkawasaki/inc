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

end IncidenceCore
