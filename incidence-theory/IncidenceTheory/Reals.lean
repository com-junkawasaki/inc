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
