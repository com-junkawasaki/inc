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

end IncidenceCore
