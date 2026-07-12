import IncidenceTheory.Peano

namespace IncidenceCore

inductive IntegerRole where
  | positiveTowardZero
  | negativeTowardZero
deriving DecidableEq, Repr

def integerRank : Int → Nat
  | .ofNat n => n
  | .negSucc n => n + 1

def integerBoundary (value : Int) : Boundary Int IntegerRole :=
  match value with
  | .ofNat 0 => []
  | .ofNat (n + 1) =>
      [{ i := .ofNat n, role := .positiveTowardZero, sign := .neg,
         mult := 1, mult_pos := by omega }]
  | .negSucc 0 =>
      [{ i := 0, role := .negativeTowardZero, sign := .neg,
         mult := 1, mult_pos := by omega }]
  | .negSucc (n + 1) =>
      [{ i := .negSucc n, role := .negativeTowardZero, sign := .neg,
         mult := 1, mult_pos := by omega }]

def integerIncidence : Incidence Int IntegerRole GraphType where
  boundary := integerBoundary
  typeFunc := fun _ => GraphType.unit
  glue := fun left right => some (left + right)
  unit := 0
  guards := Guards.permissive Int
  type_consistent := fun _ _ _ => rfl
  sign_rules := by
    intro value endpoint member
    cases endpoint.sign <;> simp
  multiplicities := fun _ endpoint _ => endpoint.mult_pos
  well_founded := by
    intro value ⟨endpoint, member, equal⟩
    cases value with
    | ofNat n =>
        cases n with
        | zero => simp [integerBoundary] at member
        | succ n =>
            simp [integerBoundary] at member
            subst endpoint
            simp at equal
            omega
    | negSucc n =>
        cases n with
        | zero =>
            simp [integerBoundary] at member
            subst endpoint
            simp at equal
        | succ n =>
            simp [integerBoundary] at member
            subst endpoint
            simp at equal
  unit_left := by intro value; simp
  unit_right := by intro value; simp
  type_preserve := by intro i j k allowed selected; rfl

theorem integerBoundary_decreases :
    ∀ value endpoint, endpoint ∈ integerBoundary value →
      integerRank endpoint.i < integerRank value := by
  intro value endpoint member
  cases value with
  | ofNat n =>
      cases n <;> simp [integerBoundary, integerRank] at member ⊢
      subst endpoint
      simp
  | negSucc n =>
      cases n <;> simp [integerBoundary, integerRank] at member ⊢
      all_goals subst endpoint <;> simp

def integerResonanceSpec : FunctionalResonanceSpec integerIncidence where
  symmetric := by
    intro i j k resonant
    simpa [integerIncidence, Int.add_comm] using resonant
  unit_left := by intro i; simp [integerIncidence]
  unit_right := by intro i; simp [integerIncidence]
  type_compatible := by intro i j k resonant; exact ⟨rfl, rfl⟩
  selected_complete := by intro i j k resonant; exact resonant

def integerAssociativeResonanceSpec :
    AssociativeResonanceSpec integerIncidence where
  reassociate := by
    intro i j k out
    constructor
    · rintro ⟨ij, hij, hout⟩
      have hijEq : i + j = ij := by simpa [integerIncidence] using hij
      subst ij
      refine ⟨j + k, ?_, ?_⟩
      · simp [integerIncidence]
      · simpa [integerIncidence, Int.add_assoc] using hout
    · rintro ⟨jk, hjk, hout⟩
      have hjkEq : j + k = jk := by simpa [integerIncidence] using hjk
      subst jk
      refine ⟨i + j, ?_, ?_⟩
      · simp [integerIncidence]
      · simpa [integerIncidence, Int.add_assoc] using hout

theorem integerIncidence_additive_inverse (value : Int) :
    integerIncidence.resonance value (-value) integerIncidence.unit := by
  simpa [integerIncidence] using Int.add_neg_cancel_right 0 value

theorem integerIncidence_not_unitReflecting :
    ¬ Nonempty (UnitReflectingResonanceSpec integerIncidence) := by
  rintro ⟨reflecting⟩
  have reflected := reflecting.reflects
    (i := (1 : Int)) (j := (-1 : Int)) (by simp [integerIncidence])
  rcases reflected with impossible | impossible <;>
    simp [integerIncidence] at impossible

theorem integerIncidence_nontrivial_resonance :
    integerIncidence.resonance 2 (-3) (-1) := by
  simp [integerIncidence]

end IncidenceCore
