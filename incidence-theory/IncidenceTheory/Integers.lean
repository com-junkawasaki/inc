import IncidenceTheory.Peano

namespace IncidenceCore

inductive IntegerRole where
  | positiveTowardZero : Nat → IntegerRole
  | negativeTowardZero : Nat → IntegerRole
deriving DecidableEq, Repr

def integerRank : Int → Nat
  | .ofNat n => n
  | .negSucc n => n + 1

def positiveIntegerEndpoint (n : Nat) : Endpoint Int IntegerRole :=
  { i := .ofNat n, role := .positiveTowardZero n, sign := .neg,
    mult := 1, mult_pos := by omega }

def negativeIntegerEndpoint (n : Nat) : Endpoint Int IntegerRole :=
  { i := if n = 0 then 0 else .negSucc (n - 1),
    role := .negativeTowardZero n, sign := .neg,
    mult := 1, mult_pos := by omega }

def integerBoundary (value : Int) : Boundary Int IntegerRole :=
  match value with
  | .ofNat 0 => []
  | .ofNat (n + 1) => [positiveIntegerEndpoint n]
  | .negSucc n => [negativeIntegerEndpoint n]

@[simp] theorem integerBoundary_zero : integerBoundary 0 = [] := rfl

@[simp] theorem integerBoundary_ofNat_succ (n : Nat) :
    integerBoundary (Int.ofNat (Nat.succ n)) = [positiveIntegerEndpoint n] :=
  rfl

@[simp] theorem integerBoundary_ofNat_add_one (n : Nat) :
    integerBoundary ((Int.ofNat n) + 1) = [positiveIntegerEndpoint n] :=
  rfl

@[simp] theorem integerBoundary_ofNat_natAddOne (n : Nat) :
    integerBoundary (Int.ofNat (n + 1)) = [positiveIntegerEndpoint n] :=
  rfl

@[simp] theorem integerBoundary_negSucc (n : Nat) :
    integerBoundary (Int.negSucc n) = [negativeIntegerEndpoint n] :=
  rfl

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
            simp [positiveIntegerEndpoint] at equal
            omega
    | negSucc n =>
        cases n with
        | zero =>
            simp [integerBoundary] at member
            subst endpoint
            simp [negativeIntegerEndpoint] at equal
        | succ n =>
            simp [integerBoundary] at member
            subst endpoint
            simp [negativeIntegerEndpoint] at equal
  unit_left := by intro value; simp
  unit_right := by intro value; simp
  type_preserve := by intro i j k allowed selected; rfl

theorem integerBoundary_decreases :
    ∀ value endpoint, endpoint ∈ integerBoundary value →
      integerRank endpoint.i < integerRank value := by
  intro value endpoint member
  cases value with
  | ofNat n =>
      cases n <;> simp [integerBoundary, integerRank,
        positiveIntegerEndpoint] at member ⊢
      subst endpoint
      simp
  | negSucc n =>
      cases n <;> simp [integerBoundary, integerRank,
        negativeIntegerEndpoint] at member ⊢
      all_goals subst endpoint <;>
        simp

theorem integerIncidence_one_not_bisim_negOne :
    ¬ approxBisim integerIncidence 1 (-1) := by
  apply not_approxBisim_of_boundary_mismatch integerIncidence 1 (-1)
    (positiveIntegerEndpoint 0)
  · simp [integerIncidence, integerBoundary]
  · intro endpoint member
    change endpoint ∈ integerBoundary (Int.negSucc 0) at member
    have endpointEq : endpoint =
        negativeIntegerEndpoint 0 := by
      simpa [integerBoundary] using member
    subst endpoint
    simp [boundaryCompatible, positiveIntegerEndpoint,
      negativeIntegerEndpoint]

theorem integerBoundary_extensional :
    ∀ x y, integerIncidence.typeFunc x = integerIncidence.typeFunc y →
      boundaryMatched integerIncidence (· = ·) x y → x = y := by
  intro x y typeEqual matched
  cases x with
  | ofNat nx =>
      cases nx with
      | zero =>
          cases y with
          | ofNat ny =>
              cases ny with
              | zero => rfl
              | succ ny =>
                  exfalso
                  obtain ⟨candidate, member, compatible, equal⟩ := matched.2
                    (positiveIntegerEndpoint ny) (by
                      change positiveIntegerEndpoint ny ∈
                        [positiveIntegerEndpoint ny]
                      simp)
                  change candidate ∈ integerBoundary (Int.ofNat 0) at member
                  simp at member
          | negSucc ny =>
              exfalso
              obtain ⟨candidate, member, compatible, equal⟩ := matched.2
                (negativeIntegerEndpoint ny) (by
                  change negativeIntegerEndpoint ny ∈
                    integerBoundary (Int.negSucc ny)
                  simp)
              change candidate ∈ integerBoundary (Int.ofNat 0) at member
              simp at member
      | succ nx =>
          cases y with
          | ofNat ny =>
              cases ny with
              | zero =>
                  exfalso
                  obtain ⟨candidate, member, compatible, equal⟩ := matched.1
                    (positiveIntegerEndpoint nx) (by
                      change positiveIntegerEndpoint nx ∈
                        [positiveIntegerEndpoint nx]
                      simp)
                  change candidate ∈ integerBoundary (Int.ofNat 0) at member
                  simp at member
              | succ ny =>
                  obtain ⟨candidate, member, compatible, equal⟩ := matched.1
                    (positiveIntegerEndpoint nx) (by
                      change positiveIntegerEndpoint nx ∈
                        [positiveIntegerEndpoint nx]
                      simp)
                  have candidateEq : candidate = positiveIntegerEndpoint ny := by
                    change candidate ∈ [positiveIntegerEndpoint ny] at member
                    simpa using member
                  subst candidate
                  have indexEq : nx = ny := by
                    simpa [boundaryCompatible, positiveIntegerEndpoint] using
                      compatible.1
                  subst ny
                  rfl
          | negSucc ny =>
              exfalso
              obtain ⟨candidate, member, compatible, equal⟩ := matched.1
                (positiveIntegerEndpoint nx) (by
                  change positiveIntegerEndpoint nx ∈
                    [positiveIntegerEndpoint nx]
                  simp)
              have candidateEq : candidate = negativeIntegerEndpoint ny := by
                change candidate ∈ integerBoundary (Int.negSucc ny) at member
                simpa using member
              subst candidate
              simp [boundaryCompatible, positiveIntegerEndpoint,
                negativeIntegerEndpoint] at compatible
  | negSucc nx =>
      cases y with
      | ofNat ny =>
          cases ny with
          | zero =>
              exfalso
              obtain ⟨candidate, member, compatible, equal⟩ := matched.1
                (negativeIntegerEndpoint nx) (by
                  change negativeIntegerEndpoint nx ∈
                    integerBoundary (Int.negSucc nx)
                  simp)
              change candidate ∈ integerBoundary (Int.ofNat 0) at member
              simp at member
          | succ ny =>
              exfalso
              obtain ⟨candidate, member, compatible, equal⟩ := matched.1
                (negativeIntegerEndpoint nx) (by
                  change negativeIntegerEndpoint nx ∈
                    integerBoundary (Int.negSucc nx)
                  simp)
              have candidateEq : candidate = positiveIntegerEndpoint ny := by
                change candidate ∈ [positiveIntegerEndpoint ny] at member
                simpa using member
              subst candidate
              simp [boundaryCompatible, positiveIntegerEndpoint,
                negativeIntegerEndpoint] at compatible
      | negSucc ny =>
          obtain ⟨candidate, member, compatible, equal⟩ := matched.1
            (negativeIntegerEndpoint nx) (by
              change negativeIntegerEndpoint nx ∈
                integerBoundary (Int.negSucc nx)
              simp)
          have candidateEq : candidate = negativeIntegerEndpoint ny := by
            change candidate ∈ integerBoundary (Int.negSucc ny) at member
            simpa using member
          subst candidate
          have indexEq : nx = ny := by
            simpa [boundaryCompatible, negativeIntegerEndpoint] using
              compatible.1
          subst ny
          rfl

theorem integerIncidence_approxBisim_iff (x y : Int) :
    approxBisim integerIncidence x y ↔ x = y := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact incidence_bisim_faithful integerIncidence integerRank
      integerBoundary_decreases integerBoundary_extensional
      bisimulation x y related
  · rintro rfl
    exact approxBisim_refl integerIncidence x

theorem integerQuotientResonanceCongruent :
    QuotientResonanceCongruent integerIncidence :=
  quotientResonanceCongruent_of_faithful integerIncidence
    integerIncidence_approxBisim_iff

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
