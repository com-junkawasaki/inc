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

def integerAdditiveGroupResonanceSpec :
    AdditiveGroupResonanceSpec integerIncidence where
  toFunctionalResonanceSpec := integerResonanceSpec
  toAssociativeResonanceSpec := integerAssociativeResonanceSpec
  inverse := fun value => -value
  inverse_mode := by intro value; simp [integerIncidence]; omega

def integerMultiplicativeResonance (i j k : Int) : Prop :=
  i * j = k

def integerDistributiveResonanceSpec :
    DistributiveResonanceSpec integerIncidence where
  one := 1
  multiply := integerMultiplicativeResonance
  symmetric := by
    intro i j k multiplied
    simpa [integerMultiplicativeResonance, Int.mul_comm] using multiplied
  unit_left := by intro i; simp [integerMultiplicativeResonance]
  unit_right := by intro i; simp [integerMultiplicativeResonance]
  associative := by
    intro i j k out
    constructor
    · rintro ⟨ij, hij, hout⟩
      subst ij
      refine ⟨j * k, rfl, ?_⟩
      simpa [integerMultiplicativeResonance, Int.mul_assoc] using hout
    · rintro ⟨jk, hjk, hout⟩
      subst jk
      refine ⟨i * j, rfl, ?_⟩
      simpa [integerMultiplicativeResonance, Int.mul_assoc] using hout
  distributes := by
    intro i j k out
    constructor
    · rintro ⟨jk, hjk, hout⟩
      have hjkEq : j + k = jk := by simpa [integerIncidence] using hjk
      subst jk
      refine ⟨i * j, i * k, rfl, rfl, ?_⟩
      simpa [integerIncidence, integerMultiplicativeResonance,
        Int.mul_add] using hout
    · rintro ⟨ij, ik, hij, hik, hout⟩
      subst ij
      subst ik
      refine ⟨j + k, ?_, ?_⟩
      · simp [integerIncidence]
      · simpa [integerIncidence, integerMultiplicativeResonance,
          Int.mul_add] using hout

theorem integer_resonance_distributive_example :
    integerIncidence.resonance
      (2 * 3) (2 * (-1)) (2 * (3 + (-1))) := by
  simp [integerIncidence]

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

/- Research cycle 68 (see RESEARCH_LOG.md): roadmap item 7 ("incidence /
resonance と内部論理・解析構造の統合") names its remaining goal as a single
universal interpretation theorem connecting resonance-driven
generation/composition to the internal-logic model and constructive real
analysis. Auditing every concrete `*ResonanceSpec` instantiation
(`Integers.lean`/`Rationals.lean`/`Reals.lean`/`GraphModel.lean`, plus the
generic combinators `Sum.lean`/`Product.lean`) against the internal-logic
apparatus (`CountablyPresentedIncidence`/Kripke soundness-completeness,
`IncidenceTheory/Logic.lean`) found that only `natIncidence` (via
`natCountablyPresentedIncidence`, `Peano.lean`) and the two generic
combinators `incidenceSum`/`incidenceProd` (via
`natSumCountablyPresentedIncidence`/`natProductCountablyPresentedIncidence`,
themselves built from `natCountablyPresentedIncidence`) are connected to it
-- every one of `integerIncidence`/`rationalIncidence`/`realIncidence`/
`finiteIncidence` has none. `Real` is ruled out immediately: `CountableAtomCoding`
demands a `code : Atom → Nat` with a left inverse `decode`, i.e. an
injection into `Nat`, which cannot exist for the uncountable reals. Among
the remaining three, `integerIncidence` is the richest `*ResonanceSpec`
instance (`FunctionalResonanceSpec`/`AssociativeResonanceSpec`/
`AdditiveGroupResonanceSpec`/`DistributiveResonanceSpec`, strictly more
structure than `finiteIncidence`'s bare `ResonanceSpec` and reusing none of
`natIncidence`'s trivial identity coding), so it is the best-scoped target
for a first non-`Nat` bridge: give `Int` a genuinely non-identity
`CountableAtomCoding` (the standard zig-zag bijection with `Nat`) and
instantiate the same generic `CountablyPresentedIncidence` machinery already
used for `Nat`, connecting the integers' resonance-driven additive/
multiplicative structure to Kripke-model soundness/completeness for the
first time. This is a modest, concrete step, not item 7's full universal
interpretation theorem -- it establishes one additional worked instance of
"resonance ↔ internal logic" beyond the identity-coded `Nat` case, on the
richest currently-available candidate; `rationalIncidence` (built over a
custom `Quotient` carrier, `IncRational`, needing a coding through
`RationalRepresentative` pairs) is the natural next target if this thread
continues, per this cycle's `RESEARCH_LOG.md` entry. -/

/-- The standard zig-zag encoding of `Int` into `Nat`: a nonnegative integer
`n` (`Int.ofNat n`) doubles to `2 * n`; a negative integer `-(n+1)`
(`Int.negSucc n`) doubles-and-shifts to `2 * n + 1` -- the two families
interleave exhaustively and disjointly across all of `Nat`. -/
def integerCode : Int → Nat
  | Int.ofNat n => 2 * n
  | Int.negSucc n => 2 * n + 1

/-- Inverse of `integerCode`: even codes decode to the nonnegative half,
odd codes decode to the corresponding `negSucc`. -/
def integerDecode (code : Nat) : Int :=
  if code % 2 = 0 then Int.ofNat (code / 2) else Int.negSucc (code / 2)

theorem integerDecode_integerCode (value : Int) :
    integerDecode (integerCode value) = value := by
  cases value with
  | ofNat n =>
      have hmod : (2 * n) % 2 = 0 := by omega
      have hdiv : (2 * n) / 2 = n := by omega
      simp [integerCode, integerDecode, hmod, hdiv]
  | negSucc n =>
      have hmod : (2 * n + 1) % 2 = 1 := by omega
      have hdiv : (2 * n + 1) / 2 = n := by omega
      simp [integerCode, integerDecode, hmod, hdiv]

/-- `Int`'s countable-atom presentation via the zig-zag coding above --
unlike `natCountablyPresentedIncidence`'s trivial identity coding
(`Peano.lean`), this is the project's first genuinely non-identity
`CountableAtomCoding` instantiation. -/
def integerAtomCoding : CountableAtomCoding Int where
  decode := integerDecode
  code := integerCode
  decode_code := integerDecode_integerCode

/-- The bridge this cycle builds: `integerIncidence` -- the richest
`*ResonanceSpec`-equipped concrete instance without a prior internal-logic
connection -- paired with its countable-atom presentation, making the
generic Kripke soundness/completeness machinery
(`IncidenceTheory/Logic.lean`) applicable to it exactly as it already is to
`natIncidence` (`Peano.lean`). -/
def integerCountablyPresentedIncidence :
    CountablyPresentedIncidence Int IntegerRole GraphType where
  incidence := integerIncidence
  atoms := integerAtomCoding

theorem integerIncidence_internalLogic_complete
    (context : List (Formula Int)) (formula : Formula Int) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  integerCountablyPresentedIncidence.internalLogic_complete context formula

theorem integerIncidence_internalLogic_consistent_iff_model
    (context : List (Formula Int)) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  integerCountablyPresentedIncidence.internalLogic_consistent_iff_model context

/- Research cycle 73 (see RESEARCH_LOG.md): cycle 72 built
`TranslationPreservation.ResonantQuotientEquivalenceCriterion` and its
`quotientResonance_iff` theorem, gated behind an explicit
`QuotientResonanceCongruent target` hypothesis, but left the theorem wholly
uninstantiated: no concrete (non-`identity`) `ResonantQuotientEquivalenceCriterion`
between any pair of this project's `Incidence` instances existed anywhere in
the tree, confirmed by grep, so the reflect direction had never actually been
exercised on a real pair. Cycle 72's own next-hypothesis framing asked
whether ANY of `natIncidence`/`integerIncidence`/`rationalIncidence`/
`realIncidence`/`finiteIncidence` satisfies `QuotientResonanceCongruent` at
all, as if this were open. Re-grepping this cycle found it was not: this
file already proves `integerQuotientResonanceCongruent` (above), and the
parallel `natQuotientResonanceCongruent` (`Peano.lean`),
`rationalQuotientResonanceCongruent` (`Rationals.lean`),
`realQuotientResonanceCongruent` (`Reals.lean`), and
`finiteQuotientResonanceCongruent` (`GraphModel.lean`) already exist too --
all five instances satisfy the hypothesis, each via
`quotientResonanceCongruent_of_faithful` (all five carriers have faithful
bisimulation, `≈ ↔ =`, except `Nat`'s which is proved by direct induction),
established long before cycle 60 (`git log -S`-confirmed: predates even the
numbered-cycle `RESEARCH_LOG.md` scheme) and already reused by the
`IncDepRawNormalizedResonanceCompletion` bundle in `CrossInstance.lean`.
Cycle 72's own tree-wide grep for the string `QuotientResonanceCongruent`
should have surfaced these; it evidently did not (an error in that cycle's
own report, corrected here rather than silently reproduced). So the actual
gap was never "does any instance satisfy the hypothesis" -- it was "has the
hypothesis, known to hold for all five, ever been paired with a genuine
non-`identity` criterion so `quotientResonance_iff` fires for real": no.

This cycle closes that gap on `integerIncidence`. Negation (`x ↦ -x`) is a
non-`identity` self-map of `Int` that preserves *and* reflects resonance
(`i + j = k ↔ (-i) + (-j) = (-k)`, pure ring cancellation, `omega`-decidable)
and preserves *and* reflects bisimulation (immediate from faithfulness,
`integerIncidence_approxBisim_iff`, since negation is a self-bijection), and
is essentially surjective (it is a bijection, witness `-j` maps to `j`).
Bundling these into a genuine
`ResonantQuotientEquivalenceCriterion integerIncidence integerIncidence` and
feeding it to `quotientResonance_iff` together with the already-available
`integerQuotientResonanceCongruent` witness yields a new concrete corollary:
quotient-level resonance on `integerIncidence` is invariant under negating
all three representatives -- `quotientResonance_iff`'s full two-directional
strength exercised on a real pair for the first time (the forward half was
already unconditionally free via `quotientResonance_forward`; only the
reflect half needed the gate, and cycle 72 hand-checked that gate is
load-bearing, not decorative). -/

theorem integerBoundary_eq_nil_iff (value : Int) :
    integerIncidence.boundary value = [] ↔ value = 0 := by
  show integerBoundary value = [] ↔ value = 0
  cases value with
  | ofNat n =>
      cases n with
      | zero => simp
      | succ n =>
          rw [integerBoundary_ofNat_succ]
          constructor
          · intro h; exact absurd h (List.cons_ne_nil _ _)
          · intro h
            exact absurd (show (n : Int) + 1 = 0 from h) (by omega)
  | negSucc n =>
      rw [integerBoundary_negSucc]
      constructor
      · intro h; exact absurd h (List.cons_ne_nil _ _)
      · intro h; exact absurd h (by omega)

def integerNegationBoundaryShapeTranslation :
    TranslationPreservation.BoundaryShapeTranslation
      integerIncidence integerIncidence where
  map := fun value => -value
  preservesReflectsNullary := by
    intro value
    rw [integerBoundary_eq_nil_iff, integerBoundary_eq_nil_iff]
    omega

def integerNegationBehavioralTranslation :
    TranslationPreservation.BehavioralBoundaryShapeTranslation
      integerIncidence integerIncidence where
  toBoundaryShapeTranslation := integerNegationBoundaryShapeTranslation
  preservesBisimulation := by
    intro i j bisimilar
    have hij := (integerIncidence_approxBisim_iff i j).mp bisimilar
    exact (integerIncidence_approxBisim_iff (-i) (-j)).mpr (by omega)

def integerNegationResonantTranslation :
    TranslationPreservation.ResonantBehavioralTranslation
      integerIncidence integerIncidence where
  toBehavioralBoundaryShapeTranslation := integerNegationBehavioralTranslation
  preservesResonance := by
    intro i j k resonant
    have hk : i + j = k := by simpa [integerIncidence] using resonant
    have hneg : (-i) + (-j) = (-k) := by omega
    simpa [integerIncidence] using hneg

def integerNegationEmbedding :
    TranslationPreservation.ResonantBehavioralEmbedding
      integerIncidence integerIncidence where
  toResonantBehavioralTranslation := integerNegationResonantTranslation
  reflectsResonance := by
    intro i j k resonant
    have hk : (-i) + (-j) = (-k) := by simpa [integerIncidence] using resonant
    have hpos : i + j = k := by omega
    simpa [integerIncidence] using hpos

/-- The concrete, non-`identity` `ResonantQuotientEquivalenceCriterion` this
cycle builds: negation as a self-equivalence of `integerIncidence`. -/
def integerNegationQuotientCriterion :
    TranslationPreservation.ResonantQuotientEquivalenceCriterion
      integerIncidence integerIncidence where
  embedding := integerNegationEmbedding
  reflectsBisimulation := by
    intro i j bisimilar
    have hij := (integerIncidence_approxBisim_iff (-i) (-j)).mp bisimilar
    exact (integerIncidence_approxBisim_iff i j).mpr (by omega)
  essentiallySurjective := by
    intro j
    refine ⟨-j, ?_⟩
    exact (integerIncidence_approxBisim_iff (-(-j)) j).mpr (by omega)

/-- The concrete corollary: `quotientResonance_iff` instantiated (for the
first time in the project) against a genuine non-`identity` criterion,
combined with the pre-existing `integerQuotientResonanceCongruent` witness.
Quotient-level resonance on `integerIncidence` is invariant under negating
all three representatives. -/
theorem integerQuotientResonance_neg_iff (i j k : Int) :
    quotientResonance integerIncidence
      (Quotient.mk (approxBisimSetoid integerIncidence) (-i))
      (Quotient.mk (approxBisimSetoid integerIncidence) (-j))
      (Quotient.mk (approxBisimSetoid integerIncidence) (-k)) ↔
    quotientResonance integerIncidence
      (Quotient.mk (approxBisimSetoid integerIncidence) i)
      (Quotient.mk (approxBisimSetoid integerIncidence) j)
      (Quotient.mk (approxBisimSetoid integerIncidence) k) := by
  have h :=
    integerNegationQuotientCriterion.quotientResonance_iff
      integerQuotientResonanceCongruent
      (qi := Quotient.mk (approxBisimSetoid integerIncidence) i)
      (qj := Quotient.mk (approxBisimSetoid integerIncidence) j)
      (qk := Quotient.mk (approxBisimSetoid integerIncidence) k)
  exact h

/-- The `integerIncidence` negation self-map is a
`TranslationPreservation.BoundaryShapeTranslation`
(`integerNegationBoundaryShapeTranslation`, cycle 73), so cycle 75's generic
`TranslationPreservation.BoundaryShapeTranslation.toIncidenceBoundaryObservationEmbedding`
(`Coherent.lean`) converts it directly into an
`IncidenceBoundaryObservationEmbedding integerIncidence integerIncidence` --
the first connection in this project between the `TranslationPreservation`
hierarchy and the boundary-observation internal-logic layer
(`IncidenceBoundaryEntails`, `Logic.lean`). Negating every index in a context
and formula together leaves `integerIncidence`'s boundary-observation
entailment invariant. -/
theorem integerNegation_incidenceBoundaryEntails_iff
    (context : List (Formula Int)) (formula : Formula Int) :
    IncidenceBoundaryEntails integerIncidence
        (Formula.mapContext (fun value => -value) context)
        (formula.map (fun value => -value)) ↔
      IncidenceBoundaryEntails integerIncidence context formula :=
  integerNegationBoundaryShapeTranslation.toIncidenceBoundaryObservationEmbedding.entails_iff
    context formula

/-- The `IncidenceLeafEntails` (rather than `IncidenceBoundaryEntails`)
counterpart of `integerNegation_incidenceBoundaryEntails_iff`, from the same
embedding via `IncidenceBoundaryObservationEmbedding.leafEntails_iff`. -/
theorem integerNegation_incidenceLeafEntails_iff
    (context : List (Formula Int)) (formula : Formula Int) :
    IncidenceLeafEntails integerIncidence
        (Formula.mapContext (fun value => -value) context)
        (formula.map (fun value => -value)) ↔
      IncidenceLeafEntails integerIncidence context formula :=
  integerNegationBoundaryShapeTranslation.toIncidenceBoundaryObservationEmbedding.leafEntails_iff
    context formula

/- Research cycle 77 (see RESEARCH_LOG.md): cycle 76 flagged
   `BoundarySquareZeroEverywhere` as the sole remaining obstruction to
   instantiating `CoherentIncidence` on `integerIncidence`, and hypothesized
   it would fail for the same "unbounded chain" reason `natIncidence` does.
   Checked directly rather than assumed: `integerIncidence`'s positive side
   IS literally `natIncidence`'s chain re-embedded via `.ofNat`
   (`integerBoundary_ofNat_succ` has the identical shape as `peanoBoundary`'s
   successor case), so the same chain link `2 ← 1 ← 0` cycle 8/9 used for
   `natIncidence` witnesses the failure here too -- via the newly packaged
   general theorem `not_boundarySquareZeroEverywhere_of_single_link_chain`
   (root file) rather than a fresh `decide`-based countermodel. -/
theorem integerIncidence_not_boundarySquareZeroEverywhere :
    ¬ BoundarySquareZeroEverywhere integerIncidence :=
  not_boundarySquareZeroEverywhere_of_single_link_chain integerIncidence
    [(2 : Int), 1, 0] 2 1 0
    (positiveIntegerEndpoint 1) (positiveIntegerEndpoint 0)
    (by simpa using integerBoundary_ofNat_succ 1) rfl (by decide)
    (by simpa using integerBoundary_ofNat_succ 0) rfl (by decide)
    (by decide) (by decide) (by decide)

/- The mirror-image witness on the negative side: `integerIncidence`'s
   negative chain `0 ← -1 ← -2 ← ...` (`integerBoundary_negSucc`,
   `negativeIntegerEndpoint`) has exactly the same single-face shape, so the
   same general theorem applies to the chain link `-2 ← -1 ← 0`. This is a
   SECOND, independent witness to the same conclusion
   (`integerIncidence_not_boundarySquareZeroEverywhere` above already
   suffices on its own) -- recorded to confirm `integerIncidence`'s
   "two-directional unboundedness" is genuinely symmetric, not just
   positive-side, before concluding anything about which structural shape is
   doing the work. -/
theorem integerIncidence_not_boundarySquareZeroEverywhere_negative_chain :
    ¬ BoundarySquareZeroEverywhere integerIncidence :=
  not_boundarySquareZeroEverywhere_of_single_link_chain integerIncidence
    [(-2 : Int), -1, 0] (-2) (-1) 0
    (negativeIntegerEndpoint 1) (negativeIntegerEndpoint 0)
    (by simpa using integerBoundary_negSucc 1) rfl (by decide)
    (by simpa using integerBoundary_negSucc 0) rfl (by decide)
    (by decide) (by decide) (by decide)

end IncidenceCore
