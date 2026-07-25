import IncidenceTheory.GeneralResonanceInternalLanguage

namespace IncidenceCore

universe u

def ResonanceLawDerivesFrom
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (extra : List (Formula (ResonanceAtom I)))
    (formula : Formula (ResonanceAtom I)) : Prop :=
  ∃ support : List (Formula (ResonanceAtom I)),
    (∀ assumption, assumption ∈ support →
      IsResonanceLawFormula inc assumption) ∧
      Derives (extra ++ support) formula

theorem resonanceLawDerivesFrom_nil_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : Formula (ResonanceAtom I)) :
    ResonanceLawDerivesFrom inc [] formula ↔
      ResonanceLawDerives inc formula := by
  constructor <;> rintro ⟨support, laws, derivation⟩ <;>
    exact ⟨support, laws, by simpa using derivation⟩

theorem resonanceLawDerivesFrom_extra_mono
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : List (Formula (ResonanceAtom I))}
    {formula : Formula (ResonanceAtom I)}
    (subset : ContextSubset source target) :
    ResonanceLawDerivesFrom inc source formula →
      ResonanceLawDerivesFrom inc target formula := by
  rintro ⟨support, laws, derivation⟩
  refine ⟨support, laws, ?_⟩
  apply derives_weaken (source := source ++ support)
  · intro assumption member
    rcases List.mem_append.mp member with sourceMember | supportMember
    · exact List.mem_append.mpr (Or.inl (subset assumption sourceMember))
    · exact List.mem_append.mpr (Or.inr supportMember)
  · exact derivation

theorem resonanceLawDerivesFrom_finite_support
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (extra context : List (Formula (ResonanceAtom I)))
    (contains : ∀ assumption, assumption ∈ context →
      ResonanceLawDerivesFrom inc extra assumption) :
    ∃ support : List (Formula (ResonanceAtom I)),
      (∀ assumption, assumption ∈ support →
        IsResonanceLawFormula inc assumption) ∧
      ∀ assumption, assumption ∈ context →
        Derives (extra ++ support) assumption := by
  induction context with
  | nil =>
      exact ⟨[], by simp, by simp⟩
  | cons head tail ih =>
      rcases contains head (by simp) with ⟨headSupport, headLaws, headDerives⟩
      rcases ih (by
        intro assumption member
        exact contains assumption (List.mem_cons_of_mem _ member)) with
        ⟨tailSupport, tailLaws, tailDerives⟩
      refine ⟨headSupport ++ tailSupport, ?_, ?_⟩
      · intro assumption member
        rcases List.mem_append.mp member with headMember | tailMember
        · exact headLaws assumption headMember
        · exact tailLaws assumption tailMember
      · intro assumption member
        rcases List.mem_cons.mp member with rfl | tailMember
        · apply derives_weaken (source := extra ++ headSupport)
          · intro formula formulaMember
            rcases List.mem_append.mp formulaMember with extraMember | headMember
            · exact List.mem_append.mpr (Or.inl extraMember)
            · exact List.mem_append.mpr
                (Or.inr (List.mem_append.mpr (Or.inl headMember)))
          · exact headDerives
        · apply derives_weaken (source := extra ++ tailSupport)
          · intro formula formulaMember
            rcases List.mem_append.mp formulaMember with extraMember | tailMember'
            · exact List.mem_append.mpr (Or.inl extraMember)
            · exact List.mem_append.mpr
                (Or.inr (List.mem_append.mpr (Or.inr tailMember')))
          · exact tailDerives assumption tailMember

theorem resonanceLawDerivesFrom_closed
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {extra context : List (Formula (ResonanceAtom I))}
    {formula : Formula (ResonanceAtom I)}
    (contains : ∀ assumption, assumption ∈ context →
      ResonanceLawDerivesFrom inc extra assumption)
    (derivation : Derives context formula) :
    ResonanceLawDerivesFrom inc extra formula := by
  rcases resonanceLawDerivesFrom_finite_support inc extra context contains with
    ⟨support, laws, supportDerives⟩
  exact ⟨support, laws, derives_substitute supportDerives derivation⟩

theorem resonanceLawDerives_closed
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {context : List (Formula (ResonanceAtom I))}
    {formula : Formula (ResonanceAtom I)}
    (contains : ∀ assumption, assumption ∈ context →
      ResonanceLawDerives inc assumption)
    (derivation : Derives context formula) :
    ResonanceLawDerives inc formula := by
  rw [← resonanceLawDerivesFrom_nil_iff]
  apply resonanceLawDerivesFrom_closed
  intro assumption member
  exact (resonanceLawDerivesFrom_nil_iff inc assumption).mpr
    (contains assumption member)
  exact derivation

def resonanceLawDeductivelyClosedTheory
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    DeductivelyClosedTheory (ResonanceAtom I) where
  contains := ResonanceLawDerives inc
  closed := resonanceLawDerives_closed

theorem resonanceLawAxiom_mem_closedTheory
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (law : ResonanceLawAxiom inc) :
    (resonanceLawDeductivelyClosedTheory inc).contains law.formula := by
  refine ⟨[law.formula], ?_, Derives.ax (by simp)⟩
  intro assumption member
  have : assumption = law.formula := by simpa using member
  subst assumption
  exact ⟨law, rfl⟩

def ResonanceLawAvoids
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (extra : List (Formula (ResonanceAtom I)))
    (forbidden : Formula (ResonanceAtom I)) : Prop :=
  ¬ ResonanceLawDerivesFrom inc extra forbidden

theorem resonanceLawDerivesFrom_or_elim
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (current : List (Formula (ResonanceAtom I)))
    (left right forbidden : Formula (ResonanceAtom I))
    (hor : ResonanceLawDerivesFrom inc current (.or left right))
    (hleft : ResonanceLawDerivesFrom inc (left :: current) forbidden)
    (hright : ResonanceLawDerivesFrom inc (right :: current) forbidden) :
    ResonanceLawDerivesFrom inc current forbidden := by
  rcases hor with ⟨orSupport, orLaws, hor⟩
  rcases hleft with ⟨leftSupport, leftLaws, hleft⟩
  rcases hright with ⟨rightSupport, rightLaws, hright⟩
  let support := orSupport ++ leftSupport ++ rightSupport
  refine ⟨support, ?_, ?_⟩
  · intro assumption member
    rcases List.mem_append.mp member with firstMember | rightMember
    · rcases List.mem_append.mp firstMember with orMember | leftMember
      · exact orLaws assumption orMember
      · exact leftLaws assumption leftMember
    · exact rightLaws assumption rightMember
  · apply Derives.orE (p := left) (q := right)
    · apply derives_weaken (source := current ++ orSupport)
      · intro assumption member
        rcases List.mem_append.mp member with currentMember | orMember
        · exact List.mem_append.mpr (Or.inl currentMember)
        · exact List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inl
              (List.mem_append.mpr (Or.inl orMember)))))
      · exact hor
    · apply derives_weaken (source := (left :: current) ++ leftSupport)
      · intro assumption member
        rcases List.mem_append.mp member with currentMember | leftMember
        · rcases List.mem_cons.mp currentMember with rfl | currentMember
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inl currentMember))
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inl
              (List.mem_append.mpr (Or.inr leftMember))))))
      · exact hleft
    · apply derives_weaken (source := (right :: current) ++ rightSupport)
      · intro assumption member
        rcases List.mem_append.mp member with currentMember | rightMember
        · rcases List.mem_cons.mp currentMember with rfl | currentMember
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inl currentMember))
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr
            (List.mem_append.mpr (Or.inr rightMember))))
      · exact hright

theorem resonanceLawAvoids_or_extension_left_or_right
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (current : List (Formula (ResonanceAtom I)))
    (left right forbidden : Formula (ResonanceAtom I))
    (avoids : ResonanceLawAvoids inc current forbidden)
    (hor : ResonanceLawDerivesFrom inc current (.or left right)) :
    ResonanceLawAvoids inc (left :: current) forbidden ∨
      ResonanceLawAvoids inc (right :: current) forbidden := by
  by_cases leftAvoids : ResonanceLawAvoids inc (left :: current) forbidden
  · exact Or.inl leftAvoids
  · right
    intro rightDerives
    apply avoids
    exact resonanceLawDerivesFrom_or_elim current left right forbidden hor
      (Classical.byContradiction (fun leftAvoids' => leftAvoids leftAvoids'))
      rightDerives

noncomputable def resonanceLawAvoidanceStep
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (forbidden : Formula (ResonanceAtom I))
    (current : List (Formula (ResonanceAtom I))) :
    Formula (ResonanceAtom I) → List (Formula (ResonanceAtom I))
  | .or left right => by
      classical
      exact if hor : ResonanceLawDerivesFrom inc current (.or left right)
        then if ResonanceLawAvoids inc (left :: current) forbidden
          then left :: current else right :: current
        else current
  | _ => current

noncomputable def resonanceLawAvoidanceChain
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I)) :
    Nat → List (Formula (ResonanceAtom I))
  | 0 => []
  | stage + 1 => resonanceLawAvoidanceStep inc forbidden
      (resonanceLawAvoidanceChain inc schedule forbidden stage)
      (schedule.formulaAt stage)

theorem resonanceLawAvoidanceStep_subset
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (forbidden : Formula (ResonanceAtom I))
    (current : List (Formula (ResonanceAtom I)))
    (candidate : Formula (ResonanceAtom I)) :
    ContextSubset current
      (resonanceLawAvoidanceStep inc forbidden current candidate) := by
  cases candidate with
  | atom | top | bot => exact fun _ member => member
  | and | imp => exact fun _ member => member
  | or left right =>
      simp only [resonanceLawAvoidanceStep]
      split
      · split <;> intro formula member <;>
          exact List.mem_cons_of_mem _ member
      · exact fun _ member => member

theorem resonanceLawAvoidanceStep_avoids
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (forbidden : Formula (ResonanceAtom I))
    (current : List (Formula (ResonanceAtom I)))
    (candidate : Formula (ResonanceAtom I))
    (avoids : ResonanceLawAvoids inc current forbidden) :
    ResonanceLawAvoids inc
      (resonanceLawAvoidanceStep inc forbidden current candidate) forbidden := by
  cases candidate <;> simp only [resonanceLawAvoidanceStep]
  all_goals try exact avoids
  case or left right =>
    split
    · rename_i hor
      split
      · assumption
      · rename_i notLeftAvoids
        rcases resonanceLawAvoids_or_extension_left_or_right
          current left right forbidden avoids hor with leftAvoids | rightAvoids
        · exact False.elim (notLeftAvoids leftAvoids)
        · exact rightAvoids
    · exact avoids

theorem resonanceLawAvoidanceChain_subset_succ
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I)) (stage : Nat) :
    ContextSubset (resonanceLawAvoidanceChain inc schedule forbidden stage)
      (resonanceLawAvoidanceChain inc schedule forbidden (stage + 1)) := by
  exact resonanceLawAvoidanceStep_subset inc forbidden _ _

theorem resonanceLawAvoidanceChain_avoids
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    (initial : ResonanceLawAvoids inc [] forbidden) :
    ∀ stage, ResonanceLawAvoids inc
      (resonanceLawAvoidanceChain inc schedule forbidden stage) forbidden := by
  intro stage
  induction stage with
  | zero => exact initial
  | succ stage ih =>
      exact resonanceLawAvoidanceStep_avoids inc forbidden _ _ ih

theorem resonanceLawAvoidanceChain_subset_of_le
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I)) {source target : Nat}
    (le : source ≤ target) :
    ContextSubset (resonanceLawAvoidanceChain inc schedule forbidden source)
      (resonanceLawAvoidanceChain inc schedule forbidden target) := by
  induction target generalizing source with
  | zero =>
      have : source = 0 := Nat.eq_zero_of_le_zero le
      subst source
      exact fun _ member => member
  | succ target ih =>
      rcases Nat.lt_or_eq_of_le le with lt | rfl
      · exact fun formula member =>
          resonanceLawAvoidanceChain_subset_succ inc schedule forbidden target
            formula (ih (Nat.le_of_lt_succ lt) formula member)
      · exact fun _ member => member

def resonanceLawAvoidanceLimitDerives
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden formula : Formula (ResonanceAtom I)) : Prop :=
  ∃ stage, ResonanceLawDerivesFrom inc
    (resonanceLawAvoidanceChain inc schedule forbidden stage) formula

theorem resonanceLawAvoidanceLimit_mono
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I)) {source target : Nat}
    (le : source ≤ target) {formula : Formula (ResonanceAtom I)} :
    ResonanceLawDerivesFrom inc
        (resonanceLawAvoidanceChain inc schedule forbidden source) formula →
      ResonanceLawDerivesFrom inc
        (resonanceLawAvoidanceChain inc schedule forbidden target) formula :=
  resonanceLawDerivesFrom_extra_mono
    (resonanceLawAvoidanceChain_subset_of_le inc schedule forbidden le)

theorem resonanceLawAvoidanceLimit_finite_bound
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I)) :
    ∀ context : List (Formula (ResonanceAtom I)),
      (∀ assumption, assumption ∈ context →
        resonanceLawAvoidanceLimitDerives inc schedule forbidden assumption) →
      ∃ stage, ∀ assumption, assumption ∈ context →
        ResonanceLawDerivesFrom inc
          (resonanceLawAvoidanceChain inc schedule forbidden stage) assumption := by
  intro context
  induction context with
  | nil => exact fun _ => ⟨0, by simp⟩
  | cons head tail ih =>
      intro contains
      rcases contains head (by simp) with ⟨headStage, headDerives⟩
      rcases ih (by
        intro assumption member
        exact contains assumption (List.mem_cons_of_mem _ member)) with
        ⟨tailStage, tailDerives⟩
      refine ⟨Nat.max headStage tailStage, ?_⟩
      intro assumption member
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact resonanceLawAvoidanceLimit_mono inc schedule forbidden
          (Nat.le_max_left _ _) headDerives
      · exact resonanceLawAvoidanceLimit_mono inc schedule forbidden
          (Nat.le_max_right _ _) (tailDerives assumption tailMember)

theorem resonanceLawAvoidanceLimit_closed
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    {context : List (Formula (ResonanceAtom I))}
    {formula : Formula (ResonanceAtom I)}
    (contains : ∀ assumption, assumption ∈ context →
      resonanceLawAvoidanceLimitDerives inc schedule forbidden assumption)
    (derivation : Derives context formula) :
    resonanceLawAvoidanceLimitDerives inc schedule forbidden formula := by
  rcases resonanceLawAvoidanceLimit_finite_bound inc schedule forbidden
    context contains with ⟨stage, stageDerives⟩
  exact ⟨stage, resonanceLawDerivesFrom_closed stageDerives derivation⟩

theorem resonanceLawAvoidanceLimit_avoids
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    (initial : ResonanceLawAvoids inc [] forbidden) :
    ¬ resonanceLawAvoidanceLimitDerives inc schedule forbidden forbidden := by
  rintro ⟨stage, derives⟩
  exact resonanceLawAvoidanceChain_avoids inc schedule forbidden initial stage derives

theorem resonanceLawAvoidanceChain_or_choice
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I)) (stage : Nat)
    (left right : Formula (ResonanceAtom I))
    (scheduled : schedule.formulaAt stage = .or left right)
    (hor : ResonanceLawDerivesFrom inc
      (resonanceLawAvoidanceChain inc schedule forbidden stage)
      (.or left right)) :
    left ∈ resonanceLawAvoidanceChain inc schedule forbidden (stage + 1) ∨
      right ∈ resonanceLawAvoidanceChain inc schedule forbidden (stage + 1) := by
  change left ∈ resonanceLawAvoidanceStep inc forbidden
      (resonanceLawAvoidanceChain inc schedule forbidden stage)
      (schedule.formulaAt stage) ∨
    right ∈ resonanceLawAvoidanceStep inc forbidden
      (resonanceLawAvoidanceChain inc schedule forbidden stage)
      (schedule.formulaAt stage)
  rw [scheduled]
  simp only [resonanceLawAvoidanceStep]
  split
  · split
    · exact Or.inl List.mem_cons_self
    · exact Or.inr List.mem_cons_self
  · rename_i notDerives
    exact False.elim (notDerives hor)

theorem resonanceLawAvoidanceLimit_prime
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    {left right : Formula (ResonanceAtom I)} :
    resonanceLawAvoidanceLimitDerives inc schedule forbidden (.or left right) →
      resonanceLawAvoidanceLimitDerives inc schedule forbidden left ∨
        resonanceLawAvoidanceLimitDerives inc schedule forbidden right := by
  rintro ⟨stage, hor⟩
  rcases schedule.revisits (.or left right) stage with
    ⟨later, stageLe, scheduled⟩
  have horLater := resonanceLawAvoidanceLimit_mono inc schedule forbidden
    stageLe hor
  rcases resonanceLawAvoidanceChain_or_choice inc schedule forbidden later
    left right scheduled horLater with leftMember | rightMember
  · exact Or.inl ⟨later + 1,
      ⟨[], by simp, by simpa using (Derives.ax leftMember)⟩⟩
  · exact Or.inr ⟨later + 1,
      ⟨[], by simp, by simpa using (Derives.ax rightMember)⟩⟩

theorem resonanceLawAvoidanceLimit_consistent
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    (initial : ResonanceLawAvoids inc [] forbidden) :
    ¬ resonanceLawAvoidanceLimitDerives inc schedule forbidden .bot := by
  rintro ⟨stage, support, laws, derivesBot⟩
  apply resonanceLawAvoidanceLimit_avoids inc schedule forbidden initial
  exact ⟨stage, support, laws, Derives.botE derivesBot⟩

noncomputable def resonanceLawAvoidancePrimeTheory
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    (initial : ResonanceLawAvoids inc [] forbidden) :
    PrimeTheory (ResonanceAtom I) where
  contains := resonanceLawAvoidanceLimitDerives inc schedule forbidden
  closed := resonanceLawAvoidanceLimit_closed inc schedule forbidden
  consistent := resonanceLawAvoidanceLimit_consistent inc schedule forbidden initial
  prime := resonanceLawAvoidanceLimit_prime inc schedule forbidden

theorem resonanceLawAvoidancePrimeTheory_contains_schema
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    (initial : ResonanceLawAvoids inc [] forbidden)
    (law : ResonanceLawAxiom inc) :
    (resonanceLawAvoidancePrimeTheory inc schedule forbidden initial).contains
      law.formula := by
  refine ⟨0, [law.formula], ?_, ?_⟩
  · intro assumption member
    have : assumption = law.formula := by simpa using member
    subst assumption
    exact ⟨law, rfl⟩
  · exact Derives.ax (by simp)

theorem resonanceLaw_relative_prime_extension
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (forbidden : Formula (ResonanceAtom I))
    (notDerives : ¬ ResonanceLawDerives inc forbidden) :
    ∃ theory : PrimeTheory (ResonanceAtom I),
      (∀ law : ResonanceLawAxiom inc, theory.contains law.formula) ∧
        ¬ theory.contains forbidden := by
  have initial : ResonanceLawAvoids inc [] forbidden := by
    rwa [ResonanceLawAvoids, resonanceLawDerivesFrom_nil_iff]
  exact ⟨resonanceLawAvoidancePrimeTheory inc schedule forbidden initial,
    resonanceLawAvoidancePrimeTheory_contains_schema inc schedule forbidden initial,
    resonanceLawAvoidanceLimit_avoids inc schedule forbidden initial⟩

structure ResonanceLawCanonicalWorld {Atom : Type u}
    (base : PrimeTheory Atom) where
  theory : PrimeTheory Atom
  above : primeTheoryLe base theory

def resonanceLawCanonicalCone {Atom : Type u} (base : PrimeTheory Atom) :
    KripkeModel Atom where
  World := ResonanceLawCanonicalWorld base
  le := fun source target => primeTheoryLe source.theory target.theory
  le_refl := fun _ => primeTheoryLe_refl _
  le_trans := fun first second => primeTheoryLe_trans first second
  valuation := fun world atom => world.theory.contains (.atom atom)
  valuation_mono := fun le holds => le _ holds

theorem resonanceLawCanonicalCone_forces_iff
    {Atom : Type u} (base : PrimeTheory Atom)
    (world : ResonanceLawCanonicalWorld base) :
    ∀ formula : Formula Atom,
      KripkeForces (resonanceLawCanonicalCone base) world formula ↔
        KripkeForces (canonicalKripkeModel Atom) world.theory formula := by
  intro formula
  induction formula generalizing world with
  | atom => exact Iff.rfl
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | and left right leftIH rightIH =>
      exact and_congr (leftIH world) (rightIH world)
  | or left right leftIH rightIH =>
      exact or_congr (leftIH world) (rightIH world)
  | imp left right leftIH rightIH =>
      constructor
      · intro coneForces target le input
        let targetWorld : ResonanceLawCanonicalWorld base :=
          ⟨target, primeTheoryLe_trans world.above le⟩
        have coneInput : KripkeForces (resonanceLawCanonicalCone base)
            targetWorld left := (leftIH targetWorld).mpr input
        have coneOutput := coneForces targetWorld le coneInput
        exact (rightIH targetWorld).mp coneOutput
      · intro canonicalForces target le input
        have canonicalInput : KripkeForces (canonicalKripkeModel Atom)
            target.theory left := (leftIH target).mp input
        have canonicalOutput := canonicalForces target.theory le canonicalInput
        exact (rightIH target).mpr canonicalOutput

theorem resonanceLawCanonicalCone_truth_lemma
    {Atom : Type u} (schedule : RecurrentFormulaSchedule Atom)
    (base : PrimeTheory Atom) (world : ResonanceLawCanonicalWorld base)
    (formula : Formula Atom) :
    KripkeForces (resonanceLawCanonicalCone base) world formula ↔
      world.theory.contains formula := by
  rw [resonanceLawCanonicalCone_forces_iff]
  exact canonical_truth_lemma_of_schedule schedule world.theory formula

theorem resonanceLawCanonicalCone_lawful
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (base : PrimeTheory (ResonanceAtom I))
    (containsSchema : ∀ law : ResonanceLawAxiom inc,
      base.contains law.formula) :
    KripkeResonanceLawModel inc (resonanceLawCanonicalCone base) := by
  intro world
  refine
    { symmetric := ?_, unit_left := ?_, unit_right := ?_,
      type_compatible := ?_ }
  · intro left right mode resonant
    apply world.theory.closed (context :=
      [resonanceSymmetryFormula left right mode,
        resonanceFormula left right mode])
    · intro assumption member
      rcases List.mem_cons.mp member with rfl | member
      · exact world.above _ (containsSchema (.symmetry left right mode))
      · have : assumption = resonanceFormula left right mode := by simpa using member
        subst assumption
        exact resonant
    · exact Derives.impE
        (p := resonanceFormula left right mode)
        (q := resonanceFormula right left mode)
        (Derives.ax (p := resonanceSymmetryFormula left right mode)
          List.mem_cons_self)
        (Derives.ax (p := resonanceFormula left right mode)
          (List.mem_cons_of_mem _ List.mem_cons_self))
  · intro value
    exact world.above _ (containsSchema (.unitLeft value))
  · intro value
    exact world.above _ (containsSchema (.unitRight value))
  · intro left right mode resonant
    apply Classical.byContradiction
    intro mismatch
    have negative := world.above _ (containsSchema (.incompatible mismatch))
    exact world.theory.consistent
      (world.theory.closed (context :=
        [Formula.neg (resonanceFormula left right mode),
          resonanceFormula left right mode]) (by
          intro assumption member
          rcases List.mem_cons.mp member with rfl | member
          · exact negative
          · have : assumption = resonanceFormula left right mode := by
              simpa using member
            subst assumption
            exact resonant)
        (Derives.impE
          (p := resonanceFormula left right mode) (q := .bot)
          (Derives.ax (p := Formula.neg (resonanceFormula left right mode))
            List.mem_cons_self)
          (Derives.ax (p := resonanceFormula left right mode)
            (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem resonanceLaw_canonical_countermodels_of_schedule
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I)) :
    ResonanceLawCanonicalCountermodels inc := by
  refine ⟨?_⟩
  intro formula notDerives
  rcases resonanceLaw_relative_prime_extension inc schedule formula notDerives with
    ⟨base, containsSchema, notContains⟩
  let root : ResonanceLawCanonicalWorld base :=
    ⟨base, primeTheoryLe_refl base⟩
  refine ⟨resonanceLawCanonicalCone base,
    resonanceLawCanonicalCone_lawful base containsSchema, root, ?_⟩
  intro forces
  exact notContains
    ((resonanceLawCanonicalCone_truth_lemma schedule base root formula).mp forces)

theorem resonanceLaw_strongCompleteness_of_schedule
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I)) :
    ResonanceLawStrongCompleteness inc :=
  (resonanceLawStrongCompleteness_iff_countermodels inc).mpr
    (resonanceLaw_canonical_countermodels_of_schedule inc schedule)

theorem resonanceLaw_kripke_complete_of_schedule
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (schedule : RecurrentFormulaSchedule (ResonanceAtom I))
    (formula : Formula (ResonanceAtom I)) :
    ResonanceLawKripkeEntails inc formula ↔
      ResonanceLawDerives inc formula :=
  (resonanceLaw_strongCompleteness_of_schedule inc schedule).iff formula

theorem resonanceLaw_kripke_complete
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (coding : CountableAtomCoding (ResonanceAtom I))
    (formula : Formula (ResonanceAtom I)) :
    ResonanceLawKripkeEntails inc formula ↔
      ResonanceLawDerives inc formula :=
  resonanceLaw_kripke_complete_of_schedule inc
    coding.formulaEnumeration.recurrentSchedule formula

structure ResonanceLawFiniteSupportClosureTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  finite_support : ∀
      (extra context : List (Formula (ResonanceAtom I))),
    (∀ assumption, assumption ∈ context →
      ResonanceLawDerivesFrom inc extra assumption) →
    ∃ support : List (Formula (ResonanceAtom I)),
      (∀ assumption, assumption ∈ support →
        IsResonanceLawFormula inc assumption) ∧
      ∀ assumption, assumption ∈ context →
        Derives (extra ++ support) assumption
  closed : ∀ {context : List (Formula (ResonanceAtom I))}
      {formula : Formula (ResonanceAtom I)},
    (∀ assumption, assumption ∈ context →
      ResonanceLawDerives inc assumption) →
    Derives context formula → ResonanceLawDerives inc formula
  contains_schema : ∀ law : ResonanceLawAxiom inc,
    (resonanceLawDeductivelyClosedTheory inc).contains law.formula

theorem resonanceLawFiniteSupportClosureTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceLawFiniteSupportClosureTheorem inc where
  finite_support := resonanceLawDerivesFrom_finite_support inc
  closed := resonanceLawDerives_closed
  contains_schema := resonanceLawAxiom_mem_closedTheory

structure ResonanceLawStrongCompletenessTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (coding : CountableAtomCoding (ResonanceAtom I)) : Prop where
  finite_support_closed : ResonanceLawFiniteSupportClosureTheorem inc
  canonical_countermodels : ResonanceLawCanonicalCountermodels inc
  strong_completeness : ResonanceLawStrongCompleteness inc
  kripke_complete : ∀ formula : Formula (ResonanceAtom I),
    ResonanceLawKripkeEntails inc formula ↔
      ResonanceLawDerives inc formula

theorem resonanceLawStrongCompletenessTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (coding : CountableAtomCoding (ResonanceAtom I)) :
    ResonanceLawStrongCompletenessTheorem inc coding where
  finite_support_closed := resonanceLawFiniteSupportClosureTheorem inc
  canonical_countermodels := resonanceLaw_canonical_countermodels_of_schedule inc
    coding.formulaEnumeration.recurrentSchedule
  strong_completeness := resonanceLaw_strongCompleteness_of_schedule inc
    coding.formulaEnumeration.recurrentSchedule
  kripke_complete := resonanceLaw_kripke_complete inc coding

end IncidenceCore
