import IncidenceTheory.ReferenceFoundationSaturation

/-! Language-layered prime Henkin extensions. -/

namespace IncidenceCore.ReferenceFoundation

noncomputable local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

noncomputable def layerCompletionStage (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (level : Nat) : Nat → Set Formula
  | 0 => base
  | stage + 1 =>
      let prior := layerCompletionStage infinity base target level stage
      let body := layerFormulaAt level stage
      let candidate :=
        if SetDerives infinity (Set.insert body prior) target
        then prior else Set.insert body prior
      let witness := body.instantiate
        (.const (layerSaturationConstant level stage))
      if SetDerives infinity candidate (.ex body)
      then Set.insert witness candidate else candidate

theorem layerCompletionStage_subset_next (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (level stage : Nat) :
    layerCompletionStage infinity base target level stage ⊆
      layerCompletionStage infinity base target level (stage + 1) := by
  intro formula member
  simp only [layerCompletionStage]
  split
  · split
    · exact Set.mem_insert_iff.mpr (Or.inr member)
    · exact member
  · split
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_insert_iff.mpr (Or.inr member)))
    · exact Set.mem_insert_iff.mpr (Or.inr member)

theorem layerCompletionStage_mono (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (level : Nat)
    {first second : Nat} (order : first ≤ second) :
    layerCompletionStage infinity base target level first ⊆
      layerCompletionStage infinity base target level second := by
  induction order with
  | refl => exact Set.Subset.rfl
  | @step second order ih =>
      exact Set.Subset.trans ih
        (layerCompletionStage_subset_next infinity base target level second)

theorem layerCompletionStage_levelBound
    (infinity : InfinitySchema) (base : Set Formula) (target : Formula)
    (level : Nat)
    (baseBound : ∀ formula ∈ base, formula.constLevelBound ≤ level) :
    ∀ stage formula,
      formula ∈ layerCompletionStage infinity base target level stage →
      formula.constLevelBound ≤ level + 1 := by
  intro stage
  induction stage with
  | zero =>
      intro formula member
      exact le_trans (baseBound formula member) (Nat.le_succ level)
  | succ stage ih =>
      intro formula member
      simp only [layerCompletionStage] at member
      split at member
      next candidateDerives =>
        split at member
        next existentialDerives =>
          rcases Set.mem_insert_iff.mp member with rfl | inPrior
          · apply le_trans
              (Formula.constLevelBound_instantiate_const_le
                (layerFormulaAt level stage)
                (layerSaturationConstant level stage))
            simp only [layerSaturationConstant_level]
            exact max_le (layerFormulaAt_levelBound level stage) (le_refl _)
          · exact ih _ inPrior
        next existentialMissing => exact ih _ member
      next candidateAvoids =>
        split at member
        next existentialDerives =>
          rcases Set.mem_insert_iff.mp member with rfl | inCandidate
          · apply le_trans
              (Formula.constLevelBound_instantiate_const_le
                (layerFormulaAt level stage)
                (layerSaturationConstant level stage))
            simp only [layerSaturationConstant_level]
            exact max_le (layerFormulaAt_levelBound level stage) (le_refl _)
          · rcases Set.mem_insert_iff.mp inCandidate with rfl | inPrior
            · exact layerFormulaAt_levelBound level stage
            · exact ih _ inPrior
        next existentialMissing =>
          rcases Set.mem_insert_iff.mp member with rfl | inPrior
          · exact layerFormulaAt_levelBound level stage
          · exact ih _ inPrior

theorem layerCompletionStage_localBound
    (infinity : InfinitySchema) (base : Set Formula) (target : Formula)
    (level : Nat)
    (baseBound : ∀ formula ∈ base, formula.localConstBound level ≤ 0) :
    ∀ stage formula,
      formula ∈ layerCompletionStage infinity base target level stage →
      formula.localConstBound level ≤ layerSaturationBound level stage := by
  intro stage
  induction stage with
  | zero =>
      intro formula member
      exact baseBound formula member
  | succ stage ih =>
      intro formula member
      simp only [layerCompletionStage] at member
      split at member
      next candidateDerives =>
        split at member
        next existentialDerives =>
          rcases Set.mem_insert_iff.mp member with rfl | inPrior
          · apply le_trans
              (Formula.localConstBound_instantiate_const_le
                (layerFormulaAt level stage) level
                (layerSaturationConstant level stage))
            simp only [layerSaturationConstant_level,
              layerSaturationConstant_local, if_pos]
            rw [layerSaturationBound_step]
            exact max_le
              (le_trans (layerFormula_localBound_le_index level stage)
                (Nat.le_succ _))
              (Nat.le_refl _)
          · exact le_trans (ih _ inPrior)
              (layerSaturationBound_le_next level stage)
        next existentialMissing =>
          exact le_trans (ih _ member)
            (layerSaturationBound_le_next level stage)
      next candidateAvoids =>
        split at member
        next existentialDerives =>
          rcases Set.mem_insert_iff.mp member with rfl | inCandidate
          · apply le_trans
              (Formula.localConstBound_instantiate_const_le
                (layerFormulaAt level stage) level
                (layerSaturationConstant level stage))
            simp only [layerSaturationConstant_level,
              layerSaturationConstant_local, if_pos]
            rw [layerSaturationBound_step]
            exact max_le
              (le_trans (layerFormula_localBound_le_index level stage)
                (Nat.le_succ _))
              (Nat.le_refl _)
          · rcases Set.mem_insert_iff.mp inCandidate with rfl | inPrior
            · exact le_trans (layerFormula_localBound_le_index level stage)
                (by rw [layerSaturationBound_step]; exact Nat.le_succ _)
            · exact le_trans (ih _ inPrior)
                (layerSaturationBound_le_next level stage)
        next existentialMissing =>
          rcases Set.mem_insert_iff.mp member with rfl | inPrior
          · exact le_trans (layerFormula_localBound_le_index level stage)
              (by rw [layerSaturationBound_step]; exact Nat.le_succ _)
          · exact le_trans (ih _ inPrior)
              (layerSaturationBound_le_next level stage)

theorem layerCompletionStage_avoids
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {level : Nat}
    (baseLevel : ∀ formula ∈ base, formula.constLevelBound ≤ level)
    (baseLocal : ∀ formula ∈ base, formula.localConstBound level ≤ 0)
    (targetLevel : target.constLevelBound ≤ level)
    (baseAvoids : ¬ SetDerives infinity base target) :
    ∀ stage, ¬ SetDerives infinity
      (layerCompletionStage infinity base target level stage) target := by
  intro stage
  induction stage with
  | zero => exact baseAvoids
  | succ stage ih =>
      simp only [layerCompletionStage]
      let body := layerFormulaAt level stage
      let constant := layerSaturationConstant level stage
      let prior := layerCompletionStage infinity base target level stage
      have bodyFresh : ¬ body.ContainsConst constant := by
        intro contains
        have below := Formula.lt_localConstBound_of_contains contains
          (layerSaturationConstant_level level stage)
        dsimp [constant, body] at below
        rw [layerSaturationConstant_local] at below
        exact (Nat.not_lt_of_ge
          (layerFormula_localBound_le_index level stage)) below
      have priorFresh : ∀ formula ∈ prior,
          ¬ formula.ContainsConst constant := by
        intro formula member contains
        have below := Formula.lt_localConstBound_of_contains contains
          (layerSaturationConstant_level level stage)
        dsimp [constant] at below
        rw [layerSaturationConstant_local] at below
        have bounded := layerCompletionStage_localBound infinity base target level
          baseLocal stage formula member
        exact (Nat.not_lt_of_ge
          (le_trans bounded (Nat.le_max_left _ _))) below
      have targetFresh : ¬ target.ContainsConst constant := by
        intro contains
        have below := Formula.lt_constLevelBound_of_contains contains
        rw [layerSaturationConstant_level] at below
        exact (Nat.not_lt_of_ge targetLevel) below
      split
      next candidateDerives =>
        split
        next existentialDerives =>
          intro derivesTarget
          exact ih (SetDerives.eliminate_fresh_witness bodyFresh priorFresh
            targetFresh existentialDerives derivesTarget)
        next existentialMissing => exact ih
      next candidateAvoids =>
        have candidateAvoidsTarget : ¬ SetDerives infinity
            (Set.insert body prior) target := candidateAvoids
        split
        next existentialDerives =>
          intro derivesTarget
          have candidateFresh : ∀ formula ∈ Set.insert body prior,
              ¬ formula.ContainsConst constant := by
            intro formula member
            rcases Set.mem_insert_iff.mp member with rfl | inPrior
            · exact bodyFresh
            · exact priorFresh formula inPrior
          exact candidateAvoidsTarget
            (SetDerives.eliminate_fresh_witness bodyFresh candidateFresh
              targetFresh existentialDerives derivesTarget)
        next existentialMissing => exact candidateAvoidsTarget

def layerCompletionChain (infinity : InfinitySchema) (base : Set Formula)
    (target : Formula) (level : Nat) : Set (Set Formula) :=
  Set.range (layerCompletionStage infinity base target level)

def layerCompletionClosure (infinity : InfinitySchema) (base : Set Formula)
    (target : Formula) (level : Nat) : Set Formula :=
  ⋃₀ layerCompletionChain infinity base target level

theorem layerCompletionChain_nonempty (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (level : Nat) :
    (layerCompletionChain infinity base target level).Nonempty :=
  ⟨layerCompletionStage infinity base target level 0, ⟨0, rfl⟩⟩

theorem layerCompletionChain_isChain (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (level : Nat) :
    IsChain (fun left right : Set Formula => left ⊆ right)
      (layerCompletionChain infinity base target level) := by
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩ distinct
  rcases Nat.le_total first second with order | order
  · exact Or.inl (layerCompletionStage_mono infinity base target level order)
  · exact Or.inr (layerCompletionStage_mono infinity base target level order)

theorem layerCompletionStage_subset_closure (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (level stage : Nat) :
    layerCompletionStage infinity base target level stage ⊆
      layerCompletionClosure infinity base target level :=
  Set.subset_sUnion_of_mem ⟨stage, rfl⟩

theorem base_subset_layerCompletionClosure (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (level : Nat) :
    base ⊆ layerCompletionClosure infinity base target level := by
  simpa [layerCompletionStage] using
    layerCompletionStage_subset_closure infinity base target level 0

theorem layerCompletionClosure_avoids
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {level : Nat}
    (baseLevel : ∀ formula ∈ base, formula.constLevelBound ≤ level)
    (baseLocal : ∀ formula ∈ base, formula.localConstBound level ≤ 0)
    (targetLevel : target.constLevelBound ≤ level)
    (baseAvoids : ¬ SetDerives infinity base target) :
    ¬ SetDerives infinity
      (layerCompletionClosure infinity base target level) target := by
  intro derivesTarget
  rcases derivesTarget with ⟨context, contextIn, derivation⟩
  rcases chain_contains_context
      (layerCompletionChain_nonempty infinity base target level)
      (layerCompletionChain_isChain infinity base target level)
      (fun formula member => contextIn formula member) with
    ⟨theory, ⟨stage, rfl⟩, contextStage⟩
  exact layerCompletionStage_avoids baseLevel baseLocal targetLevel baseAvoids stage
    ⟨context, contextStage, derivation⟩

theorem layerCompletionClosure_levelBound
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {level : Nat}
    (baseLevel : ∀ formula ∈ base, formula.constLevelBound ≤ level) :
    ∀ formula ∈ layerCompletionClosure infinity base target level,
      formula.constLevelBound ≤ level + 1 := by
  intro formula member
  rcases Set.mem_sUnion.mp member with ⟨theory, ⟨stage, rfl⟩, inStage⟩
  exact layerCompletionStage_levelBound infinity base target level baseLevel
    stage formula inStage

theorem layerCompletionClosure_decides_available
    (infinity : InfinitySchema) (base : Set Formula) (target : Formula)
    (level : Nat) {formula : Formula}
    (available : formula.constLevelBound ≤ level + 1) :
    formula ∈ layerCompletionClosure infinity base target level ∨
      SetDerives infinity
        (Set.insert formula (layerCompletionClosure infinity base target level))
        target := by
  let stage := Nat.pair (Encodable.encode formula) 0
  let prior := layerCompletionStage infinity base target level stage
  have scheduled : layerFormulaAt level stage = formula :=
    layerFormulaAt_pair available 0
  by_cases derives : SetDerives infinity (Set.insert formula prior) target
  · apply Or.inr
    apply SetDerives.mono _ derives
    intro item member
    rcases Set.mem_insert_iff.mp member with rfl | inPrior
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_iff.mpr (Or.inr
        (layerCompletionStage_subset_closure infinity base target level stage
          inPrior))
  · apply Or.inl
    apply layerCompletionStage_subset_closure infinity base target level (stage + 1)
    simp only [layerCompletionStage]
    rw [scheduled, if_neg derives]
    split
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert _ _))
    · exact Set.mem_insert _ _

theorem layerCompletionClosure_closed_available
    {infinity : InfinitySchema} {base : Set Formula} {target formula : Formula}
    {level : Nat}
    (available : formula.constLevelBound ≤ level + 1)
    (avoids : ¬ SetDerives infinity
      (layerCompletionClosure infinity base target level) target)
    (derivation : SetDerives infinity
      (layerCompletionClosure infinity base target level) formula) :
    formula ∈ layerCompletionClosure infinity base target level := by
  rcases layerCompletionClosure_decides_available infinity base target level
      available with member | insertionDerives
  · exact member
  · exact False.elim (avoids
      (SetDerives.eliminate_insert derivation insertionDerives))

theorem layerCompletionClosure_witness
    {infinity : InfinitySchema} {base : Set Formula} {target body : Formula}
    {level : Nat}
    (baseLevel : ∀ formula ∈ base, formula.constLevelBound ≤ level)
    (member : (.ex body) ∈
      layerCompletionClosure infinity base target level) :
    ∃ term : Term,
      term.constLevelBound ≤ level + 1 ∧
      body.instantiate term ∈
        layerCompletionClosure infinity base target level := by
  rcases Set.mem_sUnion.mp member with
    ⟨theory, ⟨stage, rfl⟩, inStage⟩
  have bodyAvailable : body.constLevelBound ≤ level + 1 := by
    have existentialBound := layerCompletionStage_levelBound infinity base target
      level baseLevel stage (.ex body) inStage
    exact existentialBound
  let witnessStage := Nat.pair (Encodable.encode body) stage
  have stageOrder : stage ≤ witnessStage := Nat.right_le_pair _ _
  have existentialAtWitness : SetDerives infinity
      (layerCompletionStage infinity base target level witnessStage) (.ex body) :=
    SetDerives.of_mem
      (layerCompletionStage_mono infinity base target level stageOrder inStage)
  have scheduled : layerFormulaAt level witnessStage = body :=
    layerFormulaAt_pair bodyAvailable stage
  let prior := layerCompletionStage infinity base target level witnessStage
  have priorSubsetCandidate : prior ⊆
      (if SetDerives infinity (Set.insert body prior) target
       then prior else Set.insert body prior) := by
    split
    · exact Set.Subset.rfl
    · exact Set.subset_insert _ _
  have derivesCandidate : SetDerives infinity
      (if SetDerives infinity (Set.insert body prior) target
       then prior else Set.insert body prior) (.ex body) :=
    SetDerives.mono priorSubsetCandidate existentialAtWitness
  let term : Term := .const (layerSaturationConstant level witnessStage)
  refine ⟨term, ?_, layerCompletionStage_subset_closure infinity base target level
    (witnessStage + 1) ?_⟩
  · simp [term, Term.constLevelBound, layerSaturationConstant_level]
  · simp only [layerCompletionStage]
    rw [scheduled, if_pos derivesCandidate]
    exact Set.mem_insert _ _

theorem Term.ConstFree.constLevelBound_eq_zero
    {term : Term} (free : term.ConstFree) : term.constLevelBound = 0 := by
  induction term with
  | var index => rfl
  | «const» index => exact False.elim free
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp [Term.constLevelBound, ihLeft free.1, ihRight free.2]
  | union term ih => exact ih free
  | powerset term ih => exact ih free

theorem Formula.ConstFree.constLevelBound_eq_zero
    {formula : Formula} (free : formula.ConstFree) :
    formula.constLevelBound = 0 := by
  induction formula with
  | mem left right =>
      simp [Formula.constLevelBound, free.1.constLevelBound_eq_zero,
        free.2.constLevelBound_eq_zero]
  | eq left right =>
      simp [Formula.constLevelBound, free.1.constLevelBound_eq_zero,
        free.2.constLevelBound_eq_zero]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.constLevelBound, ihLeft free.1, ihRight free.2]
  | or left right ihLeft ihRight =>
      simp [Formula.constLevelBound, ihLeft free.1, ihRight free.2]
  | imp left right ihLeft ihRight =>
      simp [Formula.constLevelBound, ihLeft free.1, ihRight free.2]
  | all body ih => exact ih free
  | ex body ih => exact ih free

structure LayeredPrimeTheory (infinity : InfinitySchema) where
  cutoff : Nat
  theory : Set Formula
  bounded : ∀ {formula}, formula ∈ theory →
    formula.constLevelBound ≤ cutoff
  closed : ∀ {formula}, formula.constLevelBound ≤ cutoff →
    SetDerives infinity theory formula → formula ∈ theory
  consistent : Formula.bot ∉ theory
  primeOr : ∀ {left right},
    max left.constLevelBound right.constLevelBound ≤ cutoff →
    ((.or left right) ∈ theory ↔ left ∈ theory ∨ right ∈ theory)
  axioms : ∀ {formula}, Axiom infinity formula → formula ∈ theory
  witness : ∀ {body}, (.ex body) ∈ theory →
    ∃ term : Term, term.constLevelBound ≤ cutoff ∧
      body.instantiate term ∈ theory

theorem LayeredPrimeTheory.derives_iff_mem
    {infinity : InfinitySchema} (world : LayeredPrimeTheory infinity)
    {formula : Formula} (available : formula.constLevelBound ≤ world.cutoff) :
    SetDerives infinity world.theory formula ↔ formula ∈ world.theory :=
  ⟨world.closed available, SetDerives.of_mem⟩

theorem LayeredPrimeTheory.bot_iff
    {infinity : InfinitySchema} (world : LayeredPrimeTheory infinity) :
    Formula.bot ∈ world.theory ↔ False :=
  ⟨world.consistent, False.elim⟩

theorem LayeredPrimeTheory.and_iff
    {infinity : InfinitySchema} (world : LayeredPrimeTheory infinity)
    {left right : Formula}
    (available : max left.constLevelBound right.constLevelBound ≤ world.cutoff) :
    ((.and left right) ∈ world.theory ↔
      left ∈ world.theory ∧ right ∈ world.theory) := by
  constructor
  · intro conjunction
    have proof := SetDerives.of_mem (infinity := infinity) conjunction
    rcases proof with ⟨context, contextIn, derivation⟩
    exact ⟨world.closed (le_trans (Nat.le_max_left _ _) available)
      ⟨context, contextIn, Derives.andElimLeft derivation⟩,
      world.closed (le_trans (Nat.le_max_right _ _) available)
      ⟨context, contextIn, Derives.andElimRight derivation⟩⟩
  · rintro ⟨leftMember, rightMember⟩
    exact world.closed available
      (SetDerives.andIntro (SetDerives.of_mem leftMember)
        (SetDerives.of_mem rightMember))

theorem LayeredPrimeTheory.ex_iff
    {infinity : InfinitySchema} (world : LayeredPrimeTheory infinity)
    {body : Formula} (available : body.constLevelBound ≤ world.cutoff) :
    ((.ex body) ∈ world.theory ↔
      ∃ term : Term, term.constLevelBound ≤ world.cutoff ∧
        body.instantiate term ∈ world.theory) := by
  constructor
  · exact world.witness
  · rintro ⟨term, termBound, instanceMember⟩
    apply world.closed (formula := .ex body) available
    rcases SetDerives.of_mem (infinity := infinity) instanceMember with
      ⟨context, contextIn, derivation⟩
    exact ⟨context, contextIn, Derives.exIntro term derivation⟩

theorem LayeredPrimeTheory.imp_forward
    {infinity : InfinitySchema}
    {current future : LayeredPrimeTheory infinity} {left right : Formula}
    (included : current.theory ⊆ future.theory)
    (rightAvailable : right.constLevelBound ≤ future.cutoff)
    (implication : (.imp left right) ∈ current.theory)
    (premise : left ∈ future.theory) : right ∈ future.theory := by
  apply future.closed rightAvailable
  exact SetDerives.impElim
    (SetDerives.of_mem (included implication)) (SetDerives.of_mem premise)

theorem LayeredPrimeTheory.all_forward
    {infinity : InfinitySchema}
    {current future : LayeredPrimeTheory infinity} {body : Formula}
    (included : current.theory ⊆ future.theory) (term : Term)
    (instanceAvailable : (body.instantiate term).constLevelBound ≤ future.cutoff)
    (universal : (.all body) ∈ current.theory) :
    body.instantiate term ∈ future.theory := by
  apply future.closed instanceAvailable
  rcases SetDerives.of_mem (infinity := infinity) (included universal) with
    ⟨context, contextIn, derivation⟩
  exact ⟨context, contextIn, Derives.allElim derivation term⟩

theorem layerCompletionClosure_primeOr
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {level : Nat} {left right : Formula}
    (available : max left.constLevelBound right.constLevelBound ≤ level + 1)
    (avoids : ¬ SetDerives infinity
      (layerCompletionClosure infinity base target level) target) :
    (.or left right) ∈ layerCompletionClosure infinity base target level ↔
      left ∈ layerCompletionClosure infinity base target level ∨
      right ∈ layerCompletionClosure infinity base target level := by
  constructor
  · intro disjunction
    by_contra neither
    simp only [not_or] at neither
    have leftAvailable : left.constLevelBound ≤ level + 1 :=
      le_trans (Nat.le_max_left _ _) available
    have rightAvailable : right.constLevelBound ≤ level + 1 :=
      le_trans (Nat.le_max_right _ _) available
    rcases layerCompletionClosure_decides_available infinity base target level
        leftAvailable with leftMember | leftDerives
    · exact neither.1 leftMember
    rcases layerCompletionClosure_decides_available infinity base target level
        rightAvailable with rightMember | rightDerives
    · exact neither.2 rightMember
    exact avoids (SetDerives.orElim_insert (SetDerives.of_mem disjunction)
      leftDerives rightDerives)
  · rintro (leftMember | rightMember)
    · apply layerCompletionClosure_closed_available available avoids
      rcases SetDerives.of_mem leftMember with ⟨context, contextIn, proof⟩
      exact ⟨context, contextIn, Derives.orIntroLeft proof⟩
    · apply layerCompletionClosure_closed_available available avoids
      rcases SetDerives.of_mem rightMember with ⟨context, contextIn, proof⟩
      exact ⟨context, contextIn, Derives.orIntroRight proof⟩

noncomputable def layerCompletionPrimeTheory
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {level : Nat}
    (baseLevel : ∀ formula ∈ base, formula.constLevelBound ≤ level)
    (targetLevel : target.constLevelBound ≤ level)
    (baseAvoids : ¬ SetDerives infinity base target) :
    LayeredPrimeTheory infinity := by
  have baseLocal : ∀ formula ∈ base,
      formula.localConstBound level ≤ 0 := by
    intro formula member
    rw [formula.localConstBound_eq_zero_of_levelBound_le level
      (baseLevel formula member)]
  have avoids : ¬ SetDerives infinity
      (layerCompletionClosure infinity base target level) target :=
    layerCompletionClosure_avoids baseLevel baseLocal targetLevel baseAvoids
  have primeOrProof : ∀ {left right : Formula},
      max left.constLevelBound right.constLevelBound ≤ level + 1 →
      ((.or left right) ∈ layerCompletionClosure infinity base target level ↔
        left ∈ layerCompletionClosure infinity base target level ∨
        right ∈ layerCompletionClosure infinity base target level) := by
    intro left right
    exact fun available =>
      layerCompletionClosure_primeOr (base := base) (target := target)
        (left := left) (right := right) available avoids
  refine {
    cutoff := level + 1
    theory := layerCompletionClosure infinity base target level
    bounded := fun {formula} member =>
      layerCompletionClosure_levelBound (infinity := infinity)
        (target := target) baseLevel formula member
    closed := ?_
    consistent := ?_
    primeOr := primeOrProof
    axioms := ?_
    witness := ?_ }
  · intro formula available derivation
    exact layerCompletionClosure_closed_available available avoids derivation
  · intro botMember
    exact avoids (SetDerives.botElim (SetDerives.of_mem botMember))
  · intro formula valid
    have available : formula.constLevelBound ≤ level + 1 := by
      rw [valid.constFree.constLevelBound_eq_zero]
      omega
    exact layerCompletionClosure_closed_available available avoids
      ⟨[], by simp, Derives.axiom valid⟩
  · intro body member
    exact layerCompletionClosure_witness baseLevel member

theorem layerCompletionPrimeTheory_base_subset
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {level : Nat}
    (baseLevel : ∀ formula ∈ base, formula.constLevelBound ≤ level)
    (targetLevel : target.constLevelBound ≤ level)
    (baseAvoids : ¬ SetDerives infinity base target) :
    base ⊆ (layerCompletionPrimeTheory baseLevel targetLevel baseAvoids).theory :=
  base_subset_layerCompletionClosure infinity base target level

theorem layerCompletionPrimeTheory_target_not_mem
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {level : Nat}
    (baseLevel : ∀ formula ∈ base, formula.constLevelBound ≤ level)
    (targetLevel : target.constLevelBound ≤ level)
    (baseAvoids : ¬ SetDerives infinity base target) :
    target ∉ (layerCompletionPrimeTheory baseLevel targetLevel baseAvoids).theory := by
  intro member
  have baseLocal : ∀ formula ∈ base,
      formula.localConstBound level ≤ 0 := by
    intro formula inBase
    rw [formula.localConstBound_eq_zero_of_levelBound_le level
      (baseLevel formula inBase)]
  exact (layerCompletionClosure_avoids baseLevel baseLocal targetLevel baseAvoids)
    (SetDerives.of_mem member)

theorem LayeredPrimeTheory.future_counterexample_of_imp_not_mem
    {infinity : InfinitySchema} (current : LayeredPrimeTheory infinity)
    {left right : Formula}
    (available : max left.constLevelBound right.constLevelBound ≤ current.cutoff)
    (missing : (.imp left right) ∉ current.theory) :
    ∃ future : LayeredPrimeTheory infinity,
      current.cutoff ≤ future.cutoff ∧
      current.theory ⊆ future.theory ∧
      left ∈ future.theory ∧ right ∉ future.theory := by
  let base := Set.insert left current.theory
  have baseLevel : ∀ formula ∈ base,
      formula.constLevelBound ≤ current.cutoff := by
    intro formula member
    rcases Set.mem_insert_iff.mp member with rfl | inCurrent
    · exact le_trans (Nat.le_max_left _ _) available
    · exact current.bounded inCurrent
  have targetLevel : right.constLevelBound ≤ current.cutoff :=
    le_trans (Nat.le_max_right _ _) available
  have baseAvoids : ¬ SetDerives infinity base right := by
    intro derivesRight
    exact missing (current.closed available
      (SetDerives.impIntro_insert derivesRight))
  let future := layerCompletionPrimeTheory baseLevel targetLevel baseAvoids
  have baseSubset : base ⊆ future.theory :=
    layerCompletionPrimeTheory_base_subset baseLevel targetLevel baseAvoids
  refine ⟨future, by simp [future, layerCompletionPrimeTheory], ?_, ?_, ?_⟩
  · exact Set.Subset.trans (Set.subset_insert _ _) baseSubset
  · exact baseSubset (Set.mem_insert left _)
  · intro member
    exact (layerCompletionClosure_avoids
      (baseLevel := baseLevel)
      (baseLocal := by
        intro formula inBase
        rw [formula.localConstBound_eq_zero_of_levelBound_le current.cutoff
          (baseLevel formula inBase)])
      targetLevel baseAvoids) (SetDerives.of_mem member)

theorem LayeredPrimeTheory.future_counterexample_of_all_not_mem
    {infinity : InfinitySchema} (current : LayeredPrimeTheory infinity)
    {body : Formula} (available : body.constLevelBound ≤ current.cutoff)
    (missing : (.all body) ∉ current.theory) :
    ∃ future : LayeredPrimeTheory infinity,
      current.cutoff ≤ future.cutoff ∧
      current.theory ⊆ future.theory ∧
      ∃ term : Term, term.constLevelBound ≤ future.cutoff ∧
        body.instantiate term ∉ future.theory := by
  let constant := Nat.pair current.cutoff 0
  let term : Term := .const constant
  let target := body.instantiate term
  have constantLevel : constant.unpair.1 = current.cutoff := by
    simp [constant]
  have bodyFresh : ¬ body.ContainsConst constant := by
    intro contains
    have below := Formula.lt_constLevelBound_of_contains contains
    rw [constantLevel] at below
    exact (Nat.not_lt_of_ge available) below
  have theoryFresh : ∀ formula ∈ current.theory,
      ¬ formula.ContainsConst constant := by
    intro formula member contains
    have below := Formula.lt_constLevelBound_of_contains contains
    rw [constantLevel] at below
    exact (Nat.not_lt_of_ge (current.bounded member)) below
  have baseAvoids : ¬ SetDerives infinity current.theory target := by
    intro derivesTarget
    rcases derivesTarget with ⟨context, contextIn, derivation⟩
    have contextFresh : ∀ formula ∈ context,
        ¬ formula.ContainsConst constant := by
      intro formula member
      exact theoryFresh formula (contextIn formula member)
    have abstracted := derivation.abstractConst constant 0
    have derivesBody : Derives infinity
        (context.map (Formula.rename Nat.succ)) body := by
      simpa [target, term,
        Formula.abstractConst_instantiate_const constant bodyFresh,
        Context.map_abstractConst_zero_eq_rename_succ constant contextFresh]
        using abstracted
    exact missing (current.closed available
      ⟨context, contextIn, Derives.allIntro derivesBody⟩)
  have baseLevel : ∀ formula ∈ current.theory,
      formula.constLevelBound ≤ current.cutoff + 1 := by
    intro formula member
    exact le_trans (current.bounded member) (Nat.le_succ _)
  have targetLevel : target.constLevelBound ≤ current.cutoff + 1 := by
    apply le_trans (Formula.constLevelBound_instantiate_const_le body constant)
    rw [constantLevel]
    exact max_le (le_trans available (Nat.le_succ _)) (Nat.le_refl _)
  let future := layerCompletionPrimeTheory baseLevel targetLevel baseAvoids
  have baseSubset : current.theory ⊆ future.theory :=
    layerCompletionPrimeTheory_base_subset baseLevel targetLevel baseAvoids
  refine ⟨future, by simp [future, layerCompletionPrimeTheory]; omega, baseSubset,
    term, ?_, ?_⟩
  · simp [term, Term.constLevelBound, constantLevel, future,
      layerCompletionPrimeTheory]
  · intro member
    exact (layerCompletionClosure_avoids
      (baseLevel := baseLevel)
      (baseLocal := by
        intro formula inBase
        rw [formula.localConstBound_eq_zero_of_levelBound_le
          (current.cutoff + 1) (baseLevel formula inBase)])
      targetLevel baseAvoids) (SetDerives.of_mem member)

end IncidenceCore.ReferenceFoundation
