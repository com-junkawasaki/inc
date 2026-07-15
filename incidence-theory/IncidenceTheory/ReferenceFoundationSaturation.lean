import IncidenceTheory.ReferenceFoundationHenkin

/-! Iterated witness closure for intuitionistic prime-theory construction. -/

namespace IncidenceCore.ReferenceFoundation

noncomputable local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

noncomputable def henkinStage (infinity : InfinitySchema)
    (base : Set Formula) (seed : Nat) : Nat → Set Formula
  | 0 => base
  | stage + 1 =>
      let prior := henkinStage infinity base seed stage
      let body := repeatedFormulaAt stage
      let witness := body.instantiate (.const (saturationConstant seed stage))
      if SetDerives infinity prior (.ex body) then Set.insert witness prior else prior

theorem henkinStage_subset_next (infinity : InfinitySchema)
    (base : Set Formula) (seed stage : Nat) :
    henkinStage infinity base seed stage ⊆
      henkinStage infinity base seed (stage + 1) := by
  intro formula member
  simp only [henkinStage]
  split
  · exact Set.mem_insert_iff.mpr (Or.inr member)
  · exact member

theorem henkinStage_mono (infinity : InfinitySchema)
    (base : Set Formula) (seed : Nat) {first second : Nat}
    (order : first ≤ second) :
    henkinStage infinity base seed first ⊆
      henkinStage infinity base seed second := by
  induction order with
  | refl => exact Set.Subset.rfl
  | @step second order ih =>
      exact Set.Subset.trans ih
        (henkinStage_subset_next infinity base seed second)

theorem seed_le_saturationBound (seed stage : Nat) :
    seed ≤ saturationBound seed stage :=
  saturationBound_mono seed (Nat.zero_le stage)

theorem henkinStage_constBound
    (infinity : InfinitySchema) (base : Set Formula) (seed : Nat)
    (baseBound : ∀ formula ∈ base, formula.constBound ≤ seed) :
    ∀ stage formula, formula ∈ henkinStage infinity base seed stage →
      formula.constBound ≤ saturationBound seed stage := by
  intro stage
  induction stage with
  | zero =>
      intro formula member
      exact baseBound formula member
  | succ stage ih =>
      intro formula member
      simp only [henkinStage] at member
      split at member
      next derives =>
        rcases Set.mem_insert_iff.mp member with equal | inPrior
        · subst formula
          apply le_trans
            (Formula.constBound_instantiate_const_le
              (repeatedFormulaAt stage) (saturationConstant seed stage))
          rw [saturationBound_step]
          have bodyBound :=
            repeatedFormula_constBound_le_saturationConstant seed stage
          omega
        · exact le_trans (ih _ inPrior)
            (saturationBound_le_next seed stage)
      next notDerives =>
        exact le_trans (ih _ member) (saturationBound_le_next seed stage)

theorem henkinStage_avoids
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {seed : Nat}
    (baseBound : ∀ formula ∈ base, formula.constBound ≤ seed)
    (targetBound : target.constBound ≤ seed)
    (baseAvoids : ¬ SetDerives infinity base target) :
    ∀ stage, ¬ SetDerives infinity (henkinStage infinity base seed stage) target := by
  intro stage
  induction stage with
  | zero => exact baseAvoids
  | succ stage ih =>
      simp only [henkinStage]
      split
      next derivesExistential =>
        intro derivesTarget
        let body := repeatedFormulaAt stage
        let constant := saturationConstant seed stage
        have bodyFresh : ¬ body.ContainsConst constant := by
          intro contains
          have below := Formula.lt_constBound_of_contains contains
          exact (Nat.not_lt_of_ge
            (repeatedFormula_constBound_le_saturationConstant seed stage)) below
        have theoryFresh : ∀ formula ∈ henkinStage infinity base seed stage,
            ¬ formula.ContainsConst constant := by
          intro formula member contains
          have below := Formula.lt_constBound_of_contains contains
          have bounded := henkinStage_constBound infinity base seed baseBound
            stage formula member
          exact (Nat.not_lt_of_ge
            (le_trans bounded (Nat.le_max_left _ _))) below
        have targetFresh : ¬ target.ContainsConst constant := by
          intro contains
          have below := Formula.lt_constBound_of_contains contains
          have bounded : target.constBound ≤ saturationBound seed stage :=
            le_trans targetBound (seed_le_saturationBound seed stage)
          exact (Nat.not_lt_of_ge
            (le_trans bounded (Nat.le_max_left _ _))) below
        exact ih (SetDerives.eliminate_fresh_witness bodyFresh theoryFresh
          targetFresh derivesExistential derivesTarget)
      next notDerives => exact ih

def henkinChain (infinity : InfinitySchema) (base : Set Formula)
    (seed : Nat) : Set (Set Formula) :=
  Set.range (henkinStage infinity base seed)

theorem henkinChain_nonempty (infinity : InfinitySchema)
    (base : Set Formula) (seed : Nat) :
    (henkinChain infinity base seed).Nonempty :=
  ⟨henkinStage infinity base seed 0, ⟨0, rfl⟩⟩

theorem henkinChain_isChain (infinity : InfinitySchema)
    (base : Set Formula) (seed : Nat) :
    IsChain (fun left right : Set Formula => left ⊆ right)
      (henkinChain infinity base seed) := by
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩ distinct
  rcases Nat.le_total first second with order | order
  · exact Or.inl (henkinStage_mono infinity base seed order)
  · exact Or.inr (henkinStage_mono infinity base seed order)

def henkinClosure (infinity : InfinitySchema) (base : Set Formula)
    (seed : Nat) : Set Formula :=
  ⋃₀ henkinChain infinity base seed

theorem henkinStage_subset_closure (infinity : InfinitySchema)
    (base : Set Formula) (seed stage : Nat) :
    henkinStage infinity base seed stage ⊆
      henkinClosure infinity base seed := by
  exact Set.subset_sUnion_of_mem ⟨stage, rfl⟩

theorem base_subset_henkinClosure (infinity : InfinitySchema)
    (base : Set Formula) (seed : Nat) :
    base ⊆ henkinClosure infinity base seed := by
  simpa [henkinStage] using henkinStage_subset_closure infinity base seed 0

theorem henkinClosure_avoids
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {seed : Nat}
    (baseBound : ∀ formula ∈ base, formula.constBound ≤ seed)
    (targetBound : target.constBound ≤ seed)
    (baseAvoids : ¬ SetDerives infinity base target) :
    ¬ SetDerives infinity (henkinClosure infinity base seed) target := by
  intro derivesTarget
  rcases derivesTarget with ⟨context, contextIn, derivation⟩
  rcases chain_contains_context
      (henkinChain_nonempty infinity base seed)
      (henkinChain_isChain infinity base seed)
      (fun formula member => contextIn formula member) with
    ⟨theory, ⟨stage, rfl⟩, contextStage⟩
  exact henkinStage_avoids baseBound targetBound baseAvoids stage
    ⟨context, contextStage, derivation⟩

theorem henkinClosure_witness
    {infinity : InfinitySchema} {base : Set Formula} {seed : Nat}
    {body : Formula}
    (existential : SetDerives infinity (henkinClosure infinity base seed)
      (.ex body)) :
    ∃ term : Term,
      body.instantiate term ∈ henkinClosure infinity base seed := by
  rcases existential with ⟨context, contextIn, derivation⟩
  rcases chain_contains_context
      (henkinChain_nonempty infinity base seed)
      (henkinChain_isChain infinity base seed)
      (fun formula member => contextIn formula member) with
    ⟨theory, ⟨stage, rfl⟩, contextStage⟩
  let witnessStage := Nat.pair (Encodable.encode body) stage
  have stageOrder : stage ≤ witnessStage := by
    exact Nat.right_le_pair _ _
  have derivesAtWitness : SetDerives infinity
      (henkinStage infinity base seed witnessStage) (.ex body) :=
    SetDerives.mono (henkinStage_mono infinity base seed stageOrder)
      ⟨context, contextStage, derivation⟩
  let term : Term := .const (saturationConstant seed witnessStage)
  refine ⟨term, henkinStage_subset_closure infinity base seed
    (witnessStage + 1) ?_⟩
  have scheduled : repeatedFormulaAt witnessStage = body := by
    exact repeatedFormulaAt_pair body stage
  simp only [henkinStage]
  rw [scheduled]
  rw [if_pos derivesAtWitness]
  exact Set.mem_insert _ _

noncomputable def completionStage (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (seed : Nat) : Nat → Set Formula
  | 0 => base
  | stage + 1 =>
      let prior := completionStage infinity base target seed stage
      let body := repeatedFormulaAt stage
      let candidate :=
        if SetDerives infinity (Set.insert body prior) target
        then prior else Set.insert body prior
      let witness := body.instantiate (.const (saturationConstant seed stage))
      if SetDerives infinity candidate (.ex body)
      then Set.insert witness candidate else candidate

theorem completionStage_subset_next (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (seed stage : Nat) :
    completionStage infinity base target seed stage ⊆
      completionStage infinity base target seed (stage + 1) := by
  intro formula member
  simp only [completionStage]
  split
  · split
    · exact Set.mem_insert_iff.mpr (Or.inr member)
    · exact member
  · split
    · exact Set.mem_insert_iff.mpr (Or.inr
        (Set.mem_insert_iff.mpr (Or.inr member)))
    · exact Set.mem_insert_iff.mpr (Or.inr member)

theorem completionStage_mono (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (seed : Nat)
    {first second : Nat} (order : first ≤ second) :
    completionStage infinity base target seed first ⊆
      completionStage infinity base target seed second := by
  induction order with
  | refl => exact Set.Subset.rfl
  | @step second order ih =>
      exact Set.Subset.trans ih
        (completionStage_subset_next infinity base target seed second)

theorem completionStage_constBound
    (infinity : InfinitySchema) (base : Set Formula) (target : Formula)
    (seed : Nat) (baseBound : ∀ formula ∈ base,
      formula.constBound ≤ seed) :
    ∀ stage formula, formula ∈ completionStage infinity base target seed stage →
      formula.constBound ≤ saturationBound seed stage := by
  intro stage
  induction stage with
  | zero =>
      intro formula member
      exact baseBound formula member
  | succ stage ih =>
      intro formula member
      simp only [completionStage] at member
      split at member
      next candidateDerives =>
        split at member
        next existentialDerives =>
          rcases Set.mem_insert_iff.mp member with equal | inPrior
          · subst formula
            apply le_trans
              (Formula.constBound_instantiate_const_le
                (repeatedFormulaAt stage) (saturationConstant seed stage))
            rw [saturationBound_step]
            have bodyBound :=
              repeatedFormula_constBound_le_saturationConstant seed stage
            omega
          · exact le_trans (ih _ inPrior)
              (saturationBound_le_next seed stage)
        next existentialMissing =>
          exact le_trans (ih _ member) (saturationBound_le_next seed stage)
      next candidateAvoids =>
        split at member
        next existentialDerives =>
          rcases Set.mem_insert_iff.mp member with equal | inCandidate
          · subst formula
            apply le_trans
              (Formula.constBound_instantiate_const_le
                (repeatedFormulaAt stage) (saturationConstant seed stage))
            rw [saturationBound_step]
            have bodyBound :=
              repeatedFormula_constBound_le_saturationConstant seed stage
            omega
          · rcases Set.mem_insert_iff.mp inCandidate with equal | inPrior
            · subst formula
              exact le_trans
                (repeatedFormula_constBound_le_saturationConstant seed stage)
                (by rw [saturationBound_step]; omega)
            · exact le_trans (ih _ inPrior)
                (saturationBound_le_next seed stage)
        next existentialMissing =>
          rcases Set.mem_insert_iff.mp member with equal | inPrior
          · subst formula
            exact le_trans
              (repeatedFormula_constBound_le_saturationConstant seed stage)
              (by rw [saturationBound_step]; omega)
          · exact le_trans (ih _ inPrior)
              (saturationBound_le_next seed stage)

theorem completionStage_avoids
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {seed : Nat}
    (baseBound : ∀ formula ∈ base, formula.constBound ≤ seed)
    (targetBound : target.constBound ≤ seed)
    (baseAvoids : ¬ SetDerives infinity base target) :
    ∀ stage,
      ¬ SetDerives infinity (completionStage infinity base target seed stage)
        target := by
  intro stage
  induction stage with
  | zero => exact baseAvoids
  | succ stage ih =>
      simp only [completionStage]
      split
      next candidateDerives =>
        split
        next existentialDerives =>
          intro derivesTarget
          let body := repeatedFormulaAt stage
          let constant := saturationConstant seed stage
          have bodyFresh : ¬ body.ContainsConst constant := by
            intro contains
            exact (Nat.not_lt_of_ge
              (repeatedFormula_constBound_le_saturationConstant seed stage))
              (Formula.lt_constBound_of_contains contains)
          have priorFresh : ∀ formula ∈
              completionStage infinity base target seed stage,
              ¬ formula.ContainsConst constant := by
            intro formula member contains
            have bounded := completionStage_constBound infinity base target seed
              baseBound stage formula member
            exact (Nat.not_lt_of_ge
              (le_trans bounded (Nat.le_max_left _ _)))
              (Formula.lt_constBound_of_contains contains)
          have targetFresh : ¬ target.ContainsConst constant := by
            intro contains
            have bounded : target.constBound ≤ saturationBound seed stage :=
              le_trans targetBound (seed_le_saturationBound seed stage)
            exact (Nat.not_lt_of_ge
              (le_trans bounded (Nat.le_max_left _ _)))
              (Formula.lt_constBound_of_contains contains)
          exact ih (SetDerives.eliminate_fresh_witness bodyFresh priorFresh
            targetFresh existentialDerives derivesTarget)
        next existentialMissing => exact ih
      next candidateAvoids =>
        have candidateAvoidsTarget : ¬ SetDerives infinity
            (Set.insert (repeatedFormulaAt stage)
              (completionStage infinity base target seed stage)) target :=
          candidateAvoids
        split
        next existentialDerives =>
          intro derivesTarget
          let body := repeatedFormulaAt stage
          let constant := saturationConstant seed stage
          let candidate := Set.insert body
            (completionStage infinity base target seed stage)
          have bodyFresh : ¬ body.ContainsConst constant := by
            intro contains
            exact (Nat.not_lt_of_ge
              (repeatedFormula_constBound_le_saturationConstant seed stage))
              (Formula.lt_constBound_of_contains contains)
          have candidateFresh : ∀ formula ∈ candidate,
              ¬ formula.ContainsConst constant := by
            intro formula member contains
            rcases Set.mem_insert_iff.mp member with rfl | inPrior
            · exact bodyFresh contains
            · have bounded := completionStage_constBound infinity base target seed
                baseBound stage formula inPrior
              exact (Nat.not_lt_of_ge
                (le_trans bounded (Nat.le_max_left _ _)))
                (Formula.lt_constBound_of_contains contains)
          have targetFresh : ¬ target.ContainsConst constant := by
            intro contains
            have bounded : target.constBound ≤ saturationBound seed stage :=
              le_trans targetBound (seed_le_saturationBound seed stage)
            exact (Nat.not_lt_of_ge
              (le_trans bounded (Nat.le_max_left _ _)))
              (Formula.lt_constBound_of_contains contains)
          exact candidateAvoidsTarget
            (SetDerives.eliminate_fresh_witness bodyFresh candidateFresh
              targetFresh existentialDerives derivesTarget)
        next existentialMissing => exact candidateAvoidsTarget

def completionChain (infinity : InfinitySchema) (base : Set Formula)
    (target : Formula) (seed : Nat) : Set (Set Formula) :=
  Set.range (completionStage infinity base target seed)

def completionClosure (infinity : InfinitySchema) (base : Set Formula)
    (target : Formula) (seed : Nat) : Set Formula :=
  ⋃₀ completionChain infinity base target seed

theorem completionChain_nonempty (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (seed : Nat) :
    (completionChain infinity base target seed).Nonempty :=
  ⟨completionStage infinity base target seed 0, ⟨0, rfl⟩⟩

theorem completionChain_isChain (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (seed : Nat) :
    IsChain (fun left right : Set Formula => left ⊆ right)
      (completionChain infinity base target seed) := by
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩ distinct
  rcases Nat.le_total first second with order | order
  · exact Or.inl (completionStage_mono infinity base target seed order)
  · exact Or.inr (completionStage_mono infinity base target seed order)

theorem completionStage_subset_closure (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (seed stage : Nat) :
    completionStage infinity base target seed stage ⊆
      completionClosure infinity base target seed :=
  Set.subset_sUnion_of_mem ⟨stage, rfl⟩

theorem base_subset_completionClosure (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) (seed : Nat) :
    base ⊆ completionClosure infinity base target seed := by
  simpa [completionStage] using
    completionStage_subset_closure infinity base target seed 0

theorem completionClosure_avoids
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {seed : Nat}
    (baseBound : ∀ formula ∈ base, formula.constBound ≤ seed)
    (targetBound : target.constBound ≤ seed)
    (baseAvoids : ¬ SetDerives infinity base target) :
    ¬ SetDerives infinity (completionClosure infinity base target seed) target := by
  intro derivesTarget
  rcases derivesTarget with ⟨context, contextIn, derivation⟩
  rcases chain_contains_context
      (completionChain_nonempty infinity base target seed)
      (completionChain_isChain infinity base target seed)
      (fun formula member => contextIn formula member) with
    ⟨theory, ⟨stage, rfl⟩, contextStage⟩
  exact completionStage_avoids baseBound targetBound baseAvoids stage
    ⟨context, contextStage, derivation⟩

theorem completionClosure_witness
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {seed : Nat} {body : Formula}
    (existential : SetDerives infinity
      (completionClosure infinity base target seed) (.ex body)) :
    ∃ term : Term,
      body.instantiate term ∈ completionClosure infinity base target seed := by
  rcases existential with ⟨context, contextIn, derivation⟩
  rcases chain_contains_context
      (completionChain_nonempty infinity base target seed)
      (completionChain_isChain infinity base target seed)
      (fun formula member => contextIn formula member) with
    ⟨theory, ⟨stage, rfl⟩, contextStage⟩
  let witnessStage := Nat.pair (Encodable.encode body) stage
  have stageOrder : stage ≤ witnessStage := Nat.right_le_pair _ _
  have derivesAtWitness : SetDerives infinity
      (completionStage infinity base target seed witnessStage) (.ex body) :=
    SetDerives.mono
      (completionStage_mono infinity base target seed stageOrder)
      ⟨context, contextStage, derivation⟩
  have scheduled : repeatedFormulaAt witnessStage = body :=
    repeatedFormulaAt_pair body stage
  let prior := completionStage infinity base target seed witnessStage
  have priorSubsetCandidate : prior ⊆
      (if SetDerives infinity (Set.insert body prior) target
       then prior else Set.insert body prior) := by
    split
    · exact Set.Subset.rfl
    · exact Set.subset_insert _ _
  have derivesCandidate : SetDerives infinity
      (if SetDerives infinity (Set.insert body prior) target
       then prior else Set.insert body prior) (.ex body) :=
    SetDerives.mono priorSubsetCandidate derivesAtWitness
  let term : Term := .const (saturationConstant seed witnessStage)
  refine ⟨term, completionStage_subset_closure infinity base target seed
    (witnessStage + 1) ?_⟩
  simp only [completionStage]
  rw [scheduled]
  rw [if_pos derivesCandidate]
  exact Set.mem_insert _ _

theorem completionClosure_decides
    (infinity : InfinitySchema) (base : Set Formula) (target : Formula)
    (seed : Nat) (formula : Formula) :
    formula ∈ completionClosure infinity base target seed ∨
      SetDerives infinity
        (Set.insert formula (completionClosure infinity base target seed)) target := by
  let stage := Nat.pair (Encodable.encode formula) 0
  let prior := completionStage infinity base target seed stage
  have scheduled : repeatedFormulaAt stage = formula :=
    repeatedFormulaAt_pair formula 0
  by_cases derives : SetDerives infinity (Set.insert formula prior) target
  · apply Or.inr
    apply SetDerives.mono _ derives
    intro item member
    rcases Set.mem_insert_iff.mp member with rfl | inPrior
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_iff.mpr (Or.inr
        (completionStage_subset_closure infinity base target seed stage inPrior))
  · apply Or.inl
    apply completionStage_subset_closure infinity base target seed (stage + 1)
    simp only [completionStage]
    rw [scheduled, if_neg derives]
    split
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert _ _))
    · exact Set.mem_insert _ _

noncomputable def completionMaximalAvoiding
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {seed : Nat}
    (baseBound : ∀ formula ∈ base, formula.constBound ≤ seed)
    (targetBound : target.constBound ≤ seed)
    (baseAvoids : ¬ SetDerives infinity base target) :
    MaximalAvoiding infinity base target where
  theory := completionClosure infinity base target seed
  base_subset := base_subset_completionClosure infinity base target seed
  avoids := completionClosure_avoids baseBound targetBound baseAvoids
  maximal := by
    intro larger included baseLarger largerAvoids
    intro formula inLarger
    rcases completionClosure_decides infinity base target seed formula with
      inClosure | insertionDerives
    · exact inClosure
    · exfalso
      apply largerAvoids
      apply SetDerives.mono _ insertionDerives
      intro item member
      rcases Set.mem_insert_iff.mp member with rfl | inClosure
      · exact inLarger
      · exact included inClosure

structure HenkinPrimeTheory (infinity : InfinitySchema)
    extends PrimeTheory infinity where
  witness : ∀ {body}, (.ex body) ∈ theory →
    ∃ term : Term, body.instantiate term ∈ theory

noncomputable def completionHenkinPrimeTheory
    {infinity : InfinitySchema} {base : Set Formula} {target : Formula}
    {seed : Nat}
    (baseBound : ∀ formula ∈ base, formula.constBound ≤ seed)
    (targetBound : target.constBound ≤ seed)
    (baseAvoids : ¬ SetDerives infinity base target) :
    HenkinPrimeTheory infinity where
  toPrimeTheory :=
    (completionMaximalAvoiding baseBound targetBound baseAvoids).toPrimeTheory
  witness := by
    intro body member
    exact completionClosure_witness (SetDerives.of_mem member)

end IncidenceCore.ReferenceFoundation
