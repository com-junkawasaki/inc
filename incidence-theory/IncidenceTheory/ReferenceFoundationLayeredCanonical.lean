import IncidenceTheory.ReferenceFoundationLayered
import IncidenceTheory.ReferenceFoundationKripke

/-! A varying-domain canonical model for the constant-free reference language.
Henkin constants are semantic parameters born at a language layer; object-level
constants are deliberately outside this completeness boundary. -/

namespace IncidenceCore.ReferenceFoundation

namespace LayeredCanonical

def termStructure : Structure where
  Carrier := Term
  membership := fun _ _ => False
  constant := fun _ => .empty
  empty := .empty
  pair := .pair
  union := .union
  powerset := .powerset

theorem evaluate_termStructure_of_constFree
    {term : Term} (free : term.ConstFree) (valuation : Nat → Term) :
    term.evaluate termStructure valuation = term.substitute valuation := by
  induction term with
  | var index => rfl
  | «const» index => exact False.elim free
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp only [Term.evaluate, Term.substitute]
      rw [ihLeft free.1, ihRight free.2]
      rfl
  | union term ih =>
      simp only [Term.evaluate, Term.substitute]
      rw [ih free]
      rfl
  | powerset term ih =>
      simp only [Term.evaluate, Term.substitute]
      rw [ih free]
      rfl

def Future {infinity : InfinitySchema}
    (current future : LayeredPrimeTheory infinity) : Prop :=
  current.cutoff ≤ future.cutoff ∧ current.theory ⊆ future.theory

theorem Future.refl {infinity : InfinitySchema}
    (world : LayeredPrimeTheory infinity) : Future world world :=
  ⟨Nat.le_refl _, Set.Subset.rfl⟩

theorem Future.trans {infinity : InfinitySchema}
    {first second third : LayeredPrimeTheory infinity} :
    Future first second → Future second third → Future first third := by
  rintro ⟨cutoffFirst, theoryFirst⟩ ⟨cutoffSecond, theorySecond⟩
  exact ⟨le_trans cutoffFirst cutoffSecond,
    Set.Subset.trans theoryFirst theorySecond⟩

def canonicalStructure (infinity : InfinitySchema) : KripkeStructure where
  World := LayeredPrimeTheory infinity
  future := Future
  future_refl := Future.refl
  future_trans := Future.trans
  toStructure := termStructure
  MembershipAt := fun world left right => (.mem left right) ∈ world.theory
  EqualityAt := fun world left right => (.eq left right) ∈ world.theory
  ExistsAt := fun world term => term.constLevelBound ≤ world.cutoff
  exists_mono := fun future existsAt => le_trans existsAt future.1
  constant_exists := by
    intro world index
    simp [termStructure, Term.constLevelBound]
  empty_exists := by
    intro world
    simp [termStructure, Term.constLevelBound]
  pair_exists := by
    intro world left right leftExists rightExists
    simpa [termStructure, Term.constLevelBound] using max_le leftExists rightExists
  union_exists := by
    intro world value valueExists
    simpa [termStructure, Term.constLevelBound] using valueExists
  powerset_exists := by
    intro world value valueExists
    simpa [termStructure, Term.constLevelBound] using valueExists
  membership_mono := by
    intro first second left right future member
    exact future.2 member
  equality_mono := by
    intro first second left right future member
    exact future.2 member

theorem substitute_available_of_constFree
    {formula : Formula} (free : formula.ConstFree)
    {cutoff : Nat} {valuation : Nat → Term}
    (valuationBound : ∀ index, (valuation index).constLevelBound ≤ cutoff) :
    (formula.substitute valuation).constLevelBound ≤ cutoff := by
  apply le_trans (formula.constLevelBound_substitute_le valuation cutoff valuationBound)
  rw [free.constLevelBound_eq_zero]
  simp

def TruthStatement {infinity : InfinitySchema} (formula : Formula) : Prop :=
  ∀ world valuation,
    (∀ index, (valuation index).constLevelBound ≤ world.cutoff) →
    (formula.substitute valuation ∈ world.theory ↔
      (canonicalStructure infinity).Force world valuation formula)

theorem truth {infinity : InfinitySchema} (formula : Formula)
    (free : formula.ConstFree) : TruthStatement (infinity := infinity) formula := by
  induction formula with
  | mem left right =>
      intro world valuation valuationBound
      simp only [Formula.substitute, KripkeStructure.Force, canonicalStructure]
      rw [evaluate_termStructure_of_constFree free.1 valuation,
        evaluate_termStructure_of_constFree free.2 valuation]
  | eq left right =>
      intro world valuation valuationBound
      simp only [Formula.substitute, KripkeStructure.Force, canonicalStructure]
      rw [evaluate_termStructure_of_constFree free.1 valuation,
        evaluate_termStructure_of_constFree free.2 valuation]
  | bot =>
      intro world valuation valuationBound
      exact world.bot_iff
  | and left right ihLeft ihRight =>
      intro world valuation valuationBound
      rw [Formula.substitute, world.and_iff]
      · exact and_congr (ihLeft free.1 world valuation valuationBound)
          (ihRight free.2 world valuation valuationBound)
      · exact max_le
          (substitute_available_of_constFree free.1 valuationBound)
          (substitute_available_of_constFree free.2 valuationBound)
  | or left right ihLeft ihRight =>
      intro world valuation valuationBound
      rw [Formula.substitute, world.primeOr]
      · exact or_congr (ihLeft free.1 world valuation valuationBound)
          (ihRight free.2 world valuation valuationBound)
      · exact max_le
          (substitute_available_of_constFree free.1 valuationBound)
          (substitute_available_of_constFree free.2 valuationBound)
  | imp left right ihLeft ihRight =>
      intro world valuation valuationBound
      simp only [Formula.substitute, KripkeStructure.Force]
      constructor
      · intro implication future futureProof leftForced
        apply (ihRight free.2 future valuation
          (fun index => le_trans (valuationBound index) futureProof.1)).mp
        exact world.imp_forward futureProof.2
          (substitute_available_of_constFree free.2
            (fun index => le_trans (valuationBound index) futureProof.1))
          implication
          ((ihLeft free.1 future valuation
            (fun index => le_trans (valuationBound index) futureProof.1)).mpr
            leftForced)
      · intro semantic
        by_contra missing
        have available : max (left.substitute valuation).constLevelBound
            (right.substitute valuation).constLevelBound ≤ world.cutoff :=
          max_le
            (substitute_available_of_constFree free.1 valuationBound)
            (substitute_available_of_constFree free.2 valuationBound)
        rcases world.future_counterexample_of_imp_not_mem available missing with
          ⟨future, cutoffOrder, included, leftMember, rightMissing⟩
        have futureProof : Future world future := ⟨cutoffOrder, included⟩
        have futureValuation : ∀ index,
            (valuation index).constLevelBound ≤ future.cutoff :=
          fun index => le_trans (valuationBound index) cutoffOrder
        have leftForced :=
          (ihLeft free.1 future valuation futureValuation).mp leftMember
        have rightForced := semantic future futureProof leftForced
        exact rightMissing
          ((ihRight free.2 future valuation futureValuation).mpr rightForced)
  | all body ih =>
      intro world valuation valuationBound
      simp only [Formula.substitute, KripkeStructure.Force]
      constructor
      · intro universal future futureProof term termExists
        have futureValuation : ∀ index,
            (valuation index).constLevelBound ≤ future.cutoff :=
          fun index => le_trans (valuationBound index) futureProof.1
        have extendedBound : ∀ index,
            ((extend term valuation) index).constLevelBound ≤ future.cutoff := by
          intro index
          cases index with
          | zero => exact termExists
          | succ index => exact futureValuation index
        apply (ih free future (extend term valuation) extendedBound).mp
        rw [← Formula.substitute_lift_instantiate]
        apply world.all_forward futureProof.2 term
        · rw [Formula.substitute_lift_instantiate]
          exact substitute_available_of_constFree (formula := body) free extendedBound
        · exact universal
      · intro semantic
        by_contra missing
        have available : (body.substitute (liftSubstitution valuation)).constLevelBound ≤
            world.cutoff := by
          apply substitute_available_of_constFree (formula := body) free
          intro index
          cases index with
          | zero => change 0 ≤ world.cutoff; omega
          | succ index =>
              change ((valuation index).rename Nat.succ).constLevelBound ≤ _
              simpa using valuationBound index
        rcases world.future_counterexample_of_all_not_mem available missing with
          ⟨future, cutoffOrder, included, term, termExists, instanceMissing⟩
        have futureProof : Future world future := ⟨cutoffOrder, included⟩
        have futureValuation : ∀ index,
            (valuation index).constLevelBound ≤ future.cutoff :=
          fun index => le_trans (valuationBound index) cutoffOrder
        have extendedBound : ∀ index,
            ((extend term valuation) index).constLevelBound ≤ future.cutoff := by
          intro index
          cases index with
          | zero => exact termExists
          | succ index => exact futureValuation index
        have forced := semantic future futureProof term termExists
        have member := (ih free future (extend term valuation) extendedBound).mpr forced
        rw [← Formula.substitute_lift_instantiate] at member
        exact instanceMissing member
  | ex body ih =>
      intro world valuation valuationBound
      simp only [Formula.substitute, KripkeStructure.Force]
      have available : (body.substitute (liftSubstitution valuation)).constLevelBound ≤
          world.cutoff := by
        apply substitute_available_of_constFree (formula := body) free
        intro index
        cases index with
        | zero => change 0 ≤ world.cutoff; omega
        | succ index =>
            change ((valuation index).rename Nat.succ).constLevelBound ≤ _
            simpa using valuationBound index
      rw [world.ex_iff available]
      constructor
      · rintro ⟨term, termExists, instanceMember⟩
        refine ⟨term, termExists, ?_⟩
        have extendedBound : ∀ index,
            ((extend term valuation) index).constLevelBound ≤ world.cutoff := by
          intro index
          cases index with
          | zero => exact termExists
          | succ index => exact valuationBound index
        apply (ih free world (extend term valuation) extendedBound).mp
        rwa [← Formula.substitute_lift_instantiate]
      · rintro ⟨term, termExists, bodyForced⟩
        refine ⟨term, termExists, ?_⟩
        have extendedBound : ∀ index,
            ((extend term valuation) index).constLevelBound ≤ world.cutoff := by
          intro index
          cases index with
          | zero => exact termExists
          | succ index => exact valuationBound index
        rw [Formula.substitute_lift_instantiate]
        exact (ih free world (extend term valuation) extendedBound).mpr bodyForced

def model (infinity : InfinitySchema) : KripkeStructure.Model infinity where
  toKripkeStructure := canonicalStructure infinity
  axiom_forced := by
    intro formula valid world valuation valuationExists
    apply (truth formula valid.constFree world valuation valuationExists).mp
    rw [valid.substitution_closed valuation]
    exact world.axioms valid

theorem countermodel_of_not_derives
    {infinity : InfinitySchema} {context : Context} {formula : Formula}
    (contextFree : ∀ item ∈ context, item.ConstFree)
    (formulaFree : formula.ConstFree)
    (notDerives : ¬ Derives infinity context formula) :
    ∃ root : LayeredPrimeTheory infinity,
      (canonicalStructure infinity).ForceContext root identitySubstitution context ∧
      ¬ (canonicalStructure infinity).Force root identitySubstitution formula := by
  let base : Set Formula := {item | item ∈ context}
  have baseLevel : ∀ item ∈ base, item.constLevelBound ≤ 0 := by
    intro item member
    rw [(contextFree item member).constLevelBound_eq_zero]
  have targetLevel : formula.constLevelBound ≤ 0 := by
    rw [formulaFree.constLevelBound_eq_zero]
  have baseAvoids : ¬ SetDerives infinity base formula := by
    rintro ⟨support, supportIn, derivation⟩
    apply notDerives
    exact derivation.weaken (by
      intro item member
      exact supportIn item member)
  let root := layerCompletionPrimeTheory baseLevel targetLevel baseAvoids
  have baseSubset : base ⊆ root.theory :=
    layerCompletionPrimeTheory_base_subset baseLevel targetLevel baseAvoids
  have targetMissing : formula ∉ root.theory :=
    layerCompletionPrimeTheory_target_not_mem baseLevel targetLevel baseAvoids
  have identityValuation : ∀ index,
      (identitySubstitution index).constLevelBound ≤ root.cutoff := by
    intro index
    simp [identitySubstitution, Term.constLevelBound]
  refine ⟨root, ?_, ?_⟩
  · intro item member
    apply (truth item (contextFree item member) root identitySubstitution
      identityValuation).mp
    simpa using baseSubset member
  · intro forced
    apply targetMissing
    have member :=
      (truth formula formulaFree root identitySubstitution identityValuation).mpr forced
    rw [Formula.substitute_id] at member
    exact member

def KripkeEntails (infinity : InfinitySchema)
    (context : Context) (formula : Formula) : Prop :=
  ∀ semanticModel : KripkeStructure.Model.{0, 0} infinity,
    semanticModel.Entails context formula

theorem complete
    {infinity : InfinitySchema} {context : Context} {formula : Formula}
    (contextFree : ∀ item ∈ context, item.ConstFree)
    (formulaFree : formula.ConstFree)
    (entails : KripkeEntails infinity context formula) :
    Derives infinity context formula := by
  by_contra notDerives
  rcases countermodel_of_not_derives contextFree formulaFree notDerives with
    ⟨root, contextForced, formulaNotForced⟩
  have valuationExists :
      (canonicalStructure infinity).ValuationExistsAt root identitySubstitution := by
    intro index
    simp [canonicalStructure, identitySubstitution, Term.constLevelBound]
  exact formulaNotForced
    (entails (model infinity) root identitySubstitution valuationExists contextForced)

end LayeredCanonical

end IncidenceCore.ReferenceFoundation
