import IncidenceTheory.ReferenceFoundationMetatheory

/-!
  Varying-domain Kripke semantics for the intuitionistic first-order
  reference calculus.  A single classical Tarski world is sound but is not a
  completeness semantics for intuitionistic implication; this module fixes the
  semantic target required by the later canonical-model construction.
-/

namespace IncidenceCore.ReferenceFoundation

universe u v

structure KripkeStructure where
  World : Type v
  future : World → World → Prop
  future_refl : ∀ world, future world world
  future_trans : ∀ {first second third},
    future first second → future second third → future first third
  toStructure : Structure
  MembershipAt : World → toStructure.Carrier → toStructure.Carrier → Prop
  EqualityAt : World → toStructure.Carrier → toStructure.Carrier → Prop
  ExistsAt : World → toStructure.Carrier → Prop
  exists_mono : ∀ {first second value}, future first second →
    ExistsAt first value → ExistsAt second value
  constant_exists : ∀ world index, ExistsAt world (toStructure.constant index)
  empty_exists : ∀ world, ExistsAt world toStructure.empty
  pair_exists : ∀ {world left right}, ExistsAt world left →
    ExistsAt world right → ExistsAt world (toStructure.pair left right)
  union_exists : ∀ {world value}, ExistsAt world value →
    ExistsAt world (toStructure.union value)
  powerset_exists : ∀ {world value}, ExistsAt world value →
    ExistsAt world (toStructure.powerset value)
  membership_mono : ∀ {first second left right}, future first second →
    MembershipAt first left right → MembershipAt second left right
  equality_mono : ∀ {first second left right}, future first second →
    EqualityAt first left right → EqualityAt second left right

namespace KripkeStructure

abbrev Carrier (model : KripkeStructure) := model.toStructure.Carrier
abbrev Valuation (model : KripkeStructure) := Nat → model.Carrier

def ValuationExistsAt (model : KripkeStructure) (world : model.World)
    (valuation : model.Valuation) : Prop :=
  ∀ index, model.ExistsAt world (valuation index)

theorem Term.evaluate_exists (model : KripkeStructure)
    {world : model.World} {valuation : model.Valuation}
    (valuationExists : model.ValuationExistsAt world valuation)
    (term : Term) :
    model.ExistsAt world (term.evaluate model.toStructure valuation) := by
  induction term with
  | var index => exact valuationExists index
  | const index => exact model.constant_exists world index
  | empty => exact model.empty_exists world
  | pair left right ihLeft ihRight => exact model.pair_exists ihLeft ihRight
  | union value ih => exact model.union_exists ih
  | powerset value ih => exact model.powerset_exists ih

def Force (model : KripkeStructure) (world : model.World)
    (valuation : model.Valuation) : Formula → Prop
  | .mem left right => model.MembershipAt world
      (left.evaluate model.toStructure valuation)
      (right.evaluate model.toStructure valuation)
  | .eq left right => model.EqualityAt world
      (left.evaluate model.toStructure valuation)
      (right.evaluate model.toStructure valuation)
  | .bot => False
  | .and left right => model.Force world valuation left ∧
      model.Force world valuation right
  | .or left right => model.Force world valuation left ∨
      model.Force world valuation right
  | .imp left right => ∀ futureWorld, model.future world futureWorld →
      model.Force futureWorld valuation left →
      model.Force futureWorld valuation right
  | .all body => ∀ futureWorld, model.future world futureWorld →
      ∀ value, model.ExistsAt futureWorld value →
        model.Force futureWorld (extend value valuation) body
  | .ex body => ∃ value, model.ExistsAt world value ∧
      model.Force world (extend value valuation) body

def ForceContext (model : KripkeStructure) (world : model.World)
    (valuation : model.Valuation) (context : Context) : Prop :=
  ∀ formula ∈ context, model.Force world valuation formula

theorem valuation_exists_mono (model : KripkeStructure)
    {first second : model.World} {valuation : model.Valuation}
    (future : model.future first second)
    (existsAt : model.ValuationExistsAt first valuation) :
    model.ValuationExistsAt second valuation :=
  fun index => model.exists_mono future (existsAt index)

theorem force_monotone (model : KripkeStructure) {formula : Formula}
    {first second : model.World} {valuation : model.Valuation}
    (future : model.future first second)
    (forced : model.Force first valuation formula) :
    model.Force second valuation formula := by
  induction formula generalizing first second valuation with
  | mem left right => exact model.membership_mono future forced
  | eq left right => exact model.equality_mono future forced
  | bot => exact forced
  | and left right ihLeft ihRight =>
      exact ⟨ihLeft future forced.1, ihRight future forced.2⟩
  | or left right ihLeft ihRight =>
      exact forced.elim (fun proof => Or.inl (ihLeft future proof))
        (fun proof => Or.inr (ihRight future proof))
  | imp left right ihLeft ihRight =>
      intro third secondThird leftForced
      exact forced third (model.future_trans future secondThird) leftForced
  | all body ih =>
      intro third secondThird value valueExists
      exact forced third (model.future_trans future secondThird) value valueExists
  | ex body ih =>
      rcases forced with ⟨value, valueExists, bodyForced⟩
      exact ⟨value, model.exists_mono future valueExists,
        ih future bodyForced⟩

theorem forceContext_monotone (model : KripkeStructure)
    {context : Context} {first second : model.World}
    {valuation : model.Valuation} (future : model.future first second)
    (forced : model.ForceContext first valuation context) :
    model.ForceContext second valuation context := by
  intro formula member
  exact model.force_monotone future (forced formula member)

theorem force_rename (model : KripkeStructure) (world : model.World)
    (valuation : model.Valuation) (rho : Nat → Nat) (formula : Formula) :
    model.Force world valuation (formula.rename rho) ↔
      model.Force world (valuation ∘ rho) formula := by
  induction formula generalizing world valuation rho with
  | mem left right => simp [Formula.rename, Force, Term.evaluate_rename]
  | eq left right => simp [Formula.rename, Force, Term.evaluate_rename]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.rename, Force, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.rename, Force, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp only [Formula.rename, Force]
      constructor <;> intro forced futureWorld future leftForced
      · apply (ihRight futureWorld valuation rho).mp
        exact forced futureWorld future
          ((ihLeft futureWorld valuation rho).mpr leftForced)
      · apply (ihRight futureWorld valuation rho).mpr
        exact forced futureWorld future
          ((ihLeft futureWorld valuation rho).mp leftForced)
  | all body ih =>
      simp only [Formula.rename, Force]
      constructor <;> intro forced futureWorld future value valueExists
      · have result := (ih futureWorld (extend value valuation)
          (liftRenaming rho)).mp
          (forced futureWorld future value valueExists)
        simpa only [extend_comp_liftRenaming] using result
      · apply (ih futureWorld (extend value valuation)
          (liftRenaming rho)).mpr
        simpa only [extend_comp_liftRenaming] using
          forced futureWorld future value valueExists
  | ex body ih =>
      simp only [Formula.rename, Force]
      constructor
      · rintro ⟨value, valueExists, forced⟩
        refine ⟨value, valueExists, ?_⟩
        rw [ih, extend_comp_liftRenaming] at forced
        exact forced
      · rintro ⟨value, valueExists, forced⟩
        refine ⟨value, valueExists, ?_⟩
        rw [ih, extend_comp_liftRenaming]
        exact forced

theorem force_substitute (model : KripkeStructure) (world : model.World)
    (valuation : model.Valuation) (substitution : Nat → Term)
    (formula : Formula) :
    model.Force world valuation (formula.substitute substitution) ↔
      model.Force world
        (fun index => (substitution index).evaluate model.toStructure valuation)
        formula := by
  induction formula generalizing world valuation substitution with
  | mem left right => simp [Formula.substitute, Force,
      Term.evaluate_substitute]
  | eq left right => simp [Formula.substitute, Force,
      Term.evaluate_substitute]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.substitute, Force, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.substitute, Force, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp only [Formula.substitute, Force]
      constructor <;> intro forced futureWorld future leftForced
      · apply (ihRight futureWorld valuation substitution).mp
        exact forced futureWorld future
          ((ihLeft futureWorld valuation substitution).mpr leftForced)
      · apply (ihRight futureWorld valuation substitution).mpr
        exact forced futureWorld future
          ((ihLeft futureWorld valuation substitution).mp leftForced)
  | all body ih =>
      simp only [Formula.substitute, Force]
      constructor <;> intro forced futureWorld future value valueExists
      · have result := (ih futureWorld (extend value valuation)
          (liftSubstitution substitution)).mp
          (forced futureWorld future value valueExists)
        simpa only [evaluate_liftSubstitution] using result
      · apply (ih futureWorld (extend value valuation)
          (liftSubstitution substitution)).mpr
        simpa only [evaluate_liftSubstitution] using
          forced futureWorld future value valueExists
  | ex body ih =>
      simp only [Formula.substitute, Force]
      constructor
      · rintro ⟨value, valueExists, forced⟩
        refine ⟨value, valueExists, ?_⟩
        rw [ih, evaluate_liftSubstitution] at forced
        exact forced
      · rintro ⟨value, valueExists, forced⟩
        refine ⟨value, valueExists, ?_⟩
        rw [ih, evaluate_liftSubstitution]
        exact forced

theorem force_instantiate (model : KripkeStructure) (world : model.World)
    (valuation : model.Valuation) (body : Formula) (term : Term) :
    model.Force world valuation (body.instantiate term) ↔
      model.Force world
        (extend (term.evaluate model.toStructure valuation) valuation) body := by
  unfold Formula.instantiate
  rw [model.force_substitute]
  apply iff_of_eq
  congr 2
  funext index
  cases index <;> rfl

theorem forceContext_rename_succ (model : KripkeStructure)
    (world : model.World) (valuation : model.Valuation)
    (value : model.Carrier) (context : Context)
    (forced : model.ForceContext world valuation context) :
    model.ForceContext world (extend value valuation)
      (context.map (Formula.rename Nat.succ)) := by
  intro formula member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  apply (model.force_rename world (extend value valuation) Nat.succ source).mpr
  simpa using forced source sourceMember

structure Model (infinity : InfinitySchema) extends KripkeStructure where
  axiom_forced : ∀ {formula}, Axiom infinity formula →
    ∀ world valuation, ValuationExistsAt toKripkeStructure world valuation →
      toKripkeStructure.Force world valuation formula

def Model.Valid {infinity : InfinitySchema} (model : Model infinity)
    (formula : Formula) : Prop :=
  ∀ world valuation, ValuationExistsAt model.toKripkeStructure world valuation →
    model.toKripkeStructure.Force world valuation formula

def Model.Entails {infinity : InfinitySchema} (model : Model infinity)
    (context : Context) (formula : Formula) : Prop :=
  ∀ world valuation, ValuationExistsAt model.toKripkeStructure world valuation →
    model.toKripkeStructure.ForceContext world valuation context →
    model.toKripkeStructure.Force world valuation formula

theorem derives_sound {infinity : InfinitySchema}
    (model : Model infinity) {context : Context} {formula : Formula}
    (proof : Derives infinity context formula) :
    model.Entails context formula := by
  intro world valuation valuationExists contextForced
  induction proof generalizing world valuation with
  | assumption member => exact contextForced _ member
  | «axiom» valid => exact model.axiom_forced valid world valuation valuationExists
  | topIntro =>
      intro futureWorld future impossible
      exact impossible
  | botElim premise ih =>
      exact (ih world valuation valuationExists contextForced).elim
  | andIntro left right ihLeft ihRight =>
      exact ⟨ihLeft world valuation valuationExists contextForced,
        ihRight world valuation valuationExists contextForced⟩
  | andElimLeft premise ih =>
      exact (ih world valuation valuationExists contextForced).1
  | andElimRight premise ih =>
      exact (ih world valuation valuationExists contextForced).2
  | orIntroLeft premise ih =>
      exact Or.inl (ih world valuation valuationExists contextForced)
  | orIntroRight premise ih =>
      exact Or.inr (ih world valuation valuationExists contextForced)
  | orElim disjunction left right ihDisjunction ihLeft ihRight =>
      rcases ihDisjunction world valuation valuationExists contextForced with
        leftForced | rightForced
      · exact ihLeft world valuation valuationExists (by
          intro item member
          simp only [List.mem_cons] at member
          exact member.elim (fun equal => equal ▸ leftForced)
            (fun tail => contextForced item tail))
      · exact ihRight world valuation valuationExists (by
          intro item member
          simp only [List.mem_cons] at member
          exact member.elim (fun equal => equal ▸ rightForced)
            (fun tail => contextForced item tail))
  | impIntro premise ih =>
      intro futureWorld future leftForced
      exact ih futureWorld valuation
        (model.toKripkeStructure.valuation_exists_mono future valuationExists)
        (by
          intro item member
          simp only [List.mem_cons] at member
          exact member.elim (fun equal => equal ▸ leftForced)
            (fun tail => model.toKripkeStructure.force_monotone future
              (contextForced item tail)))
  | impElim implication premise ihImplication ihPremise =>
      exact ihImplication world valuation valuationExists contextForced
        world (model.future_refl world)
        (ihPremise world valuation valuationExists contextForced)
  | allIntro premise ih =>
      intro futureWorld future value valueExists
      apply ih futureWorld (extend value valuation)
      · intro index
        cases index with
        | zero => exact valueExists
        | succ index => exact model.exists_mono future (valuationExists index)
      · exact model.toKripkeStructure.forceContext_rename_succ
          futureWorld valuation value _
          (model.toKripkeStructure.forceContext_monotone future contextForced)
  | allElim premise term ih =>
      apply (model.toKripkeStructure.force_instantiate world valuation _ term).mpr
      exact ih world valuation valuationExists contextForced
        world (model.future_refl world)
        (term.evaluate model.toStructure valuation)
        (KripkeStructure.Term.evaluate_exists model.toKripkeStructure
          valuationExists term)
  | exIntro term premise ih =>
      refine ⟨term.evaluate model.toStructure valuation,
        KripkeStructure.Term.evaluate_exists model.toKripkeStructure
          valuationExists term, ?_⟩
      exact (model.toKripkeStructure.force_instantiate world valuation _ term).mp
        (ih world valuation valuationExists contextForced)
  | exElim existential branch ihExistential ihBranch =>
      rcases ihExistential world valuation valuationExists contextForced with
        ⟨value, valueExists, bodyForced⟩
      have shifted := ihBranch world (extend value valuation) (by
        intro index
        cases index with
        | zero => exact valueExists
        | succ index => exact valuationExists index) (by
          intro item member
          simp only [List.mem_cons] at member
          exact member.elim (fun equal => equal ▸ bodyForced)
            (fun tail => model.toKripkeStructure.forceContext_rename_succ
              world valuation value _ contextForced item tail))
      exact (model.toKripkeStructure.force_rename world
        (extend value valuation) Nat.succ _).mp shifted

end KripkeStructure

end IncidenceCore.ReferenceFoundation
