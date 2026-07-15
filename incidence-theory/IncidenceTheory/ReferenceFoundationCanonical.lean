import IncidenceTheory.ReferenceFoundationKripke

/-!
  Canonical-model envelope for first-order completeness.  The construction of
  prime Henkin worlds is separated from the truth lemma so that the remaining
  Lindenbaum obligation has an exact checked interface.
-/

namespace IncidenceCore.ReferenceFoundation

namespace Canonical

universe u

structure Frame (infinity : InfinitySchema) where
  World : Type u
  future : World → World → Prop
  future_refl : ∀ world, future world world
  future_trans : ∀ {first second third},
    future first second → future second third → future first third
  Holds : World → Formula → Prop
  holds_mono : ∀ {first second formula}, future first second →
    Holds first formula → Holds second formula
  holds_axiom : ∀ world {formula}, Axiom infinity formula → Holds world formula
  bot_iff : ∀ world, Holds world .bot ↔ False
  and_iff : ∀ world left right,
    Holds world (.and left right) ↔ Holds world left ∧ Holds world right
  or_iff : ∀ world left right,
    Holds world (.or left right) ↔ Holds world left ∨ Holds world right
  imp_iff : ∀ world left right,
    Holds world (.imp left right) ↔
      ∀ futureWorld, future world futureWorld →
        Holds futureWorld left → Holds futureWorld right
  all_iff : ∀ world body,
    Holds world (.all body) ↔
      ∀ futureWorld, future world futureWorld →
        ∀ term, Holds futureWorld (body.instantiate term)
  ex_iff : ∀ world body,
    Holds world (.ex body) ↔ ∃ term, Holds world (body.instantiate term)

def termStructure : Structure where
  Carrier := Term
  membership := fun _ _ => False
  constant := .const
  empty := .empty
  pair := .pair
  union := .union
  powerset := .powerset

@[simp] theorem evaluate_termStructure (valuation : Nat → Term) (term : Term) :
    term.evaluate termStructure valuation = term.substitute valuation := by
  induction term with
  | var index => rfl
  | const index => rfl
  | empty => rfl
  | pair left right ihLeft ihRight =>
      change Term.pair (left.evaluate termStructure valuation)
        (right.evaluate termStructure valuation) = _
      rw [ihLeft, ihRight]
      rfl
  | union term ih =>
      change Term.union (term.evaluate termStructure valuation) = _
      rw [ih]
      rfl
  | powerset term ih =>
      change Term.powerset (term.evaluate termStructure valuation) = _
      rw [ih]
      rfl

def Frame.kripkeStructure {infinity : InfinitySchema}
    (frame : Frame infinity) : KripkeStructure where
  World := frame.World
  future := frame.future
  future_refl := frame.future_refl
  future_trans := frame.future_trans
  toStructure := termStructure
  MembershipAt := fun world left right => frame.Holds world (.mem left right)
  EqualityAt := fun world left right => frame.Holds world (.eq left right)
  ExistsAt := fun _ _ => True
  exists_mono := by intros; trivial
  constant_exists := by intros; trivial
  empty_exists := by intros; trivial
  pair_exists := by intros; trivial
  union_exists := by intros; trivial
  powerset_exists := by intros; trivial
  membership_mono := fun future proof => frame.holds_mono future proof
  equality_mono := fun future proof => frame.holds_mono future proof

/- The generalized truth statement is stable under open substitutions and is
   the induction form needed at quantifiers. -/
def TruthStatement {infinity : InfinitySchema} (frame : Frame infinity)
    (formula : Formula) : Prop :=
  ∀ world valuation,
    frame.Holds world (formula.substitute valuation) ↔
      frame.kripkeStructure.Force world valuation formula

theorem truth {infinity : InfinitySchema} (frame : Frame infinity)
    (formula : Formula) : TruthStatement frame formula := by
  induction formula with
  | mem left right =>
      intro world valuation
      simp [Formula.substitute, KripkeStructure.Force,
        Frame.kripkeStructure, evaluate_termStructure]
  | eq left right =>
      intro world valuation
      simp [Formula.substitute, KripkeStructure.Force,
        Frame.kripkeStructure, evaluate_termStructure]
  | bot =>
      intro world valuation
      exact frame.bot_iff world
  | and left right ihLeft ihRight =>
      intro world valuation
      rw [Formula.substitute, frame.and_iff]
      exact and_congr (ihLeft world valuation) (ihRight world valuation)
  | or left right ihLeft ihRight =>
      intro world valuation
      rw [Formula.substitute, frame.or_iff]
      exact or_congr (ihLeft world valuation) (ihRight world valuation)
  | imp left right ihLeft ihRight =>
      intro world valuation
      rw [Formula.substitute, frame.imp_iff]
      simp only [KripkeStructure.Force]
      constructor <;> intro implication futureWorld future leftPremise
      · apply (ihRight futureWorld valuation).mp
        exact implication futureWorld future
          ((ihLeft futureWorld valuation).mpr leftPremise)
      · apply (ihRight futureWorld valuation).mpr
        exact implication futureWorld future
          ((ihLeft futureWorld valuation).mp leftPremise)
  | all body ih =>
      intro world valuation
      rw [Formula.substitute, frame.all_iff]
      simp only [KripkeStructure.Force, Frame.kripkeStructure]
      constructor
      · intro universal futureWorld future term termExists
        apply (ih futureWorld (extend term valuation)).mp
        rw [← Formula.substitute_lift_instantiate]
        exact universal futureWorld future term
      · intro universal futureWorld future term
        rw [Formula.substitute_lift_instantiate]
        apply (ih futureWorld (extend term valuation)).mpr
        exact universal futureWorld future term trivial
  | ex body ih =>
      intro world valuation
      rw [Formula.substitute, frame.ex_iff]
      simp only [KripkeStructure.Force, Frame.kripkeStructure]
      constructor
      · rintro ⟨term, bodyHolds⟩
        refine ⟨term, trivial, ?_⟩
        apply (ih world (extend term valuation)).mp
        rwa [← Formula.substitute_lift_instantiate]
      · rintro ⟨term, termExists, bodyForced⟩
        refine ⟨term, ?_⟩
        rw [Formula.substitute_lift_instantiate]
        exact (ih world (extend term valuation)).mpr bodyForced

def Frame.model {infinity : InfinitySchema} (frame : Frame infinity) :
    KripkeStructure.Model infinity where
  toKripkeStructure := frame.kripkeStructure
  axiom_forced := by
    intro formula valid world valuation valuationExists
    apply (truth frame formula world valuation).mp
    rw [valid.substitution_closed valuation]
    exact frame.holds_axiom world valid

structure CountermodelCertificate (infinity : InfinitySchema)
    (context : Context) (formula : Formula) where
  frame : Frame.{u} infinity
  root : frame.World
  contextHolds : ∀ item ∈ context, frame.Holds root item
  formulaFails : ¬ frame.Holds root formula

def KripkeEntailsAtUniverse (infinity : InfinitySchema)
    (context : Context) (formula : Formula) : Prop :=
  ∀ model : KripkeStructure.Model.{u, 0} infinity, model.Entails context formula

theorem CountermodelCertificate.refutes_entailment
    {infinity : InfinitySchema} {context : Context} {formula : Formula}
    (certificate : CountermodelCertificate.{u} infinity context formula) :
    ¬ KripkeEntailsAtUniverse.{u} infinity context formula := by
  intro entails
  have forced := entails certificate.frame.model certificate.root identitySubstitution
    (by intro index; trivial) (by
      intro item member
      apply (truth certificate.frame item certificate.root identitySubstitution).mp
      rw [Formula.substitute_id]
      exact certificate.contextHolds item member)
  apply certificate.formulaFails
  have reflected := (truth certificate.frame formula certificate.root
    identitySubstitution).mpr forced
  rwa [Formula.substitute_id] at reflected

theorem sound_at_universe {infinity : InfinitySchema}
    {context : Context} {formula : Formula}
    (proof : Derives infinity context formula) :
    KripkeEntailsAtUniverse.{u} infinity context formula := by
  intro model
  exact KripkeStructure.derives_sound model proof

theorem complete_of_countermodels {infinity : InfinitySchema}
    (countermodel : ∀ (context : Context) (formula : Formula),
      ¬ Derives infinity context formula →
        CountermodelCertificate.{u} infinity context formula)
    {context : Context} {formula : Formula}
    (semantic : KripkeEntailsAtUniverse.{u} infinity context formula) :
    Derives infinity context formula := by
  apply Classical.byContradiction
  intro notDerivable
  exact (countermodel context formula notDerivable).refutes_entailment semantic

end Canonical

end IncidenceCore.ReferenceFoundation
