import IncidenceTheory.Coherent

namespace IncidenceCore

universe u

/-! A carrier-independent axiom schema for the internal propositional language.
Unlike a finite physical diagram, this schema does not enumerate the carrier.
Its models are exactly the symmetric, unital, type-compatible ternary
relations over the fixed incidence signature. -/

inductive ResonanceLawAxiom
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  | symmetry (left right mode : I) : ResonanceLawAxiom inc
  | unitLeft (value : I) : ResonanceLawAxiom inc
  | unitRight (value : I) : ResonanceLawAxiom inc
  | incompatible {left right mode : I}
      (mismatch : ¬ (inc.typeFunc left = inc.typeFunc right ∧
        inc.typeFunc mode = inc.typeFunc left)) : ResonanceLawAxiom inc

def ResonanceLawAxiom.formula
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T} :
    ResonanceLawAxiom inc → Formula (ResonanceAtom I)
  | .symmetry left right mode =>
      resonanceSymmetryFormula left right mode
  | .unitLeft value => resonanceFormula inc.unit value value
  | .unitRight value => resonanceFormula value inc.unit value
  | .incompatible (left := left) (right := right) (mode := mode) _ =>
      Formula.neg (resonanceFormula left right mode)

def IsResonanceLawFormula
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : Formula (ResonanceAtom I)) : Prop :=
  ∃ law : ResonanceLawAxiom inc, law.formula = formula

structure ResonanceLawModel
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (valuation : ResonanceAtom I → Prop) : Prop where
  symmetric : ∀ {left right mode}, valuation ⟨left, right, mode⟩ →
    valuation ⟨right, left, mode⟩
  unit_left : ∀ value, valuation ⟨inc.unit, value, value⟩
  unit_right : ∀ value, valuation ⟨value, inc.unit, value⟩
  type_compatible : ∀ {left right mode}, valuation ⟨left, right, mode⟩ →
    inc.typeFunc left = inc.typeFunc right ∧
      inc.typeFunc mode = inc.typeFunc left

def SatisfiesAllResonanceLawAxioms
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (valuation : ResonanceAtom I → Prop) : Prop :=
  ∀ law : ResonanceLawAxiom inc, Satisfies valuation law.formula

theorem resonanceLawAxioms_characterize_models
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (valuation : ResonanceAtom I → Prop) :
    SatisfiesAllResonanceLawAxioms inc valuation ↔
      ResonanceLawModel inc valuation := by
  constructor
  · intro satisfies
    refine
      { symmetric := ?_, unit_left := ?_, unit_right := ?_,
        type_compatible := ?_ }
    · intro left right mode resonant
      exact satisfies (.symmetry left right mode) resonant
    · intro value
      exact satisfies (.unitLeft value)
    · intro value
      exact satisfies (.unitRight value)
    · intro left right mode resonant
      apply Classical.byContradiction
      intro mismatch
      exact satisfies (.incompatible mismatch) resonant
  · intro model law
    cases law with
    | symmetry left right mode => exact model.symmetric
    | unitLeft value => exact model.unit_left value
    | unitRight value => exact model.unit_right value
    | incompatible mismatch =>
        intro resonant
        exact mismatch (model.type_compatible resonant)

theorem ResonanceSpec.physical_satisfies_all_law_axioms
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (spec : ResonanceSpec inc) :
    SatisfiesAllResonanceLawAxioms inc (resonanceValuation inc) := by
  rw [resonanceLawAxioms_characterize_models]
  exact
    { symmetric := spec.symmetric
      unit_left := spec.unit_left
      unit_right := spec.unit_right
      type_compatible := spec.type_compatible }

theorem resonanceSpec_iff_physical_models_law_axioms
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    Nonempty (ResonanceSpec inc) ↔
      SatisfiesAllResonanceLawAxioms inc (resonanceValuation inc) := by
  constructor
  · rintro ⟨spec⟩
    exact spec.physical_satisfies_all_law_axioms
  · intro satisfies
    have model :=
      (resonanceLawAxioms_characterize_models inc
        (resonanceValuation inc)).mp satisfies
    exact ⟨
      { symmetric := model.symmetric
        unit_left := model.unit_left
        unit_right := model.unit_right
        type_compatible := model.type_compatible }
    ⟩

def ResonanceLawDerives
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : Formula (ResonanceAtom I)) : Prop :=
  ∃ context : List (Formula (ResonanceAtom I)),
    (∀ assumption, assumption ∈ context →
      IsResonanceLawFormula inc assumption) ∧
    Derives context formula

def ResonanceLawSemanticallyEntails
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : Formula (ResonanceAtom I)) : Prop :=
  ∀ valuation : ResonanceAtom I → Prop,
    ResonanceLawModel inc valuation → Satisfies valuation formula

theorem resonanceLawDerives_sound
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {formula : Formula (ResonanceAtom I)} :
    ResonanceLawDerives inc formula →
      ResonanceLawSemanticallyEntails inc formula := by
  rintro ⟨context, axioms, derivation⟩ valuation model
  apply derives_sound derivation
  intro assumption member
  rcases axioms assumption member with ⟨law, rfl⟩
  exact (resonanceLawAxioms_characterize_models inc valuation).mpr model law

theorem resonanceLawDerives_physical_sound
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (spec : ResonanceSpec inc) {formula : Formula (ResonanceAtom I)}
    (derivation : ResonanceLawDerives inc formula) :
    Satisfies (resonanceValuation inc) formula := by
  exact resonanceLawDerives_sound derivation _
    ((resonanceLawAxioms_characterize_models inc _).mp
      spec.physical_satisfies_all_law_axioms)

def KripkeResonanceLawModel
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (model : KripkeModel (ResonanceAtom I)) : Prop :=
  ∀ world : model.World, ResonanceLawModel inc (model.valuation world)

theorem kripke_forces_resonanceLawAxiom
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (model : KripkeModel (ResonanceAtom I))
    (lawful : KripkeResonanceLawModel inc model)
    (world : model.World) (law : ResonanceLawAxiom inc) :
    KripkeForces model world law.formula := by
  cases law with
  | symmetry left right mode =>
      intro future _ resonant
      exact (lawful future).symmetric resonant
  | unitLeft value => exact (lawful world).unit_left value
  | unitRight value => exact (lawful world).unit_right value
  | incompatible mismatch =>
      intro future _ resonant
      exact mismatch ((lawful future).type_compatible resonant)

def ResonanceLawKripkeEntails
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : Formula (ResonanceAtom I)) : Prop :=
  ∀ (model : KripkeModel.{u, u} (ResonanceAtom I)),
    KripkeResonanceLawModel inc model →
      ∀ world : model.World, KripkeForces model world formula

theorem resonanceLawDerives_kripke_sound
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {formula : Formula (ResonanceAtom I)} :
    ResonanceLawDerives inc formula →
      ResonanceLawKripkeEntails inc formula := by
  rintro ⟨context, axioms, derivation⟩ model lawful world
  apply derives_kripke_sound derivation model world
  intro assumption member
  rcases axioms assumption member with ⟨law, rfl⟩
  exact kripke_forces_resonanceLawAxiom model lawful world law

structure ResonanceLawStrongCompleteness
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  complete : ∀ formula : Formula (ResonanceAtom I),
    ResonanceLawKripkeEntails inc formula → ResonanceLawDerives inc formula

structure ResonanceLawCanonicalCountermodels
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  countermodel : ∀ formula : Formula (ResonanceAtom I),
    ¬ ResonanceLawDerives inc formula →
      ∃ model : KripkeModel.{u, u} (ResonanceAtom I),
        KripkeResonanceLawModel inc model ∧
          ∃ world : model.World, ¬ KripkeForces model world formula

theorem resonanceLawStrongCompleteness_iff_countermodels
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceLawStrongCompleteness inc ↔
      ResonanceLawCanonicalCountermodels inc := by
  constructor
  · intro complete
    refine ⟨?_⟩
    intro formula notDerives
    have notEntails : ¬ ResonanceLawKripkeEntails inc formula := by
      intro entails
      exact notDerives (complete.complete formula entails)
    unfold ResonanceLawKripkeEntails at notEntails
    rcases Classical.not_forall.mp notEntails with ⟨model, notModel⟩
    rcases Classical.not_imp.mp notModel with ⟨lawful, notWorlds⟩
    rcases Classical.not_forall.mp notWorlds with ⟨world, notForces⟩
    exact ⟨model, lawful, world, notForces⟩
  · intro countermodels
    refine ⟨?_⟩
    intro formula entails
    apply Classical.byContradiction
    intro notDerives
    rcases countermodels.countermodel formula notDerives with
      ⟨model, lawful, world, notForces⟩
    exact notForces (entails model lawful world)

theorem ResonanceLawStrongCompleteness.iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (complete : ResonanceLawStrongCompleteness inc)
    (formula : Formula (ResonanceAtom I)) :
    ResonanceLawKripkeEntails inc formula ↔
      ResonanceLawDerives inc formula := by
  constructor
  · exact complete.complete formula
  · exact resonanceLawDerives_kripke_sound

structure GeneralResonanceInternalLanguageTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  model_characterization : ∀ valuation : ResonanceAtom I → Prop,
    SatisfiesAllResonanceLawAxioms inc valuation ↔
      ResonanceLawModel inc valuation
  physical_characterization : Nonempty (ResonanceSpec inc) ↔
    SatisfiesAllResonanceLawAxioms inc (resonanceValuation inc)
  soundness : ∀ formula : Formula (ResonanceAtom I),
    ResonanceLawDerives inc formula →
      ResonanceLawSemanticallyEntails inc formula
  kripke_soundness : ∀ formula : Formula (ResonanceAtom I),
    ResonanceLawDerives inc formula →
      ResonanceLawKripkeEntails inc formula

theorem generalResonanceInternalLanguageTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    GeneralResonanceInternalLanguageTheorem inc where
  model_characterization := resonanceLawAxioms_characterize_models inc
  physical_characterization := resonanceSpec_iff_physical_models_law_axioms inc
  soundness := fun _ => resonanceLawDerives_sound
  kripke_soundness := fun _ => resonanceLawDerives_kripke_sound

end IncidenceCore
