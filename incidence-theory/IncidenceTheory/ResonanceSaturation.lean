import IncidenceTheory.IncidenceResearch
import Mathlib.Order.Closure

namespace IncidenceCore

universe u

/- Resonance choices over a fixed incidence skeleton.  Requiring the selected
   glue graph to be included is exactly what is needed to rebuild `Incidence`;
   all other structural fields remain fixed. -/
structure ResonanceExtension
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  relation : I → I → I → Prop
  selected : ∀ {left right output}, inc.glue left right = some output →
    relation left right output

@[ext] theorem ResonanceExtension.ext
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second : ResonanceExtension inc}
    (relation_iff : ∀ left right output,
      first.relation left right output ↔ second.relation left right output) :
    first = second := by
  cases first with
  | mk firstRelation firstSelected =>
    cases second with
    | mk secondRelation secondSelected =>
      have relationEq : firstRelation = secondRelation := by
        funext left right output
        exact propext (relation_iff left right output)
      subst secondRelation
      rfl

instance ResonanceExtension.partialOrder
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T} :
    PartialOrder (ResonanceExtension inc) where
  le first second := ∀ ⦃left right output⦄,
    first.relation left right output → second.relation left right output
  le_refl _ _ _ _ resonant := resonant
  le_trans _ _ _ firstSecond secondThird _ _ _ resonant :=
    secondThird (firstSecond resonant)
  le_antisymm first second firstSecond secondFirst := by
    apply ResonanceExtension.ext
    intro left right output
    exact ⟨fun resonant => firstSecond resonant,
      fun resonant => secondFirst resonant⟩

def ResonanceExtension.model
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) : Incidence I R T :=
  { inc with
    resonance := extension.relation
    selected_resonates := extension.selected }

theorem ResonanceExtension.approxBisim_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) {first second : I} :
    approxBisim extension.model first second ↔ approxBisim inc first second :=
  Iff.rfl

def baseResonanceExtension
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceExtension inc where
  relation := inc.resonance
  selected := inc.selected_resonates

/- Existential quotient image followed by pullback along quotient projections.
   This is the closure operation on resonance extensions. -/
def ResonanceExtension.saturate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) : ResonanceExtension inc where
  relation := fun left right output =>
    quotientResonance extension.model
      (Quotient.mk (approxBisimSetoid extension.model) left)
      (Quotient.mk (approxBisimSetoid extension.model) right)
      (Quotient.mk (approxBisimSetoid extension.model) output)
  selected := fun selected =>
    quotientResonance_of_resonance (extension.selected selected)

theorem ResonanceExtension.le_saturate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) : extension ≤ extension.saturate := by
  intro left right output resonant
  exact quotientResonance_of_resonance resonant

theorem ResonanceExtension.saturate_mono
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second : ResonanceExtension inc} (included : first ≤ second) :
    first.saturate ≤ second.saturate := by
  intro left right output saturated
  rcases saturated with
    ⟨sourceLeft, sourceRight, sourceOutput, leftEq, rightEq, outputEq,
      resonant⟩
  exact ⟨sourceLeft, sourceRight, sourceOutput, leftEq, rightEq, outputEq,
    included resonant⟩

theorem ResonanceExtension.saturate_exactDescent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) :
    ResonanceRelationDescendsExactly extension.saturate.model :=
  bisimulationResonanceSaturation_exactDescent extension.model

theorem ResonanceExtension.saturate_idempotent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) :
    extension.saturate.saturate = extension.saturate := by
  apply ResonanceExtension.ext
  exact bisimulationResonanceSaturation_idempotent extension.model

def resonanceSaturationClosure
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ClosureOperator (ResonanceExtension inc) where
  toFun := ResonanceExtension.saturate
  monotone' _ _ := ResonanceExtension.saturate_mono
  le_closure' := ResonanceExtension.le_saturate
  idempotent' := ResonanceExtension.saturate_idempotent

theorem ResonanceExtension.saturate_eq_self_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) :
    extension.saturate = extension ↔
      QuotientResonanceCongruent extension.model := by
  constructor
  · intro fixed
    apply (bisimulationResonanceSaturation_eq_self_iff extension.model).mp
    intro left right output
    have relationEq := congrArg ResonanceExtension.relation fixed
    exact Iff.of_eq
      (congrFun (congrFun (congrFun relationEq left) right) output)
  · intro congruent
    apply ResonanceExtension.ext
    exact (bisimulationResonanceSaturation_eq_self_iff extension.model).mpr
      congruent

theorem resonanceSaturationClosure_isClosed_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc) :
    (resonanceSaturationClosure inc).IsClosed extension ↔
      QuotientResonanceCongruent extension.model := by
  rw [ClosureOperator.isClosed_iff]
  exact extension.saturate_eq_self_iff

/- The closed (exact-descent) resonance extensions form a reflective
   sub-poset.  This is the order-enriched categorical form of the universal
   minimality theorem; the induced closure operator is the associated
   idempotent monad on the thin category. -/
def resonanceSaturationReflection
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    GaloisInsertion (resonanceSaturationClosure inc).toCloseds
      (fun closed => (closed : ResonanceExtension inc)) :=
  (resonanceSaturationClosure inc).gi

theorem resonanceSaturation_reflection_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (extension : ResonanceExtension inc)
    (closed : (resonanceSaturationClosure inc).Closeds) :
    (resonanceSaturationClosure inc).toCloseds extension ≤ closed ↔
      extension ≤ (closed : ResonanceExtension inc) :=
  (resonanceSaturationReflection inc).gc extension closed

end IncidenceCore
