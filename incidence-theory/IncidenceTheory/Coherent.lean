import IncidenceTheory
import IncidenceTheory.Logic

/-!
  The coherent layer is the formal home for the strong Inc theorems.
  Bare `Incidence` remains intentionally permissive: it admits chains and
  cycles that refute an unconditional boundary-square law.  A
  `CoherentIncidence` instead packages precisely the extra data required for
  chain-complex, pushout, and complete propositional-logic results.
-/

namespace IncidenceCore

universe u

structure CoherentIncidence (I R T : Type u) [DecidableEq I] where
  chainPushout : ChainComplexPushoutIncidence I R T
  completeLogic : CompletePropositionalInternalLogic I

theorem CoherentIncidence.boundary_composition_zero
    {I R T : Type u} [DecidableEq I] (coherent : CoherentIncidence I R T)
    (idx : List I) (i k : I) (hi : i ∈ idx) (hk : k ∈ idx) :
    boundary_composition coherent.chainPushout.inc idx i k = 0 :=
  coherent.chainPushout.boundary_composition_zero idx i k hi hk

def CoherentIncidence.glue_creates_pushout
    {I R T : Type u} [DecidableEq I] (coherent : CoherentIncidence I R T)
    {i j k : I} (hglue : coherent.chainPushout.inc.glue i j = some k) :
    { pushout : PushoutWitness (coherent.chainPushout.glue_pushout.diagram i j) //
      pushout.apex = k } :=
  coherent.chainPushout.glue_creates_pushout hglue

theorem CoherentIncidence.kripke_complete
    {I R T : Type u} [DecidableEq I] (coherent : CoherentIncidence I R T)
    (context : List (Formula I)) (formula : Formula I) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  coherent.completeLogic.kripke_complete context formula

theorem CoherentIncidence.internal_logic_heyting
    {I R T : Type u} [DecidableEq I] (_coherent : CoherentIncidence I R T) :
    Formula.LogicalHeytingAlgebraLaws I :=
  Formula.logicalHeytingAlgebraLaws I

/- Relative consistency at the internal-logic level: the empty coherent
   theory has a Kripke model and therefore cannot derive bottom.  This is a
   theorem of the Lean metatheory used by the project; it deliberately does
   not claim that Lean proves its own consistency. -/
theorem CoherentIncidence.empty_logic_consistent
    {I R T : Type u} [DecidableEq I] (_coherent : CoherentIncidence I R T) :
    DerivationallyConsistent ([] : List (Formula I)) :=
  empty_context_consistent I

def mapEndpoint {I R Q : Type u} (classify : I → Q)
    (endpoint : Endpoint I R) : Endpoint Q R :=
  { i := classify endpoint.i,
    role := endpoint.role,
    sign := endpoint.sign,
    mult := endpoint.mult,
    mult_pos := endpoint.mult_pos }

/- A quotient-compatible coherent incidence supplies a target incidence and
   proves that the classifier respects boundary and gluing data.  These are
   the missing hypotheses which a bare quotient lacks; without them the
   `cycleIncidence` counterexample cannot be lifted to an incidence quotient. -/
structure CoherentQuotient {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    (source : CoherentIncidence I R T) where
  target : CoherentIncidence Q R T
  classification : BisimulationQuotientClassification (Q := Q) source.chainPushout.inc
  boundary_preserves : ∀ i,
    (source.chainPushout.inc.boundary i).map
      (@mapEndpoint I R Q classification.classify) =
      target.chainPushout.inc.boundary (classification.classify i)
  type_preserves : ∀ i,
    target.chainPushout.inc.typeFunc (classification.classify i) =
      source.chainPushout.inc.typeFunc i
  glue_preserves : ∀ {i j k}, source.chainPushout.inc.glue i j = some k →
    target.chainPushout.inc.glue (classification.classify i) (classification.classify j) =
      some (classification.classify k)

theorem CoherentQuotient.classify_boundary
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (i : I) :
    (source.chainPushout.inc.boundary i).map
      (@mapEndpoint I R Q quotient.classification.classify) =
      quotient.target.chainPushout.inc.boundary (quotient.classification.classify i) :=
  quotient.boundary_preserves i

theorem CoherentQuotient.classify_boundary_mem
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {i : I} {endpoint : Endpoint I R}
    (hendpoint : endpoint ∈ source.chainPushout.inc.boundary i) :
    mapEndpoint quotient.classification.classify endpoint ∈
      quotient.target.chainPushout.inc.boundary (quotient.classification.classify i) := by
  rw [← quotient.classify_boundary i]
  exact List.mem_map.mpr ⟨endpoint, hendpoint, rfl⟩

theorem CoherentQuotient.classify_boundary_preimage
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {i : I} {endpoint : Endpoint Q R}
    (hendpoint : endpoint ∈
      quotient.target.chainPushout.inc.boundary (quotient.classification.classify i)) :
    ∃ sourceEndpoint, sourceEndpoint ∈ source.chainPushout.inc.boundary i ∧
      mapEndpoint quotient.classification.classify sourceEndpoint = endpoint := by
  rw [← quotient.classify_boundary i] at hendpoint
  exact List.mem_map.mp hendpoint

theorem CoherentQuotient.classify_boundary_iff
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (i : I) (endpoint : Endpoint Q R) :
    endpoint ∈ quotient.target.chainPushout.inc.boundary (quotient.classification.classify i) ↔
      ∃ sourceEndpoint, sourceEndpoint ∈ source.chainPushout.inc.boundary i ∧
        mapEndpoint quotient.classification.classify sourceEndpoint = endpoint := by
  constructor
  · exact quotient.classify_boundary_preimage
  · rintro ⟨sourceEndpoint, hsource, hmap⟩
    rw [← hmap]
    exact quotient.classify_boundary_mem hsource

theorem CoherentQuotient.classify_type
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (i : I) :
    quotient.target.chainPushout.inc.typeFunc (quotient.classification.classify i) =
      source.chainPushout.inc.typeFunc i :=
  quotient.type_preserves i

theorem CoherentQuotient.classify_glue
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {i j k : I} (hglue : source.chainPushout.inc.glue i j = some k) :
    quotient.target.chainPushout.inc.glue (quotient.classification.classify i)
      (quotient.classification.classify j) =
      some (quotient.classification.classify k) :=
  quotient.glue_preserves hglue

theorem CoherentQuotient.target_boundary_composition_zero
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (idx : List Q) (i k : Q) (hi : i ∈ idx) (hk : k ∈ idx) :
    boundary_composition quotient.target.chainPushout.inc idx i k = 0 :=
  quotient.target.boundary_composition_zero idx i k hi hk

theorem CoherentQuotient.target_kripke_complete
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (context : List (Formula Q)) (formula : Formula Q) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  quotient.target.kripke_complete context formula

theorem CoherentQuotient.translate_derivation
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {context : List (Formula I)} {formula : Formula I}
    (derivation : Derives context formula) :
    Derives (Formula.mapContext quotient.classification.classify context)
      (formula.map quotient.classification.classify) :=
  derives_map quotient.classification.classify derivation

def CoherentQuotient.logicalMap
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source) :
    Formula.LogicalEquivalenceClass I → Formula.LogicalEquivalenceClass Q :=
  Formula.logicalMap quotient.classification.classify

theorem CoherentQuotient.logicalMap_preserves_and
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (left right : Formula.LogicalEquivalenceClass I) :
    quotient.logicalMap (Formula.logicalAnd left right) =
      Formula.logicalAnd (quotient.logicalMap left) (quotient.logicalMap right) :=
  Formula.logicalMap_and quotient.classification.classify left right

theorem CoherentQuotient.logicalMap_preserves_imp
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (left right : Formula.LogicalEquivalenceClass I) :
    quotient.logicalMap (Formula.logicalImp left right) =
      Formula.logicalImp (quotient.logicalMap left) (quotient.logicalMap right) :=
  Formula.logicalMap_imp quotient.classification.classify left right

theorem CoherentQuotient.logicalMap_preserves_neg
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (formula : Formula.LogicalEquivalenceClass I) :
    quotient.logicalMap (Formula.logicalNeg formula) =
      Formula.logicalNeg (quotient.logicalMap formula) :=
  Formula.logicalMap_neg quotient.classification.classify formula

theorem CoherentQuotient.translate_satisfies
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (valuation : Q → Prop) (formula : Formula I) :
    Satisfies valuation (formula.map quotient.classification.classify) ↔
      Satisfies (fun incidence => valuation (quotient.classification.classify incidence)) formula :=
  satisfies_map quotient.classification.classify valuation formula

/- Reflection of syntax needs more than quotient compatibility: a genuinely
   collapsing classifier cannot be inverted.  A supplied left inverse is the
   precise conservative-translation hypothesis. -/
structure CoherentQuotientLogicalRetract
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source) where
  retraction : Q → I
  left_inverse : ∀ incidence, retraction (quotient.classification.classify incidence) = incidence

theorem CoherentQuotient.reflect_derivation
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (retract : CoherentQuotientLogicalRetract quotient)
    {context : List (Formula I)} {formula : Formula I} :
    Derives (Formula.mapContext quotient.classification.classify context)
      (formula.map quotient.classification.classify) →
      Derives context formula :=
  derives_map_reflect_of_leftInverse quotient.classification.classify retract.retraction
    retract.left_inverse

theorem CoherentQuotient.translate_derivation_iff
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (retract : CoherentQuotientLogicalRetract quotient)
    (context : List (Formula I)) (formula : Formula I) :
    Derives (Formula.mapContext quotient.classification.classify context)
      (formula.map quotient.classification.classify) ↔ Derives context formula := by
  constructor
  · exact quotient.reflect_derivation retract
  · exact quotient.translate_derivation

theorem CoherentQuotient.reflect_satisfies
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (retract : CoherentQuotientLogicalRetract quotient)
    (valuation : I → Prop) (formula : Formula I) :
    Satisfies (fun target => valuation (retract.retraction target))
      (formula.map quotient.classification.classify) ↔
      Satisfies valuation formula := by
  rw [satisfies_map]
  have hvaluation :
      (fun incidence => valuation (retract.retraction
        (quotient.classification.classify incidence))) = valuation := by
    funext incidence
    rw [retract.left_inverse]
  rw [hvaluation]

theorem CoherentQuotientLogicalRetract.classifier_injective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} {quotient : CoherentQuotient (Q := Q) source}
    (retract : CoherentQuotientLogicalRetract quotient) :
    ∀ ⦃left right : I⦄,
      quotient.classification.classify left = quotient.classification.classify right →
        left = right := by
  intro left right hclassify
  have h := congrArg retract.retraction hclassify
  simpa only [retract.left_inverse] using h

theorem CoherentQuotientLogicalRetract.logicalMap_leftInverse
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} {quotient : CoherentQuotient (Q := Q) source}
    (retract : CoherentQuotientLogicalRetract quotient)
    (formula : Formula.LogicalEquivalenceClass I) :
    Formula.logicalMap retract.retraction (quotient.logicalMap formula) = formula :=
  Formula.logicalMap_leftInverse quotient.classification.classify
    retract.retraction retract.left_inverse formula

theorem CoherentQuotient.logicalMap_injective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (retract : CoherentQuotientLogicalRetract quotient) :
    ∀ ⦃left right : Formula.LogicalEquivalenceClass I⦄,
      quotient.logicalMap left = quotient.logicalMap right → left = right :=
  Formula.logicalMap_injective_of_leftInverse quotient.classification.classify
    retract.retraction retract.left_inverse

theorem CoherentQuotient.logicalMap_surjective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source) :
    ∀ target : Formula.LogicalEquivalenceClass Q,
      ∃ sourceFormula : Formula.LogicalEquivalenceClass I,
        quotient.logicalMap sourceFormula = target :=
  Formula.logicalMap_surjective quotient.classification.classify
    quotient.classification.surjective

theorem CoherentQuotient.logicalMap_bijective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (retract : CoherentQuotientLogicalRetract quotient) :
    (∀ ⦃left right : Formula.LogicalEquivalenceClass I⦄,
      quotient.logicalMap left = quotient.logicalMap right → left = right) ∧
    (∀ target : Formula.LogicalEquivalenceClass Q,
      ∃ sourceFormula : Formula.LogicalEquivalenceClass I,
        quotient.logicalMap sourceFormula = target) :=
  ⟨quotient.logicalMap_injective retract, quotient.logicalMap_surjective⟩

theorem CoherentQuotient.logicalMap_orderEmbedding_iff
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (retract : CoherentQuotientLogicalRetract quotient)
    (left right : Formula.LogicalEquivalenceClass I) :
    quotient.logicalMap left ≤ quotient.logicalMap right ↔ left ≤ right :=
  Formula.logicalMap_orderEmbedding_iff quotient.classification.classify
    retract.retraction retract.left_inverse left right

theorem CoherentQuotientLogicalRetract.source_bisim_faithful
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} {quotient : CoherentQuotient (Q := Q) source}
    (retract : CoherentQuotientLogicalRetract quotient)
    {left right : I} :
    approxBisim source.chainPushout.inc left right → left = right := by
  intro hbisim
  apply retract.classifier_injective
  exact quotient.classification.respects hbisim

noncomputable def CoherentQuotientLogicalRetract.of_source_bisim_faithful
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (faithful : ∀ {left right : I},
      approxBisim source.chainPushout.inc left right → left = right) :
    CoherentQuotientLogicalRetract quotient where
  retraction := fun target => Classical.choose (quotient.classification.surjective target)
  left_inverse := by
    intro incidence
    apply faithful
    apply quotient.classification.reflects
    exact Classical.choose_spec
      (quotient.classification.surjective (quotient.classification.classify incidence))

theorem coherentQuotient_has_logicalRetract_iff_source_bisim_faithful
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source) :
    Nonempty (CoherentQuotientLogicalRetract quotient) ↔
      ∀ {left right : I},
        approxBisim source.chainPushout.inc left right → left = right := by
  constructor
  · rintro ⟨retract⟩
    exact retract.source_bisim_faithful
  · intro faithful
    exact ⟨CoherentQuotientLogicalRetract.of_source_bisim_faithful quotient faithful⟩

def CoherentQuotient.target_glue_creates_pushout
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {i j k : Q} (hglue : quotient.target.chainPushout.inc.glue i j = some k) :
    { pushout : PushoutWitness (quotient.target.chainPushout.glue_pushout.diagram i j) //
      pushout.apex = k } :=
  quotient.target.glue_creates_pushout hglue

theorem CoherentQuotient.quotient_lift_injective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    {left right : IncidenceQuotient source.chainPushout.inc}
    (h : quotient.classification.lift left = quotient.classification.lift right) :
    left = right :=
  quotient.classification.lift_injective h

theorem CoherentQuotient.quotient_lift_surjective
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {source : CoherentIncidence I R T} (quotient : CoherentQuotient (Q := Q) source)
    (target : Q) :
    ∃ sourceClass : IncidenceQuotient source.chainPushout.inc,
      quotient.classification.lift sourceClass = target :=
  quotient.classification.lift_surjective target

end IncidenceCore
