import IncidenceTheory.DependentCoherentSemanticSubstitutionInduction

namespace IncidenceCore

universe u

/-- A semantic telescope indexed by the coherent formation-readiness telescope
    that generated it.  This keeps each semantic head aligned with its exact
    coherent formation witness, rather than storing readiness and semantics in
    unrelated structures. -/
inductive IncDepAlignedContextSemanticTree :
    {context : List IncDepRawType} →
    (wellFormed : IncDepRawCoherentContext.WellFormed context) →
    (result : IncDepRawContextSemanticResult.{u} wellFormed.toRaw) →
    Type (u + 2)
  | empty : IncDepAlignedContextSemanticTree .empty
      incDepRawEmptyContextSemantic
  | extend {context : List IncDepRawType} {type : IncDepRawType}
      {tailWellFormed : IncDepRawCoherentContext.WellFormed context}
      {formation : IncDepRawWellFormed context type}
      {headReady : IncDepRawCoherentFormationDispatchReady formation}
      {tailResult : IncDepRawContextSemanticResult.{u} tailWellFormed.toRaw}
      (tail : IncDepAlignedContextSemanticTree tailWellFormed tailResult)
      (head : IncDepRawFormationSemanticResult formation tailResult) :
      IncDepAlignedContextSemanticTree (.extend tailWellFormed headReady)
        (tailResult.extend (typeWellFormed := formation) head.semanticType)

noncomputable def IncDepAlignedContextSemanticTree.toRawTree
    {context : List IncDepRawType}
    {wellFormed : IncDepRawCoherentContext.WellFormed context}
    {result : IncDepRawContextSemanticResult.{u} wellFormed.toRaw}
    (tree : IncDepAlignedContextSemanticTree wellFormed result) :
    IncDepRawContextSemanticTree result := by
  induction tree with
  | empty => exact incDepRawEmptyContextSemanticTree
  | extend tail head ih =>
      exact IncDepRawContextSemanticTree.extend ih head

@[simp] theorem IncDepAlignedContextSemanticTree.toRawTree_empty :
    (IncDepAlignedContextSemanticTree.empty :
      IncDepAlignedContextSemanticTree
        IncDepRawCoherentContext.WellFormed.empty
          incDepRawEmptyContextSemantic).toRawTree =
      incDepRawEmptyContextSemanticTree :=
  rfl

@[simp] theorem IncDepAlignedContextSemanticTree.toRawTree_extend
    {context : List IncDepRawType} {type : IncDepRawType}
    {tailWellFormed : IncDepRawCoherentContext.WellFormed context}
    {formation : IncDepRawWellFormed context type}
    {headReady : IncDepRawCoherentFormationDispatchReady formation}
    {tailResult : IncDepRawContextSemanticResult.{u} tailWellFormed.toRaw}
    (tail : IncDepAlignedContextSemanticTree tailWellFormed tailResult)
    (head : IncDepRawFormationSemanticResult formation tailResult) :
    (IncDepAlignedContextSemanticTree.extend
      (headReady := headReady) tail head).toRawTree =
      IncDepRawContextSemanticTree.extend tail.toRawTree head :=
  rfl

/-- Align the existing canonical synthesis with the coherent readiness
    telescope that generated it.  The canonical semantic result is fixed as
    the index from the outset. -/
noncomputable def IncDepRawCoherentContext.WellFormed.alignSynthesis
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context) :
    IncDepAlignedContextSemanticTree wellFormed
      (wellFormed.synthesize model hypotheses).1 := by
  induction wellFormed with
  | empty => exact IncDepAlignedContextSemanticTree.empty
  | extend tail headReady ih =>
      simp only [IncDepRawCoherentContext.WellFormed.synthesize]
      let tailSynthesis := tail.synthesize model hypotheses
      let replacements :=
        IncDepRawSubstitutionReplacementSemanticResult.identity tailSynthesis.2
      let headDispatch :=
        (model.preservationCanonical hypotheses).formation.dispatch
          headReady tailSynthesis.2 replacements
      exact IncDepAlignedContextSemanticTree.extend ih
        headDispatch.formationResult.targetFormationResult

/-- Canonical aligned synthesis packaged with the exact existing result. -/
noncomputable def IncDepRawCoherentContext.WellFormed.synthesizeAligned
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context) :
    Sigma fun result : IncDepRawContextSemanticResult wellFormed.toRaw =>
      IncDepAlignedContextSemanticTree wellFormed result :=
  ⟨(wellFormed.synthesize model hypotheses).1,
    wellFormed.alignSynthesis model hypotheses⟩

/-- Erase alignment while retaining the dependent result/tree package. -/
noncomputable def IncDepRawCoherentContext.WellFormed.synthesizeAlignedRaw
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context) :
    Sigma fun result : IncDepRawContextSemanticResult wellFormed.toRaw =>
      IncDepRawContextSemanticTree result :=
  let aligned := wellFormed.synthesizeAligned model hypotheses
  ⟨aligned.1, aligned.2.toRawTree⟩

theorem IncDepRawCoherentContext.WellFormed.alignSynthesis_toRawTree
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context) :
    HEq (wellFormed.alignSynthesis model hypotheses).toRawTree
      (wellFormed.synthesize model hypotheses).2 := by
  induction wellFormed with
  | empty => rfl
  | extend tail headReady ih =>
      simp only [IncDepRawCoherentContext.WellFormed.alignSynthesis,
        IncDepRawCoherentContext.WellFormed.synthesize,
        IncDepAlignedContextSemanticTree.toRawTree]
      change HEq
        ((tail.alignSynthesis model hypotheses).toRawTree.extend
          ((model.preservationCanonical hypotheses).formation.dispatch
            headReady (tail.synthesize model hypotheses).2
            (IncDepRawSubstitutionReplacementSemanticResult.identity
              (tail.synthesize model hypotheses).2)).formationResult.targetFormationResult)
        ((tail.synthesize model hypotheses).2.extend
          ((model.preservationCanonical hypotheses).formation.dispatch
            headReady (tail.synthesize model hypotheses).2
            (IncDepRawSubstitutionReplacementSemanticResult.identity
              (tail.synthesize model hypotheses).2)).formationResult.targetFormationResult)
      exact heq_of_eq (congrArg
        (fun tailTree => tailTree.extend
          ((model.preservationCanonical hypotheses).formation.dispatch
            headReady (tail.synthesize model hypotheses).2
            (IncDepRawSubstitutionReplacementSemanticResult.identity
              (tail.synthesize model hypotheses).2)).formationResult.targetFormationResult)
        (eq_of_heq ih))

theorem IncDepRawCoherentContext.WellFormed.synthesizeAlignedRaw_eq
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context) :
    wellFormed.synthesizeAlignedRaw model hypotheses =
      wellFormed.synthesize model hypotheses := by
  apply Sigma.ext
  · rfl
  · exact wellFormed.alignSynthesis_toRawTree model hypotheses

theorem IncDepRawCoherentContext.WellFormed.synthesizeAligned_result_eq
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context) :
    (wellFormed.synthesizeAligned model hypotheses).1 =
      (wellFormed.synthesize model hypotheses).1 :=
  rfl

theorem IncDepRawCoherentContext.WellFormed.synthesizeAligned_tree_eq
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context) :
    HEq (wellFormed.synthesizeAligned model hypotheses).2.toRawTree
      (wellFormed.synthesize model hypotheses).2 := by
  have packageEq := wellFormed.synthesizeAlignedRaw_eq model hypotheses
  exact Sigma.mk.inj packageEq |>.2

structure IncDepAlignedContextSemanticsTheorem : Prop where
  packageExact : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context),
    wellFormed.synthesizeAlignedRaw model hypotheses =
      wellFormed.synthesize model hypotheses
  resultExact : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context),
    (wellFormed.synthesizeAligned model hypotheses).1 =
      (wellFormed.synthesize model hypotheses).1
  treeExact : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses)
    {context : List IncDepRawType}
    (wellFormed : IncDepRawCoherentContext.WellFormed context),
    HEq (wellFormed.synthesizeAligned model hypotheses).2.toRawTree
      (wellFormed.synthesize model hypotheses).2

theorem incDepAlignedContextSemanticsTheorem :
    IncDepAlignedContextSemanticsTheorem.{u} where
  packageExact :=
    IncDepRawCoherentContext.WellFormed.synthesizeAlignedRaw_eq
  resultExact :=
    IncDepRawCoherentContext.WellFormed.synthesizeAligned_result_eq
  treeExact :=
    IncDepRawCoherentContext.WellFormed.synthesizeAligned_tree_eq

end IncidenceCore
