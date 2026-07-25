import IncidenceTheory.DependentSourceHeadSemanticCoverage

namespace IncidenceCore

universe u

/-- A coherent semantic substitution anchored at both ends.  The previous
    interface retained the target tree needed for lookup coherence; arbitrary
    source-side term interpretation additionally needs the source tree. -/
structure IncDepTwoSidedCoherentSemanticSubstitutionInto
    {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source target) where
  coherent : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
    targetWellFormed targetResult substitution
  sourceTree : IncDepRawContextSemanticTree coherent.realization.sourceResult

def IncDepTwoSidedCoherentSemanticSubstitutionInto.semanticSubstitution
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution) :=
  input.coherent.semanticSubstitution

/-- The two-sided identity uses the same semantic telescope at source and
    target. -/
noncomputable def IncDepTwoSidedCoherentSemanticSubstitutionInto.identity
    {context : List IncDepRawType}
    (contextWellFormed : IncDepRawCoherentContext.WellFormed context)
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed.toRaw)
    (contextTree : IncDepRawContextSemanticTree contextResult) :
    IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} contextWellFormed
      contextWellFormed contextResult (IncDepRawSubstitution.identity context) where
  coherent := IncDepCoherentSemanticSubstitutionInto.identity
    contextWellFormed contextResult contextTree
  sourceTree := contextTree

@[simp] theorem IncDepTwoSidedCoherentSemanticSubstitutionInto.identity_sourceTree
    {context : List IncDepRawType}
    (contextWellFormed : IncDepRawCoherentContext.WellFormed context)
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed.toRaw)
    (contextTree : IncDepRawContextSemanticTree contextResult) :
    (IncDepTwoSidedCoherentSemanticSubstitutionInto.identity
      contextWellFormed contextResult contextTree).sourceTree = contextTree :=
  rfl

/-- Proof-relevant substitution replacement leaves both semantic endpoint
    trees unchanged. -/
noncomputable def IncDepTwoSidedCoherentSemanticSubstitutionInto.ofTermEq
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target)
    (termEq : first.term = second.term) :
    IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult second where
  coherent := input.coherent.ofTermEq second termEq
  sourceTree := input.sourceTree

@[simp] theorem IncDepTwoSidedCoherentSemanticSubstitutionInto.ofTermEq_sourceTree
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target)
    (termEq : first.term = second.term) :
    (input.ofTermEq second termEq).sourceTree = input.sourceTree :=
  rfl

/-- Every substitution into the empty target is two-sided coherent once its
    source semantic telescope is supplied. -/
noncomputable def IncDepRawSubstitution.twoSidedCoherentEmptySemanticInto
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw}
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source []) :
    IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed .empty
      incDepRawEmptyContextSemantic substitution where
  coherent := substitution.coherentEmptySemanticInto sourceResult
  sourceTree := sourceTree

@[simp] theorem IncDepRawSubstitution.twoSidedCoherentEmpty_sourceTree
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw}
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source []) :
    (substitution.twoSidedCoherentEmptySemanticInto sourceTree).sourceTree =
      sourceTree :=
  rfl

/-- Typing-only source-head coverage extends a two-sided coherent tail while
    retaining its exact source semantic telescope. -/
noncomputable def IncDepSourceHeadTypingSemanticCoverage.extendTwoSidedCoherently
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed targetWellFormed targetResult substitution.tail)
    (targetFormation : IncDepRawWellFormed target type)
    (targetReady : IncDepRawCoherentFormationDispatchReady targetFormation) :
    let head := coverage.buildHead tailInput.coherent targetFormation targetReady
      (substitution.term 0) substitution.headTyping
    IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult substitution :=
  let head := coverage.buildHead tailInput.coherent targetFormation targetReady
    (substitution.term 0) substitution.headTyping
  { coherent := substitution.coherentSemanticIntoOfTailAndHead
      tailInput.coherent head rfl
    sourceTree := tailInput.sourceTree }

@[simp] theorem IncDepSourceHeadTypingSemanticCoverage.extendTwoSidedCoherently_sourceTree
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed targetWellFormed targetResult substitution.tail)
    (targetFormation : IncDepRawWellFormed target type)
    (targetReady : IncDepRawCoherentFormationDispatchReady targetFormation) :
    (coverage.extendTwoSidedCoherently substitution tailInput targetFormation
      targetReady).sourceTree = tailInput.sourceTree :=
  rfl

structure IncDepTwoSidedCoherentSemanticSubstitutionTheorem : Prop where
  identityAnchored : ∀ {context : List IncDepRawType}
    (contextWellFormed : IncDepRawCoherentContext.WellFormed context)
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed.toRaw)
    (contextTree : IncDepRawContextSemanticTree contextResult),
    ∃ input : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      contextWellFormed contextWellFormed contextResult
      (IncDepRawSubstitution.identity context),
      HEq input.sourceTree contextTree ∧ input.coherent.targetTree = contextTree
  emptyAnchored : ∀ {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw}
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source []),
    ∃ input : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed .empty incDepRawEmptyContextSemantic substitution,
      HEq input.sourceTree sourceTree
  proofWitnessInvariant : ∀
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
      sourceWellFormed targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target),
    first.term = second.term →
      ∃ output : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u}
        sourceWellFormed targetWellFormed targetResult second,
        HEq output.sourceTree input.sourceTree

theorem incDepTwoSidedCoherentSemanticSubstitutionTheorem :
    IncDepTwoSidedCoherentSemanticSubstitutionTheorem.{u} where
  identityAnchored := fun contextWellFormed contextResult contextTree =>
    ⟨.identity contextWellFormed contextResult contextTree, HEq.rfl, rfl⟩
  emptyAnchored := fun sourceTree substitution =>
    ⟨substitution.twoSidedCoherentEmptySemanticInto sourceTree, HEq.rfl⟩
  proofWitnessInvariant := fun input second termEq =>
    ⟨input.ofTermEq second termEq, HEq.rfl⟩

end IncidenceCore
