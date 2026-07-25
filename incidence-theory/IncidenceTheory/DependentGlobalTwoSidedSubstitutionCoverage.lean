import IncidenceTheory.DependentSourceHeadReadinessAlignment

namespace IncidenceCore

universe u

/-- One global realization package with the supplied source endpoint retained
    exactly despite the dependent result indices. -/
structure IncDepGlobalTwoSidedSubstitutionPackage
    {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source target) where
  targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw
  input : IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed
    targetWellFormed targetResult substitution
  sourceTreeExact : HEq input.sourceTree sourceTree

/-- Unanchored global two-sided coverage: every raw substitution into a
    coherent target has some coherent semantic target result, while the source
    result and source tree are fixed exactly.  Canonical target anchoring is a
    stronger, separate equality problem. -/
def IncDepGlobalTwoSidedSubstitutionCoverage : Prop :=
  ∀ {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source target),
    Nonempty (IncDepGlobalTwoSidedSubstitutionPackage.{u} sourceWellFormed
      targetWellFormed sourceResult sourceTree substitution)

/-- The recursive construction promised by the local source-head typing gate.
    It follows the target telescope: the empty target is automatic, and each
    coherent extension is supplied by the exact arbitrary-head constructor. -/
noncomputable def IncDepSourceHeadTypingSemanticCoverage.realizeTwoSided
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source target) :
    Sigma fun targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw =>
      IncDepTwoSidedCoherentSemanticSubstitutionInto.{u} sourceWellFormed
        targetWellFormed targetResult substitution := by
  induction targetWellFormed with
  | empty =>
      exact ⟨incDepRawEmptyContextSemantic,
        substitution.twoSidedCoherentEmptySemanticInto sourceTree⟩
  | @extend target type tail formation headReady ih =>
      let tailPackage := ih substitution.tail
      let tailInput := tailPackage.2
      let head := coverage.buildHead tailInput.coherent formation headReady
        (substitution.term 0) substitution.headTyping
      exact ⟨head.extendedTargetResult,
        coverage.extendTwoSidedCoherently substitution tailInput formation
          headReady⟩

@[simp] theorem IncDepSourceHeadTypingSemanticCoverage.realizeTwoSided_sourceTree
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source target) :
    HEq (coverage.realizeTwoSided sourceWellFormed targetWellFormed sourceResult
      sourceTree substitution).2.sourceTree sourceTree := by
  induction targetWellFormed with
  | empty => exact HEq.rfl
  | @extend target type tail formation headReady ih =>
      simp only [IncDepSourceHeadTypingSemanticCoverage.realizeTwoSided]
      have tailExact := ih substitution.tail
      exact tailExact

/-- Local typing coverage therefore implies global two-sided semantic
    substitution coverage, with no additional recursive premise. -/
noncomputable def IncDepSourceHeadTypingSemanticCoverage.toGlobalTwoSidedCoverage
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses) :
    IncDepGlobalTwoSidedSubstitutionCoverage.{u} := by
  intro source target sourceWellFormed targetWellFormed sourceResult sourceTree
    substitution
  let realized := coverage.realizeTwoSided sourceWellFormed targetWellFormed
    sourceResult sourceTree substitution
  let package : IncDepGlobalTwoSidedSubstitutionPackage sourceWellFormed
      targetWellFormed sourceResult sourceTree substitution :=
    { targetResult := realized.1
      input := realized.2
      sourceTreeExact := coverage.realizeTwoSided_sourceTree sourceWellFormed
        targetWellFormed sourceResult sourceTree substitution }
  exact ⟨package⟩

/-- The stronger readiness/alignment gate inherits the same global result by
    first discharging typing-only source-head coverage. -/
noncomputable def IncDepSourceHeadReadinessAlignmentCoverage.toGlobalTwoSidedCoverage
    {model : IncDepRawSubstitutionFiberModel.{u}}
    {hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}}
    (coverage : IncDepSourceHeadReadinessAlignmentCoverage model hypotheses) :
    IncDepGlobalTwoSidedSubstitutionCoverage.{u} := by
  let typingCoverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses :=
    coverage.toTypingCoverage
  intro source target sourceWellFormed targetWellFormed sourceResult sourceTree
    substitution
  exact typingCoverage.toGlobalTwoSidedCoverage sourceWellFormed
    targetWellFormed sourceResult sourceTree substitution

structure IncDepGlobalTwoSidedSubstitutionCoverageTheorem : Prop where
  typingCoverageSuffices : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}),
    IncDepSourceHeadTypingSemanticCoverage model hypotheses →
      IncDepGlobalTwoSidedSubstitutionCoverage.{u}
  alignedReadinessSuffices : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}),
    IncDepSourceHeadReadinessAlignmentCoverage model hypotheses →
      IncDepGlobalTwoSidedSubstitutionCoverage.{u}
  sourceTreeExact : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    (coverage : IncDepSourceHeadTypingSemanticCoverage model hypotheses)
    {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (sourceTree : IncDepRawContextSemanticTree sourceResult)
    (substitution : IncDepRawSubstitution source target),
    HEq (coverage.realizeTwoSided sourceWellFormed targetWellFormed sourceResult
      sourceTree substitution).2.sourceTree sourceTree

theorem incDepGlobalTwoSidedSubstitutionCoverageTheorem :
    IncDepGlobalTwoSidedSubstitutionCoverageTheorem.{u} where
  typingCoverageSuffices := fun _ _ coverage =>
    coverage.toGlobalTwoSidedCoverage
  alignedReadinessSuffices := fun _ _ coverage =>
    coverage.toGlobalTwoSidedCoverage
  sourceTreeExact := by
    intro model hypotheses coverage source target sourceWellFormed
      targetWellFormed sourceResult sourceTree substitution
    exact coverage.realizeTwoSided_sourceTree sourceWellFormed targetWellFormed
      sourceResult sourceTree substitution

end IncidenceCore
