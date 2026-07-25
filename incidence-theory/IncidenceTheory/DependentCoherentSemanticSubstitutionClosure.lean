import IncidenceTheory.DependentCoherentSemanticSubstitution

namespace IncidenceCore

universe u

/-- Generic target-independent realizations are closed under composition; this
    is the term-independent form underlying the earlier completed-judgment
    composition theorem. -/
noncomputable def IncDepSemanticSubstitutionInto.comp
    {source middle target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepSemanticSubstitutionInto.{u} middleWellFormed
      targetWellFormed targetResult after)
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      middleWellFormed afterInput.sourceResult before) :
    IncDepSemanticSubstitutionInto.{u} sourceWellFormed targetWellFormed
      targetResult (before.comp after) where
  sourceResult := beforeInput.sourceResult
  substitutionResult := beforeInput.substitutionResult.comp
    afterInput.substitutionResult
  replacements := beforeInput.replacements.comp afterInput.replacements

@[simp] theorem IncDepSemanticSubstitutionInto.comp_map
    {source middle target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepSemanticSubstitutionInto.{u} middleWellFormed
      targetWellFormed targetResult after)
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      middleWellFormed afterInput.sourceResult before) :
    (afterInput.comp beforeInput).substitutionResult.semanticSubstitution =
      afterInput.substitutionResult.semanticSubstitution.comp
        beforeInput.substitutionResult.semanticSubstitution :=
  rfl

/-- Intrinsically coherent semantic substitutions are closed under
    composition.  Lookup equivalences and term equations are reindexed along
    the earlier semantic map. -/
noncomputable def IncDepCoherentSemanticSubstitutionInto.comp
    {source middle target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCoherentSemanticSubstitutionInto.{u} middleWellFormed
      targetWellFormed targetResult after)
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      middleWellFormed afterInput.realization.sourceResult before) :
    IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult (before.comp after) :=
  let realization := afterInput.realization.comp beforeInput.realization
  { realization := realization
    targetTree := afterInput.targetTree
    lookupCoherence := by
      intro position type lookup
      let afterCoherence := afterInput.lookupCoherence lookup
      exact
        { fiberEquivalence := afterCoherence.fiberEquivalence.reindex
            beforeInput.semanticSubstitution
          termCoherence := by
            change (afterCoherence.fiberEquivalence.reindex
                beforeInput.semanticSubstitution).transport
              (IncTerm.substitute
                (afterInput.realization.replacements.typingResult lookup).semanticTerm
                beforeInput.semanticSubstitution) =
              (afterInput.targetTree.interpretLookup lookup).semanticTerm.substitute
                (afterInput.semanticSubstitution.comp
                  beforeInput.semanticSubstitution)
            rw [IncTypeInContext.FiberEquiv.reindex_transport]
            rw [afterCoherence.termCoherence]
            rfl } }

@[simp] theorem IncDepCoherentSemanticSubstitutionInto.comp_map
    {source middle target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCoherentSemanticSubstitutionInto.{u} middleWellFormed
      targetWellFormed targetResult after)
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      middleWellFormed afterInput.realization.sourceResult before) :
    (afterInput.comp beforeInput).semanticSubstitution =
      afterInput.semanticSubstitution.comp beforeInput.semanticSubstitution :=
  rfl

/-- General source-side pairing preserves intrinsic lookup coherence. -/
noncomputable def IncDepGeneralSemanticPairingHead.coherentRealization
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base.realization type) :
    IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult head.rawPair :=
  let realization := head.realization
  let extendedTree := IncDepRawContextSemanticTree.extend base.targetTree
    head.formationResult.targetFormationResult
  { realization := realization
    targetTree := extendedTree
    lookupCoherence := by
      intro position lookupType lookup
      cases lookup with
      | here =>
          exact
            { fiberEquivalence := head.formationResult.semanticFiberEquivalence
              termCoherence := rfl }
      | there previous =>
          let previousCoherence := base.lookupCoherence previous
          exact
            { fiberEquivalence := previousCoherence.fiberEquivalence
              termCoherence := previousCoherence.termCoherence } }

@[simp] theorem IncDepGeneralSemanticPairingHead.coherentRealization_map
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base.realization type) :
    head.coherentRealization.semanticSubstitution =
      head.realization.substitutionResult.semanticSubstitution :=
  rfl

structure IncDepCoherentSemanticSubstitutionClosureTheorem : Prop where
  compositionClosed : ∀
    {source middle target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCoherentSemanticSubstitutionInto.{u} middleWellFormed
      targetWellFormed targetResult after)
    {before : IncDepRawSubstitution source middle}
    (_beforeInput : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      middleWellFormed afterInput.realization.sourceResult before),
    Nonempty (IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult (before.comp after))
  pairingClosed : ∀
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base.realization type),
    Nonempty (IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult head.rawPair)

theorem incDepCoherentSemanticSubstitutionClosureTheorem :
    IncDepCoherentSemanticSubstitutionClosureTheorem.{u} where
  compositionClosed := by
    intro source middle target sourceWellFormed middleWellFormed
      targetWellFormed targetResult after afterInput before beforeInput
    exact ⟨afterInput.comp beforeInput⟩
  pairingClosed := fun head => ⟨head.coherentRealization⟩

end IncidenceCore
