import IncidenceTheory.DependentDisplayProjectionSemantics

namespace IncidenceCore

open CategoryTheory

universe u

noncomputable def IncDepRawSubstitution.comp
    {source middle target : List IncDepRawType}
    (before : IncDepRawSubstitution source middle)
    (after : IncDepRawSubstitution middle target) :
    IncDepRawSubstitution source target where
  term index := (after.term index).substitute before.term
  preserves := by
    intro position type lookup
    have substituted := (after.preserves lookup).substitute before
    rw [IncDepRawType.substitute_comp] at substituted
    exact substituted

@[simp] theorem IncDepRawSubstitution.comp_term
    {source middle target : List IncDepRawType}
    (before : IncDepRawSubstitution source middle)
    (after : IncDepRawSubstitution middle target) (index : Nat) :
    (before.comp after).term index =
      (after.term index).substitute before.term :=
  rfl

def IncDepRawSubstitutionSemanticResult.comp
    {source middle target : List IncDepRawType}
    {before : IncDepRawSubstitution source middle}
    {after : IncDepRawSubstitution middle target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {middleWellFormed : IncDepRawContext.WellFormed middle}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {middleResult : IncDepRawContextSemanticResult middleWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (beforeResult : IncDepRawSubstitutionSemanticResult before
      sourceResult middleResult)
    (afterResult : IncDepRawSubstitutionSemanticResult after
      middleResult targetResult) :
    IncDepRawSubstitutionSemanticResult (before.comp after)
      sourceResult targetResult where
  semanticSubstitution := afterResult.semanticSubstitution.comp
    beforeResult.semanticSubstitution

@[simp] theorem IncDepRawSubstitutionSemanticResult.comp_map
    {source middle target : List IncDepRawType}
    {before : IncDepRawSubstitution source middle}
    {after : IncDepRawSubstitution middle target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {middleWellFormed : IncDepRawContext.WellFormed middle}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {middleResult : IncDepRawContextSemanticResult middleWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (beforeResult : IncDepRawSubstitutionSemanticResult before
      sourceResult middleResult)
    (afterResult : IncDepRawSubstitutionSemanticResult after
      middleResult targetResult) :
    (beforeResult.comp afterResult).semanticSubstitution =
      afterResult.semanticSubstitution.comp beforeResult.semanticSubstitution :=
  rfl

noncomputable def IncDepRawSubstitutionReplacementSemanticResult.comp
    {source middle target : List IncDepRawType}
    {before : IncDepRawSubstitution source middle}
    {after : IncDepRawSubstitution middle target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {middleWellFormed : IncDepRawContext.WellFormed middle}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {middleResult : IncDepRawContextSemanticResult middleWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {beforeResult : IncDepRawSubstitutionSemanticResult before
      sourceResult middleResult}
    {afterResult : IncDepRawSubstitutionSemanticResult after
      middleResult targetResult}
    (_beforeReplacements : IncDepRawSubstitutionReplacementSemanticResult
      beforeResult)
    (afterReplacements : IncDepRawSubstitutionReplacementSemanticResult
      afterResult) :
    IncDepRawSubstitutionReplacementSemanticResult
      (beforeResult.comp afterResult) where
  replacement := by
    intro position type lookup
    let replacement := afterReplacements.replacement lookup
    exact ⟨replacement.1.reindex beforeResult.semanticSubstitution,
      { semanticTerm := replacement.2.semanticTerm.substitute
          beforeResult.semanticSubstitution }⟩

/-- A semantic realization of a substitution into a fixed coherently
    interpreted target context, independent of any particular target term. -/
structure IncDepSemanticSubstitutionInto
    {source target : List IncDepRawType}
    (sourceWellFormed : IncDepRawCoherentContext.WellFormed source)
    (targetWellFormed : IncDepRawCoherentContext.WellFormed target)
    (targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source target) where
  sourceResult : IncDepRawContextSemanticResult sourceWellFormed.toRaw
  substitutionResult : IncDepRawSubstitutionSemanticResult substitution
    sourceResult targetResult
  replacements : IncDepRawSubstitutionReplacementSemanticResult
    substitutionResult

def IncDepSemanticSubstitutionInto.sourceContext
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (_input : IncDepSemanticSubstitutionInto sourceWellFormed targetWellFormed
      targetResult substitution) : IncDepRawFiniteContextObject where
  context := source
  wellFormed := sourceWellFormed.toRaw

def IncDepSemanticSubstitutionInto.targetContext
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (_input : IncDepSemanticSubstitutionInto sourceWellFormed targetWellFormed
      targetResult substitution) : IncDepRawFiniteContextObject where
  context := target
  wellFormed := targetWellFormed.toRaw

noncomputable def IncDepSemanticSubstitutionInto.finiteSubstitution
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepSemanticSubstitutionInto sourceWellFormed targetWellFormed
      targetResult substitution) :
    input.sourceContext ⟶ input.targetContext :=
  Quotient.mk _ substitution.toExtensional

def IncDepCompletedSemanticSubstitution.toSemanticInto
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    IncDepSemanticSubstitutionInto sourceWellFormed typing.contextWellFormed
      input.targetResult substitution where
  sourceResult := input.sourceResult
  substitutionResult := input.substitutionResult
  replacements := input.replacements

/-- Completed semantic realizations are closed under precomposition by any
    target-independent semantic realization into their source context. -/
noncomputable def IncDepCompletedSemanticSubstitution.comp
    {source middle target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCompletedSemanticSubstitution typing middleWellFormed after)
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepSemanticSubstitutionInto sourceWellFormed
      middleWellFormed afterInput.sourceResult before) :
    IncDepCompletedSemanticSubstitution typing sourceWellFormed
      (before.comp after) where
  sourceResult := beforeInput.sourceResult
  targetResult := afterInput.targetResult
  targetTree := afterInput.targetTree
  substitutionResult := beforeInput.substitutionResult.comp
    afterInput.substitutionResult
  replacements := beforeInput.replacements.comp afterInput.replacements

@[simp] theorem IncDepCompletedSemanticSubstitution.comp_map
    {source middle target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCompletedSemanticSubstitution typing middleWellFormed after)
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepSemanticSubstitutionInto sourceWellFormed
      middleWellFormed afterInput.sourceResult before) :
    (afterInput.comp beforeInput).substitutionResult.semanticSubstitution =
      afterInput.substitutionResult.semanticSubstitution.comp
        beforeInput.substitutionResult.semanticSubstitution :=
  rfl

/-- Semantic-realization composition introduces no extra syntactic map: after
    passage to the finite context category it is exactly categorical
    composition. -/
theorem IncDepCompletedSemanticSubstitution.comp_finite_exact
    {source middle target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCompletedSemanticSubstitution typing middleWellFormed after)
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepSemanticSubstitutionInto sourceWellFormed
      middleWellFormed afterInput.sourceResult before) :
    (afterInput.comp beforeInput).finiteSubstitution =
      beforeInput.finiteSubstitution ≫ afterInput.finiteSubstitution := by
  apply Quotient.sound
  intro index indexLt
  rfl

structure IncDepSemanticSubstitutionCompositionTheorem : Prop where
  rawExact : ∀ {source middle target : List IncDepRawType}
    (before : IncDepRawSubstitution source middle)
    (after : IncDepRawSubstitution middle target) (index : Nat),
    (before.comp after).term index =
      (after.term index).substitute before.term
  compositionClosed : ∀
    {source middle target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCompletedSemanticSubstitution.{u}
      typing middleWellFormed after)
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {before : IncDepRawSubstitution source middle}
    (_beforeInput : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      middleWellFormed afterInput.sourceResult before),
    Nonempty (IncDepCompletedSemanticSubstitution.{u} typing sourceWellFormed
      (before.comp after))
  finiteFunctorial : ∀
    {source middle target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {middleWellFormed : IncDepRawCoherentContext.WellFormed middle}
    {after : IncDepRawSubstitution middle target}
    (afterInput : IncDepCompletedSemanticSubstitution.{u}
      typing middleWellFormed after)
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {before : IncDepRawSubstitution source middle}
    (beforeInput : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      middleWellFormed afterInput.sourceResult before),
    (afterInput.comp beforeInput).finiteSubstitution =
      beforeInput.finiteSubstitution ≫ afterInput.finiteSubstitution

theorem incDepSemanticSubstitutionCompositionTheorem :
    IncDepSemanticSubstitutionCompositionTheorem.{u} where
  rawExact := IncDepRawSubstitution.comp_term
  compositionClosed := by
    intro source middle target term type typing middleWellFormed after
      afterInput sourceWellFormed before beforeInput
    exact ⟨afterInput.comp beforeInput⟩
  finiteFunctorial :=
    IncDepCompletedSemanticSubstitution.comp_finite_exact

end IncidenceCore
