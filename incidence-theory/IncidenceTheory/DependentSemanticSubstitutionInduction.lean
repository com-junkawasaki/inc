import IncidenceTheory.DependentRawSubstitutionDecomposition

namespace IncidenceCore

universe u

/-- Semantic realization is invariant under changing only the proof-relevant
    typing witnesses of a raw substitution.  Equality of the term function is
    the exact computational condition needed for transport. -/
noncomputable def IncDepSemanticSubstitutionInto.ofTermEq
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target)
    (_termEq : first.term = second.term) :
    IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult second := by
  let substitutionResult : IncDepRawSubstitutionSemanticResult second
      input.sourceResult targetResult :=
    { semanticSubstitution := input.substitutionResult.semanticSubstitution }
  exact
    { sourceResult := input.sourceResult
      substitutionResult := substitutionResult
      replacements :=
        { replacement := by
            intro position type lookup
            let previous := input.replacements.replacement lookup
            exact ⟨previous.1, { semanticTerm := previous.2.semanticTerm }⟩ } }

@[simp] theorem IncDepSemanticSubstitutionInto.ofTermEq_map
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target)
    (termEq : first.term = second.term) :
    (input.ofTermEq second termEq).substitutionResult.semanticSubstitution =
      input.substitutionResult.semanticSubstitution := by
  rfl

/-- Every proof-relevant raw substitution into the empty context has a
    canonical semantic realization; its unconstrained junk components are
    observationally irrelevant because the target has no lookups. -/
noncomputable def IncDepRawSubstitution.emptySemanticInto
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source []) :
    IncDepSemanticSubstitutionInto.{u} sourceWellFormed .empty
      incDepRawEmptyContextSemantic substitution where
  sourceResult := sourceResult
  substitutionResult := { semanticSubstitution := fun _ => ⟨()⟩ }
  replacements :=
    { replacement := by
        intro position type lookup
        cases lookup }

@[simp] theorem IncDepRawSubstitution.emptySemanticInto_map
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source []) :
    (substitution.emptySemanticInto sourceResult).substitutionResult.semanticSubstitution =
      fun _ => ⟨()⟩ :=
  rfl

/-- One exact induction step for arbitrary semantic-substitution coverage.
    A realization of the canonical tail plus semantic formation/typing data for
    the actual source head realizes the original proof-relevant substitution,
    not merely its reconstructed pairing. -/
noncomputable def IncDepRawSubstitution.semanticIntoOfTailAndHead
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution.tail)
    (head : IncDepGeneralSemanticPairingHead tailInput type)
    (headEq : head.headTerm = substitution.term 0) :
    IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult substitution :=
  head.realization.ofTermEq substitution (by
    funext index
    cases index with
    | zero => exact headEq
    | succ index => rfl)

@[simp] theorem IncDepRawSubstitution.semanticIntoOfTailAndHead_map
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution.tail)
    (head : IncDepGeneralSemanticPairingHead tailInput type)
    (headEq : head.headTerm = substitution.term 0) :
    ((substitution.semanticIntoOfTailAndHead tailInput head headEq)
        |>.substitutionResult.semanticSubstitution) =
      head.realization.substitutionResult.semanticSubstitution :=
  IncDepSemanticSubstitutionInto.ofTermEq_map _ _ _

/-- The recursive semantic coverage interface mirrors the canonical syntactic
    decomposition: empty targets are automatic, and each extension requires
    only the explicit semantic data for its newest component. -/
structure IncDepSemanticSubstitutionInductionTheorem : Prop where
  proofWitnessInvariant : ∀
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (_input : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target),
    first.term = second.term →
      Nonempty (IncDepSemanticSubstitutionInto.{u} sourceWellFormed
        targetWellFormed targetResult second)
  emptyRealized : ∀
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    (_sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source []),
    Nonempty (IncDepSemanticSubstitutionInto.{u} sourceWellFormed .empty
      incDepRawEmptyContextSemantic substitution)
  extendRealized : ∀
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution.tail)
    (head : IncDepGeneralSemanticPairingHead tailInput type),
    head.headTerm = substitution.term 0 →
      Nonempty (IncDepSemanticSubstitutionInto.{u} sourceWellFormed
        head.extendedWellFormed head.extendedTargetResult substitution)

theorem incDepSemanticSubstitutionInductionTheorem :
    IncDepSemanticSubstitutionInductionTheorem.{u} where
  proofWitnessInvariant := fun input second termEq =>
    ⟨input.ofTermEq second termEq⟩
  emptyRealized := fun sourceResult substitution =>
    ⟨substitution.emptySemanticInto sourceResult⟩
  extendRealized := fun substitution tailInput head headEq =>
    ⟨substitution.semanticIntoOfTailAndHead tailInput head headEq⟩

end IncidenceCore
