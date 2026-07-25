import IncidenceTheory.DependentCoherentWholeCwFReadiness

namespace IncidenceCore

universe u

/-- Intrinsic lookup coherence is invariant under replacing proof-relevant raw
    substitution witnesses while keeping the computational term function
    fixed. -/
noncomputable def IncDepCoherentSemanticSubstitutionInto.ofTermEq
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target)
    (termEq : first.term = second.term) :
    IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult second :=
  let realization := input.realization.ofTermEq second termEq
  { realization := realization
    targetTree := input.targetTree
    lookupCoherence := by
      intro position type lookup
      let previous := input.lookupCoherence lookup
      exact
        { fiberEquivalence := previous.fiberEquivalence
          termCoherence := previous.termCoherence } }

@[simp] theorem IncDepCoherentSemanticSubstitutionInto.ofTermEq_map
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target)
    (termEq : first.term = second.term) :
    (input.ofTermEq second termEq).semanticSubstitution =
      input.semanticSubstitution :=
  rfl

@[simp] theorem IncDepCoherentSemanticSubstitutionInto.ofTermEq_tree
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (input : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target)
    (termEq : first.term = second.term) :
    (input.ofTermEq second termEq).targetTree = input.targetTree :=
  rfl

/-- Empty targets have canonical intrinsically coherent realizations. -/
noncomputable def IncDepRawSubstitution.coherentEmptySemanticInto
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source []) :
    IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed .empty
      incDepRawEmptyContextSemantic substitution :=
  { realization := substitution.emptySemanticInto sourceResult
    targetTree := incDepRawEmptyContextSemanticTree
    lookupCoherence := by
      intro position type lookup
      cases lookup }

@[simp] theorem IncDepRawSubstitution.coherentEmptySemanticInto_map
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    (sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source []) :
    (substitution.coherentEmptySemanticInto sourceResult).semanticSubstitution =
      fun _ => ⟨()⟩ :=
  rfl

/-- The strengthened recursive extension step realizes the original
    proof-relevant substitution and preserves the exact extended target tree. -/
noncomputable def IncDepRawSubstitution.coherentSemanticIntoOfTailAndHead
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution.tail)
    (head : IncDepGeneralSemanticPairingHead tailInput.realization type)
    (headEq : head.headTerm = substitution.term 0) :
    IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult substitution :=
  head.coherentRealization.ofTermEq substitution (by
    funext index
    cases index with
    | zero => exact headEq
    | succ index => rfl)

@[simp] theorem IncDepRawSubstitution.coherentSemanticIntoOfTailAndHead_map
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution.tail)
    (head : IncDepGeneralSemanticPairingHead tailInput.realization type)
    (headEq : head.headTerm = substitution.term 0) :
    ((substitution.coherentSemanticIntoOfTailAndHead tailInput head headEq)
        |>.semanticSubstitution) = head.coherentRealization.semanticSubstitution :=
  rfl

structure IncDepCoherentSemanticSubstitutionInductionTheorem : Prop where
  proofWitnessInvariant : ∀
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {first : IncDepRawSubstitution source target}
    (_input : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult first)
    (second : IncDepRawSubstitution source target),
    first.term = second.term →
      Nonempty (IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
        targetWellFormed targetResult second)
  emptyRealized : ∀
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    (_sourceResult : IncDepRawContextSemanticResult.{u} sourceWellFormed.toRaw)
    (substitution : IncDepRawSubstitution source []),
    Nonempty (IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      .empty incDepRawEmptyContextSemantic substitution)
  extendRealized : ∀
    {source target : List IncDepRawType} {type : IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    (substitution : IncDepRawSubstitution source (type :: target))
    (tailInput : IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution.tail)
    (head : IncDepGeneralSemanticPairingHead tailInput.realization type),
    head.headTerm = substitution.term 0 →
      Nonempty (IncDepCoherentSemanticSubstitutionInto.{u} sourceWellFormed
        head.extendedWellFormed head.extendedTargetResult substitution)

theorem incDepCoherentSemanticSubstitutionInductionTheorem :
    IncDepCoherentSemanticSubstitutionInductionTheorem.{u} where
  proofWitnessInvariant := fun input second termEq =>
    ⟨input.ofTermEq second termEq⟩
  emptyRealized := fun sourceResult substitution =>
    ⟨substitution.coherentEmptySemanticInto sourceResult⟩
  extendRealized := fun substitution tailInput head headEq =>
    ⟨substitution.coherentSemanticIntoOfTailAndHead tailInput head headEq⟩

end IncidenceCore
