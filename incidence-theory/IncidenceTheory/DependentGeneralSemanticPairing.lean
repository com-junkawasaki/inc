import IncidenceTheory.DependentSemanticPairingRealization

namespace IncidenceCore

open CategoryTheory

universe u

/-- The exact local data needed to add an arbitrary source-side head term to a
    semantically realized substitution.  Unlike completed-term pairing, the
    head need not be the reindexing of a term already present over the target. -/
structure IncDepGeneralSemanticPairingHead
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    (base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution)
    (type : IncDepRawType) where
  targetFormation : IncDepRawWellFormed target type
  targetReady : IncDepRawCoherentFormationDispatchReady targetFormation
  headTerm : IncDepRawTerm
  headTyping : IncDepRawHasType source headTerm
    (type.substitute substitution.term)
  formationResult : IncDepRawFormationSubstitutionFiberResult
    (targetFormation := targetFormation) base.substitutionResult
  headResult : IncDepRawTypingSemanticResult headTyping base.sourceResult
    formationResult.sourceFormationResult.semanticType

def IncDepGeneralSemanticPairingHead.extendedWellFormed
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    IncDepRawCoherentContext.WellFormed (type :: target) :=
  .extend targetWellFormed head.targetReady

def IncDepGeneralSemanticPairingHead.extendedTargetResult
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    IncDepRawContextSemanticResult head.extendedWellFormed.toRaw :=
  targetResult.extend (typeWellFormed := head.targetFormation)
    head.formationResult.targetFormationResult.semanticType

/-- The proof-relevant raw pairing with an arbitrary well-typed source head. -/
noncomputable def IncDepGeneralSemanticPairingHead.rawPair
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    IncDepRawSubstitution source (type :: target) where
  term index := match index with
    | 0 => head.headTerm
    | next + 1 => substitution.term next
  preserves := by
    intro position lookupType lookup
    cases lookup with
    | here =>
        simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
          head.headTyping
    | there previous =>
        simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
          substitution.preserves previous

@[simp] theorem IncDepGeneralSemanticPairingHead.rawPair_zero
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    head.rawPair.term 0 = head.headTerm :=
  rfl

@[simp] theorem IncDepGeneralSemanticPairingHead.rawPair_succ
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) (index : Nat) :
    head.rawPair.term (index + 1) = substitution.term index :=
  rfl

/-- General pairing realization.  The semantic head is transported across the
    certified formation equivalence into the target family reindexed by the
    base semantic substitution. -/
noncomputable def IncDepGeneralSemanticPairingHead.realization
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult head.rawPair :=
  let transportedHead := head.formationResult.semanticFiberEquivalence.transport
    head.headResult.semanticTerm
  let semanticSubstitution := base.substitutionResult.semanticSubstitution.extend
    head.formationResult.targetFormationResult.semanticType transportedHead
  { sourceResult := base.sourceResult
    substitutionResult := { semanticSubstitution := semanticSubstitution }
    replacements :=
      { replacement := by
          intro position lookupType lookup
          cases lookup with
          | here =>
              exact ⟨head.formationResult.sourceFormationResult.semanticType,
                { semanticTerm := head.headResult.semanticTerm }⟩
          | there previous =>
              let previousResult := base.replacements.replacement previous
              exact ⟨previousResult.1,
                { semanticTerm := previousResult.2.semanticTerm }⟩ } }

@[simp] theorem IncDepGeneralSemanticPairingHead.realization_projection
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    (targetResult.semanticContext.extendProjection
        head.formationResult.targetFormationResult.semanticType).comp
      head.realization.substitutionResult.semanticSubstitution =
        base.substitutionResult.semanticSubstitution :=
  rfl

@[simp] theorem IncDepGeneralSemanticPairingHead.realization_variable
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    (targetResult.semanticContext.extendVariable
        head.formationResult.targetFormationResult.semanticType).substitute
      head.realization.substitutionResult.semanticSubstitution =
        head.formationResult.semanticFiberEquivalence.transport
          head.headResult.semanticTerm :=
  rfl

noncomputable def IncDepGeneralSemanticPairingHead.targetFiniteType
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    IncDepRawFiniteType base.targetContext where
  raw := type
  formation := ⟨head.targetFormation⟩

/-- The general semantic pairing recovers exactly the quotient-CwF pairing,
    including arbitrary source-side head terms. -/
theorem IncDepGeneralSemanticPairingHead.realization_finite_exact
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type) :
    head.realization.finiteSubstitution =
      head.targetFiniteType.pair base.finiteSubstitution head.headTerm
        ⟨head.headTyping⟩ := by
  apply Quotient.sound
  intro index indexLt
  cases index with
  | zero => rfl
  | succ index =>
      have outEquivalent := Quotient.exact
        (Quotient.out_eq base.finiteSubstitution)
      have baseLt : index < target.length := by
        change index + 1 < (type :: target).length at indexLt
        simpa using indexLt
      exact (outEquivalent index baseLt).symm

structure IncDepGeneralSemanticPairingTheorem : Prop where
  realizationExists : ∀
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type),
    Nonempty (IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      head.extendedWellFormed head.extendedTargetResult head.rawPair)
  finiteExact : ∀
    {source target : List IncDepRawType}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {targetWellFormed : IncDepRawCoherentContext.WellFormed target}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed.toRaw}
    {substitution : IncDepRawSubstitution source target}
    {base : IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      targetWellFormed targetResult substitution}
    {type : IncDepRawType}
    (head : IncDepGeneralSemanticPairingHead base type),
    head.realization.finiteSubstitution =
      head.targetFiniteType.pair base.finiteSubstitution head.headTerm
        ⟨head.headTyping⟩

theorem incDepGeneralSemanticPairingTheorem :
    IncDepGeneralSemanticPairingTheorem.{u} where
  realizationExists := fun head => ⟨head.realization⟩
  finiteExact := IncDepGeneralSemanticPairingHead.realization_finite_exact

end IncidenceCore
