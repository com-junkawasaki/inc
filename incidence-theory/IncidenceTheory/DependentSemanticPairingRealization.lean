import IncidenceTheory.DependentSemanticSubstitutionComposition

namespace IncidenceCore

open CategoryTheory

universe u

/-- Raw comprehension pairing for an actual (proof-relevant) substitution.
    Its newest component is the substituted term and its older components are
    inherited from the base substitution. -/
noncomputable def IncDepCompletedSemanticSubstitution.rawPair
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (_input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    IncDepRawSubstitution source (type :: target) where
  term index := match index with
    | 0 => term.substitute substitution.term
    | next + 1 => substitution.term next
  preserves := by
    intro position lookupType lookup
    cases lookup with
    | here =>
        simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
          typing.typing.substitute substitution
    | there previous =>
        simpa only [IncDepRawType.rename_substitute, Function.comp_apply] using
          substitution.preserves previous

@[simp] theorem IncDepCompletedSemanticSubstitution.rawPair_zero
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution) :
    input.rawPair.term 0 = term.substitute substitution.term :=
  rfl

@[simp] theorem IncDepCompletedSemanticSubstitution.rawPair_succ
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution typing sourceWellFormed substitution)
    (index : Nat) :
    input.rawPair.term (index + 1) = substitution.term index :=
  rfl

/-- A realized base substitution and completed term canonically realize their
    comprehension pairing into the extended interpreted target context. -/
noncomputable def IncDepCompletedSemanticSubstitution.pairSemanticInto
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution) :
    IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      typing.projectionSourceWellFormed
      (input.targetResult.extend (typeWellFormed := typing.typeWellFormed)
        ((typing.interpretAlong model sourceWellFormed substitution input)
          |>.formationResult.targetFormationResult.semanticType))
      input.rawPair := by
  let result := typing.interpretAlong model sourceWellFormed substitution input
  let targetFormation := result.formationResult.targetFormationResult
  let targetResult := input.targetResult.extend
    (typeWellFormed := typing.typeWellFormed) targetFormation.semanticType
  let substitutionResult : IncDepRawSubstitutionSemanticResult input.rawPair
      input.sourceResult targetResult :=
    { semanticSubstitution := typing.semanticPairAlong model sourceWellFormed
        substitution input }
  exact
    { sourceResult := input.sourceResult
      substitutionResult := substitutionResult
      replacements :=
        { replacement := by
            intro position lookupType lookup
            cases lookup with
            | here =>
                exact ⟨result.formationResult.sourceFormationResult.semanticType,
                  { semanticTerm :=
                      result.typingResult.sourceTermResult.semanticTerm }⟩
            | there previous =>
                let previousResult := input.replacements.replacement previous
                exact ⟨previousResult.1,
                  { semanticTerm := previousResult.2.semanticTerm }⟩ } }

@[simp] theorem IncDepCompletedSemanticSubstitution.pairSemanticInto_map
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution) :
    (input.pairSemanticInto model).substitutionResult.semanticSubstitution =
      typing.semanticPairAlong model sourceWellFormed substitution input :=
  rfl

/-- The finite morphism recovered from the semantic pairing realization is
    exactly the syntactic CwF comprehension pairing already constructed from
    the same completed term and base substitution. -/
theorem IncDepCompletedSemanticSubstitution.pairSemanticInto_finite_exact
    (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution) :
    (input.pairSemanticInto model).finiteSubstitution = input.syntacticPair := by
  apply Quotient.sound
  intro index indexLt
  cases index with
  | zero => rfl
  | succ index =>
      have outEquivalent := Quotient.exact
        (Quotient.out_eq input.finiteSubstitution)
      have baseLt : index < target.length := by
        change index + 1 < (type :: target).length at indexLt
        simpa using indexLt
      exact (outEquivalent index baseLt).symm

structure IncDepSemanticPairingRealizationTheorem : Prop where
  realized : ∀ (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution),
    Nonempty (IncDepSemanticSubstitutionInto.{u} sourceWellFormed
      typing.projectionSourceWellFormed
      (input.targetResult.extend (typeWellFormed := typing.typeWellFormed)
        ((typing.interpretAlong model sourceWellFormed substitution input)
          |>.formationResult.targetFormationResult.semanticType))
      input.rawPair)
  finiteExact : ∀ (model : IncDepCompletionModel.{u, u, u})
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    {typing : IncDepCompletedTyping target term type}
    {sourceWellFormed : IncDepRawCoherentContext.WellFormed source}
    {substitution : IncDepRawSubstitution source target}
    (input : IncDepCompletedSemanticSubstitution.{u}
      typing sourceWellFormed substitution),
    (input.pairSemanticInto model).finiteSubstitution = input.syntacticPair

theorem incDepSemanticPairingRealizationTheorem :
    IncDepSemanticPairingRealizationTheorem.{u} where
  realized := by
    intro model source target term type typing sourceWellFormed substitution input
    exact ⟨input.pairSemanticInto model⟩
  finiteExact := IncDepCompletedSemanticSubstitution.pairSemanticInto_finite_exact

end IncidenceCore
