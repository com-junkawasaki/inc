import IncidenceTheory.DependentIdentityTargetPackage

namespace IncidenceCore

universe u

/-- A realizable replacement for the impossible global rebase provider: rebase
    is requested only between results carrying provenance from one shared
    canonical formation fiber. -/
structure IncDepRawCanonicalFormationRebaseProvider where
  provide : ∀
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (canonical first second : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult),
    IncDepRawCanonicalFormationFiberResult canonical first →
    IncDepRawCanonicalFormationFiberResult canonical second →
    IncDepRawFormationSubstitutionFiberRebase first second

/-- Canonical provenance makes the scoped provider unconditional: uniqueness
    identifies both generated results with their common canonical witness. -/
def incDepRawCanonicalFormationRebaseProvider :
    IncDepRawCanonicalFormationRebaseProvider.{u} where
  provide := fun _ _ _ firstCanonical secondCanonical =>
    firstCanonical.rebase secondCanonical

def IncDepRawCanonicalFormationRebaseProvider.rebase
    (provider : IncDepRawCanonicalFormationRebaseProvider.{u})
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (canonical first second : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult)
    (firstCanonical : IncDepRawCanonicalFormationFiberResult canonical first)
    (secondCanonical : IncDepRawCanonicalFormationFiberResult canonical second) :
    IncDepRawFormationSubstitutionFiberRebase first second :=
  provider.provide canonical first second firstCanonical secondCanonical

/-- Normalize a typing result to a formation result only when both are known to
    arise from the same canonical fiber.  Unlike `normalizeFormation`, this API
    needs no globally impossible arbitrary-rebase hypothesis. -/
noncomputable def IncDepRawStrictTypingSubstitutionDispatchResult.normalizeCanonicalFormation
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {targetFormationReady :
      IncDepRawCoherentFormationDispatchReady targetFormation}
    {targetReady : IncDepRawStrictTypingDispatchReady targetTyping
      targetFormationReady}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult)
    (canonical targetFormationResult :
      IncDepRawFormationSubstitutionFiberResult
        (targetFormation := targetFormation) substitutionResult)
    (resultCanonical : IncDepRawCanonicalFormationFiberResult canonical
      result.formationResult)
    (targetCanonical : IncDepRawCanonicalFormationFiberResult canonical
      targetFormationResult) :
    IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult :=
  result.rebaseFormation targetFormationResult
    (resultCanonical.rebase targetCanonical)

@[simp] theorem IncDepRawStrictTypingSubstitutionDispatchResult.normalizeCanonicalFormation_formation
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {targetFormationReady :
      IncDepRawCoherentFormationDispatchReady targetFormation}
    {targetReady : IncDepRawStrictTypingDispatchReady targetTyping
      targetFormationReady}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult)
    (canonical targetFormationResult :
      IncDepRawFormationSubstitutionFiberResult
        (targetFormation := targetFormation) substitutionResult)
    (resultCanonical : IncDepRawCanonicalFormationFiberResult canonical
      result.formationResult)
    (targetCanonical : IncDepRawCanonicalFormationFiberResult canonical
      targetFormationResult) :
    (result.normalizeCanonicalFormation canonical targetFormationResult
      resultCanonical targetCanonical).formationResult = targetFormationResult :=
  rfl

/-- The canonical provider is inhabited in every universe, in direct contrast
    with the proved nonexistence of the unrestricted provider at universe 0. -/
theorem incDepRawCanonicalFormationRebaseProvider_nonempty :
    Nonempty IncDepRawCanonicalFormationRebaseProvider.{u} :=
  ⟨incDepRawCanonicalFormationRebaseProvider⟩

structure IncDepCanonicalRebaseTheorem : Prop where
  scopedProviderExists : Nonempty IncDepRawCanonicalFormationRebaseProvider.{u}
  unrestrictedProviderImpossible :
    ¬ Nonempty IncDepRawFormationSubstitutionFiberRebaseProvider.{0}

theorem incDepCanonicalRebaseTheorem : IncDepCanonicalRebaseTheorem.{u} where
  scopedProviderExists := incDepRawCanonicalFormationRebaseProvider_nonempty
  unrestrictedProviderImpossible :=
    incDepRaw_no_global_formation_fiber_rebase_provider

end IncidenceCore
