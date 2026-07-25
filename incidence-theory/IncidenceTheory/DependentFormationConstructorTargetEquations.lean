import IncidenceTheory.DependentMutualTargetInvarianceMotive

namespace IncidenceCore

universe u

/-- Strict Pi formation dispatch exposes exactly the Pi target interpretation
    assembled from the recursive domain and codomain target results. -/
theorem IncDepRawSubstitutionFiberModel.dispatchStrictPiFormation_target
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      domainReady substitutionResult)
    (codomainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      codomainReady domainResult.formationResult.liftSubstitution) :
    (model.dispatchStrictPiFormation domainResult codomainResult
      |>.formationResult.targetFormationResult) =
      IncDepRawFormationSemanticResult.pi
        domainResult.formationResult.targetFormationResult
        codomainResult.formationResult.targetFormationResult :=
  rfl

/-- Strict Sigma formation dispatch exposes exactly the Sigma target
    interpretation assembled from its two recursive target results. -/
theorem IncDepRawSubstitutionFiberModel.dispatchStrictSigmaFormation_target
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      domainReady substitutionResult)
    (codomainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      codomainReady domainResult.formationResult.liftSubstitution) :
    (model.dispatchStrictSigmaFormation domainResult codomainResult
      |>.formationResult.targetFormationResult) =
      IncDepRawFormationSemanticResult.sigma
        domainResult.formationResult.targetFormationResult
        codomainResult.formationResult.targetFormationResult :=
  rfl

structure IncDepFormationConstructorTargetEquationsTheorem : Prop where
  piTarget : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      domainReady substitutionResult)
    (codomainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      codomainReady domainResult.formationResult.liftSubstitution),
    (model.dispatchStrictPiFormation domainResult codomainResult
      |>.formationResult.targetFormationResult) =
      IncDepRawFormationSemanticResult.pi
        domainResult.formationResult.targetFormationResult
        codomainResult.formationResult.targetFormationResult
  sigmaTarget : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      domainReady substitutionResult)
    (codomainResult : IncDepRawStrictFormationSubstitutionDispatchResult
      codomainReady domainResult.formationResult.liftSubstitution),
    (model.dispatchStrictSigmaFormation domainResult codomainResult
      |>.formationResult.targetFormationResult) =
      IncDepRawFormationSemanticResult.sigma
        domainResult.formationResult.targetFormationResult
        codomainResult.formationResult.targetFormationResult

theorem incDepFormationConstructorTargetEquationsTheorem :
    IncDepFormationConstructorTargetEquationsTheorem.{u} where
  piTarget := IncDepRawSubstitutionFiberModel.dispatchStrictPiFormation_target
  sigmaTarget :=
    IncDepRawSubstitutionFiberModel.dispatchStrictSigmaFormation_target

end IncidenceCore
