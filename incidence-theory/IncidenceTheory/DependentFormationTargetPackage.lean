import IncidenceTheory.DependentFormationConstructorTargetEquations

namespace IncidenceCore

universe u

/-- Dependent target data for a Pi/Sigma constructor: the codomain semantic
    formation is indexed by the context extended with the chosen domain
    semantic formation.  Bundling both components turns transport into equality
    of one ordinary Sigma value. -/
def IncDepRawDependentFormationTargetPackage
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed)
    (domainFormation : IncDepRawWellFormed context domain)
    (codomainFormation : IncDepRawWellFormed (domain :: context) codomain) :=
  Sigma fun domainResult : IncDepRawFormationSemanticResult domainFormation
      contextResult =>
    IncDepRawFormationSemanticResult codomainFormation
      (contextResult.extend (typeWellFormed := domainFormation)
        domainResult.semanticType)

def IncDepRawDependentFormationTargetPackage.pi
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    (package : IncDepRawDependentFormationTargetPackage contextResult
      domainFormation codomainFormation) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.pi domainFormation codomainFormation) contextResult :=
  IncDepRawFormationSemanticResult.pi package.1 package.2

def IncDepRawDependentFormationTargetPackage.sigma
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    (package : IncDepRawDependentFormationTargetPackage contextResult
      domainFormation codomainFormation) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.sigma domainFormation codomainFormation) contextResult :=
  IncDepRawFormationSemanticResult.sigma package.1 package.2

theorem IncDepRawDependentFormationTargetPackage.pi_congr
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {first second : IncDepRawDependentFormationTargetPackage contextResult
      domainFormation codomainFormation}
    (packageEq : first = second) :
    first.pi = second.pi :=
  congrArg IncDepRawDependentFormationTargetPackage.pi packageEq

theorem IncDepRawDependentFormationTargetPackage.sigma_congr
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {first second : IncDepRawDependentFormationTargetPackage contextResult
      domainFormation codomainFormation}
    (packageEq : first = second) :
    first.sigma = second.sigma :=
  congrArg IncDepRawDependentFormationTargetPackage.sigma packageEq

/-- Extract the dependent target package consumed by strict Pi/Sigma formation
    dispatch from its recursive dispatch results. -/
def IncDepRawStrictFormationSubstitutionDispatchResult.dependentTargetPackage
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
    IncDepRawDependentFormationTargetPackage targetResult domainFormation
      codomainFormation :=
  ⟨domainResult.formationResult.targetFormationResult,
    codomainResult.formationResult.targetFormationResult⟩

@[simp] theorem IncDepRawSubstitutionFiberModel.dispatchStrictPiFormation_target_package
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
      (domainResult.dependentTargetPackage codomainResult).pi :=
  rfl

@[simp] theorem IncDepRawSubstitutionFiberModel.dispatchStrictSigmaFormation_target_package
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
      (domainResult.dependentTargetPackage codomainResult).sigma :=
  rfl

structure IncDepFormationTargetPackageTheorem : Prop where
  piCongruent : ∀
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {first second : IncDepRawDependentFormationTargetPackage contextResult
      domainFormation codomainFormation},
    first = second → first.pi = second.pi
  sigmaCongruent : ∀
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {first second : IncDepRawDependentFormationTargetPackage contextResult
      domainFormation codomainFormation},
    first = second → first.sigma = second.sigma

theorem incDepFormationTargetPackageTheorem :
    IncDepFormationTargetPackageTheorem.{u} where
  piCongruent := IncDepRawDependentFormationTargetPackage.pi_congr
  sigmaCongruent := IncDepRawDependentFormationTargetPackage.sigma_congr

end IncidenceCore
