import IncidenceTheory.DependentScopedTargetInvarianceBase

namespace IncidenceCore

universe u

def IncDepFormationPiRecursiveTargetLaw
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}) : Prop :=
  ∀ {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    let domainResult := dispatcher.formation.dispatch domainReady targetTree
      replacements
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree
      domainResult.formationResult.targetFormationResult
    let codomainResult := dispatcher.formation.dispatch codomainReady extendedTree
      (replacements.liftResult domainResult.formationResult)
    (dispatcher.formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady)
      targetTree replacements |>.formationResult.targetFormationResult) =
      (domainResult.dependentTargetPackage codomainResult).pi

def IncDepFormationSigmaRecursiveTargetLaw
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u}) : Prop :=
  ∀ {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    let domainResult := dispatcher.formation.dispatch domainReady targetTree
      replacements
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree
      domainResult.formationResult.targetFormationResult
    let codomainResult := dispatcher.formation.dispatch codomainReady extendedTree
      (replacements.liftResult domainResult.formationResult)
    (dispatcher.formation.dispatch
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady)
      targetTree replacements |>.formationResult.targetFormationResult) =
      (domainResult.dependentTargetPackage codomainResult).sigma

theorem incDepScopedCanonicalFormation_pi_recursive_target
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) :
    IncDepFormationPiRecursiveTargetLaw
      (model.scopedCanonicalStrictPreservation inputs) := by
  intro source target domain codomain substitution domainFormation
    codomainFormation sourceWellFormed targetWellFormed sourceResult
    targetResult substitutionResult domainReady codomainReady targetTree
    replacements
  rfl

theorem incDepScopedCanonicalFormation_sigma_recursive_target
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) :
    IncDepFormationSigmaRecursiveTargetLaw
      (model.scopedCanonicalStrictPreservation inputs) := by
  intro source target domain codomain substitution domainFormation
    codomainFormation sourceWellFormed targetWellFormed sourceResult
    targetResult substitutionResult domainReady codomainReady targetTree
    replacements
  rfl

private theorem incDepFormationTargetInvariantForAt_pi_of_law
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u})
    (piLaw : IncDepFormationPiRecursiveTargetLaw dispatcher)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainInvariant : IncDepFormationTargetInvariantForAt dispatcher domainReady)
    (codomainInvariant : IncDepFormationTargetInvariantForAt dispatcher
      codomainReady) :
    IncDepFormationTargetInvariantForAt dispatcher
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  let firstDomain := dispatcher.formation.dispatch domainReady targetTree
    replacements
  let secondDomain := dispatcher.formation.dispatch domainReady targetTree
    identityReplacements
  have domainEq :
      firstDomain.formationResult.targetFormationResult =
        secondDomain.formationResult.targetFormationResult :=
    domainInvariant targetTree replacements
  let firstExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    firstDomain.formationResult.targetFormationResult
  let secondExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    secondDomain.formationResult.targetFormationResult
  let firstCodomain := dispatcher.formation.dispatch codomainReady
    firstExtendedTree (replacements.liftResult firstDomain.formationResult)
  let secondCodomain := dispatcher.formation.dispatch codomainReady
    secondExtendedTree
      (identityReplacements.liftResult secondDomain.formationResult)
  let canonicalPackage := fun
      domainResult : IncDepRawFormationSemanticResult domainFormation targetResult =>
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree domainResult
    let codomainResult := dispatcher.formation.dispatch codomainReady extendedTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity extendedTree)
    (⟨domainResult, codomainResult.formationResult.targetFormationResult⟩ :
      IncDepRawDependentFormationTargetPackage targetResult domainFormation
        codomainFormation)
  have firstCodomainEq :
      firstCodomain.formationResult.targetFormationResult =
        (canonicalPackage firstDomain.formationResult.targetFormationResult).2 :=
    codomainInvariant firstExtendedTree
      (replacements.liftResult firstDomain.formationResult)
  have secondCodomainEq :
      secondCodomain.formationResult.targetFormationResult =
        (canonicalPackage secondDomain.formationResult.targetFormationResult).2 :=
    codomainInvariant secondExtendedTree
      (identityReplacements.liftResult secondDomain.formationResult)
  have firstPackageEq : firstDomain.dependentTargetPackage firstCodomain =
      canonicalPackage firstDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq firstCodomainEq
  have secondPackageEq : secondDomain.dependentTargetPackage secondCodomain =
      canonicalPackage secondDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq secondCodomainEq
  rw [piLaw domainReady codomainReady targetTree replacements,
    piLaw domainReady codomainReady targetTree identityReplacements]
  exact IncDepRawDependentFormationTargetPackage.pi_congr
    (firstPackageEq.trans ((congrArg canonicalPackage domainEq).trans
      secondPackageEq.symm))

private theorem incDepFormationTargetInvariantForAt_sigma_of_law
    (dispatcher : IncDepRawStrictMutualSubstitutionDispatcher.{u})
    (sigmaLaw : IncDepFormationSigmaRecursiveTargetLaw dispatcher)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainInvariant : IncDepFormationTargetInvariantForAt dispatcher domainReady)
    (codomainInvariant : IncDepFormationTargetInvariantForAt dispatcher
      codomainReady) :
    IncDepFormationTargetInvariantForAt dispatcher
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  let firstDomain := dispatcher.formation.dispatch domainReady targetTree
    replacements
  let secondDomain := dispatcher.formation.dispatch domainReady targetTree
    identityReplacements
  have domainEq :
      firstDomain.formationResult.targetFormationResult =
        secondDomain.formationResult.targetFormationResult :=
    domainInvariant targetTree replacements
  let firstExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    firstDomain.formationResult.targetFormationResult
  let secondExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    secondDomain.formationResult.targetFormationResult
  let firstCodomain := dispatcher.formation.dispatch codomainReady
    firstExtendedTree (replacements.liftResult firstDomain.formationResult)
  let secondCodomain := dispatcher.formation.dispatch codomainReady
    secondExtendedTree
      (identityReplacements.liftResult secondDomain.formationResult)
  let canonicalPackage := fun
      domainResult : IncDepRawFormationSemanticResult domainFormation targetResult =>
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree domainResult
    let codomainResult := dispatcher.formation.dispatch codomainReady extendedTree
      (IncDepRawSubstitutionReplacementSemanticResult.identity extendedTree)
    (⟨domainResult, codomainResult.formationResult.targetFormationResult⟩ :
      IncDepRawDependentFormationTargetPackage targetResult domainFormation
        codomainFormation)
  have firstCodomainEq :
      firstCodomain.formationResult.targetFormationResult =
        (canonicalPackage firstDomain.formationResult.targetFormationResult).2 :=
    codomainInvariant firstExtendedTree
      (replacements.liftResult firstDomain.formationResult)
  have secondCodomainEq :
      secondCodomain.formationResult.targetFormationResult =
        (canonicalPackage secondDomain.formationResult.targetFormationResult).2 :=
    codomainInvariant secondExtendedTree
      (identityReplacements.liftResult secondDomain.formationResult)
  have firstPackageEq : firstDomain.dependentTargetPackage firstCodomain =
      canonicalPackage firstDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq firstCodomainEq
  have secondPackageEq : secondDomain.dependentTargetPackage secondCodomain =
      canonicalPackage secondDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq secondCodomainEq
  rw [sigmaLaw domainReady codomainReady targetTree replacements,
    sigmaLaw domainReady codomainReady targetTree identityReplacements]
  exact IncDepRawDependentFormationTargetPackage.sigma_congr
    (firstPackageEq.trans ((congrArg canonicalPackage domainEq).trans
      secondPackageEq.symm))

theorem incDepScopedCanonicalFormationTargetInvariantAt_pi
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) domainReady)
    (codomainInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) codomainReady) :
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady) :=
  incDepFormationTargetInvariantForAt_pi_of_law _
    (incDepScopedCanonicalFormation_pi_recursive_target model inputs)
    domainInvariant codomainInvariant

theorem incDepScopedCanonicalFormationTargetInvariantAt_sigma
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) domainReady)
    (codomainInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) codomainReady) :
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady) :=
  incDepFormationTargetInvariantForAt_sigma_of_law _
    (incDepScopedCanonicalFormation_sigma_recursive_target model inputs)
    domainInvariant codomainInvariant

structure IncDepScopedPiSigmaTargetInvarianceTheorem : Prop where
  piLaw : ∀ (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepFormationPiRecursiveTargetLaw
      (model.scopedCanonicalStrictPreservation inputs)
  sigmaLaw : ∀ (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepFormationSigmaRecursiveTargetLaw
      (model.scopedCanonicalStrictPreservation inputs)
  piClosed : ∀ (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation},
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) domainReady →
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) codomainReady →
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady)
  sigmaClosed : ∀ (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation},
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) domainReady →
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) codomainReady →
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady)

theorem incDepScopedPiSigmaTargetInvarianceTheorem :
    IncDepScopedPiSigmaTargetInvarianceTheorem.{u} where
  piLaw := incDepScopedCanonicalFormation_pi_recursive_target
  sigmaLaw := incDepScopedCanonicalFormation_sigma_recursive_target
  piClosed := incDepScopedCanonicalFormationTargetInvariantAt_pi
  sigmaClosed := incDepScopedCanonicalFormationTargetInvariantAt_sigma

end IncidenceCore
