import IncidenceTheory.DependentFormationTargetPackage

namespace IncidenceCore

universe u

/-- Pi formation preserves target invariance recursively.  The domain equality
    identifies the two dependent target telescopes; each codomain result is then
    compared with identity dispatch on that common extended target tree. -/
theorem incDepCanonicalFormationTargetInvariantAt_pi
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainInvariant : IncDepCanonicalFormationTargetInvariantAt model hypotheses
      domainReady)
    (codomainInvariant : IncDepCanonicalFormationTargetInvariantAt model hypotheses
      codomainReady) :
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  let firstDomain :=
    (model.preservationCanonical hypotheses).formation.dispatch domainReady
      targetTree replacements
  let secondDomain :=
    (model.preservationCanonical hypotheses).formation.dispatch domainReady
      targetTree identityReplacements
  have domainEq :
      firstDomain.formationResult.targetFormationResult =
        secondDomain.formationResult.targetFormationResult :=
    domainInvariant targetTree replacements
  let firstExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    firstDomain.formationResult.targetFormationResult
  let secondExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    secondDomain.formationResult.targetFormationResult
  let firstLifted := replacements.liftResult firstDomain.formationResult
  let secondLifted := identityReplacements.liftResult secondDomain.formationResult
  let firstCodomain :=
    (model.preservationCanonical hypotheses).formation.dispatch codomainReady
      firstExtendedTree firstLifted
  let secondCodomain :=
    (model.preservationCanonical hypotheses).formation.dispatch codomainReady
      secondExtendedTree secondLifted
  let canonicalPackage := fun
      domainResult : IncDepRawFormationSemanticResult domainFormation targetResult =>
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree domainResult
    let codomainResult :=
      (model.preservationCanonical hypotheses).formation.dispatch codomainReady
        extendedTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity extendedTree)
    (⟨domainResult, codomainResult.formationResult.targetFormationResult⟩ :
      IncDepRawDependentFormationTargetPackage targetResult domainFormation
        codomainFormation)
  have firstCodomainEq :
      firstCodomain.formationResult.targetFormationResult =
        ((model.preservationCanonical hypotheses).formation.dispatch codomainReady
          firstExtendedTree
          (IncDepRawSubstitutionReplacementSemanticResult.identity
            firstExtendedTree)
          |>.formationResult.targetFormationResult) :=
    codomainInvariant firstExtendedTree firstLifted
  have secondCodomainEq :
      secondCodomain.formationResult.targetFormationResult =
        ((model.preservationCanonical hypotheses).formation.dispatch codomainReady
          secondExtendedTree
          (IncDepRawSubstitutionReplacementSemanticResult.identity
            secondExtendedTree)
          |>.formationResult.targetFormationResult) :=
    codomainInvariant secondExtendedTree secondLifted
  have firstPackageEq :
      firstDomain.dependentTargetPackage firstCodomain =
        canonicalPackage firstDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq firstCodomainEq
  have secondPackageEq :
      secondDomain.dependentTargetPackage secondCodomain =
        canonicalPackage secondDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq secondCodomainEq
  exact IncDepRawDependentFormationTargetPackage.pi_congr
    (firstPackageEq.trans ((congrArg canonicalPackage domainEq).trans
      secondPackageEq.symm))

/-- Sigma formation has the same recursive target-invariance closure as Pi. -/
theorem incDepCanonicalFormationTargetInvariantAt_sigma
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation}
    (domainInvariant : IncDepCanonicalFormationTargetInvariantAt model hypotheses
      domainReady)
    (codomainInvariant : IncDepCanonicalFormationTargetInvariantAt model hypotheses
      codomainReady) :
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  let firstDomain :=
    (model.preservationCanonical hypotheses).formation.dispatch domainReady
      targetTree replacements
  let secondDomain :=
    (model.preservationCanonical hypotheses).formation.dispatch domainReady
      targetTree identityReplacements
  have domainEq :
      firstDomain.formationResult.targetFormationResult =
        secondDomain.formationResult.targetFormationResult :=
    domainInvariant targetTree replacements
  let firstExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    firstDomain.formationResult.targetFormationResult
  let secondExtendedTree := IncDepRawContextSemanticTree.extend targetTree
    secondDomain.formationResult.targetFormationResult
  let firstLifted := replacements.liftResult firstDomain.formationResult
  let secondLifted := identityReplacements.liftResult secondDomain.formationResult
  let firstCodomain :=
    (model.preservationCanonical hypotheses).formation.dispatch codomainReady
      firstExtendedTree firstLifted
  let secondCodomain :=
    (model.preservationCanonical hypotheses).formation.dispatch codomainReady
      secondExtendedTree secondLifted
  let canonicalPackage := fun
      domainResult : IncDepRawFormationSemanticResult domainFormation targetResult =>
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree domainResult
    let codomainResult :=
      (model.preservationCanonical hypotheses).formation.dispatch codomainReady
        extendedTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity extendedTree)
    (⟨domainResult, codomainResult.formationResult.targetFormationResult⟩ :
      IncDepRawDependentFormationTargetPackage targetResult domainFormation
        codomainFormation)
  have firstCodomainEq :
      firstCodomain.formationResult.targetFormationResult =
        ((model.preservationCanonical hypotheses).formation.dispatch codomainReady
          firstExtendedTree
          (IncDepRawSubstitutionReplacementSemanticResult.identity
            firstExtendedTree)
          |>.formationResult.targetFormationResult) :=
    codomainInvariant firstExtendedTree firstLifted
  have secondCodomainEq :
      secondCodomain.formationResult.targetFormationResult =
        ((model.preservationCanonical hypotheses).formation.dispatch codomainReady
          secondExtendedTree
          (IncDepRawSubstitutionReplacementSemanticResult.identity
            secondExtendedTree)
          |>.formationResult.targetFormationResult) :=
    codomainInvariant secondExtendedTree secondLifted
  have firstPackageEq :
      firstDomain.dependentTargetPackage firstCodomain =
        canonicalPackage firstDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq firstCodomainEq
  have secondPackageEq :
      secondDomain.dependentTargetPackage secondCodomain =
        canonicalPackage secondDomain.formationResult.targetFormationResult := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq secondCodomainEq
  exact IncDepRawDependentFormationTargetPackage.sigma_congr
    (firstPackageEq.trans ((congrArg canonicalPackage domainEq).trans
      secondPackageEq.symm))

structure IncDepPiSigmaTargetInvarianceTheorem : Prop where
  piClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation},
    IncDepCanonicalFormationTargetInvariantAt model hypotheses domainReady →
    IncDepCanonicalFormationTargetInvariantAt model hypotheses codomainReady →
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady)
  sigmaClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation},
    IncDepCanonicalFormationTargetInvariantAt model hypotheses domainReady →
    IncDepCanonicalFormationTargetInvariantAt model hypotheses codomainReady →
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady)

theorem incDepPiSigmaTargetInvarianceTheorem :
    IncDepPiSigmaTargetInvarianceTheorem.{u} where
  piClosed := incDepCanonicalFormationTargetInvariantAt_pi
  sigmaClosed := incDepCanonicalFormationTargetInvariantAt_sigma

end IncidenceCore
