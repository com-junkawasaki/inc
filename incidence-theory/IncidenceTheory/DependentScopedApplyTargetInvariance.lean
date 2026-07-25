import IncidenceTheory.DependentScopedReflTargetInvariance

namespace IncidenceCore

universe u

/-- Reindexing a typing fiber along formation equality changes only its index,
    not its semantic target term. -/
theorem IncDepRawTypingSubstitutionFiberResult.castFormation_targetTerm_heq
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {targetFormation : IncDepRawWellFormed target type}
    {left right : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) left)
    (alignment : left = right) :
    HEq (result.castFormation alignment).targetTermResult.semanticTerm
      result.targetTermResult.semanticTerm := by
  cases alignment
  rfl

/-- Complete dependent target data for application.  Besides the domain,
    codomain, function, argument, and independently interpreted result, the
    package records the instantiation equality needed to transport application
    into the result fiber. -/
def IncDepRawApplyTargetPackage
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed)
    (domainFormation : IncDepRawWellFormed context domain)
    (codomainFormation : IncDepRawWellFormed (domain :: context) codomain)
    (resultFormation : IncDepRawWellFormed context
      (codomain.instantiate argument)) :=
  Sigma fun domainResult : IncDepRawFormationSemanticResult domainFormation
      contextResult =>
    Sigma fun codomainResult : IncDepRawFormationSemanticResult
        codomainFormation
        (contextResult.extend (typeWellFormed := domainFormation)
          domainResult.semanticType) =>
      Sigma fun _functionTerm : IncTerm
          (IncPiType domainResult.semanticType codomainResult.semanticType) =>
        Sigma fun argumentTerm : IncTerm domainResult.semanticType =>
          Sigma fun result : IncDepRawFormationSemanticResult resultFormation
              contextResult =>
            PLift (IncTypeInContext.instantiateFiber
                codomainResult.semanticType argumentTerm =
              result.semanticType)

noncomputable def IncDepRawApplyTargetPackage.applyTerm
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {resultFormation : IncDepRawWellFormed context
      (codomain.instantiate argument)}
    (package : IncDepRawApplyTargetPackage contextResult domainFormation
      codomainFormation resultFormation) :
    IncTerm package.2.2.2.2.1.semanticType :=
  cast (congrArg IncTerm package.2.2.2.2.2.down)
    (IncPiTerm.apply package.2.2.1 package.2.2.2.1)

theorem IncDepRawApplyTargetPackage.applyTerm_heq
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {resultFormation : IncDepRawWellFormed context
      (codomain.instantiate argument)}
    {first second : IncDepRawApplyTargetPackage contextResult domainFormation
      codomainFormation resultFormation}
    (packageEq : first = second) :
    HEq first.applyTerm second.applyTerm := by
  cases packageEq
  rfl

/-- Exact semantic naturality still needed to assemble the external Apply
    package: interpreting the syntactic instantiated result agrees with
    instantiating the interpreted codomain at the aligned argument target. -/
def IncDepScopedApplyInstantiationTargetCoherence
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) : Prop :=
  ∀ {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {resultFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {argumentTyping : IncDepRawHasType target argument domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (resultReady : IncDepRawCoherentFormationDispatchReady resultFormation)
    (argumentReady : IncDepRawCoherentTypingDispatchReady argumentTyping
      domainFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    let dispatcher := model.scopedCanonicalStrictPreservation inputs
    let domainResult := dispatcher.formation.dispatch domainReady targetTree
      replacements
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree
      domainResult.formationResult.targetFormationResult
    let codomainResult := dispatcher.formation.dispatch codomainReady
      extendedTree (replacements.liftResult domainResult.formationResult)
    let argumentResult := dispatcher.typing.dispatch argumentReady targetTree
      replacements
    let argumentEq := incDepScopedCanonicalTyping_formation_eq model inputs
      domainReady argumentReady targetTree replacements
    let alignedArgument := argumentResult.targetTermCast domainResult argumentEq
    let result := dispatcher.formation.dispatch resultReady targetTree
      replacements
    IncTypeInContext.instantiateFiber
        codomainResult.formationResult.targetFormationResult.semanticType
        alignedArgument =
      result.formationResult.targetFormationResult.semanticType

/-- The scoped recursive instantiate-agreement provider already proves the
    instantiation equation at the exact recursively generated/aligned inputs
    consumed by the Apply handler. -/
theorem incDepScopedApplyRecursiveInstantiationTargetCoherence
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {resultFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {argumentTyping : IncDepRawHasType target argument domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (resultReady : IncDepRawCoherentFormationDispatchReady resultFormation)
    (argumentReady : IncDepRawCoherentTypingDispatchReady argumentTyping
      domainFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    let domain := model.recursivelyGeneratedFormationFoldOfScopedInputs inputs
      domainReady
    let codomain := model.recursivelyGeneratedFormationFoldOfScopedInputs inputs
      codomainReady
    let result := model.recursivelyGeneratedFormationFoldOfScopedInputs inputs
      resultReady
    let argument := model.recursivelyGeneratedTypingFoldOfScopedInputs inputs
      argumentReady
    let argumentAgreement := inputs.agreementProvider.align domain.output
      argument.formation.output domain.recursivelyGenerated
      argument.formation.recursivelyGenerated
    let alignedArgument := argument.output.retargetFormation domain.output
      argumentAgreement
    let domainEval := domain.output.fold targetTree replacements
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree
      domainEval.result.dispatchResult.formationResult.targetFormationResult
    let liftedReplacements := replacements.liftResult
      domainEval.result.dispatchResult.formationResult
    let codomainEval := codomain.output.fold extendedTree liftedReplacements
    let argumentResult :=
      (alignedArgument.agreement.agree targetTree replacements)
        |>.typingResultAligned
    let resultEval := result.output.fold targetTree replacements
    IncTypeInContext.instantiateFiber
        codomainEval.result.dispatchResult.formationResult.targetFormationResult.semanticType
        argumentResult.targetTermResult.semanticTerm =
      resultEval.result.dispatchResult.formationResult.targetFormationResult.semanticType := by
  let domain := model.recursivelyGeneratedFormationFoldOfScopedInputs inputs
    domainReady
  let codomain := model.recursivelyGeneratedFormationFoldOfScopedInputs inputs
    codomainReady
  let result := model.recursivelyGeneratedFormationFoldOfScopedInputs inputs
    resultReady
  let argument := model.recursivelyGeneratedTypingFoldOfScopedInputs inputs
    argumentReady
  let argumentAgreement := inputs.agreementProvider.align domain.output
    argument.formation.output domain.recursivelyGenerated
    argument.formation.recursivelyGenerated
  let alignedArgument := argument.output.retargetFormation domain.output
    argumentAgreement
  let instantiateAgreement := inputs.instantiateAgreementProvider.dispatch
    domain codomain result argument alignedArgument.agreement
  let instantiateFold : IncDepRawCanonicalFormationSubstitutionFoldMotive
      resultReady :=
    IncDepRawCanonicalInstantiateSubstitutionFoldMotive domainReady
      codomainReady resultReady argumentReady domain.output.fold
        codomain.output.fold argument.output.typing alignedArgument.agreement
  let resultEval := result.output.fold targetTree replacements
  let instantiateEval := instantiateFold targetTree replacements
  have canonicalEq : resultEval.canonical = instantiateEval.canonical :=
    instantiateAgreement.agree targetTree replacements
  change instantiateEval.canonical.targetFormationResult.semanticType =
    resultEval.result.dispatchResult.formationResult.targetFormationResult.semanticType
  calc
    _ = resultEval.canonical.targetFormationResult.semanticType :=
      congrArg (fun formationResult =>
        formationResult.targetFormationResult.semanticType) canonicalEq.symm
    _ = resultEval.result.dispatchResult.formationResult.targetFormationResult.semanticType :=
      congrArg (fun formationResult =>
        formationResult.targetFormationResult.semanticType)
        resultEval.result.provenance.eq_canonical.symm

/-- The public scoped dispatcher exposes exactly the recursive instantiation
    equation proved by the generated instantiate-agreement provider. -/
theorem incDepScopedApplyInstantiationTargetCoherence
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) :
    IncDepScopedApplyInstantiationTargetCoherence model inputs := by
  intro source target domain codomain argument substitution domainFormation
    codomainFormation resultFormation argumentTyping sourceWellFormed
    targetWellFormed sourceResult targetResult substitutionResult domainReady
    codomainReady resultReady argumentReady targetTree replacements
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let domainPackage :=
    model.recursivelyGeneratedFormationFoldOfScopedInputs inputs domainReady
  let codomainPackage :=
    model.recursivelyGeneratedFormationFoldOfScopedInputs inputs codomainReady
  let resultPackage :=
    model.recursivelyGeneratedFormationFoldOfScopedInputs inputs resultReady
  let argumentPackage :=
    model.recursivelyGeneratedTypingFoldOfScopedInputs inputs argumentReady
  let argumentAgreement := inputs.agreementProvider.align domainPackage.output
    argumentPackage.formation.output domainPackage.recursivelyGenerated
    argumentPackage.formation.recursivelyGenerated
  let recursivelyAligned := argumentPackage.output.retargetFormation
    domainPackage.output argumentAgreement
  let domainResult := dispatcher.formation.dispatch domainReady targetTree
    replacements
  let argumentResult := dispatcher.typing.dispatch argumentReady targetTree
    replacements
  let argumentEq := incDepScopedCanonicalTyping_formation_eq model inputs
    domainReady argumentReady targetTree replacements
  let publiclyAligned := argumentResult.targetTermCast domainResult argumentEq
  let recursiveArgumentResult :=
    (recursivelyAligned.agreement.agree targetTree replacements)
      |>.typingResultAligned
  have publicRawEq : HEq
      argumentResult.typingResult.targetTermResult.semanticTerm
      ((argumentPackage.output.typing targetTree replacements)
        |>.typing.result.dispatchResult.typingResult.targetTermResult.semanticTerm) :=
    incDepScopedCanonicalTyping_target_term_eq_recursive model inputs
      argumentReady targetTree replacements
  have recursiveCastEq : HEq recursiveArgumentResult.targetTermResult.semanticTerm
      ((argumentPackage.output.typing targetTree replacements)
        |>.typing.result.dispatchResult.typingResult.targetTermResult.semanticTerm) := by
    exact IncDepRawTypingSubstitutionFiberResult.castFormation_targetTerm_heq
      _ _
  have alignedEq : publiclyAligned =
      recursiveArgumentResult.targetTermResult.semanticTerm :=
    eq_of_heq ((argumentResult.targetTermCast_heq domainResult argumentEq).trans
      (publicRawEq.trans recursiveCastEq.symm))
  have recursiveEq :=
    incDepScopedApplyRecursiveInstantiationTargetCoherence model inputs
      domainReady codomainReady resultReady argumentReady targetTree replacements
  change IncTypeInContext.instantiateFiber
      ((codomainPackage.output.fold
          (IncDepRawContextSemanticTree.extend targetTree
            (domainPackage.output.fold targetTree replacements).result.dispatchResult.formationResult.targetFormationResult)
          (replacements.liftResult
            (domainPackage.output.fold targetTree replacements).result.dispatchResult.formationResult))
        |>.result.dispatchResult.formationResult.targetFormationResult.semanticType)
      publiclyAligned =
    ((resultPackage.output.fold targetTree replacements)
      |>.result.dispatchResult.formationResult.targetFormationResult.semanticType)
  rw [alignedEq]
  exact recursiveEq

/-- The independently dispatched ingredients of Apply, assembled in the exact
    dependent package consumed by semantic application. -/
noncomputable def incDepScopedApplyExternalTargetPackage
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {resultFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (resultReady : IncDepRawCoherentFormationDispatchReady resultFormation)
    (functionReady : IncDepRawCoherentTypingDispatchReady functionTyping
      (.pi domainFormation codomainFormation))
    (argumentReady : IncDepRawCoherentTypingDispatchReady argumentTyping
      domainFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    IncDepRawApplyTargetPackage targetResult domainFormation codomainFormation
      resultFormation :=
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let domainResult := dispatcher.formation.dispatch domainReady targetTree
    replacements
  let extendedTree := IncDepRawContextSemanticTree.extend targetTree
    domainResult.formationResult.targetFormationResult
  let liftedReplacements := replacements.liftResult domainResult.formationResult
  let codomainResult := dispatcher.formation.dispatch codomainReady extendedTree
    liftedReplacements
  let piReady := IncDepRawCoherentFormationDispatchReady.pi domainReady
    codomainReady
  let functionResult := dispatcher.typing.dispatch functionReady targetTree
    replacements
  let functionFormationEq := incDepScopedCanonicalTyping_formation_eq model
    inputs piReady functionReady targetTree replacements
  let piTargetEq := incDepScopedCanonicalFormation_pi_recursive_target model
    inputs domainReady codomainReady targetTree replacements
  let functionTerm := functionResult.targetTermCastTo
    (domainResult.dependentTargetPackage codomainResult).pi
    ((congrArg
      IncDepRawFormationSubstitutionFiberResult.targetFormationResult
      functionFormationEq).trans piTargetEq)
  let argumentResult := dispatcher.typing.dispatch argumentReady targetTree
    replacements
  let argumentEq := incDepScopedCanonicalTyping_formation_eq model inputs
    domainReady argumentReady targetTree replacements
  let alignedArgument := argumentResult.targetTermCast domainResult argumentEq
  let result := dispatcher.formation.dispatch resultReady targetTree replacements
  let instantiationEq := incDepScopedApplyInstantiationTargetCoherence model
    inputs domainReady codomainReady resultReady argumentReady targetTree
      replacements
  ⟨domainResult.formationResult.targetFormationResult,
    ⟨codomainResult.formationResult.targetFormationResult,
      ⟨functionTerm, ⟨alignedArgument,
        ⟨result.formationResult.targetFormationResult,
          ⟨instantiationEq⟩⟩⟩⟩⟩⟩

structure IncDepScopedApplyTargetPackageTheorem : Prop where
  formationCastPreservesTerm : ∀
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {targetFormation : IncDepRawWellFormed target type}
    {left right : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) left)
    (alignment : left = right),
    HEq (result.castFormation alignment).targetTermResult.semanticTerm
      result.targetTermResult.semanticTerm
  packageCongruent : ∀
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {resultFormation : IncDepRawWellFormed context
      (codomain.instantiate argument)}
    {first second : IncDepRawApplyTargetPackage contextResult domainFormation
      codomainFormation resultFormation},
    first = second → HEq first.applyTerm second.applyTerm
  publicInstantiationCoherent : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepScopedApplyInstantiationTargetCoherence model inputs

theorem incDepScopedApplyTargetPackageTheorem :
    IncDepScopedApplyTargetPackageTheorem.{u} where
  formationCastPreservesTerm :=
    IncDepRawTypingSubstitutionFiberResult.castFormation_targetTerm_heq
  packageCongruent := IncDepRawApplyTargetPackage.applyTerm_heq
  publicInstantiationCoherent :=
    incDepScopedApplyInstantiationTargetCoherence

end IncidenceCore
