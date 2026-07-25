import IncidenceTheory.DependentScopedIdentityTargetInvariance

namespace IncidenceCore

universe u

theorem incDepScopedCanonicalTyping_target_term_eq_recursive
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {substitution : IncDepRawSubstitution source target}
    {typing : IncDepRawHasType target term type}
    {formation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    HEq
      ((model.scopedCanonicalStrictPreservation inputs).typing.dispatch ready
        targetTree replacements |>.typingResult.targetTermResult.semanticTerm)
      ((model.recursivelyGeneratedTypingFoldOfScopedInputs inputs ready
        |>.output.typing targetTree replacements)
        |>.typing.result.dispatchResult.typingResult.targetTermResult.semanticTerm) := by
  rfl

/-- Target-term invariance stated directly for the recursively generated
    anchored output underlying the public scoped dispatcher. -/
def IncDepScopedRecursiveTypingTargetTermInvariantForAt
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType target term type}
    {formation : IncDepRawWellFormed target type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation) : Prop :=
  ∀ {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source target}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    let recursive := model.recursivelyGeneratedTypingFoldOfScopedInputs inputs
      ready
    HEq
      ((recursive.output.typing targetTree replacements)
        |>.typing.result.dispatchResult.typingResult.targetTermResult.semanticTerm)
      ((recursive.output.typing targetTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity targetTree))
        |>.typing.result.dispatchResult.typingResult.targetTermResult.semanticTerm)

/-- Public target-term invariance and recursive-normal-form invariance are
    exactly equivalent. -/
theorem incDepScopedCanonicalTypingTargetTermInvariantAt_iff_recursive
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType target term type}
    {formation : IncDepRawWellFormed target type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation) :
    IncDepTypingTargetTermInvariantForAt
        (model.scopedCanonicalStrictPreservation inputs) ready ↔
      IncDepScopedRecursiveTypingTargetTermInvariantForAt model inputs ready := by
  constructor
  · intro publicInvariant source sourceWellFormed targetWellFormed sourceResult
      targetResult substitution substitutionResult targetTree replacements
    let identityReplacements :=
      IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
    exact (incDepScopedCanonicalTyping_target_term_eq_recursive model inputs
      ready targetTree replacements).symm |>.trans
        ((publicInvariant targetTree replacements).trans
          (incDepScopedCanonicalTyping_target_term_eq_recursive model inputs
            ready targetTree identityReplacements))
  · intro recursiveInvariant source sourceWellFormed targetWellFormed
      sourceResult targetResult substitution substitutionResult targetTree
      replacements
    let identityReplacements :=
      IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
    exact (incDepScopedCanonicalTyping_target_term_eq_recursive model inputs
      ready targetTree replacements).trans
        ((recursiveInvariant targetTree replacements).trans
          (incDepScopedCanonicalTyping_target_term_eq_recursive model inputs
            ready targetTree identityReplacements).symm)

/-- Exact dependent data consumed by lambda abstraction: a domain target, a
    codomain target over its extension, and a body term in that codomain. -/
def IncDepRawLambdaTargetPackage
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed)
    (domainFormation : IncDepRawWellFormed context domain)
    (codomainFormation : IncDepRawWellFormed (domain :: context) codomain) :=
  Sigma fun domainResult : IncDepRawFormationSemanticResult domainFormation
      contextResult =>
    Sigma fun codomainResult : IncDepRawFormationSemanticResult
        codomainFormation
        (contextResult.extend (typeWellFormed := domainFormation)
          domainResult.semanticType) =>
      IncTerm codomainResult.semanticType

def IncDepRawLambdaTargetPackage.lambdaTerm
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    (package : IncDepRawLambdaTargetPackage contextResult domainFormation
      codomainFormation) :
    IncTerm (IncPiType package.1.semanticType package.2.1.semanticType) :=
  IncPiTerm.lambda package.2.2

theorem IncDepRawLambdaTargetPackage.lambdaTerm_heq
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {first second : IncDepRawLambdaTargetPackage contextResult domainFormation
      codomainFormation}
    (packageEq : first = second) :
    HEq first.lambdaTerm second.lambdaTerm := by
  cases packageEq
  rfl

noncomputable def incDepScopedLambdaExternalTargetPackage
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm} {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {bodyTyping : IncDepRawHasType (domain :: target) body codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (bodyReady : IncDepRawCoherentTypingDispatchReady bodyTyping
      codomainFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    IncDepRawLambdaTargetPackage targetResult domainFormation
      codomainFormation :=
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let domainResult := dispatcher.formation.dispatch domainReady targetTree
    replacements
  let extendedTree := IncDepRawContextSemanticTree.extend targetTree
    domainResult.formationResult.targetFormationResult
  let liftedReplacements := replacements.liftResult domainResult.formationResult
  let bodyFormationResult := dispatcher.formation.dispatch
    bodyReady.formationReady extendedTree liftedReplacements
  let bodyResult := dispatcher.typing.dispatch bodyReady extendedTree
    liftedReplacements
  let bodyFormationEq := incDepScopedCanonicalTyping_formation_eq model inputs
    bodyReady.formationReady bodyReady extendedTree liftedReplacements
  ⟨domainResult.formationResult.targetFormationResult,
    ⟨bodyFormationResult.formationResult.targetFormationResult,
      bodyResult.targetTermCast bodyFormationResult bodyFormationEq⟩⟩

theorem incDepScopedLambdaExternalTargetPackage_eq
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {bodyReady : IncDepRawCoherentTypingDispatchReady bodyTyping
      codomainFormation}
    (domainInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) domainReady)
    (bodyInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) bodyReady)
    {source : List IncDepRawType}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed context}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitution : IncDepRawSubstitution source context}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    incDepScopedLambdaExternalTargetPackage model inputs domainReady bodyReady
        targetTree replacements =
      incDepScopedLambdaExternalTargetPackage model inputs domainReady bodyReady
        targetTree
          (IncDepRawSubstitutionReplacementSemanticResult.identity
            targetTree) := by
  let dispatcher := model.scopedCanonicalStrictPreservation inputs
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  let firstDomain := dispatcher.formation.dispatch domainReady targetTree
    replacements
  let secondDomain := dispatcher.formation.dispatch domainReady targetTree
    identityReplacements
  have domainEq : firstDomain.formationResult.targetFormationResult =
      secondDomain.formationResult.targetFormationResult :=
    domainInvariant targetTree replacements
  let canonicalPackage := fun
      domainResult : IncDepRawFormationSemanticResult domainFormation
        targetResult =>
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree
      domainResult
    let identityExtended :=
      IncDepRawSubstitutionReplacementSemanticResult.identity extendedTree
    let bodyFormationResult := dispatcher.formation.dispatch
      bodyReady.formationReady extendedTree identityExtended
    let bodyResult := dispatcher.typing.dispatch bodyReady extendedTree
      identityExtended
    let bodyFormationEq := incDepScopedCanonicalTyping_formation_eq model inputs
      bodyReady.formationReady bodyReady extendedTree identityExtended
    (⟨domainResult, ⟨bodyFormationResult.formationResult.targetFormationResult,
      bodyResult.targetTermCast bodyFormationResult bodyFormationEq⟩⟩ :
      IncDepRawLambdaTargetPackage targetResult domainFormation
        codomainFormation)
  have firstPackageEq :
      incDepScopedLambdaExternalTargetPackage model inputs domainReady bodyReady
          targetTree replacements =
        canonicalPackage firstDomain.formationResult.targetFormationResult := by
    let firstExtendedTree := IncDepRawContextSemanticTree.extend targetTree
      firstDomain.formationResult.targetFormationResult
    let firstLifted := replacements.liftResult firstDomain.formationResult
    let firstFormation := dispatcher.formation.dispatch
      bodyReady.formationReady firstExtendedTree firstLifted
    let canonicalFormation := dispatcher.formation.dispatch
      bodyReady.formationReady firstExtendedTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity
          firstExtendedTree)
    let firstTyping := dispatcher.typing.dispatch bodyReady firstExtendedTree
      firstLifted
    let canonicalTyping := dispatcher.typing.dispatch bodyReady
      firstExtendedTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity
          firstExtendedTree)
    have formationEq : firstFormation.formationResult.targetFormationResult =
        canonicalFormation.formationResult.targetFormationResult := by
      exact (congrArg
          IncDepRawFormationSubstitutionFiberResult.targetFormationResult
          (incDepScopedCanonicalTyping_formation_eq model inputs
            bodyReady.formationReady bodyReady firstExtendedTree
              firstLifted).symm).trans
        (((bodyInvariant firstExtendedTree firstLifted).1).trans
          (congrArg
            IncDepRawFormationSubstitutionFiberResult.targetFormationResult
            (incDepScopedCanonicalTyping_formation_eq model inputs
              bodyReady.formationReady bodyReady firstExtendedTree
                (IncDepRawSubstitutionReplacementSemanticResult.identity
                  firstExtendedTree))))
    have termEq : HEq
        (firstTyping.targetTermCast firstFormation
          (incDepScopedCanonicalTyping_formation_eq model inputs
            bodyReady.formationReady bodyReady firstExtendedTree firstLifted))
        (canonicalTyping.targetTermCast canonicalFormation
          (incDepScopedCanonicalTyping_formation_eq model inputs
            bodyReady.formationReady bodyReady firstExtendedTree
              (IncDepRawSubstitutionReplacementSemanticResult.identity
                firstExtendedTree))) :=
      (firstTyping.targetTermCast_heq firstFormation _).trans
        ((bodyInvariant firstExtendedTree firstLifted).2.trans
          (canonicalTyping.targetTermCast_heq canonicalFormation _).symm)
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Sigma.ext formationEq termEq)
  have secondPackageEq :
      incDepScopedLambdaExternalTargetPackage model inputs domainReady bodyReady
          targetTree identityReplacements =
        canonicalPackage secondDomain.formationResult.targetFormationResult := by
    let secondExtendedTree := IncDepRawContextSemanticTree.extend targetTree
      secondDomain.formationResult.targetFormationResult
    let secondLifted := identityReplacements.liftResult
      secondDomain.formationResult
    let secondFormation := dispatcher.formation.dispatch
      bodyReady.formationReady secondExtendedTree secondLifted
    let canonicalFormation := dispatcher.formation.dispatch
      bodyReady.formationReady secondExtendedTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity
          secondExtendedTree)
    let secondTyping := dispatcher.typing.dispatch bodyReady secondExtendedTree
      secondLifted
    let canonicalTyping := dispatcher.typing.dispatch bodyReady
      secondExtendedTree
        (IncDepRawSubstitutionReplacementSemanticResult.identity
          secondExtendedTree)
    have formationEq : secondFormation.formationResult.targetFormationResult =
        canonicalFormation.formationResult.targetFormationResult := by
      exact (congrArg
          IncDepRawFormationSubstitutionFiberResult.targetFormationResult
          (incDepScopedCanonicalTyping_formation_eq model inputs
            bodyReady.formationReady bodyReady secondExtendedTree
              secondLifted).symm).trans
        (((bodyInvariant secondExtendedTree secondLifted).1).trans
          (congrArg
            IncDepRawFormationSubstitutionFiberResult.targetFormationResult
            (incDepScopedCanonicalTyping_formation_eq model inputs
              bodyReady.formationReady bodyReady secondExtendedTree
                (IncDepRawSubstitutionReplacementSemanticResult.identity
                  secondExtendedTree))))
    have termEq : HEq
        (secondTyping.targetTermCast secondFormation
          (incDepScopedCanonicalTyping_formation_eq model inputs
            bodyReady.formationReady bodyReady secondExtendedTree
              secondLifted))
        (canonicalTyping.targetTermCast canonicalFormation
          (incDepScopedCanonicalTyping_formation_eq model inputs
            bodyReady.formationReady bodyReady secondExtendedTree
              (IncDepRawSubstitutionReplacementSemanticResult.identity
                secondExtendedTree))) :=
      (secondTyping.targetTermCast_heq secondFormation _).trans
        ((bodyInvariant secondExtendedTree secondLifted).2.trans
          (canonicalTyping.targetTermCast_heq canonicalFormation _).symm)
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Sigma.ext formationEq termEq)
  exact firstPackageEq.trans ((congrArg canonicalPackage domainEq).trans
    secondPackageEq.symm)

/-- Exact transport coherence needed to expose a lambda target as the lambda of
    the independently dispatched body target.  The bare generated-agreement
    provider equates formation packages but does not currently identify these
    two transported term choices. -/
def IncDepScopedLambdaRecursiveTermCoherence
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model) : Prop :=
  ∀ {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm} {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {bodyTyping : IncDepRawHasType (domain :: target) body codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (bodyReady : IncDepRawCoherentTypingDispatchReady bodyTyping
      codomainFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    let dispatcher := model.scopedCanonicalStrictPreservation inputs
    let domainResult := dispatcher.formation.dispatch domainReady targetTree
      replacements
    let extendedTree := IncDepRawContextSemanticTree.extend targetTree
      domainResult.formationResult.targetFormationResult
    let liftedReplacements := replacements.liftResult domainResult.formationResult
    let bodyFormationResult := dispatcher.formation.dispatch
      bodyReady.formationReady extendedTree liftedReplacements
    let bodyResult := dispatcher.typing.dispatch bodyReady extendedTree
      liftedReplacements
    let bodyFormationEq := incDepScopedCanonicalTyping_formation_eq model inputs
      bodyReady.formationReady bodyReady extendedTree liftedReplacements
    let result := dispatcher.typing.dispatch
      (IncDepRawCoherentTypingDispatchReady.lambdaRule domainReady bodyReady)
      targetTree replacements
    HEq result.typingResult.targetTermResult.semanticTerm
      (IncPiTerm.lambda
        (bodyResult.targetTermCast bodyFormationResult bodyFormationEq))

theorem incDepScopedCanonicalTypingTargetTermInvariantAt_lambda
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (lambdaCoherence : IncDepScopedLambdaRecursiveTermCoherence model inputs)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {bodyReady : IncDepRawCoherentTypingDispatchReady bodyTyping
      codomainFormation}
    (domainInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) domainReady)
    (bodyInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) bodyReady) :
    IncDepTypingTargetTermInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.lambdaRule domainReady
        bodyReady) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  let identityReplacements :=
    IncDepRawSubstitutionReplacementSemanticResult.identity targetTree
  have packageEq := incDepScopedLambdaExternalTargetPackage_eq model inputs
    domainInvariant bodyInvariant targetTree replacements
  exact (lambdaCoherence domainReady bodyReady targetTree replacements).trans
    ((IncDepRawLambdaTargetPackage.lambdaTerm_heq packageEq).trans
      (lambdaCoherence domainReady bodyReady targetTree
        identityReplacements).symm)

theorem incDepScopedCanonicalTypingTargetInvariantAt_lambda
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (lambdaCoherence : IncDepScopedLambdaRecursiveTermCoherence model inputs)
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
    {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
    {bodyReady : IncDepRawCoherentTypingDispatchReady bodyTyping
      codomainFormation}
    (domainInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) domainReady)
    (bodyInvariant : IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) bodyReady) :
    IncDepTypingTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.lambdaRule domainReady
        bodyReady) := by
  have bodyFormationInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      bodyReady.formationReady :=
    incDepScopedCanonicalFormationTargetInvariantAt_of_typing model inputs
      bodyReady bodyInvariant
  have lambdaFormationInvariant : IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.pi domainReady
        bodyReady.formationReady) :=
    incDepScopedCanonicalFormationTargetInvariantAt_pi model inputs
      domainInvariant bodyFormationInvariant
  have lambdaTermInvariant : IncDepTypingTargetTermInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentTypingDispatchReady.lambdaRule domainReady
        bodyReady) :=
    incDepScopedCanonicalTypingTargetTermInvariantAt_lambda model inputs
      lambdaCoherence domainInvariant bodyInvariant
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  exact ⟨incDepScopedCanonicalTypingFormationTargetInvariantAt model inputs
      (IncDepRawCoherentTypingDispatchReady.lambdaRule domainReady bodyReady)
      lambdaFormationInvariant targetTree replacements,
    lambdaTermInvariant targetTree replacements⟩

structure IncDepScopedLambdaTargetInvarianceTheorem : Prop where
  lambdaClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepScopedLambdaRecursiveTermCoherence model inputs →
    ∀ {context : List IncDepRawType} {domain codomain : IncDepRawType}
      {body : IncDepRawTerm}
      {domainFormation : IncDepRawWellFormed context domain}
      {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
      {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
      {domainReady : IncDepRawCoherentFormationDispatchReady domainFormation}
      {bodyReady : IncDepRawCoherentTypingDispatchReady bodyTyping
        codomainFormation},
      IncDepFormationTargetInvariantForAt
          (model.scopedCanonicalStrictPreservation inputs) domainReady →
        IncDepTypingTargetInvariantForAt
          (model.scopedCanonicalStrictPreservation inputs) bodyReady →
        IncDepTypingTargetInvariantForAt
          (model.scopedCanonicalStrictPreservation inputs)
          (IncDepRawCoherentTypingDispatchReady.lambdaRule domainReady
            bodyReady)

theorem incDepScopedLambdaTargetInvarianceTheorem :
    IncDepScopedLambdaTargetInvarianceTheorem.{u} where
  lambdaClosed := incDepScopedCanonicalTypingTargetInvariantAt_lambda

structure IncDepScopedTypingRecursiveNormalizationTheorem : Prop where
  targetTermNormalizes : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {substitution : IncDepRawSubstitution source target}
    {typing : IncDepRawHasType target term type}
    {formation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult),
    HEq
      ((model.scopedCanonicalStrictPreservation inputs).typing.dispatch ready
        targetTree replacements |>.typingResult.targetTermResult.semanticTerm)
      ((model.recursivelyGeneratedTypingFoldOfScopedInputs inputs ready
        |>.output.typing targetTree replacements)
        |>.typing.result.dispatchResult.typingResult.targetTermResult.semanticTerm)

theorem incDepScopedTypingRecursiveNormalizationTheorem :
    IncDepScopedTypingRecursiveNormalizationTheorem.{u} where
  targetTermNormalizes :=
    incDepScopedCanonicalTyping_target_term_eq_recursive

end IncidenceCore
