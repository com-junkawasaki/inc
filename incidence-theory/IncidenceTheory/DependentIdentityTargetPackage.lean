import IncidenceTheory.DependentPiSigmaTargetInvariance

namespace IncidenceCore

universe u

/-- The target data consumed by Identity formation: a semantic interpretation
    of the carrier type together with both endpoints in that exact fiber. -/
def IncDepRawIdentityFormationTargetPackage
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed)
    (typeFormation : IncDepRawWellFormed context type) :=
  Sigma fun typeResult : IncDepRawFormationSemanticResult typeFormation
      contextResult =>
    IncTerm typeResult.semanticType × IncTerm typeResult.semanticType

def IncDepRawIdentityFormationTargetPackage.identity
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    (package : IncDepRawIdentityFormationTargetPackage contextResult
      typeFormation) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.identity typeFormation leftTyping rightTyping)
      contextResult :=
  IncDepRawFormationSemanticResult.identity package.1 package.2.1 package.2.2

theorem IncDepRawIdentityFormationTargetPackage.identity_congr
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {first second : IncDepRawIdentityFormationTargetPackage contextResult
      typeFormation}
    (packageEq : first = second) :
    first.identity (leftTyping := leftTyping) (rightTyping := rightTyping) =
      second.identity (leftTyping := leftTyping) (rightTyping := rightTyping) :=
  congrArg (fun package => package.identity
    (leftTyping := leftTyping) (rightTyping := rightTyping)) packageEq

/-- Extract the exact target package supplied to strict Identity formation. -/
def IncDepRawStrictFormationSubstitutionDispatchResult.identityTargetPackage
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    (typeResult : IncDepRawStrictFormationSubstitutionDispatchResult typeReady
      substitutionResult)
    (leftResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := leftTyping) typeResult.formationResult)
    (rightResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := rightTyping) typeResult.formationResult) :
    IncDepRawIdentityFormationTargetPackage targetResult typeFormation :=
  ⟨typeResult.formationResult.targetFormationResult,
    ⟨leftResult.targetTermResult.semanticTerm,
      rightResult.targetTermResult.semanticTerm⟩⟩

@[simp] theorem IncDepRawSubstitutionFiberModel.dispatchStrictIdentityFormation_target_package
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    (leftReady : IncDepRawStrictTypingDispatchReady leftTyping typeReady)
    (rightReady : IncDepRawStrictTypingDispatchReady rightTyping typeReady)
    (typeResult : IncDepRawStrictFormationSubstitutionDispatchResult typeReady
      substitutionResult)
    (leftResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := leftTyping) typeResult.formationResult)
    (rightResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := rightTyping) typeResult.formationResult) :
    (model.dispatchStrictIdentityFormation leftReady rightReady typeResult
      leftResult rightResult |>.formationResult.targetFormationResult) =
      (typeResult.identityTargetPackage leftResult rightResult).identity :=
  rfl

/-- Exact remaining compatibility boundary for the Identity induction case.
    Formation and typing invariance before normalization do not imply this law
    for an arbitrary rebase provider: its transported endpoints may depend on
    source-side data. -/
def IncDepCanonicalIdentityTargetPackageInvariance
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}) :
    Prop :=
  ∀ {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation}
    {rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation},
    IncDepCanonicalFormationTargetInvariantAt model hypotheses typeReady →
    IncDepCanonicalTypingTargetInvariantAt model hypotheses leftReady →
    IncDepCanonicalTypingTargetInvariantAt model hypotheses rightReady →
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.identity typeReady leftReady
        rightReady)

theorem incDepCanonicalFormationTargetInvariantAt_identity
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u})
    (identityInvariance :
      IncDepCanonicalIdentityTargetPackageInvariance model hypotheses)
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
    {leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation}
    {rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation}
    (typeInvariant : IncDepCanonicalFormationTargetInvariantAt model hypotheses
      typeReady)
    (leftInvariant : IncDepCanonicalTypingTargetInvariantAt model hypotheses
      leftReady)
    (rightInvariant : IncDepCanonicalTypingTargetInvariantAt model hypotheses
      rightReady) :
    IncDepCanonicalFormationTargetInvariantAt model hypotheses
      (IncDepRawCoherentFormationDispatchReady.identity typeReady leftReady
        rightReady) :=
  identityInvariance typeInvariant leftInvariant rightInvariant

structure IncDepIdentityTargetPackageTheorem : Prop where
  packageCongruent : ∀
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {first second : IncDepRawIdentityFormationTargetPackage contextResult
      typeFormation},
    first = second →
      first.identity (leftTyping := leftTyping) (rightTyping := rightTyping) =
      second.identity (leftTyping := leftTyping) (rightTyping := rightTyping)
  boundaryExact : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (hypotheses : IncDepRawCanonicalSubstitutionPreservationHypotheses.{u, u}),
    IncDepCanonicalIdentityTargetPackageInvariance model hypotheses →
    ∀ {context : List IncDepRawType} {type : IncDepRawType}
      {left right : IncDepRawTerm}
      {typeFormation : IncDepRawWellFormed context type}
      {leftTyping : IncDepRawHasType context left type}
      {rightTyping : IncDepRawHasType context right type}
      {typeReady : IncDepRawCoherentFormationDispatchReady typeFormation}
      {leftReady : IncDepRawCoherentTypingDispatchReady leftTyping typeFormation}
      {rightReady : IncDepRawCoherentTypingDispatchReady rightTyping typeFormation},
      IncDepCanonicalFormationTargetInvariantAt model hypotheses typeReady →
      IncDepCanonicalTypingTargetInvariantAt model hypotheses leftReady →
      IncDepCanonicalTypingTargetInvariantAt model hypotheses rightReady →
      IncDepCanonicalFormationTargetInvariantAt model hypotheses
        (IncDepRawCoherentFormationDispatchReady.identity typeReady leftReady
          rightReady)

theorem incDepIdentityTargetPackageTheorem :
    IncDepIdentityTargetPackageTheorem.{u} where
  packageCongruent :=
    IncDepRawIdentityFormationTargetPackage.identity_congr
  boundaryExact := incDepCanonicalFormationTargetInvariantAt_identity

end IncidenceCore
