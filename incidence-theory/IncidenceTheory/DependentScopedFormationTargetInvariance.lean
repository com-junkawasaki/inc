import IncidenceTheory.DependentScopedIdentityTargetInvariance

namespace IncidenceCore

universe u

theorem incDepScopedCanonicalFormationTargetInvariance_of_typing
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    (pathCoherence : IncDepScopedIdentityRecursivePathCoherence model inputs)
    (typingInvariance : IncDepScopedCanonicalTypingTargetInvariance model inputs) :
    IncDepScopedCanonicalFormationTargetInvariance model inputs := by
  rw [incDepScopedCanonicalFormationTargetInvariance_iff_local]
  intro target type targetFormation ready
  exact IncDepRawCoherentFormationDispatchReady.rec
    (motive_1 := fun _ ready => IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs) ready)
    (motive_2 := fun _ _ _ => True)
    (incDepScopedCanonicalFormationTargetInvariantAt_base model inputs)
    (incDepScopedCanonicalFormationTargetInvariantAt_unit model inputs)
    (fun _ _ domainIH codomainIH =>
      incDepScopedCanonicalFormationTargetInvariantAt_pi model inputs
        domainIH codomainIH)
    (fun _ _ domainIH codomainIH =>
      incDepScopedCanonicalFormationTargetInvariantAt_sigma model inputs
        domainIH codomainIH)
    (fun typeReady leftReady rightReady typeIH _ _ =>
      incDepScopedCanonicalFormationTargetInvariantAt_identity model inputs
        pathCoherence typeIH (typingInvariance leftReady)
        (typingInvariance rightReady))
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    ready

structure IncDepScopedFormationTargetInvarianceTheorem : Prop where
  closesFromTyping : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model),
    IncDepScopedIdentityRecursivePathCoherence model inputs →
    IncDepScopedCanonicalTypingTargetInvariance model inputs →
    IncDepScopedCanonicalFormationTargetInvariance model inputs

theorem incDepScopedFormationTargetInvarianceTheorem :
    IncDepScopedFormationTargetInvarianceTheorem.{u} where
  closesFromTyping :=
    incDepScopedCanonicalFormationTargetInvariance_of_typing

end IncidenceCore
