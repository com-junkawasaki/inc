import IncidenceTheory.DependentDispatcherTargetInvariance

namespace IncidenceCore

universe u

theorem incDepScopedCanonicalFormationTargetInvariantAt_base
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {index : Nat} :
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.base
        (context := context) (index := index)) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  rfl

theorem incDepScopedCanonicalFormationTargetInvariantAt_unit
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} :
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.unit (context := context)) := by
  intro source sourceWellFormed targetWellFormed sourceResult targetResult
    substitution substitutionResult targetTree replacements
  rfl

structure IncDepScopedTargetInvarianceBaseTheorem : Prop where
  baseClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType} {index : Nat},
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.base
        (context := context) (index := index))
  unitClosed : ∀
    (model : IncDepRawSubstitutionFiberModel.{u})
    (inputs : IncDepRawCanonicalScopedRecursiveFoldInputs.{u} model)
    {context : List IncDepRawType},
    IncDepFormationTargetInvariantForAt
      (model.scopedCanonicalStrictPreservation inputs)
      (IncDepRawCoherentFormationDispatchReady.unit (context := context))

theorem incDepScopedTargetInvarianceBaseTheorem :
    IncDepScopedTargetInvarianceBaseTheorem.{u} where
  baseClosed := incDepScopedCanonicalFormationTargetInvariantAt_base
  unitClosed := incDepScopedCanonicalFormationTargetInvariantAt_unit

end IncidenceCore
