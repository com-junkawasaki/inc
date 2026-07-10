/- Merkle-ID: foundation.axiomatization.A2
   A2: Type Consistency - Boundary incidences share the same type as the parent. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

structure IncidenceType (I : Type u) (T : Type v) where
  boundary : I → Boundary I Unit  -- Simplified for A2 focus
  typeFunc : I → T
  type_consistent : ∀ (i : I), ∀ (e : Endpoint I Unit), e ∈ boundary i → typeFunc e.i = typeFunc i

/- A2 theorem: Type consistency in boundaries -/
theorem type_consistency_theorem {I : Type u} {T : Type v} (inc : IncidenceType I T) :
  ∀ i e, e ∈ inc.boundary i → inc.typeFunc e.i = inc.typeFunc i :=
  inc.type_consistent

end IncidenceCore
