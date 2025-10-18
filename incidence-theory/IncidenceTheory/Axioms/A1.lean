/- Merkle-ID: foundation.axiomatization.A1
   A1: Finite Endpoints - For all i, ∂(i) is finite. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

/- A1 is automatically satisfied by using List (finite by construction) -/
theorem finite_endpoints_theorem {I R : Type u} (boundary : I → Boundary I R) :
  ∀ i, (boundary i).length < Nat.inf := by
  intro i
  -- Lists are finite by construction in Lean
  simp

end IncidenceCore
