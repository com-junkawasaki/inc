/- Merkle-ID: foundation.axiomatization.A1
   A1: Finite Endpoints - For all i, ∂(i) is finite. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

/- A1 is automatically satisfied by using List (finite by construction) -/
theorem finite_endpoints_theorem {I R : Type u} (boundary : I → Boundary I R) :
  ∀ i, ∃ n : Nat, (boundary i).length = n := by
  intro i
  exact ⟨(boundary i).length, rfl⟩

end IncidenceCore
