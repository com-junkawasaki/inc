/- Merkle-ID: foundation.axiomatization.A4
   A4: Multiplicities - Each boundary entry has multiplicity ≥ 1. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

/- A4 enforcement through structure invariant -/
theorem multiplicities_theorem {I R : Type u} (boundary : I → Boundary I R) :
  ∀ i e, e ∈ boundary i → e.mult ≥ 1 := by
  intro i e he
  exact e.mult_pos

end IncidenceCore
