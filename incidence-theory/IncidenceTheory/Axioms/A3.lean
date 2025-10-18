/- Merkle-ID: foundation.axiomatization.A3
   A3: Sign Rules - Orientations are restricted to -1, 0, or +1. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

/- A3 is enforced by the Sign inductive type definition -/
theorem sign_rules_theorem {I R : Type u} (boundary : I → Boundary I R) :
  ∀ i e, e ∈ boundary i → (e.sign = Sign.neg ∨ e.sign = Sign.zero ∨ e.sign = Sign.pos) := by
  intro i e he
  cases e.sign
  · left; rfl
  · right; left; rfl
  · right; right; rfl

end IncidenceCore
