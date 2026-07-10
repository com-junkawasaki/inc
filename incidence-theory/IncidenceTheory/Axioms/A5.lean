/- Merkle-ID: foundation.axiomatization.A5
   A5: Well-founded Mode - Well-founded boundary recursion. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

/- A5: Well-founded recursion on boundaries -/
theorem well_founded_theorem {I R : Type u} [DecidableEq I]
  (boundary : I → Boundary I R) (rank : I → Nat)
  (decreases : ∀ i e, e ∈ boundary i → rank e.i < rank i) :
  -- A decreasing natural-number rank rules out direct boundary cycles.
  ∀ i, ¬(∃ e ∈ boundary i, e.i = i) := by
  intro i ⟨e, he, hei⟩
  have hlt := decreases i e he
  rw [hei] at hlt
  exact Nat.lt_irrefl _ hlt

end IncidenceCore
