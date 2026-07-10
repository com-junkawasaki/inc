/- Merkle-ID: foundation.axiomatization.A5
   A5: Well-founded Mode - Well-founded boundary recursion. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

/- A5 is a genuine constraint (no self-loops in the boundary): an arbitrary
   `boundary : I → Boundary I R` need not satisfy it, so it cannot be a
   theorem about unconstrained boundaries. It is instead an axiom every
   well-formed incidence must supply (see `Incidence.well_founded` in
   Axioms.lean); this lemma packages that hypothesis for A5-only callers. -/
theorem well_founded_theorem {I R : Type u} [DecidableEq I]
  (boundary : I → Boundary I R)
  (hwf : ∀ i, ¬(∃ e ∈ boundary i, e.i = i)) :
  ∀ i, ¬(∃ e ∈ boundary i, e.i = i) := hwf

end IncidenceCore
