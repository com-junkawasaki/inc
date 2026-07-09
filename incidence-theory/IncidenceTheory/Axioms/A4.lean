/- Merkle-ID: foundation.axiomatization.A4
   A4: Multiplicities - Each boundary entry has multiplicity ≥ 1. -/
import IncidenceTheory.Axioms.Basic

namespace IncidenceCore

/- A4 is a genuine constraint on well-formed incidences: an arbitrary
   `boundary : I → Boundary I R` need not satisfy it (Nat includes 0), so
   it cannot be a theorem about unconstrained boundaries. It is instead an
   axiom every well-formed incidence must supply (see `Incidence.multiplicities`
   in Axioms.lean); this lemma packages that hypothesis for A4-only callers. -/
theorem multiplicities_theorem {I R : Type u} (boundary : I → Boundary I R)
  (hmult : ∀ i e, e ∈ boundary i → e.mult ≥ 1) :
  ∀ i e, e ∈ boundary i → e.mult ≥ 1 := hmult

end IncidenceCore
