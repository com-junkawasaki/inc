/- Merkle-ID: foundation.axiomatization
   Complete Incidence Theory axioms, organized by module -/
import IncidenceTheory.Axioms.Basic
import IncidenceTheory.Axioms.A1
import IncidenceTheory.Axioms.A2
import IncidenceTheory.Axioms.A3
import IncidenceTheory.Axioms.A4
import IncidenceTheory.Axioms.A5
import IncidenceTheory.Axioms.A6_A8
import IncidenceTheory.Axioms.A9_A13
import IncidenceTheory.Axioms.A14_A17

/- Complete Incidence structure combining all axioms -/
namespace IncidenceCore

/- Full Incidence structure (A1-A17) -/
structure Incidence (I R T : Type u) [DecidableEq I] where
  -- Core structure from A1-A5
  boundary        : I → Boundary I R
  typeFunc        : I → T

  -- Gluing from A6-A8
  glue            : I → I → Option I
  unit            : I

  -- Guards from A9-A13
  guards          : Guards I

  -- Linear algebra from A16-A17
  boundaryMatrix  : Matrix I I Int
  laplacian       : Matrix I I Int

  -- Invariants from all axioms
  type_consistent : ∀ (i : I), ∀ (e : Endpoint I R), e ∈ boundary i → typeFunc e.i = typeFunc i
  sign_rules      : ∀ (i : I), ∀ (e : Endpoint I R), e ∈ boundary i → (e.sign = Sign.neg ∨ e.sign = Sign.zero ∨ e.sign = Sign.pos)
  multiplicities  : ∀ (i : I), ∀ (e : Endpoint I R), e ∈ boundary i → e.mult ≥ 1
  well_founded    : ∀ i, ¬(∃ e ∈ boundary i, e.i = i)
  unit_left       : ∀ i, glue unit i = some i
  unit_right      : ∀ i, glue i unit = some i
  type_preserve   : ∀ {i j k}, guards.allow i j → glue i j = some k → typeFunc k = typeFunc i

end IncidenceCore
