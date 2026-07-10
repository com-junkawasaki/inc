/- Merkle-ID: foundation.axiomatization.A6_A8
   Gluing Operations: A6 (Existence), A7 (Unit), A8 (Associativity) -/
import IncidenceTheory.Axioms.Basic
import IncidenceTheory.Axioms.A2

namespace IncidenceCore

/- Structure with gluing operation -/
structure IncidenceGluing (I R T : Type u) extends IncidenceType I T where
  glue : I → I → Option I  -- A6: Gluing always exists (option for guards)
  unit : I

  -- A7: Unit laws
  unit_left  : ∀ i, glue unit i = some i
  unit_right : ∀ i, glue i unit = some i

  -- A8: Associativity under guards
  associativity : ∀ i j k, Option.bind (glue i j) (fun ij => glue ij k) =
                           Option.bind (glue j k) (fun jk => glue i jk)

end IncidenceCore
