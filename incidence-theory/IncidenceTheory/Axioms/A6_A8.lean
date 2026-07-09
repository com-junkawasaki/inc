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

  -- A8: Associativity under guards (guarded, partial: glue(glue i j, k) = glue(i, glue j k)
  -- whenever both sides are defined, via Option.bind chaining)
  associativity : ∀ i j k,
    (glue i j).bind (fun ij => glue ij k) = (glue j k).bind (fun jk => glue i jk)

end IncidenceCore
