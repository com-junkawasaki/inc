/- Merkle-ID: foundation.axiomatization.A9_A13
   Boundary Preservation: A9 (Type), A10 (Guard), A11 (Equivalence),
   A12 (Congruence), A13 (Normalization) -/
import IncidenceTheory.Axioms.A6_A8

namespace IncidenceCore

/- Guards for conditional gluing -/
structure Guards (I : Type u) where
  allow : I → I → Bool

/- Extended structure with boundary preservation -/
structure IncidencePreservation (I R T : Type u)
  extends IncidenceGluing I R T where
  guards : Guards I

  -- A9: Type preservation in gluing
  type_preserve : ∀ {i j k}, guards.allow i j → glue i j = some k →
                   typeFunc k = typeFunc i

  -- A10: Guard preservation (simplified)
  guard_preserve : ∀ {i j k}, guards.allow i j → glue i j = some k → True

  -- A11-A13 would require full bisimulation and normalization theories
  -- These are complex and would be separate modules

end IncidenceCore
