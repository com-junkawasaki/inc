/-!
  A minimal concrete model instantiating the canonical Incidence API.
  This trivial model uses empty boundaries so that type and sign laws hold vacuously.
  It serves as a baseline to keep the library green while richer models are developed.
-/

namespace IncidenceCore

universe u

variable {I T : Type u} [Inhabited I] [Inhabited T]

/- A trivial incidence structure over roles = Unit. -/
def trivialIncidence : Incidence I Unit T where
  boundary := fun _ => []
  typeFunc := fun _ => default
  glue     := fun i _ => some i
  unit     := default
  type_consistent := by
    intro i e h
    cases h
  sign_rules := by
    intro i e h
    cases h

/- Reflexivity of bisimilarity for the trivial model (follows from general lemma). -/
theorem approxBisim_refl_trivial (i : I) :
  approxBisim (trivialIncidence : Incidence I Unit T) i i :=
  approxBisim_refl _ _

end IncidenceCore
