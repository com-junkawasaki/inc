import IncidenceTheory.FoundationIncidenceWitness

/-!
  The actual infinity sentence used by ADR-2607141850/G3.  Unlike
  `finiteInfinitySchema`, this is not `top`: it asks for a set containing the
  empty set and closed under the von Neumann successor operation.
-/

namespace IncidenceCore.ReferenceFoundation

def actualInfinity : Sentence :=
  .ex (.and
    (.mem .empty (.var 0))
    (.all (.imp
      (.mem (.var 0) (.var 1))
      (.mem (Term.successor (.var 0)) (.var 1)))))

theorem actualInfinity_closed : actualInfinity.closed := by
  intro rho
  rfl

theorem actualInfinity_substitution_closed (substitution : Nat → Term) :
    actualInfinity.substitute substitution = actualInfinity := by
  rfl

def actualInfinitySchema : InfinitySchema where
  statement := actualInfinity
  closed := actualInfinity_closed
  const_free := by trivial
  substitution_closed := actualInfinity_substitution_closed

theorem actualInfinity_is_not_finite_placeholder :
    actualInfinitySchema.statement ≠ finiteInfinitySchema.statement := by
  intro equal
  cases equal

end IncidenceCore.ReferenceFoundation
