/- Merkle-ID: foundation.axiomatization.basic
   Basic structures and types for Incidence Theory -/
universe u

/- Signs for oriented endpoints (A3). -/
inductive Sign where
  | neg
  | zero
  | pos
deriving DecidableEq, Repr

/- Endpoint of an incidence boundary with role, sign, and multiplicity (A2/A3/A4). -/
structure Endpoint (I R : Type u) where
  i    : I
  role : R
  sign : Sign
  mult : Nat
deriving Repr

/- For now we model a multiset as a list with multiset semantics.
   Future: swap to Multiset once the dependency is available. -/
abbrev Boundary (I R : Type u) := List (Endpoint I R)
