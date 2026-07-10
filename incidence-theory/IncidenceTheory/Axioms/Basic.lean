/- Merkle-ID: foundation.axiomatization.basic
   Basic structures and types for Incidence Theory -/
universe u v

/- Signs for oriented endpoints (A3). -/
inductive Sign where
  | neg
  | zero
  | pos
deriving DecidableEq, Repr

/- Endpoint of an incidence boundary with role, sign, and multiplicity (A2/A3/A4). -/
structure Endpoint (I : Type u) (R : Type v) where
  i    : I
  role : R
  sign : Sign
  mult : Nat
  mult_pos : 1 ≤ mult
deriving Repr

/- For now we model a multiset as a list with multiset semantics.
   Future: swap to Multiset once the dependency is available. -/
abbrev Boundary (I : Type u) (R : Type v) := List (Endpoint I R)
