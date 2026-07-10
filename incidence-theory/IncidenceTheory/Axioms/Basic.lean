/- Merkle-ID: foundation.axiomatization.basic
   Basic structures and types for Incidence Theory -/
universe u v w

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

/- Minimal matrix abstraction using functions over finite indices.
   Canonical definition (A16); shared by every module that needs it so it
   is declared exactly once (avoids duplicate-declaration errors). -/
def Matrix (m : Type u) (n : Type v) (α : Type w) := m → n → α
