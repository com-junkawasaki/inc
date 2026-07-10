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
structure Endpoint (I : Type u) (R : Type v) where
  i    : I
  role : R
  sign : Sign
  mult : Nat
  mult_pos : 1 ≤ mult := by omega
deriving Repr

/- For now we model a multiset as a list with multiset semantics.
   Future: swap to Multiset once the dependency is available. -/
abbrev Boundary (I : Type u) (R : Type v) := List (Endpoint I R)

/- Minimal matrix abstraction using functions over finite indices.
   Canonical definition (A16); shared by every module that needs it so it
   is declared exactly once (avoids duplicate-declaration errors). -/
namespace IncidenceCore

def Matrix (m : Type u) (n : Type v) (α : Type w) := m → n → α

end IncidenceCore
