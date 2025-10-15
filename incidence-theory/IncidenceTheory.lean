universe u

structure Incidence (I R T : Type u) where
  boundary : I → List (I × R × Int × Nat)
  typeFunc : I → T
  gluing   : I → I → I
  unit     : I
  -- Axiom A1: Finite Endpoints
  finite_endpoints : ∀ i, (boundary i).length < 1000
  -- Axiom A2: Type Consistency
  type_consistent : ∀ i j r s m, (j, r, s, m) ∈ boundary i → typeFunc j = typeFunc i
  -- Axiom A3: Sign Rules
  sign_rules : ∀ i j r s m, (j, r, s, m) ∈ boundary i → s = -1 ∨ s = 0 ∨ s = 1

def glue {I R T : Type u} (inc : Incidence I R T) (i j : I) : I :=
  inc.gluing i j

def approx {I R T : Type u} (inc : Incidence I R T) (i j : I) : Prop :=
  inc.typeFunc i = inc.typeFunc j ∧ inc.boundary i = inc.boundary j

theorem approx_refl {I R T : Type u} (inc : Incidence I R T) (i : I) :
    approx inc i i :=
  And.intro rfl rfl

theorem approx_symm {I R T : Type u} {inc : Incidence I R T} {i j : I} :
    approx inc i j → approx inc j i :=
  fun h => And.intro (Eq.symm h.left) (Eq.symm h.right)

theorem approx_trans {I R T : Type u} {inc : Incidence I R T} {i j k : I} :
    approx inc i j → approx inc j k → approx inc i k :=
  fun hij hjk =>
    let hT := Eq.trans hij.left hjk.left
    let hB := Eq.trans hij.right hjk.right
    And.intro hT hB

-- Axiom A2: Type Consistency Theorem
theorem type_consistency {I R T : Type u} (inc : Incidence I R T) (i j : I) (r : R) (s : Int) (m : Nat) :
  (j, r, s, m) ∈ inc.boundary i → inc.typeFunc j = inc.typeFunc i :=
inc.type_consistent i j r s m

-- Axiom A3: Sign Rules Theorem
theorem sign_rules_theorem {I R T : Type u} (inc : Incidence I R T) (i j : I) (r : R) (s : Int) (m : Nat) :
  (j, r, s, m) ∈ inc.boundary i → s = -1 ∨ s = 0 ∨ s = 1 :=
inc.sign_rules i j r s m

/-
  Canonical Incidence API (namespaced) — toward multiset boundaries and guarded gluing.
  This section does not replace legacy defs above yet; it provides a stable surface
  to migrate callers incrementally without breaking existing files.
-/

namespace IncidenceCore

universe u

/- Signs for oriented endpoints. -/
inductive Sign where
  | neg
  | zero
  | pos
deriving DecidableEq, Repr

/- Endpoint of an incidence boundary with role, sign, and multiplicity. -/
structure Endpoint (I R : Type u) where
  i    : I
  role : R
  sign : Sign
  mult : Nat
deriving Repr

/- For now we model a multiset as a list with multiset semantics.
   Future: swap to Multiset once the dependency is available. -/
abbrev Boundary (I R : Type u) := List (Endpoint I R)

/- Canonical Incidence structure with guarded gluing. -/
structure Incidence (I R T : Type u) where
  boundary        : I → Boundary I R
  typeFunc        : I → T
  glue            : I → I → Option I
  unit            : I
  type_consistent : ∀ (i : I), ∀ (e : Endpoint I R), e ∈ boundary i → typeFunc e.i = typeFunc i
  sign_rules      : ∀ (i : I), ∀ (e : Endpoint I R), e ∈ boundary i → (e.sign = Sign.neg ∨ e.sign = Sign.zero ∨ e.sign = Sign.pos)

/- Observational equivalence (temporary, equality-based; to be replaced by bisimulation).
   Uses exact boundary equality; callers should not rely on order sensitivity. -/
def approxEq {I R T : Type u} (inc : Incidence I R T) (i j : I) : Prop :=
  inc.typeFunc i = inc.typeFunc j ∧ inc.boundary i = inc.boundary j

theorem approxEq_refl {I R T : Type u} (inc : Incidence I R T) (i : I) :
  approxEq inc i i := And.intro rfl rfl

theorem approxEq_symm {I R T : Type u} {inc : Incidence I R T} {i j : I} :
  approxEq inc i j → approxEq inc j i :=
  fun h => And.intro (Eq.symm h.left) (Eq.symm h.right)

theorem approxEq_trans {I R T : Type u} {inc : Incidence I R T} {i j k : I} :
  approxEq inc i j → approxEq inc j k → approxEq inc i k :=
  fun hij hjk => And.intro (Eq.trans hij.left hjk.left) (Eq.trans hij.right hjk.right)

/- Convenience to apply guarded gluing. -/
def applyGlue {I R T : Type u} (inc : Incidence I R T) (i j : I) : Option I :=
  inc.glue i j

end IncidenceCore

/- Linear algebra signatures for incidence structures. -/

namespace IncidenceCore

/- Minimal matrix abstraction using functions over finite indices.
   We avoid external deps; users can later replace with mathlib `Matrix`. -/
def Matrix (m n : Type u) (α : Type u) := m → n → α

/- Boundary matrix over a chosen finite index set of incidences. -/
def boundaryMatrix {I R T : Type u}
  (inc : Incidence I R T)
  (idx : List I) : Matrix I I Int :=
  fun i j =>
    -- count signed multiplicities of j in boundary of i
    let entries := inc.boundary i
    let signed (e : Endpoint I R) : Int :=
      match e.sign with
      | Sign.neg  => - (Int.ofNat e.mult)
      | Sign.zero => 0
      | Sign.pos  => Int.ofNat e.mult
    entries.foldl (fun acc e => if e.i = j then acc + signed e else acc) 0

/- Laplacian L = Bᵀ ⬝ B with naive multiplication over Int. -/
def laplacian {I R T : Type u}
  (inc : Incidence I R T)
  (idx : List I) : Matrix I I Int :=
  let B := boundaryMatrix inc idx
  fun i j =>
    -- naive finite sum over idx as rows/cols proxy
    let rec dot (xs : List I) (acc : Int) : Int :=
      match xs with
      | []      => acc
      | k :: ks => dot ks (acc + (B k i) * (B k j))
    dot idx 0

end IncidenceCore

/- Pushout≅Gluing specification: guards, type preservation, unit/assoc under preconditions. -/

namespace IncidenceCore

/- Guards declare when gluing is permitted. -/
structure Guards (I : Type u) where
  allow : I → I → Bool

/- Gluing specification relative to an incidence. -/
structure GluingSpec {I R T : Type u} (inc : Incidence I R T) where
  guards           : Guards I
  unit_ok          : ∀ i, guards.allow i inc.unit = true ∧ inc.glue i inc.unit = some i ∧ inc.glue inc.unit i = some i
  type_preserve    : ∀ {i j k}, guards.allow i j = true → inc.glue i j = some k → inc.typeFunc k = inc.typeFunc i
  guard_preserve   : ∀ {i j k}, guards.allow i j = true → inc.glue i j = some k → True
  assoc_when_ok    : ∀ {i j k ij ijk jk},
    guards.allow i j = true → inc.glue i j = some ij →
    guards.allow ij k = true → inc.glue ij k = some ijk →
    guards.allow j k = true → inc.glue j k = some jk →
    guards.allow i jk = true → inc.glue i jk = some ijk

/- A default permissive guard (always true). -/
def Guards.permissive (I : Type u) : Guards I := { allow := fun _ _ => true }

/- A trivial GluingSpec for any incidence with left-biased glue. -/
def trivialGluingSpec {I R T : Type u} (inc : Incidence I R T) : GluingSpec inc :=
  { guards := Guards.permissive I
  , unit_ok := by
      intro i; constructor; simp; constructor <;> simp
  , type_preserve := by
      intro i j k _ h; cases h; rfl
  , guard_preserve := by
      intro; trivial
  , assoc_when_ok := by
      intro i j k ij ijk jk h1 h2 h3 h4 h5 h6 h7
      cases h2; cases h4; cases h6; simp at *; simp
  }

end IncidenceCore

/- Bisimulation skeleton over the canonical API. -/

namespace IncidenceCore

/- Endpoint compatibility (role/sign/mult preserved). -/
def boundaryCompatible {I R T : Type u} (inc : Incidence I R T)
  (e₁ e₂ : Endpoint I R) : Prop :=
  e₁.role = e₂.role ∧ e₁.sign = e₂.sign ∧ e₁.mult = e₂.mult

/- Boundary matching w.r.t. a relation rel on incidences. -/
def boundaryMatched {I R T : Type u} (inc : Incidence I R T)
  (rel : I → I → Prop) (i j : I) : Prop :=
  (∀ e ∈ inc.boundary i, ∃ e', e' ∈ inc.boundary j ∧ boundaryCompatible inc e e' ∧ rel e.i e'.i) ∧
  (∀ e' ∈ inc.boundary j, ∃ e, e ∈ inc.boundary i ∧ boundaryCompatible inc e e' ∧ rel e.i e'.i)

/- A bisimulation is a relation preserved by types and boundary matching. -/
def IsBisimulation {I R T : Type u} (inc : Incidence I R T)
  (rel : I → I → Prop) : Prop :=
  ∀ i j, rel i j → inc.typeFunc i = inc.typeFunc j ∧ boundaryMatched inc rel i j

/- Bisimilarity: related by some bisimulation. -/
def approxBisim {I R T : Type u} (inc : Incidence I R T) (i j : I) : Prop :=
  ∃ rel, IsBisimulation inc rel ∧ rel i j

/- Equality relation is a bisimulation. -/
theorem isBisimulation_rfl {I R T : Type u} (inc : Incidence I R T) :
  IsBisimulation inc (fun a b => a = b) := by
  intro i j hij
  cases hij with
  | rfl =>
    refine And.intro rfl ?match
    unfold boundaryMatched boundaryCompatible
    constructor
    · intro e he
      refine ⟨e, ?_, ?_, rfl⟩
      · simpa using he
      · simp
    · intro e he
      refine ⟨e, ?_, ?_, rfl⟩
      · simpa using he
      · simp

theorem approxBisim_refl {I R T : Type u} (inc : Incidence I R T) (i : I) :
  approxBisim inc i i := by
  refine ⟨(fun a b => a = b), isBisimulation_rfl inc, rfl⟩

/- Symmetry: if rel is a bisimulation then its converse is also. -/
theorem isBisimulation_symm {I R T : Type u} {inc : Incidence I R T}
  {rel : I → I → Prop} (h : IsBisimulation inc rel) :
  IsBisimulation inc (fun a b => rel b a) := by
  intro i j hij
  have := h j i hij
  rcases this with ⟨hT, hM⟩
  refine And.intro hT ?H
  unfold boundaryMatched at hM ⊢
  constructor
  · intro e he
    rcases hM.right e he with ⟨e', he', hC, hRel⟩
    exact ⟨e', he', hC, hRel⟩
  · intro e' he'
    rcases hM.left e' he' with ⟨e, he, hC, hRel⟩
    exact ⟨e, he, hC, hRel⟩

theorem approxBisim_symm {I R T : Type u} {inc : Incidence I R T} {i j : I} :
  approxBisim inc i j → approxBisim inc j i := by
  intro ⟨rel, hRel, hij⟩
  exact ⟨(fun a b => rel b a), isBisimulation_symm hRel, hij⟩

end IncidenceCore
