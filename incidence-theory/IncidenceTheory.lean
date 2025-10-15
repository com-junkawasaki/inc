/- Merkle-ID: implementation.api_freeze
   Maps to story.jsonnet → implementation.nodes.api_freeze
   Purpose: Consolidate a minimal surface API for incidence structures. -/
universe u

/- Merkle-ID: implementation.core_refactor
   story.jsonnet → implementation.nodes.core_refactor
   Canonical Incidence API (namespaced) — multiset-like boundary & guarded gluing. -/

namespace IncidenceCore

/- Signs for oriented endpoints. -/
/- Merkle-ID: foundation.axiomatization
   Sign domain (A3). -/
inductive Sign where
  | neg
  | zero
  | pos
deriving DecidableEq, Repr

/- Endpoint of an incidence boundary with role, sign, and multiplicity. -/
/- Merkle-ID: foundation.axiomatization
   Endpoint with role/sign/multiplicity (A2/A3/A4). -/
structure Endpoint (I R : Type u) where
  i    : I
  role : R
  sign : Sign
  mult : Nat
deriving Repr

/- For now we model a multiset as a list with multiset semantics.
   Future: swap to Multiset once the dependency is available. -/
/- Merkle-ID: implementation.core
   boundary as list with multiset semantics; swap to Multiset later. -/
abbrev Boundary (I R : Type u) := List (Endpoint I R)

/- Canonical Incidence structure with guarded gluing. -/
/- Merkle-ID: implementation.core
   canonical incidence with guarded gluing. -/
structure Incidence (I R T : Type u) where
  boundary        : I → Boundary I R
  typeFunc        : I → T
  glue            : I → I → Option I
  unit            : I
  type_consistent : ∀ (i : I), ∀ (e : Endpoint I R), e ∈ boundary i → typeFunc e.i = typeFunc i
  sign_rules      : ∀ (i : I), ∀ (e : Endpoint I R), e ∈ boundary i → (e.sign = Sign.neg ∨ e.sign = Sign.zero ∨ e.sign = Sign.pos)

/- Observational equivalence (temporary, equality-based; to be replaced by bisimulation).
   Uses exact boundary equality; callers should not rely on order sensitivity. -/
/- Merkle-ID: foundation.logic
   equality-based approx (temporary). -/
def approxEq {I R T : Type u} (inc : Incidence I R T) (i j : I) : Prop :=
  inc.typeFunc i = inc.typeFunc j ∧ inc.boundary i = inc.boundary j

/- New API: reflexivity stated for approxBisim. -/
theorem approxEq_refl {I R T : Type u} (inc : Incidence I R T) (i : I) :
  approxBisim inc i i := approxBisim_refl inc i

/- New API: symmetry stated for approxBisim. -/
theorem approxEq_symm {I R T : Type u} {inc : Incidence I R T} {i j : I} :
  approxBisim inc i j → approxBisim inc j i :=
  fun h => approxBisim_symm h

/- New API: transitivity stated for approxBisim. -/
theorem approxEq_trans {I R T : Type u} {inc : Incidence I R T} {i j k : I} :
  approxBisim inc i j → approxBisim inc j k → approxBisim inc i k :=
  fun hij hjk => approxBisim_trans hij hjk

/- Merkle-ID: foundation.logic
   approxEq is a bisimulation (strict equality on boundaries). -/
theorem isBisimulation_approxEq {I R T : Type u} (inc : Incidence I R T) :
  IsBisimulation inc (approxEq inc) := by
  intro i j hij
  rcases hij with ⟨hT, hB⟩
  refine And.intro hT ?H
  unfold boundaryMatched
  constructor
  · intro e he
    refine ⟨e, ?he', ?hC, ?hRel⟩
    · -- transport membership along boundary equality
      simpa [hB] using he
    · -- endpoint matches itself
      unfold boundaryCompatible; simp
    · exact And.intro rfl rfl
  · intro e' he'
    refine ⟨e', ?he, ?hC, ?hRel⟩
    · -- transport membership in the other direction
      simpa [hB.symm] using he'
    · unfold boundaryCompatible; simp
    · exact And.intro rfl rfl

-- Bridge approxEq ⇒ approxBisim removed (migration complete).

/- Convenience to apply guarded gluing. -/
/- Merkle-ID: implementation.core
   guarded gluing helper. -/
def applyGlue {I R T : Type u} (inc : Incidence I R T) (i j : I) : Option I :=
  inc.glue i j

end IncidenceCore

/- Linear algebra signatures for incidence structures. -/

namespace IncidenceCore

/- Minimal matrix abstraction using functions over finite indices.
   We avoid external deps; users can later replace with mathlib `Matrix`. -/
universe v w
def Matrix (m : Type u) (n : Type v) (α : Type w) := m → n → α

/- Boundary matrix over a chosen finite index set of incidences. -/
def boundaryMatrix {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T)
  (idx : List I) : Matrix I I Int :=
  fun i j =>
    -- count signed multiplicities of j in boundary of i
    let _ := idx -- mark idx as used to satisfy linter
    let entries := inc.boundary i
    let signed (e : Endpoint I R) : Int :=
      match e.sign with
      | Sign.neg  => - (Int.ofNat e.mult)
      | Sign.zero => 0
      | Sign.pos  => Int.ofNat e.mult
    entries.foldl (fun acc e => by
      by_cases h : e.i = j
      · exact acc + signed e
      · exact acc) 0

/- Laplacian L = Bᵀ ⬝ B with naive multiplication over Int. -/
def laplacian {I R T : Type u} [DecidableEq I]
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

end IncidenceCore

/- Merkle-ID: foundation.logic
   bisimulation skeleton over canonical API. -/

namespace IncidenceCore

/- Endpoint compatibility (role/sign/mult preserved). -/
/- Merkle-ID: foundation.axiomatization
   endpoint compatibility notion for ≈. -/
def boundaryCompatible {I R T : Type u} (_inc : Incidence I R T)
  (e₁ e₂ : Endpoint I R) : Prop :=
  e₁.role = e₂.role ∧ e₁.sign = e₂.sign ∧ e₁.mult = e₂.mult

/- boundaryCompatible is symmetric. -/
theorem boundaryCompatible_symm {I R T : Type u} {inc : Incidence I R T} {e1 e2 : Endpoint I R} :
  boundaryCompatible inc e1 e2 → boundaryCompatible inc e2 e1 := by
  intro h
  unfold boundaryCompatible
  simp [h.left, h.right.left, h.right.right]

/- Chaining compatibility through an intermediate endpoint. -/
theorem boundaryCompatible_trans {I R T : Type u} {inc : Incidence I R T}
  {e₁ e₂ e₃ : Endpoint I R} :
  boundaryCompatible inc e₁ e₂ → boundaryCompatible inc e₂ e₃ → boundaryCompatible inc e₁ e₃ := by
  intro h12 h23
  unfold boundaryCompatible at h12 h23 ⊢
  rcases h12 with ⟨hr12, hs12, hm12⟩
  rcases h23 with ⟨hr23, hs23, hm23⟩
  exact And.intro (hr12.trans hr23) (And.intro (hs12.trans hs23) (hm12.trans hm23))

/- Boundary matching w.r.t. a relation rel on incidences. -/
/- Merkle-ID: foundation.logic
   boundary matching definition for bisimulation. -/
def boundaryMatched {I R T : Type u} (inc : Incidence I R T)
  (rel : I → I → Prop) (i j : I) : Prop :=
  (∀ e ∈ inc.boundary i, ∃ e', e' ∈ inc.boundary j ∧ boundaryCompatible inc e e' ∧ rel e.i e'.i) ∧
  (∀ e' ∈ inc.boundary j, ∃ e, e ∈ inc.boundary i ∧ boundaryCompatible inc e e' ∧ rel e.i e'.i)

/- A bisimulation is a relation preserved by types and boundary matching. -/
/- Merkle-ID: foundation.logic
   bisimulation predicate. -/
def IsBisimulation {I R T : Type u} (inc : Incidence I R T)
  (rel : I → I → Prop) : Prop :=
  ∀ i j, rel i j → inc.typeFunc i = inc.typeFunc j ∧ boundaryMatched inc rel i j

/- Bisimilarity: related by some bisimulation. -/
/- Merkle-ID: foundation.logic
   bisimilarity. -/
def approxBisim {I R T : Type u} (inc : Incidence I R T) (i j : I) : Prop :=
  ∃ rel, IsBisimulation inc rel ∧ rel i j

/- Equality relation is a bisimulation. -/
/- Merkle-ID: foundation.models
   base bisimulation instance (equality). -/
theorem isBisimulation_rfl {I R T : Type u} (inc : Incidence I R T) :
  IsBisimulation inc (fun a b => a = b) := by
  intro i j hij
  cases hij with
  | refl =>
    refine And.intro rfl ?_
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

/- Merkle-ID: foundation.logic
   reflexivity of bisimilarity. -/
theorem approxBisim_refl {I R T : Type u} (inc : Incidence I R T) (i : I) :
  approxBisim inc i i := by
  refine ⟨(fun a b => a = b), isBisimulation_rfl inc, rfl⟩

/- Symmetry: if rel is a bisimulation then its converse is also. -/
/- Merkle-ID: foundation.logic
   symmetry of bisimulation. -/
theorem isBisimulation_symm {I R T : Type u} {inc : Incidence I R T}
  {rel : I → I → Prop} (h : IsBisimulation inc rel) :
  IsBisimulation inc (fun a b => rel b a) := by
  intro i j hij
  have hij' := h j i hij
  rcases hij' with ⟨hTji, hM⟩
  have hT : inc.typeFunc i = inc.typeFunc j := Eq.symm hTji
  refine And.intro hT ?H
  unfold boundaryMatched at hM ⊢
  constructor
  · intro e he
    rcases hM.right e he with ⟨e', he', hC, hRel⟩
    exact ⟨e', he', boundaryCompatible_symm hC, hRel⟩
  · intro e' he'
    rcases hM.left e' he' with ⟨e, he, hC, hRel⟩
    exact ⟨e, he, boundaryCompatible_symm hC, hRel⟩

/- Merkle-ID: foundation.logic
   symmetry of bisimilarity. -/
theorem approxBisim_symm {I R T : Type u} {inc : Incidence I R T} {i j : I} :
  approxBisim inc i j → approxBisim inc j i := by
  intro ⟨rel, hRel, hij⟩
  exact ⟨(fun a b => rel b a), isBisimulation_symm hRel, hij⟩

/- Composition of two bisimulations is a bisimulation. -/
theorem isBisimulation_comp {I R T : Type u} {inc : Incidence I R T}
  {rel₁ rel₂ : I → I → Prop}
  (h₁ : IsBisimulation inc rel₁) (h₂ : IsBisimulation inc rel₂) :
  IsBisimulation inc (fun a c => ∃ b, rel₁ a b ∧ rel₂ b c) := by
  intro i k hik
  rcases hik with ⟨j, hij, hjk⟩
  have hTij := (h₁ i j hij).left
  have hMj := (h₁ i j hij).right
  have hTjk := (h₂ j k hjk).left
  have hMk := (h₂ j k hjk).right
  -- Types align transitively
  have hTik : inc.typeFunc i = inc.typeFunc k := hTij.trans hTjk
  -- Boundary matching by chaining matches through j
  refine And.intro hTik ?H
  unfold boundaryMatched at hMj hMk ⊢
  constructor
  · intro e he
    rcases hMj.left e he with ⟨e2, he2, hC12, hRel12⟩
    rcases hMk.left e2 he2 with ⟨e3, he3, hC23, hRel23⟩
    refine ⟨e3, he3, ?hC13, ?hRel13⟩
    · exact boundaryCompatible_trans hC12 hC23
    · exact ⟨e2.i, hRel12, hRel23⟩
  · intro e3 he3
    rcases hMk.right e3 he3 with ⟨e2, he2, hC32, hRel32⟩
    rcases hMj.right e2 he2 with ⟨e, he, hC21, hRel21⟩
    refine ⟨e, he, ?hC31, ?hRel31⟩
    · -- hC31 : boundaryCompatible e e3
      -- We have hC21 : compat e2 e and hC32 : compat e3 e2; chain via symmetry+trans
      have hC23 : boundaryCompatible inc e2 e3 := boundaryCompatible_symm hC32
      have hC13 : boundaryCompatible inc e e2 := boundaryCompatible_symm hC21
      exact boundaryCompatible_trans hC13 hC23
    · exact ⟨e2.i, hRel21, hRel32⟩

/- Transitivity of bisimilarity via composition. -/
theorem approxBisim_trans {I R T : Type u} {inc : Incidence I R T} {i j k : I} :
  approxBisim inc i j → approxBisim inc j k → approxBisim inc i k := by
  intro hIJ hJK
  rcases hIJ with ⟨rel₁, h₁, hij⟩
  rcases hJK with ⟨rel₂, h₂, hjk⟩
  exact ⟨(fun a c => ∃ b, rel₁ a b ∧ rel₂ b c), isBisimulation_comp h₁ h₂, ⟨j, hij, hjk⟩⟩

end IncidenceCore
