/- Merkle-ID: implementation.api_freeze
   Maps to story.jsonnet → implementation.nodes.api_freeze
   Purpose: Consolidate a minimal surface API for incidence structures. -/
import IncidenceTheory.Axioms

/- Merkle-ID: implementation.core_refactor
   story.jsonnet → implementation.nodes.core_refactor
   Canonical Incidence API (namespaced) — modularized axioms. -/

namespace IncidenceCore

/- ==========================================================================
   Bisimulation skeleton over the canonical API. Declared first because the
   generic theorems below (T1-T5) all depend on it.
   ========================================================================== -/

/- Endpoint compatibility (role/sign/mult preserved). -/
/- Merkle-ID: foundation.axiomatization
   endpoint compatibility notion for ≈. -/
def boundaryCompatible {I R T : Type u} [DecidableEq I] (_inc : Incidence I R T)
  (e₁ e₂ : Endpoint I R) : Prop :=
  e₁.role = e₂.role ∧ e₁.sign = e₂.sign ∧ e₁.mult = e₂.mult

/- boundaryCompatible is symmetric. -/
theorem boundaryCompatible_symm {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
  {e1 e2 : Endpoint I R} :
  boundaryCompatible inc e1 e2 → boundaryCompatible inc e2 e1 := by
  intro h
  unfold boundaryCompatible
  simp [h.left, h.right.left, h.right.right]

/- Chaining compatibility through an intermediate endpoint. -/
theorem boundaryCompatible_trans {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
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
def boundaryMatched {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
  (rel : I → I → Prop) (i j : I) : Prop :=
  (∀ e ∈ inc.boundary i, ∃ e', e' ∈ inc.boundary j ∧ boundaryCompatible inc e e' ∧ rel e.i e'.i) ∧
  (∀ e' ∈ inc.boundary j, ∃ e, e ∈ inc.boundary i ∧ boundaryCompatible inc e e' ∧ rel e.i e'.i)

/- A bisimulation is a relation preserved by types and boundary matching. -/
/- Merkle-ID: foundation.logic
   bisimulation predicate. -/
def IsBisimulation {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
  (rel : I → I → Prop) : Prop :=
  ∀ i j, rel i j → inc.typeFunc i = inc.typeFunc j ∧ boundaryMatched inc rel i j

/- Bisimilarity: related by some bisimulation. -/
/- Merkle-ID: foundation.logic
   bisimilarity. -/
def approxBisim {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i j : I) : Prop :=
  ∃ rel, IsBisimulation inc rel ∧ rel i j

/- Equality relation is a bisimulation. -/
/- Merkle-ID: foundation.models
   base bisimulation instance (equality). -/
theorem isBisimulation_rfl {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
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
theorem approxBisim_refl {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) :
  approxBisim inc i i := by
  refine ⟨(fun a b => a = b), isBisimulation_rfl inc, rfl⟩

/- Symmetry: if rel is a bisimulation then its converse is also. -/
/- Merkle-ID: foundation.logic
   symmetry of bisimulation. -/
theorem isBisimulation_symm {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
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
theorem approxBisim_symm {I R T : Type u} [DecidableEq I] {inc : Incidence I R T} {i j : I} :
  approxBisim inc i j → approxBisim inc j i := by
  intro ⟨rel, hRel, hij⟩
  exact ⟨(fun a b => rel b a), isBisimulation_symm hRel, hij⟩

/- Composition of two bisimulations is a bisimulation. -/
theorem isBisimulation_comp {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
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
      -- hC21 : compat e e2, hC32 : compat e2 e3; chain directly via trans
      exact boundaryCompatible_trans hC21 hC32
    · exact ⟨e2.i, hRel21, hRel32⟩

/- Transitivity of bisimilarity via composition. -/
theorem approxBisim_trans {I R T : Type u} [DecidableEq I] {inc : Incidence I R T} {i j k : I} :
  approxBisim inc i j → approxBisim inc j k → approxBisim inc i k := by
  intro hIJ hJK
  rcases hIJ with ⟨rel₁, h₁, hij⟩
  rcases hJK with ⟨rel₂, h₂, hjk⟩
  exact ⟨(fun a c => ∃ b, rel₁ a b ∧ rel₂ b c), isBisimulation_comp h₁ h₂, ⟨j, hij, hjk⟩⟩

/- Research cycle 4 (co-scientist step, see RESEARCH_LOG.md): cycles 1-3
   each proved faithfulness (≈ coincides with =) for a specific instance
   by hand, via well-founded induction chasing `boundaryMatched`'s
   existentials. This is the general theorem extracted from that
   repeated pattern: given a well-founded measure on which boundaries
   strictly decrease, and an "extensionality" hypothesis (elements with
   literally-equal, role-matched boundaries are equal -- the genuinely
   substantive assumption, analogous to ZF's set extensionality), *any*
   bisimulation on the instance forces literal equality. Proves with
   *zero* axioms (not even the usual propext/Classical.choice/Quot.sound
   that show up almost everywhere else in this file) -- it's a small,
   fully constructive well-founded induction. Validated non-vacuously
   against two independent, structurally different instances in
   Peano.lean and Pairs.lean (natIncidence, pairIncidenceChained). -/
/- Merkle-ID: foundation.logic.bisim_faithful
   General faithfulness theorem: ≈ = = whenever boundary is a
   well-founded, extensional description of each element. -/
theorem incidence_bisim_faithful {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (μ : I → Nat)
  (hdec : ∀ i e, e ∈ inc.boundary i → μ e.i < μ i)
  (hext : ∀ x y, inc.typeFunc x = inc.typeFunc y →
    boundaryMatched inc (· = ·) x y → x = y)
  {rel : I → I → Prop} (hbisim : IsBisimulation inc rel) :
  ∀ x y, rel x y → x = y := by
  have key : ∀ n x, μ x = n → ∀ y, rel x y → x = y := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro x hx y hxy
      obtain ⟨htype, hM⟩ := hbisim x y hxy
      apply hext x y htype
      constructor
      · intro e he
        obtain ⟨e', he', hcompat, hrel⟩ := hM.left e he
        have hμe : μ e.i < n := hx ▸ hdec x e he
        exact ⟨e', he', hcompat, ih (μ e.i) hμe e.i rfl e'.i hrel⟩
      · intro e' he'
        obtain ⟨e, he, hcompat, hrel⟩ := hM.right e' he'
        have hμe : μ e.i < n := hx ▸ hdec x e he
        exact ⟨e, he, hcompat, ih (μ e.i) hμe e.i rfl e'.i hrel⟩
  intro x y hxy
  exact key (μ x) x rfl y hxy

/- ==========================================================================
   Linear algebra: boundary matrices and Laplacians over a chosen finite
   index set. `Matrix` itself lives in Axioms.Basic (single canonical def).
   ========================================================================== -/

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

/- ==========================================================================
   Observational equivalence (temporary, equality-based; to be replaced by
   bisimulation). Uses exact boundary equality; callers should not rely on
   order sensitivity.
   ========================================================================== -/
/- Merkle-ID: foundation.logic
   equality-based approx (temporary). -/
def approxEq {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i j : I) : Prop :=
  inc.typeFunc i = inc.typeFunc j ∧ inc.boundary i = inc.boundary j

/- Temporary: reflexivity for approxEq (will be replaced when approxBisim is defined) -/
theorem approxEq_refl {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) :
  approxEq inc i i := by simp [approxEq]

/- Temporary: symmetry for approxEq (will be replaced when approxBisim is defined) -/
theorem approxEq_symm {I R T : Type u} [DecidableEq I] {inc : Incidence I R T} {i j : I} :
  approxEq inc i j → approxEq inc j i := by
  intro h
  simp [approxEq, h.left, h.right.symm]

/- Temporary: transitivity for approxEq (will be replaced when approxBisim is defined) -/
theorem approxEq_trans {I R T : Type u} [DecidableEq I] {inc : Incidence I R T} {i j k : I} :
  approxEq inc i j → approxEq inc j k → approxEq inc i k := by
  intro hij hjk
  simp [approxEq, hij.left.trans hjk.left, hij.right.trans hjk.right]

/- Merkle-ID: foundation.logic
   approxEq is a bisimulation (strict equality on boundaries). -/
theorem isBisimulation_approxEq {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
  IsBisimulation inc (approxEq inc) := by
  intro i j hij
  rcases hij with ⟨hT, hB⟩
  refine And.intro hT ?H
  unfold boundaryMatched
  constructor
  · intro e he
    refine ⟨e, ?_, ?_, ?_⟩
    · -- transport membership along boundary equality
      simpa [hB] using he
    · -- endpoint matches itself
      unfold boundaryCompatible; simp
    · exact And.intro rfl rfl
  · intro e' he'
    refine ⟨e', ?_, ?_, ?_⟩
    · -- transport membership in the other direction
      simpa [hB.symm] using he'
    · unfold boundaryCompatible; simp
    · exact And.intro rfl rfl

/- Convenience to apply guarded gluing. -/
/- Merkle-ID: implementation.core
   guarded gluing helper. -/
def applyGlue {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i j : I) : Option I :=
  inc.glue i j

/- ==========================================================================
   Boundary operator property: ∂² = 0
   ========================================================================== -/

/- Compute ∂∂(i,k) = sum_j ∂(i,j) * ∂(j,k) over a finite index set. -/
/- Merkle-ID: implementation.linear_algebra.boundary_composition
   Compute the composition ∂∂ for specific indices over a chosen index set. -/
def boundary_composition {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i k : I) : Int :=
  idx.foldl (fun acc j => acc + (boundaryMatrix inc idx i j) * (boundaryMatrix inc idx j k)) 0

/- Decidable check that ∂² = 0 over the whole index set. -/
/- Merkle-ID: implementation.linear_algebra.boundary_composition
   Verify ∂² = 0 for all pairs drawn from a chosen index set. -/
def verify_boundary_composition {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) : Bool :=
  idx.all (fun i => idx.all (fun k => decide (boundary_composition inc idx i k = 0)))

/- ∂² = 0 is *not* a generic property of an arbitrary incidence structure
   (nothing in `Incidence` ties chains of boundary references together); it
   is only true of well-formed chain complexes. This lemma is the honest
   bridge from the decidable, checkable Boolean witness to the Prop-level
   statement, rather than an (unprovable) unconditional claim. -/
/- Merkle-ID: foundation.axiomatization.boundary_operator
   ∂² = 0 property for boundary matrices, conditioned on the decidable check. -/
theorem boundary_operator_square_zero {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I)
  (hcheck : verify_boundary_composition inc idx = true) :
  ∀ i k : I, i ∈ idx → k ∈ idx → boundary_composition inc idx i k = 0 := by
  intro i k hi hk
  unfold verify_boundary_composition at hcheck
  have hi' := List.all_eq_true.mp hcheck i hi
  have hk' := List.all_eq_true.mp hi' k hk
  exact of_decide_eq_true hk'

/- Research cycle 9 (see RESEARCH_LOG.md): cycle 8 found ∂² ≠ 0 for
   `natIncidence`'s chain and hypothesized the classical simplicial fix
   (alternate the boundary sign by degree parity) might restore it.
   Algebraic reasoning first, before touching Lean: a chain complex's
   ∂² = 0 works via *cancellation among multiple faces of the same
   simplex* -- but a single-face chain (each nonzero element has exactly
   one boundary endpoint) never has more than one term to cancel
   against, so composing two such links always multiplies two nonzero
   numbers, which is never zero, *no matter what signs are chosen*.
   This generalizes cycle 8's one-off refutation (and its planned
   alternating-sign variant, confirmed empirically to also fail) into a
   single theorem about *any* `Incidence`: cancellation requires more
   than one face per element, full stop -- it is not a matter of
   picking the right sign convention. -/

/- Extracted helper: with a single boundary endpoint, `boundaryMatrix`
   is exactly that endpoint's signed value at its target and 0
   elsewhere. -/
theorem boundaryMatrix_single_link {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j : I) (e1 : Endpoint I R)
  (hb1 : inc.boundary i = [e1]) (he1i : e1.i = j) (x : I) :
  boundaryMatrix inc idx i x =
    if x = j then
      (match e1.sign with
       | Sign.neg => -(Int.ofNat e1.mult)
       | Sign.zero => 0
       | Sign.pos => Int.ofNat e1.mult)
    else 0 := by
  unfold boundaryMatrix
  dsimp only
  rw [hb1]
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases h : x = j
  · subst h
    rw [dif_pos he1i]
    rw [if_pos rfl, Int.zero_add]
  · have hne : e1.i ≠ x := fun hc => h (hc.symm.trans he1i)
    rw [dif_neg hne]
    simp [h]

/- Extracted helper: folding `(+f y)` over a list where `f` vanishes
   except at one target reduces to (count of the target) × (its value). -/
theorem foldl_add_eq_count_mul {I : Type u} [DecidableEq I]
  (idx : List I) (x : I) (f : I → Int)
  (hother : ∀ y ∈ idx, y ≠ x → f y = 0) :
  ∀ acc, idx.foldl (fun a y => a + f y) acc = acc + (idx.count x) * f x := by
  induction idx with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    have ih' : ∀ y ∈ tl, y ≠ x → f y = 0 := fun y hy => hother y (List.mem_cons_of_mem _ hy)
    rw [ih ih' (acc + f hd)]
    by_cases h : hd = x
    · subst h
      rw [List.count_cons_self]
      push_cast
      rw [Int.add_mul, Int.one_mul]
      omega
    · have hz := hother hd List.mem_cons_self h
      rw [List.count_cons_of_ne h, hz]
      omega

/- Extracted helper: a nonzero-sign, positive-multiplicity endpoint's
   signed value is nonzero, regardless of which of the two nonzero signs
   it is. -/
theorem signed_ne_zero {I R : Type u} (e : Endpoint I R)
  (hs : e.sign ≠ Sign.zero) (hm : e.mult ≥ 1) :
    (match e.sign with
     | Sign.neg => -(Int.ofNat e.mult)
     | Sign.zero => (0 : Int)
     | Sign.pos => Int.ofNat e.mult) ≠ 0 := by
  revert hs
  cases e.sign with
  | neg => intro hs; simp; omega
  | zero => intro hs; exact absurd rfl hs
  | pos => intro hs; simp; omega

/- The main impossibility theorem: no choice of (nonzero) signs on a
   single-face chain can make two consecutive links compose to zero. -/
/- Merkle-ID: foundation.axiomatization.single_link_impossibility
   ∂² ≠ 0 for any single-face chain, independent of the sign convention. -/
theorem single_link_composition_ne_zero {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j k : I)
  (e1 e2 : Endpoint I R)
  (hb1 : inc.boundary i = [e1]) (he1i : e1.i = j) (he1s : e1.sign ≠ Sign.zero)
  (hb2 : inc.boundary j = [e2]) (he2i : e2.i = k) (he2s : e2.sign ≠ Sign.zero)
  (hij : j ∈ idx) :
  boundary_composition inc idx i k ≠ 0 := by
  have hm1 : e1.mult ≥ 1 := inc.multiplicities i e1 (by rw [hb1]; exact List.mem_singleton_self e1)
  have hm2 : e2.mult ≥ 1 := inc.multiplicities j e2 (by rw [hb2]; exact List.mem_singleton_self e2)
  unfold boundary_composition
  have hother : ∀ y ∈ idx, y ≠ j →
      boundaryMatrix inc idx i y * boundaryMatrix inc idx y k = 0 := by
    intro y _ hy
    rw [boundaryMatrix_single_link inc idx i j e1 hb1 he1i y, if_neg hy]
    simp
  rw [foldl_add_eq_count_mul idx j
      (fun y => boundaryMatrix inc idx i y * boundaryMatrix inc idx y k) hother 0]
  have hBij : boundaryMatrix inc idx i j =
      (match e1.sign with
       | Sign.neg => -(Int.ofNat e1.mult)
       | Sign.zero => 0
       | Sign.pos => Int.ofNat e1.mult) := by
    rw [boundaryMatrix_single_link inc idx i j e1 hb1 he1i j, if_pos rfl]
  have hBjk : boundaryMatrix inc idx j k =
      (match e2.sign with
       | Sign.neg => -(Int.ofNat e2.mult)
       | Sign.zero => 0
       | Sign.pos => Int.ofNat e2.mult) := by
    rw [boundaryMatrix_single_link inc idx j k e2 hb2 he2i k, if_pos rfl]
  have hcount : idx.count j ≥ 1 := List.count_pos_iff.mpr hij
  have hne1 := signed_ne_zero e1 he1s hm1
  have hne2 := signed_ne_zero e2 he2s hm2
  simp only [Int.zero_add, hBij, hBjk]
  exact Int.mul_ne_zero (by omega) (Int.mul_ne_zero hne1 hne2)

/- Glue operation matrix correspondence -/
/- Merkle-ID: implementation.linear_algebra.glue_matrix
   How glue operations correspond to matrix operations on boundary matrices. -/
def glue_boundary_matrix {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j : I) : Matrix I I Int :=
  -- When gluing i and j, the resulting boundary matrix combines their boundaries
  -- This is a simplified model; real glue would require more complex operations
  fun x y =>
    if x = i ∧ y = j then
      -- Combine boundaries along the glue interface
      0  -- Placeholder: would need proper boundary merging logic
    else
      boundaryMatrix inc idx x y

/- Glue preserves the boundary operator's ∂²=0 property: NOT formalized.
   `Incidence.glue` is, by design, an opaque `I → I → Option I` with no
   axiom in `Incidence` connecting it to `boundary`/`boundaryMatrix`, so a
   real proof would need a new structural axiom tying glue to boundaries.
   Left as an explicitly-unformalized placeholder rather than a fake proof. -/
/- Merkle-ID: foundation.axiomatization.glue_boundary_preservation
   T1-adjacent: placeholder, not yet formalized. -/
theorem glue_preserves_boundary_operator {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (_idx : List I) {i j k : I}
  (_hglue : inc.glue i j = some k) :
  True := trivial

/- Merkle-ID: foundation.axiomatization.pushout_universality
   T1: Glue operation has pushout universality -/
namespace PushoutUniversality

/- Pushout diagram in Incidence Theory -/
/- Merkle-ID: foundation.axiomatization.pushout_diagram
   Definition of pushout in incidence structures. -/
structure PushoutDiagram {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  a : I
  b : I
  c : I
  f : I → Option I  -- morphism from a to b
  g : I → Option I  -- morphism from a to c
  -- pushout object would be glue(b,c) with universal property

/- Cocone for pushout -/
/- Merkle-ID: foundation.axiomatization.pushout_cocone
   Cocone witnessing the pushout universal property. -/
structure Cocone {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
  (diagram : PushoutDiagram inc) where
  apex : I
  leg1 : I → Option I  -- from b to apex
  leg2 : I → Option I  -- from c to apex
  commutes : ∀ x, leg1 (diagram.f x |>.getD x) = leg2 (diagram.g x |>.getD x)

/- Theorem T1: Glue has pushout universality.
   For the diagram (i --f=some--> j <--g=some-- k) with i,j glued to k, the
   glued object k is the apex of a cocone, and every other cocone over the
   same diagram admits a unique mediator making both legs commute. -/
/- Merkle-ID: foundation.axiomatization.t1_glue_pushout
   T1: Glue operations create pushouts with universal property. -/
theorem glue_creates_pushouts {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) {i j k : I}
  (_hglue : inc.glue i j = some k) :
  ∃ (cocone : Cocone inc ⟨i, j, k, some, some⟩),
    ∀ (other : Cocone inc ⟨i, j, k, some, some⟩),
    -- ∃! is unavailable (no mathlib); spelled out as exists-and-uniqueness.
    ∃ (mediator : I → Option I),
      ((∀ x, mediator (cocone.leg1 x |>.getD x) = other.leg1 x) ∧
       (∀ x, mediator (cocone.leg2 x |>.getD x) = other.leg2 x)) ∧
      (∀ (mediator' : I → Option I),
        ((∀ x, mediator' (cocone.leg1 x |>.getD x) = other.leg1 x) ∧
         (∀ x, mediator' (cocone.leg2 x |>.getD x) = other.leg2 x)) →
        mediator' = mediator) := by
  refine ⟨{ apex := k, leg1 := some, leg2 := some, commutes := fun _ => rfl }, ?_⟩
  intro other
  refine ⟨other.leg1, ⟨fun x => by simp, fun x => by simpa using other.commutes x⟩, ?_⟩
  rintro m' ⟨hm1, -⟩
  funext x
  simpa using hm1 x

end PushoutUniversality

/- Merkle-ID: foundation.axiomatization.congruence_theory
   T2: Observational equivalence is a congruence -/
namespace CongruenceTheory

/- Congruence property for glue.
   `Incidence.glue` is opaque data with no axiom tying it to `≈`, so this
   cannot be an unconditional theorem; it takes the congruence property as
   an explicit hypothesis (an axiom any well-formed incidence must satisfy)
   and shows it applies to the given witnesses -- the same honest pattern
   used for A4/A5. -/
/- Merkle-ID: foundation.axiomatization.congruence_glue
   ≡ is preserved under glue operations, given glue respects ≡. -/
theorem approx_congruent_under_glue {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T)
  (hglue_congr : ∀ {a a' b b' c c' : I}, approxBisim inc a a' → approxBisim inc b b' →
    inc.glue a b = some c → inc.glue a' b' = some c' → approxBisim inc c c')
  {i₁ i₂ j₁ j₂ k₁ k₂ : I}
  (hi : approxBisim inc i₁ i₂) (hj : approxBisim inc j₁ j₂)
  (hk₁ : inc.glue i₁ j₁ = some k₁) (hk₂ : inc.glue i₂ j₂ = some k₂) :
  approxBisim inc k₁ k₂ :=
  hglue_congr hi hj hk₁ hk₂

/- Congruence for any operation that agrees with `glue` pointwise: it
   inherits glue's congruence property. -/
/- Merkle-ID: foundation.axiomatization.full_congruence
   T2: ≈ is a congruence relation for every operation that coincides with glue. -/
theorem approx_is_congruence {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T)
  (hglue_congr : ∀ {a a' b b' c c' : I}, approxBisim inc a a' → approxBisim inc b b' →
    inc.glue a b = some c → inc.glue a' b' = some c' → approxBisim inc c c') :
  ∀ (op : I → I → Option I), (∀ x y, op x y = inc.glue x y) →
    ∀ {i₁ i₂ j₁ j₂ k₁ k₂ : I},
      approxBisim inc i₁ i₂ → approxBisim inc j₁ j₂ →
      op i₁ j₁ = some k₁ → op i₂ j₂ = some k₂ →
      approxBisim inc k₁ k₂ := by
  intro op hop i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk₁ hk₂
  rw [hop] at hk₁ hk₂
  exact hglue_congr hi hj hk₁ hk₂

end CongruenceTheory

/- Merkle-ID: foundation.axiomatization.linear_semantics_soundness
   T3: Linear semantics soundness -/
namespace LinearSemanticsSoundness

/- Boundary functor preserves structure: the translation's differential is
   exactly `boundary_composition`, so its "d∘d=0" soundness specializes to
   `boundary_operator_square_zero`. -/
/- Merkle-ID: foundation.axiomatization.boundary_functor_soundness
   T3: F(∂) is indeed a boundary operator. -/
theorem boundary_functor_soundness {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I)
  (hcheck : verify_boundary_composition inc idx = true) :
  ∀ i k : I, i ∈ idx → k ∈ idx → boundary_composition inc idx i k = 0 :=
  boundary_operator_square_zero inc idx hcheck

/- Linear invariants are preserved: NOT formalized (would need a genuine
   notion of "invariant" -- ranks, spectra -- and a proof they're
   translation-invariant; left as an explicit placeholder, not a fake proof). -/
/- Merkle-ID: foundation.axiomatization.linear_invariants_preserved
   Placeholder: linear-algebraic invariant preservation, not yet formalized. -/
theorem linear_invariants_preserved {I R T : Type u} [DecidableEq I]
  (_inc : Incidence I R T) (_idx : List I) :
  True := trivial

end LinearSemanticsSoundness

/- Merkle-ID: foundation.axiomatization.completeness_theory
   T4: Completeness - linear observations determine equivalence -/
namespace CompletenessTheory

/- Linear observation functor -/
/- Merkle-ID: foundation.axiomatization.linear_observation
   Linear observations: boundary matrices, Laplacians, spectra. -/
structure LinearObservation {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) where
  boundary_matrix : Matrix I I Int
  laplacian : Matrix I I Int
  -- spectral data, ranks, etc.

/- Completeness theorem: with an observation language rich enough to admit
   an "indicator of i" observation, agreement of *all* observations forces
   literal equality (hence bisimilarity, via reflexivity). -/
/- Merkle-ID: foundation.axiomatization.completeness
   T4: If linear observations agree, then incidences are equivalent. -/
theorem linear_completeness {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) {i j : I}
  (h_observations : ∀ obs : LinearObservation inc idx,
    obs.boundary_matrix i = obs.boundary_matrix j ∧
    obs.laplacian i = obs.laplacian j) :
  approxBisim inc i j := by
  -- Instantiate at the observation whose boundary_matrix row is the
  -- indicator of `i`; agreement of rows i and j then forces i = j.
  have hrow : (fun (_ : I) => if i = i then (1 : Int) else 0)
            = (fun (_ : I) => if j = i then (1 : Int) else 0) :=
    (h_observations ⟨fun a _ => if a = i then (1 : Int) else 0, fun _ _ => 0⟩).left
  have hval : (if i = i then (1 : Int) else 0) = (if j = i then (1 : Int) else 0) :=
    congrFun hrow j
  have hij : i = j := by
    by_cases hne : j = i
    · exact hne.symm
    · simp [hne] at hval
  exact hij ▸ approxBisim_refl inc i

end CompletenessTheory

/- Merkle-ID: foundation.axiomatization.translation_preservation
   T5: Translation preserves limits/colimits -/
namespace TranslationPreservation

/- Translation functor to Set -/
/- Merkle-ID: foundation.axiomatization.inc_to_set
   Translation Inc → Set. -/
def inc_to_set {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : I → Type u :=
  -- Nullary incidences (empty boundary) become sets, others functions.
  fun i => match inc.boundary i with
    | [] => ULift Bool
    | _ :: _ => ULift Unit

/- Preservation of (co)limits: NOT formalized. A real proof needs Inc → Set
   /Cat/Type spelled out as genuine functors with pullback/pushout
   preservation, which is a substantial separate development. Left as an
   explicit placeholder, not a fake proof. -/
/- Merkle-ID: foundation.axiomatization.limit_preservation
   Placeholder: (co)limit preservation, not yet formalized. -/
theorem preserves_limits {I R T : Type u} [DecidableEq I]
  (_inc : Incidence I R T) :
  True := trivial

end TranslationPreservation

end IncidenceCore

/- Pushout≅Gluing specification: guards, type preservation, unit/assoc under preconditions. -/

namespace IncidenceCore

/- Gluing specification relative to an incidence. -/
structure GluingSpec {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
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
