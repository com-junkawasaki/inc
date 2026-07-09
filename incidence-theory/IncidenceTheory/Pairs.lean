import IncidenceTheory.GraphModel

/- Merkle-ID: implementation.graph_model.pairs
   story.jsonnet → implementation.nodes.pairs
   Ordered pairs realized as a concrete `Incidence` instance: a `pair a b`
   is an incidence whose `boundary` has exactly two endpoints, one per
   role (`fst`/`snd`), pointing at `a` and `b`. The projections aren't a
   bolted-on Lean-level accessor -- they *are* the boundary structure,
   the same relational vocabulary `triIncidence`'s edges and
   `natIncidence`'s predecessor chain already used.

   Research cycle 2 (see RESEARCH_LOG.md): this file also records a
   genuine negative finding, not just a success. Pairing is well-behaved
   (jointly injective, recoverable from `boundary`), but bare atoms with
   no further boundary structure are *not* separated by Inc's abstract
   bisimulation `≈` -- unlike `natIncidence`, where the predecessor chain
   gave every element a unique "distance from zero", an atom's boundary
   is `[]` regardless of *which* atom it is, so nothing stops a
   bisimulation from relating any two atoms to each other. This is
   recorded honestly (with a concrete proof) rather than glossed over.

   Research cycle 3: fixes exactly that gap. `pairIncidenceChained` gives
   atoms the same predecessor-chain boundary `natIncidence` used (tagged
   with a distinct `chain` role so it can never be confused with a
   `fst`/`snd` projection edge), and recovers *full* faithfulness for the
   whole `PairId` type (`pairIncidenceChained_rel_eq`) -- confirming
   "well-founded carrier + boundary structure that actually distinguishes
   elements, with roles kept disjoint across purposes" as a general
   recipe, not a Peano-specific accident. `pairIncidence` (flat atoms,
   the collapsing one) is kept alongside deliberately, as a permanent,
   proven illustration of what goes wrong without that structure. -/

namespace IncidenceCore

inductive PairRole where | fst | snd | chain
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.pairs.carrier
   Atoms (opaque leaves, indexed for concreteness) and pairs, nestable. -/
inductive PairId where
  | atom (n : Nat)
  | pair (a b : PairId)
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.pairs.boundary
   An atom has no boundary (a leaf); a pair's boundary is its two
   projections. -/
def pairBoundary : PairId → Boundary PairId PairRole
  | PairId.atom _ => []
  | PairId.pair a b =>
    [ { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
    , { i := b, role := PairRole.snd, sign := Sign.pos, mult := 1 } ]

/- Merkle-ID: implementation.graph_model.pairs.incidence
   Pairs as an Incidence; `glue` is left-biased (same shape as
   `triIncidence`'s) with `atom 0` as unit -- `glue` isn't the focus
   here, `boundary`-as-projection is. -/
def pairIncidence : Incidence PairId PairRole GraphType where
  boundary := pairBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = PairId.atom 0 then some j else some i
  unit     := PairId.atom 0
  guards   := Guards.permissive PairId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i with
    | atom n => simp [pairBoundary] at h
    | pair a b => simp [pairBoundary] at h; rcases h with h | h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i with
    | atom n => simp [pairBoundary] at h
    | pair a b => simp [pairBoundary] at h; rcases h with h | h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i with
    | atom n => simp [pairBoundary] at he
    | pair a b =>
      simp [pairBoundary] at he
      have hspec := PairId.pair.sizeOf_spec a b
      rcases he with he | he <;> subst he <;>
        (have hs := congrArg sizeOf hei.symm; simp at hs; try omega)
  unit_left := by intro i; simp
  unit_right := by
    intro i
    by_cases h : i = PairId.atom 0 <;> simp [h]
  type_preserve := fun _ _ => rfl

/- Projections are literally recoverable from `boundary`, not a bolted-on
   Lean-level accessor: pairing IS the boundary structure. -/
theorem pairIncidence_boundary_pair (a b : PairId) :
  pairIncidence.boundary (PairId.pair a b) =
    [ { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
    , { i := b, role := PairRole.snd, sign := Sign.pos, mult := 1 } ] := rfl

/- Joint injectivity of pairing (Kuratowski-pair-style: `(a, b)`
   determines `a` and `b` uniquely) -- the property that makes pairs
   usable as the building block for relations/functions. -/
theorem pairIncidence_pair_injective {a b a' b' : PairId}
  (h : PairId.pair a b = PairId.pair a' b') : a = a' ∧ b = b' := by
  injection h with h1 h2
  exact ⟨h1, h2⟩

/- Negative finding (see file docstring): bare atoms carry no
   distinguishing boundary structure, so `≈` does not separate them.
   Concrete witness: `atom 0 ≈ atom 1` even though `atom 0 ≠ atom 1`. -/
theorem pairIncidence_atoms_collapse :
  approxBisim pairIncidence (PairId.atom 0) (PairId.atom 1) := by
  refine ⟨fun x y => (∃ m, x = PairId.atom m) ∧ (∃ n, y = PairId.atom n), ?_, ?_, ?_⟩
  · intro x y ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    subst hm; subst hn
    refine ⟨rfl, ?_, ?_⟩ <;> simp [pairIncidence, pairBoundary]
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem pairIncidence_atoms_not_eq : (PairId.atom 0 : PairId) ≠ PairId.atom 1 := by
  simp

/- Merkle-ID: implementation.graph_model.pairs.boundary_chained
   Cycle 3 fix: atom (n+1)'s boundary points at atom n via a `chain`
   role, disjoint from `fst`/`snd`, so it can never be mistaken for a
   pair's projection edge. atom 0 is the chain's base case. -/
def pairBoundaryChained : PairId → Boundary PairId PairRole
  | PairId.atom 0 => []
  | PairId.atom (n + 1) =>
    [ { i := PairId.atom n, role := PairRole.chain, sign := Sign.neg, mult := 1 } ]
  | PairId.pair a b =>
    [ { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
    , { i := b, role := PairRole.snd, sign := Sign.pos, mult := 1 } ]

/- Merkle-ID: implementation.graph_model.pairs.incidence_chained
   Same shape as `pairIncidence`, but atoms now carry the predecessor
   chain. -/
def pairIncidenceChained : Incidence PairId PairRole GraphType where
  boundary := pairBoundaryChained
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = PairId.atom 0 then some j else some i
  unit     := PairId.atom 0
  guards   := Guards.permissive PairId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i with
    | atom n => cases n with
      | zero => simp [pairBoundaryChained] at h
      | succ k => simp [pairBoundaryChained] at h; subst h; simp
    | pair a b => simp [pairBoundaryChained] at h; rcases h with h | h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i with
    | atom n => cases n with
      | zero => simp [pairBoundaryChained] at h
      | succ k => simp [pairBoundaryChained] at h; subst h; simp
    | pair a b => simp [pairBoundaryChained] at h; rcases h with h | h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i with
    | atom n => cases n with
      | zero => simp [pairBoundaryChained] at he
      | succ k => simp [pairBoundaryChained] at he; subst he; simp_all
    | pair a b =>
      simp [pairBoundaryChained] at he
      have hspec := PairId.pair.sizeOf_spec a b
      rcases he with he | he <;> subst he <;>
        (have hs := congrArg sizeOf hei.symm; simp at hs; try omega)
  unit_left := by intro i; simp
  unit_right := by
    intro i
    by_cases h : i = PairId.atom 0 <;> simp [h]
  type_preserve := fun _ _ => rfl

/- Research cycle 4 (see RESEARCH_LOG.md): the substantive hypothesis of
   the general `incidence_bisim_faithful` theorem (root file), applied to
   `pairIncidenceChained` -- this replaces cycle 3's bespoke
   induction (kept in git history, not duplicated here) with an
   instantiation of the general theorem, exercising it against the most
   structurally complex of the three confirming instances (atoms *and*
   nested pairs, two disjoint edge roles). -/
theorem pairIncidenceChained_hdec :
  ∀ i e, e ∈ pairIncidenceChained.boundary i → sizeOf e.i < sizeOf i := by
  intro i e h
  cases i with
  | atom n => cases n with
    | zero => simp [pairIncidenceChained, pairBoundaryChained] at h
    | succ k =>
      simp [pairIncidenceChained, pairBoundaryChained] at h
      subst h
      simp
  | pair a b =>
    simp [pairIncidenceChained, pairBoundaryChained] at h
    have hspec := PairId.pair.sizeOf_spec a b
    rcases h with h | h <;> subst h <;> simp <;> omega

theorem pairIncidenceChained_hext :
  ∀ x y, pairIncidenceChained.typeFunc x = pairIncidenceChained.typeFunc y →
    boundaryMatched pairIncidenceChained (· = ·) x y → x = y := by
  intro x y _ ⟨hL, hR⟩
  cases x with
  | atom m =>
    cases y with
    | atom n =>
      cases m with
      | zero =>
        cases n with
        | zero => rfl
        | succ j =>
          exfalso
          obtain ⟨e, he, -⟩ :=
            hR { i := PairId.atom j, role := PairRole.chain, sign := Sign.neg, mult := 1 }
              (by simp [pairIncidenceChained, pairBoundaryChained])
          simp [pairIncidenceChained, pairBoundaryChained] at he
      | succ k =>
        cases n with
        | zero =>
          exfalso
          obtain ⟨e, he, -⟩ :=
            hL { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
              (by simp [pairIncidenceChained, pairBoundaryChained])
          simp [pairIncidenceChained, pairBoundaryChained] at he
        | succ j =>
          obtain ⟨e', he', -, heq⟩ :=
            hL { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
              (by simp [pairIncidenceChained, pairBoundaryChained])
          simp [pairIncidenceChained, pairBoundaryChained] at he'
          subst he'
          simp at heq
          rw [heq]
    | pair a b =>
      exfalso
      cases m with
      | zero =>
        obtain ⟨e, he, -⟩ :=
          hR { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
      | succ k =>
        obtain ⟨e, he, hcompat, -⟩ :=
          hL { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
        rcases he with he | he <;> subst he <;> simp [boundaryCompatible] at hcompat
  | pair a b =>
    cases y with
    | atom n =>
      exfalso
      cases n with
      | zero =>
        obtain ⟨e, he, -⟩ :=
          hL { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
      | succ k =>
        obtain ⟨e, he, hcompat, -⟩ :=
          hR { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
        rcases he with he | he <;> subst he <;> simp [boundaryCompatible] at hcompat
    | pair a' b' =>
      obtain ⟨e1, he1, hcompat1, heq1⟩ :=
        hL { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
          (by simp [pairIncidenceChained, pairBoundaryChained])
      obtain ⟨e2, he2, hcompat2, heq2⟩ :=
        hL { i := b, role := PairRole.snd, sign := Sign.pos, mult := 1 }
          (by simp [pairIncidenceChained, pairBoundaryChained])
      simp [pairIncidenceChained, pairBoundaryChained] at he1 he2
      rcases he1 with he1 | he1 <;> rcases he2 with he2 | he2 <;>
        subst he1 <;> subst he2 <;>
        simp [boundaryCompatible] at hcompat1 hcompat2
      simp at heq1 heq2
      rw [heq1, heq2]

/- Faithfulness, cleanly stated: `≈` coincides exactly with `=` on the
   chained instance -- for atoms *and* arbitrarily nested pairs. Derived
   from the general theorem rather than a bespoke induction. -/
theorem pairIncidenceChained_approxBisim_iff (x y : PairId) :
  approxBisim pairIncidenceChained x y ↔ x = y := by
  constructor
  · rintro ⟨rel, hbisim, hxy⟩
    exact incidence_bisim_faithful pairIncidenceChained sizeOf
      pairIncidenceChained_hdec pairIncidenceChained_hext hbisim x y hxy
  · intro h; subst h; exact approxBisim_refl pairIncidenceChained x

/- Research cycle 5 (co-scientist step, see RESEARCH_LOG.md): the same
   T5 translation-faithfulness question as `natToFiniteSet` in
   `Peano.lean`, but for the richer nested-pair structure -- a genuine
   test since a naive translation could plausibly flatten/confuse
   nesting. `pairToShape` is built by exactly `pairBoundaryChained`'s own
   recursion (atom -> leaf, pair -> node of the two recursive
   translations) and is injective, so it reflects `≈` rather than
   erasing it, for atoms *and* arbitrarily nested pairs. -/
inductive PairShape where
  | leaf (n : Nat)
  | node (l r : PairShape)
deriving DecidableEq, Repr

def pairToShape : PairId → PairShape
  | PairId.atom n => PairShape.leaf n
  | PairId.pair a b => PairShape.node (pairToShape a) (pairToShape b)

theorem pairToShape_injective {x y : PairId} (h : pairToShape x = pairToShape y) :
  x = y := by
  induction x generalizing y with
  | atom m =>
    cases y with
    | atom n => simp [pairToShape] at h; rw [h]
    | pair a b => simp [pairToShape] at h
  | pair a b iha ihb =>
    cases y with
    | atom n => simp [pairToShape] at h
    | pair a' b' =>
      simp [pairToShape] at h
      have ha : a = a' := iha h.1
      have hb : b = b' := ihb h.2
      rw [ha, hb]

theorem pairToShape_reflects_approxBisim {x y : PairId}
  (h : pairToShape x = pairToShape y) : approxBisim pairIncidenceChained x y := by
  rw [pairIncidenceChained_approxBisim_iff]
  exact pairToShape_injective h

/- Research cycle 8 (see RESEARCH_LOG.md, `natIncidence` finding first):
   the same ∂² = 0 failure, independently confirmed on this instance --
   the atom-chain inside `pairIncidenceChained` is structurally the same
   unbounded-depth, same-sign chain as `natIncidence`'s, and it fails
   for the same reason. Also checked whether composing *through* a
   `pair` node behaves differently (it doesn't -- the nonzero value
   just propagates in via the chain reachable from a `pair`'s `snd`
   endpoint). -/
def pairIdx6 : List PairId :=
  [PairId.atom 0, PairId.atom 1, PairId.atom 2, PairId.atom 3,
   PairId.pair (PairId.atom 0) (PairId.atom 1),
   PairId.pair (PairId.atom 1) (PairId.atom 2)]

theorem pairIncidenceChained_not_boundary_square_zero :
  verify_boundary_composition pairIncidenceChained pairIdx6 = false := by
  decide

theorem pairIncidenceChained_boundary_composition_witness :
  boundary_composition pairIncidenceChained pairIdx6
    (PairId.pair (PairId.atom 0) (PairId.atom 1)) (PairId.atom 0) = -1 := by
  decide

/- Research cycle 24 (see RESEARCH_LOG.md): cycle 8's ∂² check above only
   ever composed through a single-level `pair`. `PathId`'s `edge` (cycles
   16-19) is also a two-entry-boundary element, but its two targets are
   always plain `Nat`-indexed nodes, never elements with boundaries of
   their own reaching back into the same territory -- so `edge`'s
   "elsewhere zero" picture (cycle 19) was zero by *structural absence*
   of any path, not by algebraic cancellation. `PairId.pair` is
   different: it can nest (`pair (pair a b) c`), so two *different*
   entries of an outer `pair`'s boundary can have boundaries of their
   own that *converge* on the same target. Tested concretely first
   (`#eval`): `pair (pair (atom n) (atom (n+1))) (atom (n+2))` composed
   against `atom (n+1)` -- the inner pair's `snd` targets `atom (n+1)`
   directly (`+1`), and `atom (n+2)`'s own predecessor-chain link *also*
   targets `atom (n+1)` (`-1`) -- checked for `n = 0, 3, 7` before
   formalizing, confirming a genuine parametrized family, not a
   coincidence at one specific value. -/
theorem pairIncidenceChained_atom_chain_boundary (idx : List PairId) (n : Nat) :
  boundaryMatrix pairIncidenceChained idx (PairId.atom (n + 1)) (PairId.atom n) = -1 := by
  simp [boundaryMatrix_eq_foldl, pairIncidenceChained, pairBoundaryChained]

theorem pairIncidenceChained_atom_chain_boundary_zero (idx : List PairId) (n : Nat) :
  boundaryMatrix pairIncidenceChained idx (PairId.atom (n + 2)) (PairId.atom n) = 0 := by
  simp [boundaryMatrix_eq_foldl, pairIncidenceChained, pairBoundaryChained]

theorem pairIncidenceChained_pair_fst_boundary (idx : List PairId) (a b : PairId) (hne : a ≠ b) :
  boundaryMatrix pairIncidenceChained idx (PairId.pair a b) a = 1 := by
  rw [boundaryMatrix_two_link pairIncidenceChained idx (PairId.pair a b) a b
    { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
    { i := b, role := PairRole.snd, sign := Sign.pos, mult := 1 }
    rfl rfl rfl hne a]
  simp [hne]

theorem pairIncidenceChained_pair_snd_boundary (idx : List PairId) (a b : PairId) (hne : a ≠ b) :
  boundaryMatrix pairIncidenceChained idx (PairId.pair a b) b = 1 := by
  rw [boundaryMatrix_two_link pairIncidenceChained idx (PairId.pair a b) a b
    { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
    { i := b, role := PairRole.snd, sign := Sign.pos, mult := 1 }
    rfl rfl rfl hne b]
  simp [Ne.symm hne]

/- The failure, generalized over all `n`: composing against the
   innermost pair's *first* atom is nonzero (the chain from `atom (n+2)`
   never reaches back that far, so there's nothing to cancel against --
   the same "only one term" shape `single_link_composition_ne_zero`
   (cycle 9) captures, just reached here via `two_link_composition_value`
   since the source has two entries). -/
theorem pairIncidenceChained_nested_pair_witness (n : Nat) :
  boundary_composition pairIncidenceChained
    [PairId.pair (PairId.atom n) (PairId.atom (n + 1)), PairId.atom (n + 2)]
    (PairId.pair (PairId.pair (PairId.atom n) (PairId.atom (n + 1))) (PairId.atom (n + 2)))
    (PairId.atom n) = 1 := by
  rw [two_link_composition_value pairIncidenceChained
    [PairId.pair (PairId.atom n) (PairId.atom (n + 1)), PairId.atom (n + 2)]
    (PairId.pair (PairId.pair (PairId.atom n) (PairId.atom (n + 1))) (PairId.atom (n + 2)))
    (PairId.pair (PairId.atom n) (PairId.atom (n + 1))) (PairId.atom (n + 2)) (PairId.atom n)
    { i := PairId.pair (PairId.atom n) (PairId.atom (n + 1)), role := PairRole.fst, sign := Sign.pos, mult := 1 }
    { i := PairId.atom (n + 2), role := PairRole.snd, sign := Sign.pos, mult := 1 }
    rfl rfl rfl (by simp)]
  rw [pairIncidenceChained_pair_fst_boundary _ (PairId.atom n) (PairId.atom (n + 1)) (by simp),
      pairIncidenceChained_atom_chain_boundary_zero]
  simp

/- The genuinely new finding, generalized over all `n`: composing
   against `atom (n+1)` -- reached BOTH via the inner pair's `snd`
   AND via `atom (n+2)`'s chain link -- vanishes by real cancellation
   (`1 + (-1) = 0`), the first instance in this project of `∂²`
   canceling via *converging paths from recursive nesting*, distinct
   from `simplexIncidence.face`'s cancellation (cycle 11, a deliberately
   chosen alternating-sum convention on a *single* element's own
   boundary) and from `pathIncidenceChained`'s "elsewhere zero" (cycle
   19, structural absence of any path at all). -/
theorem pairIncidenceChained_nested_pair_cancellation (n : Nat) :
  boundary_composition pairIncidenceChained
    [PairId.pair (PairId.atom n) (PairId.atom (n + 1)), PairId.atom (n + 2)]
    (PairId.pair (PairId.pair (PairId.atom n) (PairId.atom (n + 1))) (PairId.atom (n + 2)))
    (PairId.atom (n + 1)) = 0 := by
  rw [two_link_composition_value pairIncidenceChained
    [PairId.pair (PairId.atom n) (PairId.atom (n + 1)), PairId.atom (n + 2)]
    (PairId.pair (PairId.pair (PairId.atom n) (PairId.atom (n + 1))) (PairId.atom (n + 2)))
    (PairId.pair (PairId.atom n) (PairId.atom (n + 1))) (PairId.atom (n + 2)) (PairId.atom (n + 1))
    { i := PairId.pair (PairId.atom n) (PairId.atom (n + 1)), role := PairRole.fst, sign := Sign.pos, mult := 1 }
    { i := PairId.atom (n + 2), role := PairRole.snd, sign := Sign.pos, mult := 1 }
    rfl rfl rfl (by simp)]
  rw [pairIncidenceChained_pair_snd_boundary _ (PairId.atom n) (PairId.atom (n + 1)) (by simp),
      pairIncidenceChained_atom_chain_boundary]
  simp

end IncidenceCore
