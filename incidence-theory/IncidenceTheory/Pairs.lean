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

/- Atom-index faithfulness for the chained boundary -- same argument as
   `natIncidence_rel_eq`, since the chain is structurally identical. -/
theorem pairIncidenceChained_atom_rel_eq {rel : PairId → PairId → Prop}
  (hbisim : IsBisimulation pairIncidenceChained rel) :
  ∀ m n, rel (PairId.atom m) (PairId.atom n) → m = n := by
  intro m
  induction m with
  | zero =>
    intro n hmn
    obtain ⟨-, hM⟩ := hbisim (PairId.atom 0) (PairId.atom n) hmn
    match n, hM with
    | 0, _ => rfl
    | j + 1, hM =>
      exfalso
      obtain ⟨e, he, -⟩ :=
        hM.right { i := PairId.atom j, role := PairRole.chain, sign := Sign.neg, mult := 1 }
          (by simp [pairIncidenceChained, pairBoundaryChained])
      simp [pairIncidenceChained, pairBoundaryChained] at he
  | succ k ih =>
    intro n hmn
    obtain ⟨-, hM⟩ := hbisim (PairId.atom (k + 1)) (PairId.atom n) hmn
    match n, hM with
    | 0, hM =>
      exfalso
      obtain ⟨e, he, -⟩ :=
        hM.left { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
          (by simp [pairIncidenceChained, pairBoundaryChained])
      simp [pairIncidenceChained, pairBoundaryChained] at he
    | j + 1, hM =>
      obtain ⟨e', he', -, hrel⟩ :=
        hM.left { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
          (by simp [pairIncidenceChained, pairBoundaryChained])
      simp [pairIncidenceChained, pairBoundaryChained] at he'
      subst he'
      have := ih j hrel
      omega

/- Cycle 3's main result: full faithfulness recovered for the whole
   PairId type (atoms *and* pairs, arbitrarily nested), not just atoms
   in isolation. Proved by structural induction on `x`, using the
   `chain`/`fst`/`snd` role split to rule out atom-vs-pair mismatches. -/
theorem pairIncidenceChained_rel_eq {rel : PairId → PairId → Prop}
  (hbisim : IsBisimulation pairIncidenceChained rel) :
  ∀ x y, rel x y → x = y := by
  intro x
  induction x with
  | atom m =>
    intro y hxy
    obtain ⟨-, hM⟩ := hbisim (PairId.atom m) y hxy
    cases y with
    | atom n => exact congrArg PairId.atom (pairIncidenceChained_atom_rel_eq hbisim m n hxy)
    | pair a b =>
      exfalso
      cases m with
      | zero =>
        obtain ⟨e, he, -⟩ :=
          hM.right { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
      | succ k =>
        obtain ⟨e, he, hcompat, -⟩ :=
          hM.left { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
        rcases he with he | he <;> subst he <;> simp [boundaryCompatible] at hcompat
  | pair a b iha ihb =>
    intro y hxy
    obtain ⟨-, hM⟩ := hbisim (PairId.pair a b) y hxy
    cases y with
    | atom n =>
      exfalso
      cases n with
      | zero =>
        obtain ⟨e, he, -⟩ :=
          hM.left { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
      | succ k =>
        obtain ⟨e, he, hcompat, -⟩ :=
          hM.right { i := PairId.atom k, role := PairRole.chain, sign := Sign.neg, mult := 1 }
            (by simp [pairIncidenceChained, pairBoundaryChained])
        simp [pairIncidenceChained, pairBoundaryChained] at he
        rcases he with he | he <;> subst he <;> simp [boundaryCompatible] at hcompat
    | pair a' b' =>
      obtain ⟨e1, he1, hcompat1, hrel1⟩ :=
        hM.left { i := a, role := PairRole.fst, sign := Sign.pos, mult := 1 }
          (by simp [pairIncidenceChained, pairBoundaryChained])
      obtain ⟨e2, he2, hcompat2, hrel2⟩ :=
        hM.left { i := b, role := PairRole.snd, sign := Sign.pos, mult := 1 }
          (by simp [pairIncidenceChained, pairBoundaryChained])
      simp [pairIncidenceChained, pairBoundaryChained] at he1 he2
      rcases he1 with he1 | he1 <;> rcases he2 with he2 | he2 <;>
        subst he1 <;> subst he2 <;>
        simp [boundaryCompatible] at hcompat1 hcompat2
      have ha : a = a' := iha a' hrel1
      have hb : b = b' := ihb b' hrel2
      rw [ha, hb]

/- Faithfulness, cleanly stated: `≈` coincides exactly with `=` on the
   chained instance -- for atoms *and* arbitrarily nested pairs. -/
theorem pairIncidenceChained_approxBisim_iff (x y : PairId) :
  approxBisim pairIncidenceChained x y ↔ x = y := by
  constructor
  · rintro ⟨rel, hbisim, hxy⟩
    exact pairIncidenceChained_rel_eq hbisim x y hxy
  · intro h; subst h; exact approxBisim_refl pairIncidenceChained x

end IncidenceCore
