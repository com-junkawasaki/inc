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
   recorded honestly (with a concrete proof) rather than glossed over. -/

namespace IncidenceCore

inductive PairRole where | fst | snd
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

end IncidenceCore
