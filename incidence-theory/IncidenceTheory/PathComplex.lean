import IncidenceTheory.Peano

/- Merkle-ID: implementation.graph_model.path_complex
   story.jsonnet → implementation.nodes.path_complex
   Research cycle 10 (see RESEARCH_LOG.md): a sanity check queued after
   cycles 8-9 located the real cause of ∂² ≠ 0 for chain instances as
   "single-face, not the finiteness of the triangle" -- build an
   INFINITE 2-graded structure and confirm it satisfies ∂² = 0 for the
   same trivial reason the (finite) triangle does, ruling out
   finite-vs-infinite as ever having been the actual variable.

   `node n` is a leaf (empty boundary, matching `natIncidence`'s `0`
   and the triangle's nodes); `edge n` connects `node n` to
   `node (n+1)` via two signed endpoints, exactly `triIncidence`'s edge
   shape (just unbounded instead of a 3-cycle). Proved via the new
   general sufficient-condition theorem
   (`boundary_composition_zero_of_leaf_boundary`, root file) rather than
   a `decide` call -- a *stronger* result than
   `triangle_boundary_square_zero`, which only checks one finite index
   set: this holds for every edge, at every index set, at once. -/

namespace IncidenceCore

inductive PathId where
  | node (n : Nat)
  | edge (n : Nat)
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.path_complex.boundary
   node n is a leaf; edge n's boundary is [node n (neg), node (n+1) (pos)]. -/
def pathBoundary : PathId → Boundary PathId PeanoRole
  | PathId.node _ => []
  | PathId.edge n =>
    [ { i := PathId.node n, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
    , { i := PathId.node (n + 1), role := PeanoRole.pred, sign := Sign.pos, mult := 1 } ]

def pathIncidence : Incidence PathId PeanoRole GraphType where
  boundary := pathBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = PathId.node 0 then some j else some i
  unit     := PathId.node 0
  guards   := Guards.permissive PathId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i with
    | node n => simp [pathBoundary] at h
    | edge n => simp [pathBoundary] at h; rcases h with h | h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i with
    | node n => simp [pathBoundary] at h
    | edge n => simp [pathBoundary] at h; rcases h with h | h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i with
    | node n => simp [pathBoundary] at he
    | edge n =>
      simp [pathBoundary] at he
      rcases he with he | he <;> subst he <;> simp_all
  unit_left := by intro i; simp
  unit_right := by
    intro i
    by_cases h : i = PathId.node 0 <;> simp [h]
  type_preserve := fun _ _ => rfl

/- Every edge's boundary reaches only nodes, which are leaves -- so the
   general sufficient-condition theorem directly proves ∂² = 0 for
   EVERY edge, at EVERY index set and target, in one shot. Confirms
   finite-vs-infinite was never the real variable (cycles 8-9 already
   located it as single-face vs. multi-face). -/
theorem pathIncidence_boundary_square_zero (idx : List PathId) (n : Nat) (k : PathId) :
  boundary_composition pathIncidence idx (PathId.edge n) k = 0 :=
  boundary_composition_zero_of_leaf_boundary pathIncidence idx (PathId.edge n) k
    (by intro e he; simp [pathIncidence, pathBoundary] at he
        rcases he with he | he <;> subst he <;> simp [pathIncidence, pathBoundary])

/- Research cycle 13 (see RESEARCH_LOG.md): a self-correction. Cycle 12's
   log claimed `pathIncidence`'s nodes are "not uniformly empty-boundary,
   only node 0 needs checking" -- an unverified assumption, wrong on
   inspection: `pathBoundary (PathId.node _) = []` for *every* `n`, not
   just `0` (unlike `natIncidence`'s `0`, which is uniquely the only
   empty-boundary element in its chain). So `pathIncidence`'s nodes
   collapse under `≈` exactly like `simplexIncidence`'s vertices did
   (cycle 12) -- a fourth independent instance of the same pattern
   (`pairIncidence`'s flat atoms, `simplexIncidence`'s vertices, and now
   `pathIncidence`'s nodes), caught by re-checking a prior cycle's claim
   before building on it rather than trusting it as given. -/
theorem pathIncidence_nodes_collapse :
  approxBisim pathIncidence (PathId.node 0) (PathId.node 1) := by
  refine ⟨fun x y => (∃ m, x = PathId.node m) ∧ (∃ n, y = PathId.node n), ?_, ?_⟩
  · intro x y ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    subst hm; subst hn
    refine ⟨rfl, ?_, ?_⟩ <;> simp [pathIncidence, pathBoundary]
  · exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩

theorem pathIncidence_nodes_not_eq :
  (PathId.node 0 : PathId) ≠ PathId.node 1 := by simp

/- Research cycle 14 (see RESEARCH_LOG.md): the fix cycle 13 queued --
   apply cycle 3's exact remedy (give the collapsing leaves a
   distinguishing chain-style boundary, tagged with a role disjoint from
   the existing edge-endpoint role so the two can never be confused) to
   `pathIncidence`'s nodes. `PathRole` is a fresh role type (not reusing
   `PeanoRole`, which has only one constructor, `pred` -- not enough
   room to keep edge-endpoints and node-chain-links role-disjoint).
   `node 0` stays the chain's base case (still `[]`); `node (n+1)`
   gains a single `chain`-role link to `node n`; edges keep their
   original two-endpoint shape, now tagged `edgeEnd` instead of `pred`.
   `pathIncidence` itself (cycle 10) is left untouched -- its own
   `pathIncidence_boundary_square_zero` still holds and doesn't need
   this fix; this is a new, separate instance, same relationship as
   `pairIncidence`/`pairIncidenceChained` (cycle 2/3). -/
inductive PathRole where | edgeEnd | chain
deriving DecidableEq, Repr

def pathBoundaryChained : PathId → Boundary PathId PathRole
  | PathId.node 0 => []
  | PathId.node (n + 1) =>
    [ { i := PathId.node n, role := PathRole.chain, sign := Sign.neg, mult := 1 } ]
  | PathId.edge n =>
    [ { i := PathId.node n, role := PathRole.edgeEnd, sign := Sign.neg, mult := 1 }
    , { i := PathId.node (n + 1), role := PathRole.edgeEnd, sign := Sign.pos, mult := 1 } ]

def pathIncidenceChained : Incidence PathId PathRole GraphType where
  boundary := pathBoundaryChained
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = PathId.node 0 then some j else some i
  unit     := PathId.node 0
  guards   := Guards.permissive PathId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i with
    | node n => cases n with
      | zero => simp [pathBoundaryChained] at h
      | succ k => simp [pathBoundaryChained] at h; subst h; simp
    | edge n => simp [pathBoundaryChained] at h; rcases h with h | h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i with
    | node n => cases n with
      | zero => simp [pathBoundaryChained] at h
      | succ k => simp [pathBoundaryChained] at h; subst h; simp
    | edge n => simp [pathBoundaryChained] at h; rcases h with h | h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i with
    | node n => cases n with
      | zero => simp [pathBoundaryChained] at he
      | succ k => simp [pathBoundaryChained] at he; subst he; simp_all
    | edge n =>
      simp [pathBoundaryChained] at he
      rcases he with he | he <;> subst he <;> simp_all
  unit_left := by intro i; simp
  unit_right := by
    intro i
    by_cases h : i = PathId.node 0 <;> simp [h]
  type_preserve := fun _ _ => rfl

/- Measure: node n < edge n < node (n+1), giving a genuine well-founded
   decrease for both the node-chain links and the edge-to-node links. -/
def pathMeasure : PathId → Nat
  | .node n => n
  | .edge n => n + 2

theorem pathIncidenceChained_hdec :
  ∀ i e, e ∈ pathIncidenceChained.boundary i → pathMeasure e.i < pathMeasure i := by
  intro i e h
  cases i with
  | node n => cases n with
    | zero => simp [pathIncidenceChained, pathBoundaryChained] at h
    | succ k =>
      simp [pathIncidenceChained, pathBoundaryChained] at h
      subst h
      simp [pathMeasure]
  | edge n =>
    simp [pathIncidenceChained, pathBoundaryChained] at h
    rcases h with h | h <;> subst h <;> simp [pathMeasure]

theorem pathIncidenceChained_hext :
  ∀ x y, pathIncidenceChained.typeFunc x = pathIncidenceChained.typeFunc y →
    boundaryMatched pathIncidenceChained (· = ·) x y → x = y := by
  intro x y _ ⟨hL, hR⟩
  cases x with
  | node m =>
    cases y with
    | node n =>
      cases m with
      | zero =>
        cases n with
        | zero => rfl
        | succ j =>
          exfalso
          obtain ⟨e, he, -⟩ := hR { i := PathId.node j, role := PathRole.chain, sign := Sign.neg, mult := 1 }
            (by simp [pathIncidenceChained, pathBoundaryChained])
          simp [pathIncidenceChained, pathBoundaryChained] at he
      | succ k =>
        cases n with
        | zero =>
          exfalso
          obtain ⟨e, he, -⟩ := hL { i := PathId.node k, role := PathRole.chain, sign := Sign.neg, mult := 1 }
            (by simp [pathIncidenceChained, pathBoundaryChained])
          simp [pathIncidenceChained, pathBoundaryChained] at he
        | succ j =>
          obtain ⟨e', he', -, heq⟩ := hL { i := PathId.node k, role := PathRole.chain, sign := Sign.neg, mult := 1 }
            (by simp [pathIncidenceChained, pathBoundaryChained])
          simp [pathIncidenceChained, pathBoundaryChained] at he'
          subst he'
          simp at heq
          rw [heq]
    | edge n =>
      exfalso
      cases m with
      | zero =>
        obtain ⟨e, he, -⟩ := hR { i := PathId.node n, role := PathRole.edgeEnd, sign := Sign.neg, mult := 1 }
          (by simp [pathIncidenceChained, pathBoundaryChained])
        simp [pathIncidenceChained, pathBoundaryChained] at he
      | succ k =>
        obtain ⟨e, he, hcompat, -⟩ := hL { i := PathId.node k, role := PathRole.chain, sign := Sign.neg, mult := 1 }
          (by simp [pathIncidenceChained, pathBoundaryChained])
        simp [pathIncidenceChained, pathBoundaryChained] at he
        rcases he with he | he <;> subst he <;> simp [boundaryCompatible] at hcompat
  | edge m =>
    cases y with
    | node n =>
      exfalso
      obtain ⟨e, he, hcompat, -⟩ := hL { i := PathId.node m, role := PathRole.edgeEnd, sign := Sign.neg, mult := 1 }
        (by simp [pathIncidenceChained, pathBoundaryChained])
      cases n with
      | zero => simp [pathIncidenceChained, pathBoundaryChained] at he
      | succ k =>
        simp [pathIncidenceChained, pathBoundaryChained] at he
        subst he
        simp [boundaryCompatible] at hcompat
    | edge n =>
      obtain ⟨e1, he1, hcompat1, heq1⟩ := hL { i := PathId.node m, role := PathRole.edgeEnd, sign := Sign.neg, mult := 1 }
        (by simp [pathIncidenceChained, pathBoundaryChained])
      simp [pathIncidenceChained, pathBoundaryChained] at he1
      rcases he1 with he1 | he1
      · subst he1; simp at heq1; rw [heq1]
      · subst he1; simp [boundaryCompatible] at hcompat1

/- The fix works: full faithfulness recovered for the whole PathId type
   once nodes carry the same distinguishing chain natIncidence's do. -/
theorem pathIncidenceChained_approxBisim_iff (x y : PathId) :
  approxBisim pathIncidenceChained x y ↔ x = y := by
  constructor
  · rintro ⟨rel, hbisim, hxy⟩
    exact incidence_bisim_faithful pathIncidenceChained pathMeasure
      pathIncidenceChained_hdec pathIncidenceChained_hext hbisim x y hxy
  · intro h; subst h; exact approxBisim_refl pathIncidenceChained x

/- Research cycle 16 (see RESEARCH_LOG.md): cycle 14 fixed the collapse
   by giving each `node (n+1)` a single-link chain boundary to
   `node n`. But that shape -- an element whose boundary is exactly one
   nonzero-signed link, pointing to another element with the same shape
   -- is *precisely* `single_link_composition_ne_zero`'s (cycle 9,
   root file) hypothesis: consecutive single-link chains can never
   cancel. So the fix that makes `pathIncidenceChained` faithful should,
   for the same structural reason as `natIncidence`'s and
   `pairIncidenceChained`'s chains (cycle 8), make it fail `∂² = 0`.

   Confirmed, and *for free*: this is a direct application of cycle 9's
   general theorem to `node`'s chain shape, not a new proof -- the
   payoff of having generalized in the first place. Also checked wider
   (via `#eval`, honestly reported rather than silently narrowed): the
   failure isn't confined to the node-chain. `edge n`'s two-entry
   boundary (`node n`/`node (n+1)`, both now non-leaves for `n ≥ 1`)
   *also* composes nonzero -- e.g. `edge 1` against `node 0` gives `1`,
   `edge 1` against `node 1` gives `-1`. This is a genuinely richer
   failure surface than `natIncidence`/`pairIncidenceChained` ever had
   (neither has a multi-entry element at all), and it isn't covered by
   `single_link_composition_ne_zero` (which needs a *singleton*
   boundary at the source) -- left as a concrete witness rather than a
   forced general theorem, since generalizing the two-entry case would
   need genuinely new machinery, not a quick corollary. -/
theorem pathIncidenceChained_not_boundary_square_zero (n : Nat) (idx : List PathId)
  (hmem : PathId.node (n + 1) ∈ idx) :
  boundary_composition pathIncidenceChained idx (PathId.node (n + 2)) (PathId.node n) ≠ 0 :=
  single_link_composition_ne_zero pathIncidenceChained idx
    (PathId.node (n + 2)) (PathId.node (n + 1)) (PathId.node n)
    { i := PathId.node (n + 1), role := PathRole.chain, sign := Sign.neg, mult := 1 }
    { i := PathId.node n, role := PathRole.chain, sign := Sign.neg, mult := 1 }
    rfl rfl (by simp)
    rfl rfl (by simp)
    hmem

def pathChainedIdx : List PathId :=
  [PathId.node 0, PathId.node 1, PathId.node 2, PathId.node 3,
   PathId.edge 0, PathId.edge 1, PathId.edge 2]

theorem pathIncidenceChained_not_boundary_square_zero_check :
  verify_boundary_composition pathIncidenceChained pathChainedIdx = false := by
  decide

/- The node-chain witness, concretely (an instance of the general
   theorem above, at n = 0). -/
theorem pathIncidenceChained_node_witness :
  boundary_composition pathIncidenceChained pathChainedIdx
    (PathId.node 2) (PathId.node 0) = 1 := by
  decide

/- The edge witness: multi-entry elements fail too, not just the
   chain -- the wider failure surface noted above, concretely. -/
theorem pathIncidenceChained_edge_witness :
  boundary_composition pathIncidenceChained pathChainedIdx
    (PathId.edge 1) (PathId.node 0) = 1 := by
  decide

/- Research cycle 17 (see RESEARCH_LOG.md): cycle 16 left the edge-level
   failure as a concrete `decide` witness (`pathIncidenceChained_edge_witness`
   above) rather than a general theorem, since `edge n`'s two-entry
   boundary didn't fit `single_link_composition_ne_zero`'s (singleton-
   boundary) hypothesis. Closed that gap by extending the root file's
   machinery one step: `boundaryMatrix_two_link` +
   `foldl_add_eq_count_mul_two` + `two_link_composition_value` (all fully
   general, not `PathComplex`-specific) give an exact closed-form value
   for a two-entry-boundary composition, the same way
   `single_link_composition_ne_zero` did for one entry. These three small
   lemmas needed the exact `dif`/`ite`-unfolding and generalized-
   accumulator induction techniques from cycle 9/10 (re-applied, not
   rediscovered), plus care with `if`-condition orientation (`a = b` vs.
   `b = a`) that `rw`/`simp` don't treat as interchangeable -- the main
   source of iteration in this cycle. -/

/- `node n` never appears in its own boundary (the chain always points
   strictly backward), so its self-composition term is always zero --
   needed as a building block for the edge witness below. -/
theorem pathIncidenceChained_node_self_boundary_zero (idx : List PathId) (n : Nat) :
  boundaryMatrix pathIncidenceChained idx (PathId.node n) (PathId.node n) = 0 := by
  cases n with
  | zero => simp [boundaryMatrix_eq_foldl, pathIncidenceChained, pathBoundaryChained]
  | succ k => simp [boundaryMatrix_eq_foldl, pathIncidenceChained, pathBoundaryChained]

theorem pathIncidenceChained_node_chain_boundary (idx : List PathId) (n : Nat) :
  boundaryMatrix pathIncidenceChained idx (PathId.node (n + 1)) (PathId.node n) = -1 := by
  simp [boundaryMatrix_eq_foldl, pathIncidenceChained, pathBoundaryChained]

/- `node (n+2)`'s chain link points only to `node (n+1)`, never to
   `node n` two steps back. -/
theorem pathIncidenceChained_node_chain_boundary_zero (idx : List PathId) (n : Nat) :
  boundaryMatrix pathIncidenceChained idx (PathId.node (n + 2)) (PathId.node n) = 0 := by
  simp [boundaryMatrix_eq_foldl, pathIncidenceChained, pathBoundaryChained]

/- The wider failure, now general over ALL n (not just the n = 1
   instance cycle 16 checked): every `edge n` composes to exactly -1
   against its own start node. -/
theorem pathIncidenceChained_edge_node_witness (n : Nat) :
  boundary_composition pathIncidenceChained [PathId.node n, PathId.node (n + 1)]
    (PathId.edge n) (PathId.node n) = -1 := by
  rw [two_link_composition_value pathIncidenceChained [PathId.node n, PathId.node (n + 1)]
    (PathId.edge n) (PathId.node n) (PathId.node (n + 1)) (PathId.node n)
    { i := PathId.node n, role := PathRole.edgeEnd, sign := Sign.neg, mult := 1 }
    { i := PathId.node (n + 1), role := PathRole.edgeEnd, sign := Sign.pos, mult := 1 }
    rfl rfl rfl (by simp)]
  rw [pathIncidenceChained_node_self_boundary_zero, pathIncidenceChained_node_chain_boundary]
  simp

/- ...and every `edge (n+1)` composes to exactly +1 against its
   predecessor's start node, matching cycle 16's `edge 1` vs. `node 0`
   witness as the n = 0 instance of this general fact. -/
theorem pathIncidenceChained_edge_prev_node_witness (n : Nat) :
  boundary_composition pathIncidenceChained [PathId.node (n + 1), PathId.node (n + 2)]
    (PathId.edge (n + 1)) (PathId.node n) = 1 := by
  rw [two_link_composition_value pathIncidenceChained [PathId.node (n + 1), PathId.node (n + 2)]
    (PathId.edge (n + 1)) (PathId.node (n + 1)) (PathId.node (n + 2)) (PathId.node n)
    { i := PathId.node (n + 1), role := PathRole.edgeEnd, sign := Sign.neg, mult := 1 }
    { i := PathId.node (n + 2), role := PathRole.edgeEnd, sign := Sign.pos, mult := 1 }
    rfl rfl rfl (by simp)]
  rw [pathIncidenceChained_node_chain_boundary, pathIncidenceChained_node_chain_boundary_zero]
  simp

end IncidenceCore
