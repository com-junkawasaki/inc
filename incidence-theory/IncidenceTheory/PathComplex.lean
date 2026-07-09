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

end IncidenceCore
