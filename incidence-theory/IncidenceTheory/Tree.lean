import IncidenceTheory.GraphModel

/- Merkle-ID: implementation.graph_model.tree
   story.jsonnet → implementation.nodes.tree
   Research cycle 29 (see RESEARCH_LOG.md): a fifth new `Incidence`
   instance, testing a structural shape none of the prior four
   (`natIncidence`, `pairIncidenceChained`, `pathIncidenceChained`,
   `simplexIncidence`, `cycleIncidence`) tried -- a *ternary*-branching
   tree, rather than `PairId`'s strictly binary nesting. `node a b c`
   has a genuine *three*-entry boundary (uniform `pos` sign, unlike
   `simplexIncidence.face`'s deliberately alternating sum), making
   `treeIncidence.node` the *second* real three-entry-boundary instance
   in this project (`simplexIncidence.face`, cycle 11, was the first --
   and the *only* one, which is exactly why cycle 20 declined to build
   general three-entry `boundaryMatched`/`∂²` machinery: no second
   instance existed yet to justify it). That condition is now met, but
   building that generalization is left as its own follow-up (queued in
   `RESEARCH_LOG.md`) rather than folded into this instance-introduction
   cycle.

   Honest scope note: this instance did *not* surface a qualitatively
   new phenomenon the way `cycleIncidence` (cycles 26-28) did -- what it
   confirms is that three already-established patterns ("flat leaves
   collapse", "leaf-boundary sufficiency", "non-leaf boundary reach
   generically fails ∂² = 0") generalize cleanly from binary to ternary
   branching, via a mix of direct general-theorem reuse and concrete
   `decide` witnesses. That confirmation is itself worth recording, not
   a consolation prize -- it rules out "these patterns were secretly
   about binary branching specifically" as an unstated assumption. -/

namespace IncidenceCore

inductive TernaryRole where | c1 | c2 | c3
deriving DecidableEq, Repr

inductive TreeId where
  | leaf (n : Nat)
  | node (a b c : TreeId)
deriving DecidableEq, Repr

def treeBoundary : TreeId → Boundary TreeId TernaryRole
  | TreeId.leaf _ => []
  | TreeId.node a b c =>
    [ { i := a, role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
    , { i := b, role := TernaryRole.c2, sign := Sign.pos, mult := 1 }
    , { i := c, role := TernaryRole.c3, sign := Sign.pos, mult := 1 } ]

def treeIncidence : Incidence TreeId TernaryRole GraphType where
  boundary := treeBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = TreeId.leaf 0 then some j else some i
  unit     := TreeId.leaf 0
  guards   := Guards.permissive TreeId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i with
    | leaf n => simp [treeBoundary] at h
    | node a b c => simp [treeBoundary] at h; rcases h with h | h | h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i with
    | leaf n => simp [treeBoundary] at h
    | node a b c => simp [treeBoundary] at h; rcases h with h | h | h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i with
    | leaf n => simp [treeBoundary] at he
    | node a b c =>
      simp [treeBoundary] at he
      rcases he with he | he | he <;> subst he <;>
        (have hsz := congrArg sizeOf hei; simp [TreeId.node.sizeOf_spec] at hsz <;> omega)
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = TreeId.leaf 0 <;> simp [h]
  type_preserve := fun _ _ => rfl

/- 1. "Flat leaves collapse" (cycles 2/12/13/18/26), a fifth
   confirmation: bare `leaf n`s have no boundary structure to
   distinguish them, so `≈` relates any two -- unchanged by branching
   factor. -/
theorem treeIncidence_leaves_collapse :
  approxBisim treeIncidence (TreeId.leaf 0) (TreeId.leaf 1) := by
  refine ⟨fun x y => (∃ m, x = TreeId.leaf m) ∧ (∃ n, y = TreeId.leaf n), ?_, ?_⟩
  · intro x y ⟨⟨m, hx⟩, ⟨n, hy⟩⟩
    subst hx; subst hy
    refine ⟨rfl, ?_, ?_⟩ <;> simp [treeIncidence, treeBoundary]
  · exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩

theorem treeIncidence_leaves_not_eq : (TreeId.leaf 0 : TreeId) ≠ TreeId.leaf 1 := by simp

/- 2. "Leaf-boundary sufficiency" (`boundary_composition_zero_of_leaf_boundary`,
   cycle 10) applies "for free" to a genuinely 3-entry element too --
   the general theorem never assumed a specific arity, only that every
   boundary entry reaches a leaf. -/
theorem treeIncidence_leaf_children_zero (idx : List TreeId) (k : TreeId) :
  boundary_composition treeIncidence idx
    (TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2)) k = 0 :=
  boundary_composition_zero_of_leaf_boundary treeIncidence idx
    (TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2)) k
    (by intro e he; simp [treeIncidence, treeBoundary] at he
        rcases he with he | he | he <;> subst he <;> rfl)

/- 3. Non-leaf children -> genuine `∂² ≠ 0`, checked concretely.
   `outerTree = node (node (leaf 0) (leaf 1) (leaf 2)) (leaf 3) (leaf 4)`
   composed against `leaf 0`/`1`/`2` (reached two levels deep, through
   the *inner* node) is nonzero, while against `leaf 3`/`4` (direct
   leaf children) is zero -- the same "only one active branch, no
   cancellation" shape `single_link_composition_ne_zero` (cycle 9)
   captures for a 1-entry boundary, here for a 3-entry one where only
   one of the three branches happens to reach any given target. A
   general 3-entry `∂²` theorem (mirroring cycle 17's `two_link_*`
   construction) is a natural follow-up now that this is a second real
   3-entry instance (after `simplexIncidence.face`), but is not
   attempted here -- left as concrete `decide` witnesses, the same
   honest staging cycle 8 used for `natIncidence` before cycle 9
   generalized it. -/
def nestedIdx : List TreeId :=
  [TreeId.leaf 0, TreeId.leaf 1, TreeId.leaf 2, TreeId.leaf 3, TreeId.leaf 4,
   TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2),
   TreeId.node (TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2)) (TreeId.leaf 3) (TreeId.leaf 4)]

def outerTree : TreeId :=
  TreeId.node (TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2)) (TreeId.leaf 3) (TreeId.leaf 4)

theorem treeIncidence_nonleaf_composition_witness :
  boundary_composition treeIncidence nestedIdx outerTree (TreeId.leaf 0) = 1 := by
  decide

theorem treeIncidence_not_boundary_square_zero :
  verify_boundary_composition treeIncidence nestedIdx = false := by
  decide

/- Research cycle 30 (see RESEARCH_LOG.md): generalizes the concrete
   `treeIncidence_nonleaf_composition_witness` above into a real
   theorem, over *any* choice of the inner node's three children (not
   just `leaf 0`/`1`/`2`) and *any* two leaf-boundary outer siblings
   (not just `leaf 3`/`4`), using the new `three_link_composition_value`
   (root file) -- validating that general theorem against this
   instance, the second real 3-entry instance alongside
   `simplexIncidence.face` that motivated building it in the first
   place. -/
theorem treeIncidence_node_x_boundary (idx : List TreeId) (x y z : TreeId)
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
  boundaryMatrix treeIncidence idx (TreeId.node x y z) x = 1 := by
  rw [boundaryMatrix_three_link treeIncidence idx (TreeId.node x y z) x y z
    { i := x, role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
    { i := y, role := TernaryRole.c2, sign := Sign.pos, mult := 1 }
    { i := z, role := TernaryRole.c3, sign := Sign.pos, mult := 1 }
    rfl rfl rfl rfl hxy hxz hyz x]
  simp [hxy, hxz]

/- The general shape behind `treeIncidence_nonleaf_composition_witness`:
   composing an outer node against the inner node's first child is
   nonzero for *any* well-formed choice of children, not just the one
   concrete instance checked by `decide`. -/
theorem treeIncidence_outer_composition_general (x y z d e : TreeId)
  (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
  (hnd : TreeId.node x y z ≠ d) (hne_ : TreeId.node x y z ≠ e) (hde : d ≠ e)
  (hdleaf : treeIncidence.boundary d = []) (heleaf : treeIncidence.boundary e = []) :
  boundary_composition treeIncidence [TreeId.node x y z, d, e]
    (TreeId.node (TreeId.node x y z) d e) x = 1 := by
  rw [three_link_composition_value treeIncidence [TreeId.node x y z, d, e]
    (TreeId.node (TreeId.node x y z) d e) (TreeId.node x y z) d e x
    { i := TreeId.node x y z, role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
    { i := d, role := TernaryRole.c2, sign := Sign.pos, mult := 1 }
    { i := e, role := TernaryRole.c3, sign := Sign.pos, mult := 1 }
    rfl rfl rfl rfl hnd hne_ hde]
  rw [treeIncidence_node_x_boundary [TreeId.node x y z, d, e] x y z hxy hxz hyz,
    boundaryMatrix_eq_zero_of_leaf treeIncidence [TreeId.node x y z, d, e] d x hdleaf,
    boundaryMatrix_eq_zero_of_leaf treeIncidence [TreeId.node x y z, d, e] e x heleaf]
  simp [hnd, hne_, Ne.symm hnd, Ne.symm hne_]

end IncidenceCore
