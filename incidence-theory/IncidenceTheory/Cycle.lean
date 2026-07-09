import IncidenceTheory.GraphModel

/- Merkle-ID: implementation.graph_model.cycle
   story.jsonnet → implementation.nodes.cycle
   Research cycle 26 (see RESEARCH_LOG.md): every prior instance
   (`natIncidence`, `pairIncidenceChained`, `pathIncidenceChained`,
   `simplexIncidence`) is fundamentally *acyclic* -- a well-founded chain
   or a finite tree/simplex with at least one empty-boundary leaf. This
   file tests a genuinely different shape: a closed 4-cycle, `c0 → c3 →
   c2 → c1 → c0`, where *every* element has exactly one boundary entry
   and *none* has an empty one. `Incidence`'s own `well_founded` field
   (`∀ i, ¬∃ e ∈ boundary i, e.i = i`) only forbids a *direct* self-loop,
   not a longer cycle, so this is a legitimate, buildable instance, not
   a workaround.

   Two things this instance is built to test that no prior instance
   could: (1) does the "flat leaves collapse" pattern (cycles 2/12/13/18
   -- multiple elements sharing *identical* boundary structure become
   `≈`-related) generalize beyond *shared emptiness* specifically, to
   *any* uniform boundary shape lacking a well-founded anchor? (2) `glue`
   here is genuine `Z/4Z` addition -- the first *group*-structured `glue`
   in this project (commutative, every element invertible), unlike
   `natIncidence`'s infinite monoid or the left-biased *non-group*
   selection every other instance used. -/

namespace IncidenceCore

inductive CycleRole where | chain
deriving DecidableEq, Repr

inductive CycleId where | c0 | c1 | c2 | c3
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.cycle.boundary
   Every element points to its cyclic predecessor -- no base case,
   unlike every prior chain-shaped instance. -/
def cyclePred : CycleId → CycleId
  | .c0 => .c3
  | .c1 => .c0
  | .c2 => .c1
  | .c3 => .c2

def cycleBoundary : CycleId → Boundary CycleId CycleRole
  | ci => [{ i := cyclePred ci, role := CycleRole.chain, sign := Sign.neg, mult := 1 }]

def cycleToNat : CycleId → Nat
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3

def cycleOfNat : Nat → CycleId
  | 0 => .c0 | 1 => .c1 | 2 => .c2 | _ => .c3

/- `Z/4Z` addition -- a genuine finite group, the first `glue` in this
   project with inverses (see `cycleIncidence_glue_has_inverse` below). -/
def cycleAdd (x y : CycleId) : CycleId := cycleOfNat ((cycleToNat x + cycleToNat y) % 4)

def cycleIncidence : Incidence CycleId CycleRole GraphType where
  boundary := cycleBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => some (cycleAdd i j)
  unit     := CycleId.c0
  guards   := Guards.permissive CycleId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [cycleBoundary] at h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i <;> simp [cycleBoundary] at h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [cycleBoundary, cyclePred] at he <;> subst he <;> simp_all
  unit_left := by intro i; cases i <;> simp [cycleAdd, cycleToNat, cycleOfNat]
  unit_right := by intro i; cases i <;> simp [cycleAdd, cycleToNat, cycleOfNat]
  type_preserve := fun _ _ => rfl

def cycleIdx : List CycleId := [CycleId.c0, CycleId.c1, CycleId.c2, CycleId.c3]

/- ∂² still fails here, exactly as `single_link_composition_ne_zero`
   (cycle 9) predicts for any single-link chain -- the general theorem
   applies "for free" to a cyclic instance too, not just linear ones
   (`natIncidence`, `pathIncidenceChained`'s nodes, `pairIncidenceChained`'s
   atoms). Not a new phenomenon, but worth confirming the theorem's
   reach isn't accidentally tied to acyclicity. -/
theorem cycleIncidence_c0_composition_ne_zero (idx : List CycleId) (hmem : CycleId.c3 ∈ idx) :
  boundary_composition cycleIncidence idx CycleId.c0 CycleId.c2 ≠ 0 :=
  single_link_composition_ne_zero cycleIncidence idx CycleId.c0 CycleId.c3 CycleId.c2
    { i := CycleId.c3, role := CycleRole.chain, sign := Sign.neg, mult := 1 }
    { i := CycleId.c2, role := CycleRole.chain, sign := Sign.neg, mult := 1 }
    rfl rfl (by simp)
    rfl rfl (by simp)
    hmem

theorem cycleIncidence_not_boundary_square_zero :
  verify_boundary_composition cycleIncidence cycleIdx = false := by decide

/- The genuinely new finding: the SAME "everything related to
   everything" relation cycles 2/12/13/18 used to collapse elements
   sharing *empty* boundary also witnesses a bisimulation here, where
   *no* element has empty boundary at all -- every element's single
   boundary entry has an identical shape (`chain`, `neg`, `1`), and that
   uniformity alone is enough: `boundaryMatched` only needs *some*
   compatible, related counterpart to exist, and the fully-related
   relation trivially supplies one regardless of which specific element
   it is. The "flat leaves collapse" pattern was never really about
   *emptiness* -- it's about *lacking a well-founded, distinguishing
   measure*, and a uniform cycle is a second, structurally different way
   to lack one. -/
theorem cycleIncidence_isBisimulation_full : IsBisimulation cycleIncidence (fun _ _ => True) := by
  intro i j _
  refine ⟨rfl, ?_, ?_⟩
  · intro e he
    cases i <;> simp [cycleIncidence, cycleBoundary] at he <;> subst he <;>
      exact ⟨{ i := cyclePred j, role := CycleRole.chain, sign := Sign.neg, mult := 1 },
        by simp [cycleIncidence, cycleBoundary], ⟨rfl, rfl, rfl⟩, trivial⟩
  · intro e he
    cases j <;> simp [cycleIncidence, cycleBoundary] at he <;> subst he <;>
      exact ⟨{ i := cyclePred i, role := CycleRole.chain, sign := Sign.neg, mult := 1 },
        by simp [cycleIncidence, cycleBoundary], ⟨rfl, rfl, rfl⟩, trivial⟩

/- ALL FOUR elements collapse into a single `≈`-class -- not merely
   "some pair", the strongest form of this pattern seen yet, since
   there's no substructure here at all (unlike `simplexIncidence`, where
   vertices/edges/face stayed separated by differing boundary shapes). -/
theorem cycleIncidence_all_collapse (x y : CycleId) : approxBisim cycleIncidence x y :=
  ⟨fun _ _ => True, cycleIncidence_isBisimulation_full, trivial⟩

theorem cycleIncidence_c0_ne_c1 : (CycleId.c0 : CycleId) ≠ CycleId.c1 := by simp

/- `glue` is commutative (`Z/4Z` addition) -- checked as a `decide`,
   the same way `natIncidence`'s commutativity was checked in cycle 1. -/
theorem cycleIncidence_glue_comm (x y : CycleId) :
  cycleIncidence.glue x y = cycleIncidence.glue y x := by
  cases x <;> cases y <;> decide

/- The genuinely new algebraic property: every element has an inverse
   (sums to `unit = c0`) -- no prior `glue` in this project had this
   (`natIncidence`'s addition has no inverses in `Nat`; every other
   instance's `glue` was left-biased selection, not a group operation at
   all). -/
theorem cycleIncidence_glue_has_inverse (x : CycleId) :
  ∃ y, cycleIncidence.glue x y = some CycleId.c0 := by
  cases x
  · exact ⟨CycleId.c0, by decide⟩
  · exact ⟨CycleId.c3, by decide⟩
  · exact ⟨CycleId.c2, by decide⟩
  · exact ⟨CycleId.c1, by decide⟩

end IncidenceCore
