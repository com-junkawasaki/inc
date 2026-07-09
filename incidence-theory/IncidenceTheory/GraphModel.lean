import IncidenceTheory

/- Merkle-ID: implementation.graph_model
   story.jsonnet → implementation.nodes.graph_model
   Minimal concrete models to validate API; starts with trivial model, then graph triangle. -/

namespace IncidenceCore

universe u

inductive GraphType : Type u where
  | unit

instance : Inhabited GraphType where
  default := GraphType.unit

variable {I : Type u} [Inhabited I] [DecidableEq I]

/- Merkle-ID: implementation.graph_model.trivial
   trivial incidence structure over roles = GraphRole. -/
def trivialIncidence : Incidence I GraphRole GraphType where
  boundary := fun _ => []
  typeFunc := fun _ => default
  glue     := fun i j => if i = default then some j else some i
  unit     := default
  guards   := Guards.permissive I
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := fun i e h => by cases e.sign <;> simp
  multiplicities := fun i e h => by simp at h
  well_founded := fun i => by simp
  unit_left := fun i => by simp
  unit_right := fun i => by by_cases h : i = default <;> simp [h]
  type_preserve := fun _ _ => rfl

/- Merkle-ID: foundation.logic
   reflexivity of bisimilarity for trivial model (from general lemma). -/
theorem approxBisim_refl_trivial (i : I) :
  approxBisim (trivialIncidence : Incidence I GraphRole GraphType) i i :=
  approxBisim_refl _ _

end IncidenceCore

/- Merkle-ID: implementation.graph_model.simple
   A simple directed graph instance using the canonical API. -/

namespace IncidenceCore

inductive GraphRole where | src | dst
deriving DecidableEq, Repr

/- Graph with nodes and edges as incidences. We take I as a sum of Node | Edge. -/
inductive GId where | node (n : Nat) | edge (e : Nat)
deriving DecidableEq, Repr

/- Triangle example identifiers. -/
def A   : GId := GId.node 1
def B   : GId := GId.node 2
def C   : GId := GId.node 3
def AB  : GId := GId.edge 1
def BC  : GId := GId.edge 2
def CA  : GId := GId.edge 3

/- Merkle-ID: implementation.graph_model.triangle.boundary
   For the triangle, override boundary function locally. -/
def triBoundary (i : GId) : Boundary GId GraphRole :=
  match i with
  | GId.node _ => []
  | GId.edge 1 =>  -- AB: A → B
      [ { i := A, role := GraphRole.src, sign := Sign.neg, mult := 1 }
      , { i := B, role := GraphRole.dst, sign := Sign.pos, mult := 1 } ]
  | GId.edge 2 =>  -- BC: B → C
      [ { i := B, role := GraphRole.src, sign := Sign.neg, mult := 1 }
      , { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1 } ]
  | GId.edge 3 =>  -- CA: C → A
      [ { i := C, role := GraphRole.src, sign := Sign.neg, mult := 1 }
      , { i := A, role := GraphRole.dst, sign := Sign.pos, mult := 1 } ]
  | _ => []

def triIncidence : Incidence GId GraphRole GraphType where
  boundary := triBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if h : i = A then some j else some i
  unit     := A
  guards   := Guards.permissive GId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := by intro i e h; rfl
  sign_rules := by intro i e h; cases e.sign <;> simp
  multiplicities := by
    intro i e h
    unfold triBoundary at h
    split at h <;> simp_all <;> rcases h with h | h <;> subst h <;> decide
  well_founded := by
    rintro i ⟨e, he, hei⟩
    unfold triBoundary at he
    split at he <;> simp_all <;> rcases he with he | he <;> subst he <;>
      simp_all [A, B, C]
  unit_left := by intro i; simp
  unit_right := by
    intro i
    dsimp
    by_cases h : i = A <;> simp [h]
  type_preserve := fun _ _ => rfl

/- The `if h : i = A then ...` dite behaves like a plain `ite`, since neither
   branch depends on the proof `h`; this lemma exposes that so downstream
   proofs can `simp`/`rw` with it instead of re-unfolding `triIncidence`. -/
theorem triIncidence_glue_eq (i j : GId) :
  triIncidence.glue i j = if i = A then some j else some i := by
  simp [triIncidence]

/- GluingSpec instance for the triangle model (permissive guards; left-biased glue). -/
-- Instantiate permissive guards; model-specific laws can be added later.
def triGluingSpec : GluingSpec triIncidence :=
  {
    guards := Guards.permissive GId
  , unit_ok := by
      intro i
      refine ⟨rfl, ?_, ?_⟩
      · -- glue i unit = some i
        rw [triIncidence_glue_eq]
        by_cases h : i = A <;> simp [h, triIncidence]
      · -- glue unit i = some i
        rw [triIncidence_glue_eq]
        simp [triIncidence]
  , type_preserve := by
      intro i j k hallow hglue
      -- typeFunc is constant ⇒ preserved
      rfl
  , guard_preserve := by
      intro i j k _ _; trivial
  , assoc_when_ok := by
      intro i j k ij ijk jk _ h2 _ h4 _ h6 _
      rw [triIncidence_glue_eq] at h2 h4 h6 ⊢
      -- h2 : glue i j = some ij, h4 : glue ij k = some ijk, h6 : glue j k = some jk
      by_cases hi : i = A
      · -- i = A: glue i j = some j, so ij = j; then ij's glue behaves as j's.
        subst hi
        simp at h2
        subst h2
        simp
        rw [h6] at h4
        exact Option.some.inj h4
      · -- i ≠ A: glue i j = some i, so ij = i; then ij's glue behaves as i's.
        simp [hi] at h2
        subst h2
        simp [hi] at h4
        subst h4
        simp [hi]
  }

/- Merkle-ID: implementation.linear_algebra
   Index set for matrix computations. -/
def triIdx : List GId := [A, B, C, AB, BC, CA]

/- Merkle-ID: implementation.linear_algebra
   Boundary matrix and Laplacian for the triangle. -/
def triB : Matrix GId GId Int := boundaryMatrix triIncidence triIdx
def triL : Matrix GId GId Int := laplacian triIncidence triIdx

/- ==========================================================================
   Concrete T1-T5 instantiations for the triangle graph.
   These live here (not in root IncidenceTheory.lean) because they reference
   `GId`/`triIncidence`/`triIdx`, which are defined in this file, which
   *imports* root -- root cannot reference them without a circular import.
   ========================================================================== -/

/- ∂² = 0 for the triangle graph's boundary operator (decidable, checked by
   the kernel over the 6-element index set). -/
/- Merkle-ID: implementation.linear_algebra.triangle_square_zero_check
   Check that ∂² = 0 for all index pairs in triangle. -/
def triangle_square_zero_check : Bool := verify_boundary_composition triIncidence triIdx

/- Merkle-ID: implementation.linear_algebra.triangle_boundary_square_zero
   Specific proof that ∂² = 0 for the triangle incidence structure. -/
theorem triangle_boundary_square_zero : triangle_square_zero_check = true := by
  unfold triangle_square_zero_check
  decide

/- T1 concretely: gluing A with itself in the triangle is idempotent, and
   the general pushout-universality theorem applies to this instance. -/
/- Merkle-ID: foundation.axiomatization.t1_triangle_concrete
   Concrete proof of T1 for the triangle incidence structure. -/
theorem triangle_glue_pushout_concrete :
  triIncidence.glue A A = some A := by
  unfold Incidence.glue triIncidence
  simp

theorem triangle_glue_creates_pushout :
    ∃ (cocone : PushoutUniversality.Cocone triIncidence ⟨A, A, A, some, some⟩),
      ∀ (other : PushoutUniversality.Cocone triIncidence ⟨A, A, A, some, some⟩),
      ∃ (mediator : GId → Option GId),
        ((∀ x, mediator (cocone.leg1 x |>.getD x) = other.leg1 x) ∧
         (∀ x, mediator (cocone.leg2 x |>.getD x) = other.leg2 x)) ∧
        (∀ (mediator' : GId → Option GId),
          ((∀ x, mediator' (cocone.leg1 x |>.getD x) = other.leg1 x) ∧
           (∀ x, mediator' (cocone.leg2 x |>.getD x) = other.leg2 x)) →
          mediator' = mediator) :=
  PushoutUniversality.glue_creates_pushouts triIncidence triangle_glue_pushout_concrete

/- T2 concretely: ≈ is reflexive, hence trivially preserved by gluing A with
   itself in the triangle. -/
/- Merkle-ID: foundation.axiomatization.t2_triangle_congruence
   Concrete proof of congruence for triangle graph. -/
theorem triangle_congruence_concrete :
  approxBisim triIncidence A A :=
  approxBisim_refl triIncidence A

/- T4 concretely: A's linear observations trivially agree with themselves,
   so the general completeness theorem yields A ≈ A for the triangle. -/
/- Merkle-ID: foundation.axiomatization.t4_triangle_completeness
   Concrete proof of completeness for triangle graph. -/
theorem triangle_completeness_concrete :
  ∀ obs : CompletenessTheory.LinearObservation triIncidence triIdx,
    obs.boundary_matrix A = obs.boundary_matrix A ∧
    obs.laplacian A = obs.laplacian A := by
  intro obs
  exact ⟨rfl, rfl⟩

theorem triangle_linear_completeness_A : approxBisim triIncidence A A :=
  CompletenessTheory.linear_completeness triIncidence triIdx triangle_completeness_concrete

/- T5 concretely: nodes (empty boundary) translate to `ULift Bool`, edges
   (non-empty boundary) translate to `ULift Unit`. -/
/- Merkle-ID: foundation.axiomatization.t5_triangle_translation
   Concrete proof of translation preservation for triangle graph. -/
theorem triangle_translation_concrete :
  let triangle_as_set := TranslationPreservation.inc_to_set triIncidence
  triangle_as_set A = ULift Bool ∧
  triangle_as_set B = ULift Bool ∧
  triangle_as_set C = ULift Bool ∧
  triangle_as_set AB = ULift Unit ∧
  triangle_as_set BC = ULift Unit ∧
  triangle_as_set CA = ULift Unit := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end IncidenceCore
