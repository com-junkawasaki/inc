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

variable {I : Type u} [Inhabited I]

/- Merkle-ID: implementation.graph_model.trivial
   trivial incidence structure over roles = GraphRole. -/
def trivialIncidence : Incidence I GraphRole GraphType where
  boundary := fun _ => []
  typeFunc := fun _ => default
  glue     := fun i _ => some i
  unit     := default
  type_consistent := fun i e h => rfl
  sign_rules := fun i e h => by cases e.sign <;> simp

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

/- Merkle-ID: implementation.graph_model.simple.boundary
   Boundary encodes endpoints for edges; nodes have empty boundary. -/
def graphBoundary : GId → Boundary GId GraphRole
  | GId.node _ => []
  | GId.edge 0  => []
  | GId.edge (Nat.succ k) => []

/- Merkle-ID: implementation.graph_model.simple.incidence
   Minimal graph incidence (placeholder boundary; to be populated per example). -/
def graphIncidence : Incidence GId GraphRole GraphType where
  boundary := graphBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if h : i = (GId.node 1) then some j else some i -- temporary; replaced by triIncidence below
  unit     := GId.node 0
  type_consistent := fun i e h => rfl
  sign_rules := fun i e h => by cases e.sign <;> simp

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
  | GId.edge 1 =>
      [ { i := A, role := GraphRole.src, sign := Sign.pos, mult := 1 }
      , { i := B, role := GraphRole.dst, sign := Sign.pos, mult := 1 } ]
  | GId.edge 2 =>
      [ { i := B, role := GraphRole.src, sign := Sign.pos, mult := 1 }
      , { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1 } ]
  | GId.edge 3 =>
      [ { i := C, role := GraphRole.src, sign := Sign.pos, mult := 1 }
      , { i := A, role := GraphRole.dst, sign := Sign.pos, mult := 1 } ]
  | _ => []

def triIncidence : Incidence GId GraphRole GraphType where
  boundary := triBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if h : i = A then some j else some i
  unit     := A
  type_consistent := by intro i e h; rfl
  sign_rules := by intro i e h; cases e.sign <;> simp

/- GluingSpec instance for the triangle model (permissive guards; left-biased glue). -/
-- Instantiate permissive guards; model-specific laws can be added later.
def triGluingSpec : GluingSpec triIncidence :=
  {
    guards := Guards.permissive GId
  , unit_ok := by
      intro i
      constructor
      · rfl
      constructor
      · -- glue i unit = some i
        unfold Incidence.glue triIncidence
        dsimp
        by_cases h : i = A
        · -- i = unit ⇒ glue i unit = some unit = some i
          simpa [h]
        · -- i ≠ unit ⇒ glue i unit = some i
          simp [h]
      · -- glue unit i = some i
        unfold Incidence.glue triIncidence
        dsimp
        -- left is unit
        have : A = A := rfl
        simp [this]
  , type_preserve := by
      intro i j k hallow hglue
      -- typeFunc is constant ⇒ preserved
      rfl
  , guard_preserve := by
      intro i j k _ _; trivial
  , assoc_when_ok := by
      intro i j k ij ijk jk h1 h2 h3 h4
      -- Unfold glue and do case analysis on whether i = A
      unfold Incidence.glue at h1 h2 h3 h4
      dsimp at h1 h2 h3 h4
      -- Show both paths compute to the same result under our glue
      by_cases hi : i = A
      · -- i is unit: glue i j = j, so ij = j; ij ⬝ k = j ⬝ k; i ⬝ jk = jk; both equal
        subst hi
        -- From h1: ij = j
        simp at h1
        -- From h2: ijk = (if j = A then k else j)
        cases h1; clear h1
        -- Compute h2 and h3/h4 shapes
        by_cases hj : j = A
        · subst hj; simp at h2 h3 h4; cases h3; simpa using h2
        · simp [hj] at h2 h3 h4; cases h3; simpa using h2
      · -- i not unit: glue i j = i, so ij = i; ij ⬝ k = i; j ⬝ k = (if j = A then k else j); i ⬝ jk = i
        have hij : ij = i := by
          -- from h1
          simp [hi] at h1; exact h1
        have hijk : ijk = i := by
          -- from h2
          cases hij; simp [hi] at h2; exact h2
        -- Right path yields i regardless of jk because left is i ≠ A
        cases hijk; simp [hi] at h4; exact h4
  }

/- Merkle-ID: implementation.linear_algebra
   Index set for matrix computations. -/
def triIdx : List GId := [A, B, C, AB, BC, CA]

/- Merkle-ID: implementation.linear_algebra
   Boundary matrix and Laplacian for the triangle. -/
def triB : Matrix GId GId Int := boundaryMatrix triIncidence triIdx
def triL : Matrix GId GId Int := laplacian triIncidence triIdx

end IncidenceCore
