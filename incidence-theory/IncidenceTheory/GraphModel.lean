import IncidenceTheory
import IncidenceTheory.FiniteSet
import IncidenceTheory.HFSets
import IncidenceTheory.Logic

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
  glue     := fun i j => if i = default then some j else if j = default then some i else some i
  unit     := default
  guards   := { allow := fun _ _ => true }
  type_consistent := fun i e h => rfl
  sign_rules := fun i e h => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by simp
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = default <;> simp [h]
  type_preserve := by intro i j k _ _; rfl

/- Merkle-ID: foundation.logic
   reflexivity of bisimilarity for trivial model (from general lemma). -/
theorem approxBisim_refl_trivial (i : I) :
  approxBisim (trivialIncidence : Incidence I GraphRole GraphType) i i :=
  approxBisim_refl _ _

theorem trivial_boundary_square_zero (idx : List I) :
    boundarySquareZero (trivialIncidence : Incidence I GraphRole GraphType) idx := by
  apply empty_boundaries_square_zero
  intro i
  rfl

theorem trivial_total_isBisimulation :
    IsBisimulation (trivialIncidence : Incidence I GraphRole GraphType) (fun _ _ => True) := by
  intro i j hij
  refine ⟨rfl, ?_⟩
  simp [boundaryMatched, trivialIncidence]

theorem trivial_approxBisim_total (i j : I) :
    approxBisim (trivialIncidence : Incidence I GraphRole GraphType) i j :=
  ⟨(fun _ _ => True), trivial_total_isBisimulation, trivial⟩

def trivialLinearCompleteness (idx : List I) :
    LinearCompletenessSpec (trivialIncidence : Incidence I GraphRole GraphType) idx where
  complete := by
    intro i j h
    exact trivial_approxBisim_total i j

theorem trivial_glue_respects_approxBisim :
    GlueRespects (trivialIncidence : Incidence I GraphRole GraphType)
      (approxBisim (trivialIncidence : Incidence I GraphRole GraphType)) := by
  intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk₁ hk₂
  exact trivial_approxBisim_total k₁ k₂

end IncidenceCore

/- Merkle-ID: implementation.graph_model.simple
   A simple directed graph instance using the canonical API. -/

namespace IncidenceCore

inductive GraphRole where | src | dst
deriving DecidableEq, Repr

/- A finite, well-founded, nonempty-boundary model.  `root` has one endpoint
   (`leaf`), so this is not merely the empty-boundary model. -/
inductive FiniteIncidence where | leaf | root
deriving DecidableEq, Repr

def finiteRank : FiniteIncidence → Nat
  | .leaf => 0
  | .root => 1

def finiteBoundary : FiniteIncidence → Boundary FiniteIncidence GraphRole
  | .leaf => []
  | .root =>
      [{ i := .leaf, role := .src, sign := .pos, mult := 1, mult_pos := by omega }]

def finiteGlue : FiniteIncidence → FiniteIncidence → Option FiniteIncidence
  | .leaf, j => some j
  | .root, .leaf => some .root
  | .root, .root => some .root

theorem finiteBoundary_decreases :
    ∀ i e, e ∈ finiteBoundary i → finiteRank e.i < finiteRank i := by
  intro i e he
  cases i with
  | leaf => simp [finiteBoundary] at he
  | root =>
    simp [finiteBoundary] at he
    rcases he with rfl
    simp [finiteRank]

def finiteIncidence : Incidence FiniteIncidence GraphRole GraphType where
  boundary := finiteBoundary
  typeFunc := fun _ => GraphType.unit
  glue := finiteGlue
  unit := .leaf
  guards := Guards.permissive FiniteIncidence
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro i e he; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    intro i ⟨e, he, hei⟩
    cases i with
    | leaf => simp [finiteBoundary] at he
    | root =>
      simp [finiteBoundary] at he
      rcases he with rfl
      simp at hei
  unit_left := by intro i; cases i <;> rfl
  unit_right := by intro i; cases i <;> rfl
  type_preserve := by intro i j k hallow hglue; rfl

theorem finiteGlue_associative (i j k : FiniteIncidence) :
    Option.bind (finiteGlue i j) (fun ij => finiteGlue ij k) =
      Option.bind (finiteGlue j k) (fun jk => finiteGlue i jk) := by
  cases i <;> cases j <;> cases k <;> rfl

/- Concrete witnesses for the layered A2/A6--A10 interfaces.  Those legacy
   interfaces use `Unit` as their endpoint-role parameter; this model is the
   role-erasure of the nonempty finite incidence model above. -/
def finiteUnitBoundary : FiniteIncidence → Boundary FiniteIncidence Unit
  | .leaf => []
  | .root =>
      [{ i := .leaf, role := (), sign := .pos, mult := 1, mult_pos := by omega }]

def finiteUnitGluing : IncidenceGluing FiniteIncidence GraphRole GraphType where
  boundary := finiteUnitBoundary
  typeFunc := fun _ => GraphType.unit
  type_consistent := by intro i e he; rfl
  glue := finiteGlue
  unit := .leaf
  unit_left := by intro i; cases i <;> rfl
  unit_right := by intro i; cases i <;> rfl
  associativity := finiteGlue_associative

def finiteUnitPreservation : IncidencePreservation FiniteIncidence GraphRole GraphType where
  toIncidenceGluing := finiteUnitGluing
  guards := Guards.permissive FiniteIncidence
  type_preserve := by intro i j k hallow hglue; rfl
  guard_preserve := by intro i j k hallow hglue; trivial

theorem finite_model_no_direct_boundary_cycle :
    ∀ i, ¬(∃ e ∈ finiteBoundary i, e.i = i) :=
  well_founded_theorem finiteBoundary finiteRank finiteBoundary_decreases

def finiteGluingSpec : GluingSpec finiteIncidence where
  unit_ok := fun i => ⟨finiteIncidence.unit_right i, finiteIncidence.unit_left i⟩
  type_preserve := fun _ _ => rfl
  assoc_when_ok := by
    intro i j k ij ijk jk _ hij _ hijk _ hjk _
    have hleft :
        Option.bind (finiteIncidence.glue i j) (fun x => finiteIncidence.glue x k) = some ijk := by
      simp [hij, hijk]
    have hright :
        Option.bind (finiteIncidence.glue j k) (fun x => finiteIncidence.glue i x) = some ijk := by
      change Option.bind (finiteGlue j k) (fun x => finiteGlue i x) = some ijk
      rw [← finiteGlue_associative i j k]
      change Option.bind (finiteGlue i j) (fun x => finiteGlue x k) = some ijk at hleft
      exact hleft
    simpa [hjk] using hright

def finiteIdx : List FiniteIncidence := [.leaf, .root]

def finiteAlgebraicModel : IncidenceAlgebraic FiniteIncidence GraphRole GraphType where
  toIncidencePreservation := finiteUnitPreservation
  boundaryMatrix := boundaryMatrix finiteIncidence finiteIdx
  laplacian := laplacian finiteIncidence finiteIdx

theorem finiteAlgebraic_boundaryMatrix :
    finiteAlgebraicModel.boundaryMatrix = boundaryMatrix finiteIncidence finiteIdx := rfl

theorem finiteAlgebraic_laplacian :
    finiteAlgebraicModel.laplacian = laplacian finiteIncidence finiteIdx := rfl

theorem finite_model_boundary_square_zero : boundarySquareZero finiteIncidence finiteIdx := by
  intro i k hi hk
  simp [finiteIdx] at hi hk
  rcases hi with rfl | rfl <;> rcases hk with rfl | rfl <;> native_decide

def finiteLinearCompleteness : LinearCompletenessSpec finiteIncidence finiteIdx where
  complete := by
    intro i j h
    cases i <;> cases j
    · exact approxBisim_refl finiteIncidence .leaf
    · have hsep := (h .leaf (by simp [finiteIdx])).left
      simp [boundaryMatrix, finiteIncidence, finiteBoundary] at hsep
    · have hsep := (h .leaf (by simp [finiteIdx])).left
      simp [boundaryMatrix, finiteIncidence, finiteBoundary] at hsep
    · exact approxBisim_refl finiteIncidence .root

theorem finite_linear_completeness {i j : FiniteIncidence}
    (h : sameLinearObservations finiteIncidence finiteIdx i j) :
    approxBisim finiteIncidence i j :=
  linear_completeness finiteLinearCompleteness h

def finiteLogicContext : List (IncidenceFormula FiniteIncidence) :=
  [.atom .root, .imp (.atom .root) (.atom .leaf)]

def finiteLogicDerivation : Derives finiteLogicContext (.atom .leaf) :=
  Derives.impE (p := Formula.atom FiniteIncidence.root)
    (q := Formula.atom FiniteIncidence.leaf)
    (Derives.ax (by simp [finiteLogicContext]))
    (Derives.ax (by simp [finiteLogicContext]))

theorem finiteLogic_modus_ponens_sound (valuation : FiniteIncidence → Prop)
    (holds : ContextSatisfies valuation finiteLogicContext) : valuation .leaf :=
  derives_sound finiteLogicDerivation holds

/- A finite extensional-set fragment: subsets of the two atoms `a` and `b`.
   A set incidence has exactly its members as boundary endpoints. -/
structure TwoSet where
  hasA : Bool
  hasB : Bool
deriving DecidableEq, Repr

def twoSetEmpty : TwoSet := { hasA := false, hasB := false }

def twoSetUnion (s t : TwoSet) : TwoSet :=
  { hasA := s.hasA || t.hasA, hasB := s.hasB || t.hasB }

inductive TwoAtom where | a | b
deriving DecidableEq, Repr

def twoSetContains (s : TwoSet) : TwoAtom → Bool
  | .a => s.hasA
  | .b => s.hasB

theorem twoSetUnion_contains (s t : TwoSet) (atom : TwoAtom) :
    twoSetContains (twoSetUnion s t) atom =
      (twoSetContains s atom || twoSetContains t atom) := by
  cases atom <;> rfl

theorem twoSetUnion_empty_left (s : TwoSet) : twoSetUnion twoSetEmpty s = s := by
  cases s with
  | mk hasA hasB => cases hasA <;> cases hasB <;> rfl

theorem twoSetUnion_empty_right (s : TwoSet) : twoSetUnion s twoSetEmpty = s := by
  cases s with
  | mk hasA hasB => cases hasA <;> cases hasB <;> rfl

theorem twoSetUnion_commutative (s t : TwoSet) : twoSetUnion s t = twoSetUnion t s := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;> rfl

theorem twoSetUnion_associative (s t u : TwoSet) :
    twoSetUnion (twoSetUnion s t) u = twoSetUnion s (twoSetUnion t u) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases u with
      | mk ua ub =>
        cases sa <;> cases sb <;> cases ta <;> cases tb <;>
          cases ua <;> cases ub <;> rfl

theorem twoSetUnion_idempotent (s : TwoSet) : twoSetUnion s s = s := by
  cases s with
  | mk hasA hasB => cases hasA <;> cases hasB <;> rfl

theorem twoSet_extensional (s t : TwoSet)
    (h : ∀ atom, twoSetContains s atom = twoSetContains t atom) : s = t := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      have ha := h TwoAtom.a
      have hb := h TwoAtom.b
      simp [twoSetContains] at ha hb
      cases ha
      cases hb
      rfl

inductive SetIncidence where
  | atomA
  | atomB
  | set (members : TwoSet)
deriving DecidableEq, Repr

def setBoundary : SetIncidence → Boundary SetIncidence GraphRole
  | .atomA | .atomB => []
  | .set members =>
      (if members.hasA then
        [{ i := .atomA, role := .src, sign := .pos, mult := 1, mult_pos := by omega }]
       else []) ++
      (if members.hasB then
        [{ i := .atomB, role := .src, sign := .pos, mult := 1, mult_pos := by omega }]
       else [])

def atomAEndpoint : Endpoint SetIncidence GraphRole :=
  { i := .atomA, role := .src, sign := .pos, mult := 1, mult_pos := by omega }

def atomBEndpoint : Endpoint SetIncidence GraphRole :=
  { i := .atomB, role := .src, sign := .pos, mult := 1, mult_pos := by omega }

theorem setBoundary_membership_atomA (s : TwoSet) :
    atomAEndpoint ∈ setBoundary (.set s) ↔ s.hasA = true := by
  cases s with
  | mk hasA hasB =>
    cases hasA <;> cases hasB <;> simp [setBoundary, atomAEndpoint]

theorem setBoundary_membership_atomB (s : TwoSet) :
    atomBEndpoint ∈ setBoundary (.set s) ↔ s.hasB = true := by
  cases s with
  | mk hasA hasB =>
    cases hasA <;> cases hasB <;> simp [setBoundary, atomBEndpoint]

theorem setBoundary_union_membership_atomA (s t : TwoSet) :
    atomAEndpoint ∈ setBoundary (.set (twoSetUnion s t)) ↔
      atomAEndpoint ∈ setBoundary (.set s) ∨ atomAEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;>
        simp [setBoundary, atomAEndpoint, twoSetUnion]

theorem setBoundary_union_membership_atomB (s t : TwoSet) :
    atomBEndpoint ∈ setBoundary (.set (twoSetUnion s t)) ↔
      atomBEndpoint ∈ setBoundary (.set s) ∨ atomBEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;>
        simp [setBoundary, atomBEndpoint, twoSetUnion]

def setRank : SetIncidence → Nat
  | .atomA | .atomB => 0
  | .set _ => 1

theorem setBoundary_decreases :
    ∀ i e, e ∈ setBoundary i → setRank e.i < setRank i := by
  intro i e he
  cases i with
  | atomA => simp [setBoundary] at he
  | atomB => simp [setBoundary] at he
  | set members =>
    cases members with
    | mk hasA hasB =>
      cases hasA <;> cases hasB <;> simp [setBoundary] at he
      all_goals rcases he with rfl | rfl <;> simp [setRank]

theorem set_boundary_extensional (s t : TwoSet) :
    setBoundary (.set s) = setBoundary (.set t) ↔ s = t := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;>
        simp [setBoundary]

theorem twoSetUnion_hasA (s t : TwoSet) :
    (twoSetUnion s t).hasA = (s.hasA || t.hasA) := rfl

theorem twoSetUnion_hasB (s t : TwoSet) :
    (twoSetUnion s t).hasB = (s.hasB || t.hasB) := rfl

def setGlue (i j : SetIncidence) : Option SetIncidence :=
  if i = .set twoSetEmpty then some j
  else if j = .set twoSetEmpty then some i
  else some i

def setIncidenceModel : Incidence SetIncidence GraphRole GraphType where
  boundary := setBoundary
  typeFunc := fun _ => GraphType.unit
  glue := setGlue
  unit := .set twoSetEmpty
  guards := Guards.permissive SetIncidence
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro i e he; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := well_founded_theorem setBoundary setRank setBoundary_decreases
  unit_left := by intro i; simp [setGlue]
  unit_right := by
    intro i
    by_cases h : i = SetIncidence.set twoSetEmpty <;> simp [setGlue, h]
  type_preserve := by intro i j k hallow hglue; rfl

theorem setGlue_associative (i j k : SetIncidence) :
    Option.bind (setGlue i j) (fun ij => setGlue ij k) =
      Option.bind (setGlue j k) (fun jk => setGlue i jk) := by
  by_cases hi : i = SetIncidence.set twoSetEmpty <;>
    by_cases hj : j = SetIncidence.set twoSetEmpty <;>
    by_cases hk : k = SetIncidence.set twoSetEmpty <;>
    simp [setGlue, hi, hj, hk]

/- Hereditarily finite set syntax as a genuinely recursive incidence model.
   Its structural boundary is distinct from extensional set membership. -/
def hfBoundary : HFSet → Boundary HFSet GraphRole
  | .empty => []
  | .insert head tail =>
      [ { i := head, role := .src, sign := .pos, mult := 1, mult_pos := by omega }
      , { i := tail, role := .dst, sign := .pos, mult := 1, mult_pos := by omega } ]

theorem hfBoundary_decreases :
    ∀ i e, e ∈ hfBoundary i → e.i.rank < i.rank := by
  intro i e he
  cases i with
  | empty => simp [hfBoundary] at he
  | insert head tail =>
    simp [hfBoundary] at he
    rcases he with rfl | rfl
    · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

def hfGlue (i j : HFSet) : Option HFSet :=
  if i = .empty then some j else if j = .empty then some i else some i

def hfIncidence : Incidence HFSet GraphRole GraphType where
  boundary := hfBoundary
  typeFunc := fun _ => GraphType.unit
  glue := hfGlue
  unit := .empty
  guards := Guards.permissive HFSet
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro i e he; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := well_founded_theorem hfBoundary HFSet.rank hfBoundary_decreases
  unit_left := by intro i; simp [hfGlue]
  unit_right := by
    intro i
    by_cases h : i = HFSet.empty <;> simp [hfGlue, h]
  type_preserve := by intro i j k hallow hglue; rfl

theorem hfGlue_associative (i j k : HFSet) :
    Option.bind (hfGlue i j) (fun ij => hfGlue ij k) =
      Option.bind (hfGlue j k) (fun jk => hfGlue i jk) := by
  by_cases hi : i = HFSet.empty <;> by_cases hj : j = HFSet.empty <;>
    by_cases hk : k = HFSet.empty <;> simp [hfGlue, hi, hj, hk]

/- Graph with nodes and edges as incidences. We take I as a sum of Node | Edge. -/
inductive GId where | node (n : Nat) | edge (e : Nat)
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.simple.boundary
   Boundary encodes endpoints for edges; nodes have empty boundary. -/
def graphBoundary : GId → Boundary GId GraphRole
  | GId.node _ => []
  | GId.edge 0  => []
  | GId.edge (Nat.succ _) => []

/- Merkle-ID: implementation.graph_model.simple.incidence
   Minimal graph incidence with empty boundaries. -/
def graphIncidence : Incidence GId GraphRole GraphType where
  boundary := graphBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = (GId.node 0) then some j else some i
  unit     := GId.node 0
  guards   := { allow := fun _ _ => true }
  type_consistent := fun i e h => rfl
  sign_rules := fun i e h => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    intro i ⟨e, he, _⟩
    cases i with
    | node n => simp [graphBoundary] at he
    | edge n => cases n <;> simp [graphBoundary] at he
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = GId.node 0 <;> simp [h]
  type_preserve := by intro i j k _ _; rfl

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
      [ { i := A, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega }
      , { i := B, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ]
  | GId.edge 2 =>  -- BC: B → C
      [ { i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega }
      , { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ]
  | GId.edge 3 =>  -- CA: C → A
      [ { i := C, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega }
      , { i := A, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ]
  | _ => []

def triIncidence : Incidence GId GraphRole GraphType where
  boundary := triBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if h : i = A then some j else some i
  unit     := A
  guards   := { allow := fun _ _ => true }
  type_consistent := by intro i e h; rfl
  sign_rules := by intro i e h; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    intro i ⟨e, he, hei⟩
    cases i with
    | node n => simp [triBoundary] at he
    | edge n =>
      simp only [triBoundary] at he
      split at he <;> simp_all [A, B, C]
      all_goals
        rcases he with rfl | rfl <;> simp at hei
  unit_left := by
    intro i
    change (if A = A then some i else some A) = some i
    simp
  unit_right := by
    intro i
    change (if i = A then some A else some i) = some i
    by_cases h : i = A <;> simp [h]
  type_preserve := by intro i j k _ _; rfl

theorem tri_glue_associative (i j k : GId) :
    Option.bind (triIncidence.glue i j) (fun ij => triIncidence.glue ij k) =
      Option.bind (triIncidence.glue j k) (fun jk => triIncidence.glue i jk) := by
  by_cases hi : i = A <;> by_cases hj : j = A <;> simp [triIncidence, hi, hj]

def triGluingSpec : GluingSpec triIncidence where
  unit_ok := fun i => ⟨triIncidence.unit_right i, triIncidence.unit_left i⟩
  type_preserve := fun _ _ => rfl
  assoc_when_ok := by
    intro i j k ij ijk jk _ hij _ hijk _ hjk _
    have hleft :
        Option.bind (triIncidence.glue i j) (fun x => triIncidence.glue x k) = some ijk := by
      simp [hij, hijk]
    have hright :
        Option.bind (triIncidence.glue j k) (fun x => triIncidence.glue i x) = some ijk := by
      rw [← tri_glue_associative i j k]
      exact hleft
    simpa [hjk] using hright

/- Merkle-ID: implementation.linear_algebra
   Index set for matrix computations. -/
def triIdx : List GId := [A, B, C, AB, BC, CA]

/- Merkle-ID: implementation.linear_algebra
   Boundary matrix and Laplacian for the triangle. -/
def triB : Matrix GId GId Int := boundaryMatrix triIncidence triIdx
def triL : Matrix GId GId Int := laplacian triIncidence triIdx

/- Checked entries of the triangle's incidence matrix and Laplacian. -/
theorem triB_AB_A : triB AB A = -1 := by native_decide
theorem triB_AB_B : triB AB B = 1 := by native_decide
theorem triB_BC_B : triB BC B = -1 := by native_decide
theorem triB_BC_C : triB BC C = 1 := by native_decide
theorem triB_CA_C : triB CA C = -1 := by native_decide
theorem triB_CA_A : triB CA A = 1 := by native_decide

theorem triL_AA : triL A A = 2 := by native_decide
theorem triL_BB : triL B B = 2 := by native_decide
theorem triL_CC : triL C C = 2 := by native_decide

/- The finite triangle calculation used by the executable. -/
def triangle_boundary_composition (i k : GId) : Int :=
  triIdx.foldl (fun acc j => acc + triB i j * triB j k) 0

def triangle_square_zero_check : Bool :=
  triIdx.all (fun i => triIdx.all (fun k => triangle_boundary_composition i k = 0))

/- This is a concrete theorem, not an assumption about arbitrary incidences. -/
theorem triangle_boundary_square_zero : triangle_square_zero_check = true := by
  native_decide

theorem triangle_satisfies_boundarySquareZero : boundarySquareZero triIncidence triIdx := by
  intro i k hi hk
  simp [triIdx] at hi hk
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

/- A fully concrete T5 witness: the terminal category and its identity
   translation preserve its unique pushout. -/
def terminalCategory : IncCategory Unit where
  Hom := fun _ _ => Unit
  id := fun _ => ()
  comp := fun _ _ => ()
  id_comp := by intro a b f; rfl
  comp_id := by intro a b f; rfl
  assoc := by intro a b c d f g h; rfl

def terminalFunctor : IncFunctor terminalCategory terminalCategory where
  obj := id
  map := fun _ => ()
  map_id := by intro a; rfl
  map_comp := by intro a b c g f; rfl

def terminalCospan : MorphismCospan terminalCategory where
  a := ()
  b := ()
  c := ()
  left := ()
  right := ()

def terminalPushout : MorphismPushout terminalCospan where
  apex := ()
  inl := ()
  inr := ()
  commutes := rfl
  lift := fun _ _ _ _ => ()
  lift_inl := by intro q leftLeg rightLeg h; cases leftLeg; rfl
  lift_inr := by intro q leftLeg rightLeg h; cases rightLeg; rfl
  lift_unique := by intro q leftLeg rightLeg h mediator hl hr; cases mediator; rfl

def terminalFunctorPreservesPushout :
    PushoutPreserving terminalFunctor terminalPushout where
  mapped_pushout := terminalPushout
  apex_is_image := rfl

def terminal_translation_preserves_pushout :
    MorphismPushout (terminalFunctor.mapCospan terminalCospan) :=
  translation_preserves_pushout terminalPushout terminalFunctorPreservesPushout

/- A non-singleton object model using the triangle's incidence identifiers. -/
def triangleCategory : IncCategory GId where
  Hom := fun _ _ => Unit
  id := fun _ => ()
  comp := fun _ _ => ()
  id_comp := by intro a b f; rfl
  comp_id := by intro a b f; rfl
  assoc := by intro a b c d f g h; rfl

def triangleCospan : MorphismCospan triangleCategory where
  a := A
  b := A
  c := B
  left := ()
  right := ()

def trianglePushout : MorphismPushout triangleCospan where
  apex := B
  inl := ()
  inr := ()
  commutes := rfl
  lift := fun _ _ _ _ => ()
  lift_inl := by intro q leftLeg rightLeg h; cases leftLeg; rfl
  lift_inr := by intro q leftLeg rightLeg h; cases rightLeg; rfl
  lift_unique := by intro q leftLeg rightLeg h mediator hl hr; cases mediator; rfl

def triangleIdentityPreservesPushout :
    PushoutPreserving (IncFunctor.identity triangleCategory) trianglePushout where
  mapped_pushout := trianglePushout
  apex_is_image := rfl

def triangle_translation_preserves_pushout :
    MorphismPushout ((IncFunctor.identity triangleCategory).mapCospan triangleCospan) :=
  translation_preserves_pushout trianglePushout triangleIdentityPreservesPushout

def terminalSetCospan : Cospan Unit where
  a := ()
  b := ()
  c := ()
  left := id
  right := id

def terminalSetPushout : PushoutWitness terminalSetCospan where
  apex := ()
  inl := id
  inr := id
  commutes := by intro x; rfl
  lift := fun _ _ _ => id
  lift_inl := by
    intro leftLeg rightLeg h x
    cases x
    cases leftLeg ()
    rfl
  lift_inr := by
    intro leftLeg rightLeg h x
    cases x
    cases rightLeg ()
    rfl
  lift_unique := by
    intro leftLeg rightLeg h mediator hl hr
    funext x
    cases x
    cases mediator ()
    rfl

def terminalIncidencePushoutSpec :
    GluePushoutSpec (trivialIncidence : Incidence Unit GraphRole GraphType) where
  diagram := fun _ _ => terminalSetCospan
  witness := by
    intro i j k hglue
    cases i
    cases j
    cases k
    exact ⟨terminalSetPushout, rfl⟩

def terminal_glue_creates_pushout :
    { pushout : PushoutWitness (terminalIncidencePushoutSpec.diagram () ()) //
      pushout.apex = () } :=
  glue_creates_pushout terminalIncidencePushoutSpec rfl

end IncidenceCore
