/-!
  A minimal concrete model instantiating the canonical Incidence API.
  This trivial model uses empty boundaries so that type and sign laws hold vacuously.
  It serves as a baseline to keep the library green while richer models are developed.
-/

namespace IncidenceCore

universe u

variable {I T : Type u} [Inhabited I] [Inhabited T]

/- A trivial incidence structure over roles = Unit. -/
def trivialIncidence : Incidence I Unit T where
  boundary := fun _ => []
  typeFunc := fun _ => default
  glue     := fun i _ => some i
  unit     := default
  type_consistent := by
    intro i e h
    cases h
  sign_rules := by
    intro i e h
    cases h

/- Reflexivity of bisimilarity for the trivial model (follows from general lemma). -/
theorem approxBisim_refl_trivial (i : I) :
  approxBisim (trivialIncidence : Incidence I Unit T) i i :=
  approxBisim_refl _ _

end IncidenceCore

/- A simple directed graph instance using the canonical API. -/

namespace IncidenceCore

inductive Role where | src | dst
deriving DecidableEq, Repr

/- Graph with nodes and edges as incidences. We take I as a sum of Node | Edge. -/
inductive GId where | node (n : Nat) | edge (e : Nat)
deriving DecidableEq, Repr

/- Boundary encodes endpoints for edges; nodes have empty boundary. -/
def graphBoundary : GId → Boundary GId Role
  | GId.node _ => []
  | GId.edge 0  => []
  | GId.edge (Nat.succ k) => []

/- Minimal graph incidence (placeholder boundary; to be populated per example). -/
def graphIncidence : Incidence GId Role Unit where
  boundary := graphBoundary
  typeFunc := fun _ => ()
  glue     := fun i _ => some i
  unit     := GId.node 0
  type_consistent := by
    intro i e h
    cases h
  sign_rules := by
    intro i e h
    cases h

/- Triangle example identifiers. -/
def A   : GId := GId.node 1
def B   : GId := GId.node 2
def C   : GId := GId.node 3
def AB  : GId := GId.edge 1
def BC  : GId := GId.edge 2
def CA  : GId := GId.edge 3

/- For the triangle, we override boundary function locally. -/
def triBoundary (i : GId) : Boundary GId Role :=
  match i with
  | GId.node _ => []
  | GId.edge 1 =>
      [ { i := A, role := Role.src, sign := Sign.pos, mult := 1 }
      , { i := B, role := Role.dst, sign := Sign.pos, mult := 1 } ]
  | GId.edge 2 =>
      [ { i := B, role := Role.src, sign := Sign.pos, mult := 1 }
      , { i := C, role := Role.dst, sign := Sign.pos, mult := 1 } ]
  | GId.edge 3 =>
      [ { i := C, role := Role.src, sign := Sign.pos, mult := 1 }
      , { i := A, role := Role.dst, sign := Sign.pos, mult := 1 } ]
  | _ => []

def triIncidence : Incidence GId Role Unit :=
  { graphIncidence with boundary := triBoundary }

/- GluingSpec instance for the triangle model (permissive guards; left-biased glue). -/
def triGluingSpec : GluingSpec triIncidence :=
  trivialGluingSpec triIncidence

/- Index set for matrix computations. -/
def triIdx : List GId := [A, B, C, AB, BC, CA]

/- Boundary matrix and Laplacian for the triangle. -/
def triB : Matrix GId GId Int := boundaryMatrix triIncidence triIdx
def triL : Matrix GId GId Int := laplacian triIncidence triIdx

end IncidenceCore
