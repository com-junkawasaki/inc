import IncidenceTheory.GraphModel

/- Merkle-ID: implementation.graph_model.simplex
   story.jsonnet → implementation.nodes.simplex
   Research cycle 11 (see RESEARCH_LOG.md): cycles 8-10 charted the two
   extremes of ∂² = 0 -- single-face chains always fail (cycle 9), and
   leaf-reaching boundaries always trivially succeed (cycle 10, for the
   "nothing beyond dimension 0" reason). This is the genuine middle
   ground: a *multi-face* element (cycle 9's impossibility doesn't
   apply) whose faces are *not* leaves (cycle 10's sufficiency doesn't
   apply either) -- a real filled 2-simplex, built with the classical
   simplicial alternating-sum boundary convention
   (`∂[0,1,2] = [1,2] - [0,2] + [0,1]`), which is exactly what makes
   `∂² = 0` a theorem (not an accident) in real simplicial homology.

   Checked empirically first (`#eval`) before formalizing, per this
   project's established discipline: `simplexIncidence` (the correct
   alternating convention) satisfies `∂² = 0` genuinely -- not via
   dimension exhaustion, but via real term-by-term cancellation, e.g.
   `∂∂(face, v0) = (+1)·(0) + (-1)·(-1) + (+1)·(-1) = 0`. `wrongSimplexIncidence`
   (the same shape with the alternation dropped, all `+`) *fails*
   (`-2`, `0`, `2` at the three vertices) -- confirming the alternating
   convention is load-bearing, not incidental: this codebase's
   `boundaryMatrix`/`Int`-multiplication machinery does reproduce the
   classical mechanism when the construction is right, and does not
   paper over a wrong one. -/

namespace IncidenceCore

inductive SimplexRole where | src | dst
deriving DecidableEq, Repr

inductive SimplexId where
  | v0 | v1 | v2
  | e01 | e02 | e12
  | face
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.simplex.boundary
   Vertices are leaves; edges are ∂[i,j] = [j] - [i]; face is the
   standard alternating sum ∂[0,1,2] = [1,2] - [0,2] + [0,1]. -/
def simplexBoundary : SimplexId → Boundary SimplexId SimplexRole
  | SimplexId.v0 => []
  | SimplexId.v1 => []
  | SimplexId.v2 => []
  | SimplexId.e01 =>
    [ { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
    , { i := SimplexId.v1, role := SimplexRole.dst, sign := Sign.pos, mult := 1 } ]
  | SimplexId.e02 =>
    [ { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
    , { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 } ]
  | SimplexId.e12 =>
    [ { i := SimplexId.v1, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
    , { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 } ]
  | SimplexId.face =>
    [ { i := SimplexId.e12, role := SimplexRole.src, sign := Sign.pos, mult := 1 }
    , { i := SimplexId.e02, role := SimplexRole.dst, sign := Sign.neg, mult := 1 }
    , { i := SimplexId.e01, role := SimplexRole.dst, sign := Sign.pos, mult := 1 } ]

def simplexIncidence : Incidence SimplexId SimplexRole GraphType where
  boundary := simplexBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = SimplexId.v0 then some j else some i
  unit     := SimplexId.v0
  guards   := Guards.permissive SimplexId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [simplexBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  multiplicities := by
    intro i e h
    cases i <;> simp [simplexBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [simplexBoundary] at he <;>
      first
        | (rcases he with he | he | he <;> subst he <;> simp_all)
        | (rcases he with he | he <;> subst he <;> simp_all)
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = SimplexId.v0 <;> simp [h]
  type_preserve := fun _ _ => rfl

def simplexIdx : List SimplexId :=
  [SimplexId.v0, SimplexId.v1, SimplexId.v2, SimplexId.e01, SimplexId.e02, SimplexId.e12, SimplexId.face]

/- Real cancellation, checked comprehensively (not just at `face`):
   the whole boundary-composition table is zero, matching classical
   simplicial homology. -/
theorem simplexIncidence_boundary_square_zero :
  verify_boundary_composition simplexIncidence simplexIdx = true := by
  decide

/- Sensitivity check: the same 3-face shape with the alternation
   dropped (all `+` on `face`'s boundary). -/
def wrongSimplexBoundary : SimplexId → Boundary SimplexId SimplexRole
  | SimplexId.face =>
    [ { i := SimplexId.e12, role := SimplexRole.src, sign := Sign.pos, mult := 1 }
    , { i := SimplexId.e02, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
    , { i := SimplexId.e01, role := SimplexRole.dst, sign := Sign.pos, mult := 1 } ]
  | i => simplexBoundary i

def wrongSimplexIncidence : Incidence SimplexId SimplexRole GraphType where
  boundary := wrongSimplexBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = SimplexId.v0 then some j else some i
  unit     := SimplexId.v0
  guards   := Guards.permissive SimplexId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [wrongSimplexBoundary, simplexBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  multiplicities := by
    intro i e h
    cases i <;> simp [wrongSimplexBoundary, simplexBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [wrongSimplexBoundary, simplexBoundary] at he <;>
      first
        | (rcases he with he | he | he <;> subst he <;> simp_all)
        | (rcases he with he | he <;> subst he <;> simp_all)
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = SimplexId.v0 <;> simp [h]
  type_preserve := fun _ _ => rfl

/- The alternating sign is load-bearing, not incidental: drop it and
   ∂² ≠ 0 -- a concrete witness at v0. -/
theorem wrongSimplexIncidence_not_boundary_square_zero :
  verify_boundary_composition wrongSimplexIncidence simplexIdx = false := by
  decide

theorem wrongSimplexIncidence_witness :
  boundary_composition wrongSimplexIncidence simplexIdx SimplexId.face SimplexId.v0 = -2 := by
  decide

end IncidenceCore
