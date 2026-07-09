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

/- Research cycle 12 (see RESEARCH_LOG.md): tried to validate cycle 4's
   general faithfulness theorem against `simplexIncidence` as a third,
   genuinely 3-graded (vertex/edge/face) data point -- and hit a real
   surprise instead of a confirmation. `v0`, `v1`, `v2` all have empty
   boundary with *no* structure distinguishing one from another (unlike
   `natIncidence`'s `0`, uniquely the only empty-boundary element in its
   chain). This is exactly cycle 2's "flat atoms collapse" pattern,
   independently rediscovered in a third, structurally unrelated
   instance -- not a Peano/Pairs-specific quirk, but a general
   phenomenon whenever an `Incidence` has *multiple* elements sharing
   empty (or otherwise identical) boundary. -/
theorem simplexIncidence_vertices_collapse :
  approxBisim simplexIncidence SimplexId.v0 SimplexId.v1 := by
  refine ⟨fun x y =>
    (x = SimplexId.v0 ∨ x = SimplexId.v1 ∨ x = SimplexId.v2) ∧
    (y = SimplexId.v0 ∨ y = SimplexId.v1 ∨ y = SimplexId.v2), ?_, ?_⟩
  · intro x y ⟨hx, hy⟩
    refine ⟨rfl, ?_, ?_⟩ <;>
      (rcases hx with hx | hx | hx <;> subst hx <;>
       rcases hy with hy | hy | hy <;> subst hy <;>
        simp [simplexIncidence, simplexBoundary])
  · exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩

theorem simplexIncidence_vertices_not_eq :
  (SimplexId.v0 : SimplexId) ≠ SimplexId.v1 := by simp

/- Research cycle 18 (see RESEARCH_LOG.md): the collapse conjectured
   here in cycle 12 -- confirmed, on the third attempt, with a
   genuinely different strategy rather than a third repeat of the
   hand-rolled existential case split that stalled twice before. The
   relation below relates any two vertices to each other AND any two
   edges to each other (leaving `face` untouched); `boundaryMatched` for
   an edge pair then reduces to exhibiting the positional pairing
   between their two boundary entries and invoking the root file's new
   `boundaryMatched_of_two_entries`/`boundaryMatched_symm` (cycle 18)
   instead of unfolding existentials by hand. -/
def simplexEdgeVertexRel (x y : SimplexId) : Prop :=
  (x = SimplexId.v0 ∨ x = SimplexId.v1 ∨ x = SimplexId.v2) ∧
  (y = SimplexId.v0 ∨ y = SimplexId.v1 ∨ y = SimplexId.v2) ∨
  (x = SimplexId.e01 ∨ x = SimplexId.e02 ∨ x = SimplexId.e12) ∧
  (y = SimplexId.e01 ∨ y = SimplexId.e02 ∨ y = SimplexId.e12)

theorem simplexEdgeVertexRel_symm : ∀ a b, simplexEdgeVertexRel a b → simplexEdgeVertexRel b a := by
  intro a b h
  unfold simplexEdgeVertexRel at h ⊢
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨hb, ha⟩
  · exact Or.inr ⟨hb, ha⟩

theorem simplexCompat_refl (e : Endpoint SimplexId SimplexRole) :
  boundaryCompatible simplexIncidence e e := ⟨rfl, rfl, rfl⟩

/- The vertex case is vacuous (both boundaries empty, as in cycle 12's
   proof); the edge case is nine ordered pairs, each closed by a direct
   `boundaryMatched_of_two_entries` term (three "self" pairs, three
   canonical unordered pairs, and their three reverses via
   `boundaryMatched_symm`) -- `first | ... | ...` tries each candidate
   term per generated goal, so this is nine deterministic term-mode
   proofs, not a search. -/
theorem simplexEdgeVertexRel_isBisimulation :
  IsBisimulation simplexIncidence simplexEdgeVertexRel := by
  intro i j hij
  refine ⟨rfl, ?_⟩
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rcases hi with hi | hi | hi <;> subst hi <;> rcases hj with hj | hj | hj <;> subst hj <;>
      simp [boundaryMatched, simplexIncidence, simplexBoundary]
  · rcases hi with hi | hi | hi <;> subst hi <;> rcases hj with hj | hj | hj <;> subst hj <;>
      first
      | exact boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel _ _ _ _ _ _
          rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inl rfl⟩)
          (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩)
      | exact boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel _ _ _ _ _ _
          rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inl rfl⟩)
          (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩)
      | exact boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel _ _ _ _ _ _
          rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩)
          (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩)
      | exact boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel
          SimplexId.e01 SimplexId.e02
          { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
          { i := SimplexId.v1, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
          { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
          { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
          rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inl rfl⟩)
          (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)
      | exact boundaryMatched_symm simplexIncidence simplexEdgeVertexRel _ _ simplexEdgeVertexRel_symm
          (boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel
            SimplexId.e01 SimplexId.e02
            { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
            { i := SimplexId.v1, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
            { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
            { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
            rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inl rfl⟩)
            (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩))
      | exact boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel
          SimplexId.e01 SimplexId.e12
          { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
          { i := SimplexId.v1, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
          { i := SimplexId.v1, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
          { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
          rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩)
          (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)
      | exact boundaryMatched_symm simplexIncidence simplexEdgeVertexRel _ _ simplexEdgeVertexRel_symm
          (boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel
            SimplexId.e01 SimplexId.e12
            { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
            { i := SimplexId.v1, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
            { i := SimplexId.v1, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
            { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
            rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩)
            (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩))
      | exact boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel
          SimplexId.e02 SimplexId.e12
          { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
          { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
          { i := SimplexId.v1, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
          { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
          rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩)
          (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩)
      | exact boundaryMatched_symm simplexIncidence simplexEdgeVertexRel _ _ simplexEdgeVertexRel_symm
          (boundaryMatched_of_two_entries simplexIncidence simplexEdgeVertexRel
            SimplexId.e02 SimplexId.e12
            { i := SimplexId.v0, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
            { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
            { i := SimplexId.v1, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
            { i := SimplexId.v2, role := SimplexRole.dst, sign := Sign.pos, mult := 1 }
            rfl rfl (simplexCompat_refl _) (Or.inl ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩)
            (simplexCompat_refl _) (Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩))

theorem simplexIncidence_edges_collapse :
  approxBisim simplexIncidence SimplexId.e01 SimplexId.e02 := by
  refine ⟨simplexEdgeVertexRel, simplexEdgeVertexRel_isBisimulation, ?_⟩
  exact Or.inr ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩

theorem simplexIncidence_edges_not_eq :
  (SimplexId.e01 : SimplexId) ≠ SimplexId.e02 := by simp

end IncidenceCore
