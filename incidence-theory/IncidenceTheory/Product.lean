import IncidenceTheory.Peano

/- Merkle-ID: implementation.graph_model.product
   story.jsonnet → implementation.nodes.product
   Research cycle 31 (see RESEARCH_LOG.md): every construction in this
   project up to this point built a specific *instance* of `Incidence`
   (naturals, pairs, paths, a simplex, a cycle, a tree) -- a model
   chosen by hand for a particular carrier type. This file does
   something categorically different: a *generic constructor*,
   `incidenceProd`, that takes *any* two `Incidence` structures and
   produces a third, proving all seven structural obligations once, for
   every pair of instances, rather than per-instance. This is the first
   concrete milestone toward the much larger, originally-deferred
   research question (can Inc's primitive vocabulary -- `boundary`,
   `glue`, `≈` -- support type-theoretic connectives *internally*,
   generically, rather than only modeling specific mathematical objects
   as one-off instances?). Scoped deliberately to the single simplest
   connective (a product/pair-type-style constructor), not the whole
   vision (functions, dependent types, identity types, induction) --
   the same discipline that turned the original, much larger question
   into the tractable `natIncidence` instance at the very start of this
   project's history.

   Construction: `(i1, i2) : I1 × I2`'s boundary is `i1`'s boundary
   (in `inc1`) transported into the product with a `Sum.inl`-tagged
   role, *plus* `i2`'s boundary (in `inc2`) transported with a
   `Sum.inr`-tagged role -- the standard "box product" shape from
   algebraic topology (a product complex's boundary touches `(∂i1, i2)`
   and `(i1, ∂i2)`). `glue`/`unit`/`guards` combine componentwise. Every
   one of the seven proof obligations reduces directly to the
   corresponding obligation of `inc1` or `inc2` (whichever side an
   entry or the gluing outcome came from) -- proven *once*, generically,
   using only the `Incidence` interface, not by inspecting any specific
   `inc1`/`inc2`. -/

namespace IncidenceCore

def prodBoundary {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
  (I1 × I2) → Boundary (I1 × I2) (R1 ⊕ R2)
  | (i1, i2) =>
    (inc1.boundary i1).map (fun e =>
      ({ i := (e.i, i2), role := Sum.inl e.role, sign := e.sign, mult := e.mult } :
        Endpoint (I1 × I2) (R1 ⊕ R2))) ++
    (inc2.boundary i2).map (fun e =>
      ({ i := (i1, e.i), role := Sum.inr e.role, sign := e.sign, mult := e.mult } :
        Endpoint (I1 × I2) (R1 ⊕ R2)))

def prodGlue {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
  (I1 × I2) → (I1 × I2) → Option (I1 × I2)
  | (i1, i2), (j1, j2) =>
    match inc1.glue i1 j1, inc2.glue i2 j2 with
    | some k1, some k2 => some (k1, k2)
    | _, _ => none

/- The product's guards only allow gluing when *both* components'
   guards allow it -- not unconditionally permissive -- so that
   `type_preserve` can genuinely delegate to `inc1`/`inc2`'s own
   `type_preserve` obligations rather than assuming something about
   them that isn't given. -/
def prodGuards {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) : Guards (I1 × I2) where
  allow := fun (i1, i2) (j1, j2) => inc1.guards.allow i1 j1 && inc2.guards.allow i2 j2

def incidenceProd {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
  Incidence (I1 × I2) (R1 ⊕ R2) (T1 × T2) where
  boundary := prodBoundary inc1 inc2
  typeFunc := fun (i1, i2) => (inc1.typeFunc i1, inc2.typeFunc i2)
  glue := prodGlue inc1 inc2
  unit := (inc1.unit, inc2.unit)
  guards := prodGuards inc1 inc2
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := by
    intro (i1, i2) e he
    simp only [prodBoundary, List.mem_append, List.mem_map] at he
    rcases he with ⟨e', he', heq⟩ | ⟨e', he', heq⟩
    · subst heq; simp [inc1.type_consistent i1 e' he']
    · subst heq; simp [inc2.type_consistent i2 e' he']
  sign_rules := by
    intro i e he
    cases h : e.sign <;> simp
  multiplicities := by
    intro (i1, i2) e he
    simp only [prodBoundary, List.mem_append, List.mem_map] at he
    rcases he with ⟨e', he', heq⟩ | ⟨e', he', heq⟩
    · subst heq; exact inc1.multiplicities i1 e' he'
    · subst heq; exact inc2.multiplicities i2 e' he'
  well_founded := by
    intro i hex
    obtain ⟨i1, i2⟩ := i
    obtain ⟨e, he, hei⟩ := hex
    simp only [prodBoundary, List.mem_append, List.mem_map] at he
    rcases he with ⟨e', he', heq⟩ | ⟨e', he', heq⟩
    · subst heq
      simp at hei
      exact inc1.well_founded i1 ⟨e', he', hei⟩
    · subst heq
      simp at hei
      exact inc2.well_founded i2 ⟨e', he', hei⟩
  unit_left := by
    intro (i1, i2)
    simp [prodGlue, inc1.unit_left i1, inc2.unit_left i2]
  unit_right := by
    intro (i1, i2)
    simp [prodGlue, inc1.unit_right i1, inc2.unit_right i2]
  type_preserve := by
    intro (i1, i2) (j1, j2) (k1, k2) hallow hglue
    simp only [prodGuards, Bool.and_eq_true] at hallow
    simp only [prodGlue] at hglue
    rcases hk1 : inc1.glue i1 j1 with _ | k1' <;> rcases hk2 : inc2.glue i2 j2 with _ | k2' <;>
      simp [hk1, hk2] at hglue
    obtain ⟨hk1eq, hk2eq⟩ := hglue
    subst hk1eq; subst hk2eq
    simp [inc1.type_preserve (i:=i1) (j:=j1) (k:=k1') hallow.1 hk1,
      inc2.type_preserve (i:=i2) (j:=j2) (k:=k2') hallow.2 hk2]

theorem prodBoundary_mem_left {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (i1 : I1) (i2 : I2)
  (e1 : Endpoint I1 R1) (he1 : e1 ∈ inc1.boundary i1) :
  ({ i := (e1.i, i2), role := Sum.inl e1.role, sign := e1.sign, mult := e1.mult } :
    Endpoint (I1 × I2) (R1 ⊕ R2)) ∈ prodBoundary inc1 inc2 (i1, i2) := by
  simp only [prodBoundary, List.mem_append, List.mem_map]
  exact Or.inl ⟨e1, he1, rfl⟩

theorem prodBoundary_mem_right {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (i1 : I1) (i2 : I2)
  (e2 : Endpoint I2 R2) (he2 : e2 ∈ inc2.boundary i2) :
  ({ i := (i1, e2.i), role := Sum.inr e2.role, sign := e2.sign, mult := e2.mult } :
    Endpoint (I1 × I2) (R1 ⊕ R2)) ∈ prodBoundary inc1 inc2 (i1, i2) := by
  simp only [prodBoundary, List.mem_append, List.mem_map]
  exact Or.inr ⟨e2, he2, rfl⟩

/- The congruence/functoriality property expected of any genuine
   product construction: `≈` on the components implies `≈` on the
   product. Proved directly from the components' own witnessing
   relations (`rel1`, `rel2`) combined pointwise -- not via any
   instance-specific reasoning, matching the fully generic style of
   `incidenceProd` itself. -/
theorem incidenceProd_approxBisim_of_approxBisim
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {i1 j1 : I1} {i2 j2 : I2}
  (h1 : approxBisim inc1 i1 j1) (h2 : approxBisim inc2 i2 j2) :
  approxBisim (incidenceProd inc1 inc2) (i1, i2) (j1, j2) := by
  obtain ⟨rel1, hbisim1, hij1⟩ := h1
  obtain ⟨rel2, hbisim2, hij2⟩ := h2
  refine ⟨fun (a1, a2) (b1, b2) => rel1 a1 b1 ∧ rel2 a2 b2, ?_, hij1, hij2⟩
  intro a b hab
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨hr1, hr2⟩ := hab
  obtain ⟨htype1, hmatch1⟩ := hbisim1 a1 b1 hr1
  obtain ⟨htype2, hmatch2⟩ := hbisim2 a2 b2 hr2
  refine ⟨by simp [incidenceProd, htype1, htype2], ?_, ?_⟩
  · intro e he
    simp only [incidenceProd, prodBoundary, List.mem_append, List.mem_map] at he
    rcases he with ⟨e1, he1, heq⟩ | ⟨e2, he2, heq⟩
    · subst heq
      obtain ⟨e1', he1', hcompat1, hrel1'⟩ := hmatch1.left e1 he1
      exact ⟨{ i := (e1'.i, b2), role := Sum.inl e1'.role, sign := e1'.sign, mult := e1'.mult },
        prodBoundary_mem_left inc1 inc2 b1 b2 e1' he1',
        ⟨congrArg Sum.inl hcompat1.1, hcompat1.2⟩, hrel1', hr2⟩
    · subst heq
      obtain ⟨e2', he2', hcompat2, hrel2'⟩ := hmatch2.left e2 he2
      exact ⟨{ i := (b1, e2'.i), role := Sum.inr e2'.role, sign := e2'.sign, mult := e2'.mult },
        prodBoundary_mem_right inc1 inc2 b1 b2 e2' he2',
        ⟨congrArg Sum.inr hcompat2.1, hcompat2.2⟩, hr1, hrel2'⟩
  · intro e he
    simp only [incidenceProd, prodBoundary, List.mem_append, List.mem_map] at he
    rcases he with ⟨e1, he1, heq⟩ | ⟨e2, he2, heq⟩
    · subst heq
      obtain ⟨e1', he1', hcompat1, hrel1'⟩ := hmatch1.right e1 he1
      exact ⟨{ i := (e1'.i, a2), role := Sum.inl e1'.role, sign := e1'.sign, mult := e1'.mult },
        prodBoundary_mem_left inc1 inc2 a1 a2 e1' he1',
        ⟨congrArg Sum.inl hcompat1.1, hcompat1.2⟩, hrel1', hr2⟩
    · subst heq
      obtain ⟨e2', he2', hcompat2, hrel2'⟩ := hmatch2.right e2 he2
      exact ⟨{ i := (a1, e2'.i), role := Sum.inr e2'.role, sign := e2'.sign, mult := e2'.mult },
        prodBoundary_mem_right inc1 inc2 a1 a2 e2' he2',
        ⟨congrArg Sum.inr hcompat2.1, hcompat2.2⟩, hr1, hrel2'⟩

/- Concrete sanity check: `natIncidence × natIncidence`'s boundary at
   `(2, 3)` combines exactly one entry from each side (`natIncidence`'s
   own single-link chain shape at both `2` and `3`), and reflexivity
   (hence the congruence theorem above) is exercisable on a real
   instance, not just vacuously well-typed. -/
example : (prodBoundary natIncidence natIncidence (2, 3)).length = 2 := by decide

example : (incidenceProd natIncidence natIncidence).unit = (0, 0) := by decide

example : approxBisim (incidenceProd natIncidence natIncidence) (2, 3) (2, 3) :=
  approxBisim_refl _ _

example (h1 : approxBisim natIncidence 2 2) (h2 : approxBisim natIncidence 3 3) :
    approxBisim (incidenceProd natIncidence natIncidence) (2, 3) (2, 3) :=
  incidenceProd_approxBisim_of_approxBisim natIncidence natIncidence h1 h2

end IncidenceCore
