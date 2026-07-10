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
      ({ i := (e.i, i2), role := Sum.inl e.role, sign := e.sign, mult := e.mult,
         mult_pos := e.mult_pos } :
        Endpoint (I1 × I2) (R1 ⊕ R2))) ++
    (inc2.boundary i2).map (fun e =>
      ({ i := (i1, e.i), role := Sum.inr e.role, sign := e.sign, mult := e.mult,
         mult_pos := e.mult_pos } :
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
  ({ i := (e1.i, i2), role := Sum.inl e1.role, sign := e1.sign, mult := e1.mult,
     mult_pos := e1.mult_pos } :
    Endpoint (I1 × I2) (R1 ⊕ R2)) ∈ prodBoundary inc1 inc2 (i1, i2) := by
  simp only [prodBoundary, List.mem_append, List.mem_map]
  exact Or.inl ⟨e1, he1, rfl⟩

theorem prodBoundary_mem_right {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (i1 : I1) (i2 : I2)
  (e2 : Endpoint I2 R2) (he2 : e2 ∈ inc2.boundary i2) :
  ({ i := (i1, e2.i), role := Sum.inr e2.role, sign := e2.sign, mult := e2.mult,
     mult_pos := e2.mult_pos } :
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
      exact ⟨{ i := (e1'.i, b2), role := Sum.inl e1'.role, sign := e1'.sign, mult := e1'.mult, mult_pos := e1'.mult_pos },
        prodBoundary_mem_left inc1 inc2 b1 b2 e1' he1',
        ⟨congrArg Sum.inl hcompat1.1, hcompat1.2⟩, hrel1', hr2⟩
    · subst heq
      obtain ⟨e2', he2', hcompat2, hrel2'⟩ := hmatch2.left e2 he2
      exact ⟨{ i := (b1, e2'.i), role := Sum.inr e2'.role, sign := e2'.sign, mult := e2'.mult, mult_pos := e2'.mult_pos },
        prodBoundary_mem_right inc1 inc2 b1 b2 e2' he2',
        ⟨congrArg Sum.inr hcompat2.1, hcompat2.2⟩, hr1, hrel2'⟩
  · intro e he
    simp only [incidenceProd, prodBoundary, List.mem_append, List.mem_map] at he
    rcases he with ⟨e1, he1, heq⟩ | ⟨e2, he2, heq⟩
    · subst heq
      obtain ⟨e1', he1', hcompat1, hrel1'⟩ := hmatch1.right e1 he1
      exact ⟨{ i := (e1'.i, a2), role := Sum.inl e1'.role, sign := e1'.sign, mult := e1'.mult, mult_pos := e1'.mult_pos },
        prodBoundary_mem_left inc1 inc2 a1 a2 e1' he1',
        ⟨congrArg Sum.inl hcompat1.1, hcompat1.2⟩, hrel1', hr2⟩
    · subst heq
      obtain ⟨e2', he2', hcompat2, hrel2'⟩ := hmatch2.right e2 he2
      exact ⟨{ i := (a1, e2'.i), role := Sum.inr e2'.role, sign := e2'.sign, mult := e2'.mult, mult_pos := e2'.mult_pos },
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

/- Research cycle 32 (see RESEARCH_LOG.md): cycle 31's congruence
   theorem only went one direction (`≈` on components ⇒ `≈` on the
   product). Does the CONVERSE hold -- does `≈` on the product force
   `≈` on both components, i.e. is the product's `≈` *exactly*
   componentwise `≈`, not merely implied by it? Given a witnessing
   relation `rel` for the product, its *projection* onto `I1`
   (`rel1 a1 b1 := ∃ a2 b2, rel (a1, a2) (b1, b2)`) turns out to itself
   be a bisimulation for `inc1` -- because `boundaryCompatible`
   requires *matching* `Sum.inl`/`Sum.inr` tags (a `Sum.inl`-tagged
   entry can never be compatible with a `Sum.inr`-tagged one), so any
   `boundaryMatched` witness for a left-tagged entry in the product must
   itself be left-tagged, i.e. come from `inc1`'s own boundary --
   `rel`'s own existentials supply the witnesses `rel1` needs directly,
   with no new machinery. Symmetric for `inc2`. -/
theorem incidenceProd_project
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {i1 j1 : I1} {i2 j2 : I2}
  (h : approxBisim (incidenceProd inc1 inc2) (i1, i2) (j1, j2)) :
  approxBisim inc1 i1 j1 ∧ approxBisim inc2 i2 j2 := by
  obtain ⟨rel, hbisim, hij⟩ := h
  constructor
  · refine ⟨fun a1 b1 => ∃ a2 b2, rel (a1, a2) (b1, b2), ?_, i2, j2, hij⟩
    intro a1 b1 ⟨a2, b2, hr⟩
    obtain ⟨htype, hmatch⟩ := hbisim (a1, a2) (b1, b2) hr
    refine ⟨by simpa using congrArg Prod.fst htype, ?_, ?_⟩
    · intro e1 he1
      obtain ⟨e', he', hcompat, hrel'⟩ := hmatch.left
        { i := (e1.i, a2), role := Sum.inl e1.role, sign := e1.sign, mult := e1.mult, mult_pos := e1.mult_pos }
        (prodBoundary_mem_left inc1 inc2 a1 a2 e1 he1)
      simp only [incidenceProd, prodBoundary, List.mem_append, List.mem_map] at he'
      rcases he' with ⟨e1', he1', heq⟩ | ⟨e2', he2', heq⟩
      · subst heq
        refine ⟨e1', he1', ?_, a2, b2, ?_⟩
        · exact ⟨(Sum.inl.injEq _ _).mp hcompat.1, hcompat.2⟩
        · simpa using hrel'
      · subst heq
        exfalso
        simp [boundaryCompatible] at hcompat
    · intro e1' he1'
      obtain ⟨e, he, hcompat, hrel'⟩ := hmatch.right
        { i := (e1'.i, b2), role := Sum.inl e1'.role, sign := e1'.sign, mult := e1'.mult, mult_pos := e1'.mult_pos }
        (prodBoundary_mem_left inc1 inc2 b1 b2 e1' he1')
      simp only [incidenceProd, prodBoundary, List.mem_append, List.mem_map] at he
      rcases he with ⟨e1, he1, heq⟩ | ⟨e2, he2, heq⟩
      · subst heq
        refine ⟨e1, he1, ?_, a2, b2, ?_⟩
        · exact ⟨(Sum.inl.injEq _ _).mp hcompat.1, hcompat.2⟩
        · simpa using hrel'
      · subst heq
        exfalso
        simp [boundaryCompatible] at hcompat
  · refine ⟨fun a2 b2 => ∃ a1 b1, rel (a1, a2) (b1, b2), ?_, i1, j1, hij⟩
    intro a2 b2 ⟨a1, b1, hr⟩
    obtain ⟨htype, hmatch⟩ := hbisim (a1, a2) (b1, b2) hr
    refine ⟨by simpa using congrArg Prod.snd htype, ?_, ?_⟩
    · intro e2 he2
      obtain ⟨e', he', hcompat, hrel'⟩ := hmatch.left
        { i := (a1, e2.i), role := Sum.inr e2.role, sign := e2.sign, mult := e2.mult, mult_pos := e2.mult_pos }
        (prodBoundary_mem_right inc1 inc2 a1 a2 e2 he2)
      simp only [incidenceProd, prodBoundary, List.mem_append, List.mem_map] at he'
      rcases he' with ⟨e1', he1', heq⟩ | ⟨e2', he2', heq⟩
      · subst heq
        exfalso
        simp [boundaryCompatible] at hcompat
      · subst heq
        refine ⟨e2', he2', ?_, a1, b1, ?_⟩
        · exact ⟨(Sum.inr.injEq _ _).mp hcompat.1, hcompat.2⟩
        · simpa using hrel'
    · intro e2' he2'
      obtain ⟨e, he, hcompat, hrel'⟩ := hmatch.right
        { i := (b1, e2'.i), role := Sum.inr e2'.role, sign := e2'.sign, mult := e2'.mult, mult_pos := e2'.mult_pos }
        (prodBoundary_mem_right inc1 inc2 b1 b2 e2' he2')
      simp only [incidenceProd, prodBoundary, List.mem_append, List.mem_map] at he
      rcases he with ⟨e1, he1, heq⟩ | ⟨e2, he2, heq⟩
      · subst heq
        exfalso
        simp [boundaryCompatible] at hcompat
      · subst heq
        refine ⟨e2, he2, ?_, a1, b1, ?_⟩
        · exact ⟨(Sum.inr.injEq _ _).mp hcompat.1, hcompat.2⟩
        · simpa using hrel'

/- The full characterization, upgrading cycle 31's one-directional
   congruence theorem into a genuine iff: the product's `≈` is *exactly*
   componentwise `≈`, no more and no less. -/
theorem incidenceProd_approxBisim_iff
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  (i1 j1 : I1) (i2 j2 : I2) :
  approxBisim (incidenceProd inc1 inc2) (i1, i2) (j1, j2) ↔
    approxBisim inc1 i1 j1 ∧ approxBisim inc2 i2 j2 :=
  ⟨incidenceProd_project inc1 inc2,
   fun ⟨h1, h2⟩ => incidenceProd_approxBisim_of_approxBisim inc1 inc2 h1 h2⟩

/- The payoff: faithfulness (`≈ ↔ =`) transports cleanly through the
   product whenever both factors are individually faithful -- answering
   the question cycle 31 queued but didn't check. Unlike `∂² = 0`, which
   the collapse-fix (cycles 8/16/27) provably could *never* preserve
   alongside faithfulness, `≈`-faithfulness itself transports through
   this construction with no cost at all. -/
theorem incidenceProd_faithful_of_faithful
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  (hf1 : ∀ x y : I1, approxBisim inc1 x y ↔ x = y)
  (hf2 : ∀ x y : I2, approxBisim inc2 x y ↔ x = y) :
  ∀ p q : I1 × I2, approxBisim (incidenceProd inc1 inc2) p q ↔ p = q := by
  intro (p1, p2) (q1, q2)
  rw [incidenceProd_approxBisim_iff, hf1, hf2]
  constructor
  · rintro ⟨rfl, rfl⟩; rfl
  · intro h; simp_all

/- Concrete confirmation: `natIncidence × natIncidence` is fully
   faithful, via the general theorem applied to `natIncidence`'s own
   faithfulness (cycle 4) twice -- not vacuous, a real instantiation. -/
example : ∀ p q : Nat × Nat, approxBisim (incidenceProd natIncidence natIncidence) p q ↔ p = q :=
  incidenceProd_faithful_of_faithful natIncidence natIncidence
    natIncidence_approxBisim_iff natIncidence_approxBisim_iff

/- Research cycle 34 (see RESEARCH_LOG.md): a T5-style translation
   result for `incidenceProd`, twice deferred (cycles 31, 32). Rather
   than build a one-off translation for `natIncidence × natIncidence`
   specifically, the natural GENERIC statement -- mirroring how
   `incidenceProd` itself is generic -- is: pairing two translations
   that each reflect their own instance's `≈` produces a translation
   that reflects `≈` on the product. This is a direct consequence of
   `incidenceProd_approxBisim_iff` (cycle 32) plus each translation's
   own reflection property, needing no new machinery. -/
theorem incidenceProd_translation_reflects
  {I1 S1 I2 S2 : Type u} [DecidableEq I1] [DecidableEq I2] {R1 T1 R2 T2 : Type u}
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  (t1 : I1 → S1) (t2 : I2 → S2)
  (ht1 : ∀ x y, t1 x = t1 y → approxBisim inc1 x y)
  (ht2 : ∀ x y, t2 x = t2 y → approxBisim inc2 x y)
  {p q : I1 × I2} (h : (t1 p.1, t2 p.2) = (t1 q.1, t2 q.2)) :
  approxBisim (incidenceProd inc1 inc2) p q := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  rw [incidenceProd_approxBisim_iff]
  exact ⟨ht1 p1 q1 h.1, ht2 p2 q2 h.2⟩

/- While instantiating the generic theorem against `natToFiniteSet`
   (cycle 5), a second, independent question arose: does
   `natToFiniteSet` -- built and checked for injectivity only, back
   when no `glue` in this project had algebraic structure worth
   checking against a translation -- happen to *also* be a
   `glue`-homomorphism, the same lens cycle 28 first applied to
   `cycleToNat`? Checked empirically first (`#eval`,
   `natToFiniteSet 3 ++ natToFiniteSet 4 == natToFiniteSet 7` and two
   more concrete cases): all agreed. Proof needed induction on the
   *first* summand (`Nat.succ_add`, not `Nat.add_succ`) to line up with
   `List.cons_append`'s associativity -- the first induction attempt
   (on the second summand) produced a residual (`a :: (xs ++ ys) = xs
   ++ a :: ys`) that isn't true for general lists, a genuine direction
   mismatch caught immediately by the type-checker, not a deep
   difficulty. -/
theorem natToFiniteSet_glue_hom (m n : Nat) :
  natToFiniteSet (m + n) = natToFiniteSet m ++ natToFiniteSet n := by
  induction m with
  | zero => simp [natToFiniteSet]
  | succ k ih => simp [Nat.succ_add, natToFiniteSet, ih]

def natProdToFiniteSet : Nat × Nat → List Unit × List Unit :=
  fun p => (natToFiniteSet p.1, natToFiniteSet p.2)

/- Concrete instantiation of the generic theorem: the paired
   translation reflects `≈` on `natIncidence × natIncidence`. -/
theorem natProdToFiniteSet_reflects_approxBisim {p q : Nat × Nat}
  (h : natProdToFiniteSet p = natProdToFiniteSet q) :
    approxBisim (incidenceProd natIncidence natIncidence) p q := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [natProdToFiniteSet, Prod.mk.injEq] at h
  exact incidenceProd_translation_reflects natIncidence natIncidence
    natToFiniteSet natToFiniteSet
    (fun x y hxy => natToFiniteSet_reflects_approxBisim hxy)
    (fun x y hxy => natToFiniteSet_reflects_approxBisim hxy)
    (by simp [h.1, h.2])

/- Ties the whole picture together: the paired translation is ALSO a
   genuine `glue`-homomorphism for the product, combining
   `natToFiniteSet_glue_hom` on each side with `incidenceProd`'s own
   componentwise `glue` -- the same "faithful reflector AND algebra
   homomorphism" achievement cycle 28 reached for `cycleToNat`, now
   for a *generic* construction rather than one hand-built instance. -/
theorem natProdToFiniteSet_glue_hom (p q : Nat × Nat) :
  ((incidenceProd natIncidence natIncidence).glue p q).map natProdToFiniteSet =
    some (natToFiniteSet p.1 ++ natToFiniteSet q.1, natToFiniteSet p.2 ++ natToFiniteSet q.2) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [incidenceProd, prodGlue, natIncidence]
  simp [natProdToFiniteSet, natToFiniteSet_glue_hom]

/- Research cycle 37 (see RESEARCH_LOG.md): audit item queued from
   cycle 36 -- does `incidenceProd_translation_reflects` (cycle 34)
   have an analogous subtlety to the one cycle 36 found for
   `incidenceSum` (the `Sum.elim`-vs-`Sum.map` choice)? Confirmed by
   inspection: the theorem already pairs translations via `(t1 p.1, t2
   p.2) = (t1 q.1, t2 q.2)`, landing in a genuine `S1 × S2` -- exactly
   the `Prod.map`-shaped, non-collapsing form, never the collapsing
   shared-target form that caused cycles 33/36's trouble for sums.

   Why there's no *natural* temptation toward the bad form for products
   the way there was for sums: `Sum.elim t1 t2 : I1 ⊕ I2 → S` exists in
   the standard library *because* `Sum` has two genuinely distinct
   cases that must be resolved into one output type -- it's the
   eliminator `Sum` is built around. `Prod` has no analogous
   eliminator into a single shared type: every element of `I1 × I2`
   already carries BOTH components simultaneously, so pairing them
   componentwise into `S1 × S2` (never merging them into one `S`) is
   the *only* idiomatic translation shape -- there is no tempting
   one-line alternative the way `Sum.elim` is for sums.

   This isn't because products are structurally immune to the
   underlying failure mode, though -- confirmed concretely below: a
   deliberately *constructed* shared-target collapse (mirroring
   `Sum.elim`'s shape) fails for the product exactly the way it would
   have for the sum. -/
def prodCollapseTrivial : Nat × Nat → List Unit := fun _ => []

theorem prodCollapseTrivial_collapses :
  prodCollapseTrivial (0, 0) = prodCollapseTrivial (0, 1) := rfl

theorem prodCollapseTrivial_not_reflects :
  ¬ approxBisim (incidenceProd natIncidence natIncidence) (0, 0) (0, 1) := by
  rw [incidenceProd_faithful_of_faithful natIncidence natIncidence
    natIncidence_approxBisim_iff natIncidence_approxBisim_iff]
  simp

end IncidenceCore
