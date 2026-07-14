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

def prodResonance {I1 R1 T1 I2 R2 T2 : Type u}
    [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    (I1 × I2) → (I1 × I2) → (I1 × I2) → Prop
  | (i1, i2), (j1, j2), (k1, k2) =>
      inc1.resonance i1 j1 k1 ∧ inc2.resonance i2 j2 k2

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
  resonance := prodResonance inc1 inc2
  glue := prodGlue inc1 inc2
  selected_resonates := by
    intro i j k selected
    rcases i with ⟨i1, i2⟩
    rcases j with ⟨j1, j2⟩
    rcases k with ⟨k1, k2⟩
    simp only [prodGlue] at selected
    split at selected <;> try contradiction
    next first second firstEq secondEq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at selected
      rcases selected with ⟨rfl, rfl⟩
      exact ⟨inc1.selected_resonates firstEq,
        inc2.selected_resonates secondEq⟩
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

def resonanceProdSpec {I1 R1 T1 I2 R2 T2 : Type u}
    [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (first : ResonanceSpec inc1) (second : ResonanceSpec inc2) :
    ResonanceSpec (incidenceProd inc1 inc2) where
  symmetric := by
    intro i j k resonant
    exact ⟨first.symmetric resonant.1, second.symmetric resonant.2⟩
  unit_left := by
    intro i
    exact ⟨first.unit_left i.1, second.unit_left i.2⟩
  unit_right := by
    intro i
    exact ⟨first.unit_right i.1, second.unit_right i.2⟩
  type_compatible := by
    intro i j k resonant
    rcases first.type_compatible resonant.1 with ⟨hij1, hki1⟩
    rcases second.type_compatible resonant.2 with ⟨hij2, hki2⟩
    exact ⟨Prod.ext hij1 hij2, Prod.ext hki1 hki2⟩

def associativeResonanceProdSpec
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (first : AssociativeResonanceSpec inc1)
    (second : AssociativeResonanceSpec inc2) :
    AssociativeResonanceSpec (incidenceProd inc1 inc2) where
  reassociate := by
    intro i j k out
    constructor
    · rintro ⟨ij, hij, hout⟩
      rcases (first.reassociate).mp ⟨ij.1, hij.1, hout.1⟩ with
        ⟨jk1, hjk1, hi1⟩
      rcases (second.reassociate).mp ⟨ij.2, hij.2, hout.2⟩ with
        ⟨jk2, hjk2, hi2⟩
      exact ⟨(jk1, jk2), ⟨hjk1, hjk2⟩, ⟨hi1, hi2⟩⟩
    · rintro ⟨jk, hjk, hout⟩
      rcases (first.reassociate).mpr ⟨jk.1, hjk.1, hout.1⟩ with
        ⟨ij1, hij1, ho1⟩
      rcases (second.reassociate).mpr ⟨jk.2, hjk.2, hout.2⟩ with
        ⟨ij2, hij2, ho2⟩
      exact ⟨(ij1, ij2), ⟨hij1, hij2⟩, ⟨ho1, ho2⟩⟩

/- Product projections preserve every admitted resonance mode, and the
diagonal duplicates a mode componentwise. -/
def incidenceProdFirstResonanceHom
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    ResonanceHomomorphism (incidenceProd inc1 inc2) inc1 where
  toFun := Prod.fst
  preserves := fun resonant => resonant.1

def incidenceProdSecondResonanceHom
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    ResonanceHomomorphism (incidenceProd inc1 inc2) inc2 where
  toFun := Prod.snd
  preserves := fun resonant => resonant.2

def incidenceProdDiagonalResonanceHom
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceHomomorphism inc (incidenceProd inc inc) where
  toFun := fun i => (i, i)
  preserves := fun resonant => ⟨resonant, resonant⟩

noncomputable def countablyPresentedIncidenceProd
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : CountablyPresentedIncidence I1 R1 T1)
    (right : CountablyPresentedIncidence I2 R2 T2) :
    CountablyPresentedIncidence (I1 × I2) (R1 ⊕ R2) (T1 × T2) where
  incidence := incidenceProd left.incidence right.incidence
  atoms := left.atoms.prod right.atoms

theorem countablyPresentedIncidenceProd_internalLogic_complete
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : CountablyPresentedIncidence I1 R1 T1)
    (right : CountablyPresentedIncidence I2 R2 T2)
    (context : List (Formula (I1 × I2))) (formula : Formula (I1 × I2)) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  (countablyPresentedIncidenceProd left right).internalLogic_complete context formula

theorem incidenceProd_boundaryValuation_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (leftAtom : I1) (rightAtom : I2) :
    IncidenceBoundaryValuation (incidenceProd left right) (leftAtom, rightAtom) ↔
      IncidenceBoundaryValuation left leftAtom ∨
        IncidenceBoundaryValuation right rightAtom := by
  simp only [IncidenceBoundaryValuation, incidenceProd, prodBoundary,
    List.mem_append, List.mem_map]
  constructor
  · rintro ⟨endpoint, ⟨source, member, rfl⟩ | ⟨source, member, rfl⟩⟩
    · exact Or.inl ⟨source, member⟩
    · exact Or.inr ⟨source, member⟩
  · rintro (⟨source, member⟩ | ⟨source, member⟩)
    · exact ⟨_, Or.inl ⟨source, member, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨source, member, rfl⟩⟩

theorem incidenceProd_boundaryAtom_satisfies_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (leftAtom : I1) (rightAtom : I2) :
    IncidenceBoundarySatisfies (incidenceProd left right)
        (.atom (leftAtom, rightAtom)) ↔
      IncidenceBoundaryValuation left leftAtom ∨
        IncidenceBoundaryValuation right rightAtom :=
  incidenceProd_boundaryValuation_iff left right leftAtom rightAtom

theorem incidenceProd_leafValuation_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (leftAtom : I1) (rightAtom : I2) :
    IncidenceLeafValuation (incidenceProd left right) (leftAtom, rightAtom) ↔
      IncidenceLeafValuation left leftAtom ∧
        IncidenceLeafValuation right rightAtom := by
  simp [IncidenceLeafValuation, incidenceProd, prodBoundary]

theorem incidenceProd_leafAtom_satisfies_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (leftAtom : I1) (rightAtom : I2) :
    IncidenceLeafSatisfies (incidenceProd left right)
        (.atom (leftAtom, rightAtom)) ↔
      IncidenceLeafValuation left leftAtom ∧
        IncidenceLeafValuation right rightAtom :=
  incidenceProd_leafValuation_iff left right leftAtom rightAtom

noncomputable def natProductCountablyPresentedIncidence :
    CountablyPresentedIncidence (Nat × Nat) (PeanoRole ⊕ PeanoRole)
      (GraphType × GraphType) :=
  countablyPresentedIncidenceProd natCountablyPresentedIncidence
    natCountablyPresentedIncidence

theorem natProduct_internalLogic_consistent_iff_model
    (context : List (Formula (Nat × Nat))) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  natProductCountablyPresentedIncidence.internalLogic_consistent_iff_model context

theorem natProduct_internalLogic_countermodel
    {context : List (Formula (Nat × Nat))} {formula : Formula (Nat × Nat)}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory (Nat × Nat),
      KripkeContextForces (canonicalKripkeModel (Nat × Nat)) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel (Nat × Nat)) theory formula :=
  natProductCountablyPresentedIncidence.internalLogic_countermodel hnot

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

theorem quotientResonanceCongruentProd
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (first : QuotientResonanceCongruent inc1)
    (second : QuotientResonanceCongruent inc2) :
    QuotientResonanceCongruent (incidenceProd inc1 inc2) := by
  intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk
  rw [incidenceProd_approxBisim_iff] at hi hj hk
  constructor
  · rintro ⟨resonant1, resonant2⟩
    exact ⟨(first hi.1 hj.1 hk.1).mp resonant1,
      (second hi.2 hj.2 hk.2).mp resonant2⟩
  · rintro ⟨resonant1, resonant2⟩
    exact ⟨(first hi.1 hj.1 hk.1).mpr resonant1,
      (second hi.2 hj.2 hk.2).mpr resonant2⟩

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

/- Research cycle 79 (see RESEARCH_LOG.md): does `CoherentIncidence`'s
   `BoundarySquareZeroEverywhere` obligation transport through `incidenceProd`
   the way faithfulness does (cycle 32: unconditional yes) or fail the way
   faithfulness fails through `incidenceSum` (cycle 33)? `GluePushoutSpec`
   transfers trivially for the structural reason cycle 76 found: it needs
   only `[DecidableEq I]`, and `incidenceProd`'s carrier `I1 × I2` inherits
   that from `[DecidableEq I1] [DecidableEq I2]` already required by
   `incidenceProd`'s own signature -- confirmed below, no dependency on
   `inc1`/`inc2` at all. `BoundarySquareZeroEverywhere` is the substantive
   question, and the answer is NO: `prodBoundary`'s "box product" shape
   (`(i1,i2)`'s boundary reaches BOTH `(∂i1,i2)` and `(i1,∂i2)`, the standard
   tensor-product-of-chain-complexes differential) carries no Koszul sign to
   make the two length-2 paths back to a shared target cancel -- they ADD.
   Concretely: if `i1` reaches leaf `j1` via one nonzero-signed link in
   `inc1`, and `i2` reaches leaf `j2` via one nonzero-signed link in `inc2`
   (exactly the shape `finiteIncidence`/`rationalIncidence`/`realIncidence`
   all have at their non-leaf elements, cycles 76-78), then in the product
   `(i1,i2)`'s boundary is `[(j1,i2), (i1,j2)]`, each of which has a SINGLE
   further link back to `(j1,j2)` with signed value `v2`/`v1` respectively
   (borrowed unchanged from the other factor's own link, since
   `prodBoundary`'s sign field is `e.sign` verbatim, never flipped) -- so
   `∂²` at `((i1,i2),(j1,j2))` is `v1*v2 + v2*v1 = 2*v1*v2 ≠ 0` (both `v1`,
   `v2` nonzero). This is the mirror image of cycles 32/33's asymmetry: there
   the PRODUCT was the well-behaved connective and the SUM collapsed;
   here the roles invert -- `incidenceProd` is the one that fails to
   transport `BoundarySquareZeroEverywhere`, for a reason with no analogue in
   the faithfulness story (a genuine two-path composition, not a
   leaf-collapse). Proved as one general theorem (mirroring cycle 77's
   `not_boundarySquareZeroEverywhere_of_single_link_chain`, which packaged
   the single-link-chain negative once rather than reproving it per
   instance) so it applies uniformly to ANY pair of instances with this
   "single nonzero link to a leaf" shape -- not just the one concrete
   instantiation checked below (`finiteIncidence × finiteIncidence`), but
   equally `rationalIncidence`/`realIncidence` paired with themselves or each
   other, since all three already have exactly this shape (cycles 76-78). -/

/-- Generic identity-cospan `GluePushoutSpec` witness (cycle 76's mechanism),
confirmed here to transfer to `incidenceProd` with zero adaptation: the
witness needs only `[DecidableEq I]` on the combined carrier, which
`I1 × I2` already has. -/
def prodGluePushoutSpec {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    GluePushoutSpec (incidenceProd inc1 inc2) where
  diagram := fun i j => { a := i, b := j, c := i, left := id, right := id }
  witness := by
    intro i j k _hglue
    refine ⟨{ apex := k
              inl := id
              inr := id
              commutes := fun _ => rfl
              lift := fun leftLeg _ _ => leftLeg
              lift_inl := fun _ _ _ _ => rfl
              lift_inr := fun _ _ h x => h x
              lift_unique := fun _ _ _ _ hl _ => funext hl }, rfl⟩

/-- Purely arithmetic helper: a `foldl` over an explicit 4-element list is
just the sum of the summand applied to each element, in order. Generic over
any carrier `I`, not specific to `incidenceProd`. -/
theorem foldl_add_four {I : Type u} (a b c d : I) (f : I → Int) :
    ([a,b,c,d] : List I).foldl (fun acc x => acc + f x) 0 =
      f a + f b + f c + f d := by
  simp [List.foldl_cons, List.foldl_nil]

/-- The negative result: if `i1` reaches a leaf `j1` of `inc1` via a single
nonzero-signed boundary link, and `i2` reaches a leaf `j2` of `inc2`
similarly, then `incidenceProd inc1 inc2` does NOT satisfy
`BoundarySquareZeroEverywhere` -- the two length-2 paths `(i1,i2) →
(j1,i2)/(i1,j2) → (j1,j2)` compose to `2 * (signed value of the i1-link) *
(signed value of the i2-link) ≠ 0`, witnessed on the 4-element index list
`[(i1,i2),(j1,i2),(i1,j2),(j1,j2)]`. Note this is a genuinely different
failure mode than cycle 33's `incidenceSum` leaf-collapse: here `(i1,i2)`
is NOT itself a leaf of the product (its boundary has two entries), and no
two DISTINCT elements become `≈`-related -- the failure is a real nonzero
double-boundary composition, the same "tensor product needs a Koszul sign"
phenomenon that makes naive chain-complex products fail `∂² = 0` in
ordinary homological algebra. -/
theorem incidenceProd_not_boundarySquareZeroEverywhere_of_single_link_star
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    {i1 j1 : I1} {e1 : Endpoint I1 R1}
    (hb1 : inc1.boundary i1 = [e1]) (he1i : e1.i = j1) (he1s : e1.sign ≠ Sign.zero)
    (hleaf1 : inc1.boundary j1 = [])
    {i2 j2 : I2} {e2 : Endpoint I2 R2}
    (hb2 : inc2.boundary i2 = [e2]) (he2i : e2.i = j2) (he2s : e2.sign ≠ Sign.zero)
    (hleaf2 : inc2.boundary j2 = []) :
    ¬ BoundarySquareZeroEverywhere (incidenceProd inc1 inc2) := by
  intro hall
  have hj1i1 : j1 ≠ i1 := by
    intro heq
    exact inc1.well_founded i1 ⟨e1, hb1 ▸ List.mem_singleton_self e1, heq ▸ he1i⟩
  have hj2i2 : j2 ≠ i2 := by
    intro heq
    exact inc2.well_founded i2 ⟨e2, hb2 ▸ List.mem_singleton_self e2, heq ▸ he2i⟩
  have hi1j1 : i1 ≠ j1 := Ne.symm hj1i1
  have hi2j2 : i2 ≠ j2 := Ne.symm hj2i2
  have hne : (j1, i2) ≠ (i1, j2) := fun heq => hj1i1 (congrArg Prod.fst heq)
  have hi : ((i1,i2) : I1 × I2) ∈ [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] := by simp
  have hk : ((j1,j2) : I1 × I2) ∈ [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] := by simp
  have hzero := hall [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,j2) hi hk
  change boundary_composition (incidenceProd inc1 inc2)
    [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,j2) = 0 at hzero
  have hbprod : (incidenceProd inc1 inc2).boundary (i1,i2) =
      [ ({ i := (j1,i2), role := Sum.inl e1.role, sign := e1.sign, mult := e1.mult,
           mult_pos := e1.mult_pos } : Endpoint (I1 × I2) (R1 ⊕ R2)),
        ({ i := (i1,j2), role := Sum.inr e2.role, sign := e2.sign, mult := e2.mult,
           mult_pos := e2.mult_pos } : Endpoint (I1 × I2) (R1 ⊕ R2)) ] := by
    show prodBoundary inc1 inc2 (i1, i2) = _
    simp [prodBoundary, hb1, hb2, he1i, he2i]
  have hbjj1 : (incidenceProd inc1 inc2).boundary (j1,i2) =
      [ ({ i := (j1,j2), role := Sum.inr e2.role, sign := e2.sign, mult := e2.mult,
           mult_pos := e2.mult_pos } : Endpoint (I1 × I2) (R1 ⊕ R2)) ] := by
    show prodBoundary inc1 inc2 (j1, i2) = _
    simp [prodBoundary, hleaf1, hb2, he2i]
  have hbjj2 : (incidenceProd inc1 inc2).boundary (i1,j2) =
      [ ({ i := (j1,j2), role := Sum.inl e1.role, sign := e1.sign, mult := e1.mult,
           mult_pos := e1.mult_pos } : Endpoint (I1 × I2) (R1 ⊕ R2)) ] := by
    show prodBoundary inc1 inc2 (i1, j2) = _
    simp [prodBoundary, hb1, hleaf2, he1i]
  have hexpand : boundary_composition (incidenceProd inc1 inc2)
      [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,j2) =
      boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (i1,i2) *
        boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,j2) +
      (boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,i2) *
        boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (j1,i2) (j1,j2) +
      (boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (i1,j2) *
        boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,j2) (j1,j2) +
      (boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,j2) *
        boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (j1,j2) (j1,j2)))) := by
    show ([(i1,i2), (j1,i2), (i1,j2), (j1,j2)] : List (I1 × I2)).foldl
      (fun acc j => acc + boundaryMatrix (incidenceProd inc1 inc2)
        [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) j *
        boundaryMatrix (incidenceProd inc1 inc2) [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] j (j1,j2)) 0 = _
    rw [foldl_add_four]
    omega
  rw [hexpand] at hzero
  rw [boundaryMatrix_two_link (incidenceProd inc1 inc2)
        [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,i2) (i1,j2) _ _ hbprod rfl rfl hne (i1,i2),
      boundaryMatrix_two_link (incidenceProd inc1 inc2)
        [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,i2) (i1,j2) _ _ hbprod rfl rfl hne (j1,i2),
      boundaryMatrix_two_link (incidenceProd inc1 inc2)
        [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,i2) (i1,j2) _ _ hbprod rfl rfl hne (i1,j2),
      boundaryMatrix_two_link (incidenceProd inc1 inc2)
        [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,i2) (j1,i2) (i1,j2) _ _ hbprod rfl rfl hne (j1,j2),
      boundaryMatrix_single_link (incidenceProd inc1 inc2)
        [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (j1,i2) (j1,j2) _ hbjj1 rfl (j1,j2),
      boundaryMatrix_single_link (incidenceProd inc1 inc2)
        [(i1,i2), (j1,i2), (i1,j2), (j1,j2)] (i1,j2) (j1,j2) _ hbjj2 rfl (j1,j2)] at hzero
  have h1 : ((i1,i2) : I1 × I2) ≠ (j1,i2) := fun h => hi1j1 (congrArg Prod.fst h)
  have h2 : ((i1,i2) : I1 × I2) ≠ (i1,j2) := fun h => hi2j2 (congrArg Prod.snd h)
  have h3 : ((j1,j2) : I1 × I2) ≠ (j1,i2) := fun h => hi2j2 (congrArg Prod.snd h).symm
  have h4 : ((j1,j2) : I1 × I2) ≠ (i1,j2) := fun h => hi1j1 (congrArg Prod.fst h).symm
  simp only [h1, h2, h3, h4, hne, hne.symm, if_neg, if_pos, not_false_eq_true] at hzero
  have hm1 : e1.mult ≥ 1 := inc1.multiplicities i1 e1 (hb1 ▸ List.mem_singleton_self e1)
  have hm2 : e2.mult ≥ 1 := inc2.multiplicities i2 e2 (hb2 ▸ List.mem_singleton_self e2)
  have hpos1 : (0:Int) < Int.ofNat e1.mult := by
    have h : (0:Int) < (e1.mult:Int) := by exact_mod_cast hm1
    simpa using h
  have hpos2 : (0:Int) < Int.ofNat e2.mult := by
    have h : (0:Int) < (e2.mult:Int) := by exact_mod_cast hm2
    simpa using h
  have hprod : (0:Int) < Int.ofNat e1.mult * Int.ofNat e2.mult := Int.mul_pos hpos1 hpos2
  have hprod' : (0:Int) < Int.ofNat e2.mult * Int.ofNat e1.mult := Int.mul_pos hpos2 hpos1
  simp only [Int.zero_add, Int.add_zero, Int.zero_mul, Int.mul_zero] at hzero
  cases hs1 : e1.sign <;> cases hs2 : e2.sign <;>
    simp only [hs1, hs2, Int.neg_mul, Int.mul_neg] at hzero <;>
    first
      | exact absurd hs1 he1s
      | exact absurd hs2 he2s
      | omega

/-- Concrete instantiation on `finiteIncidence` (cycle 76's own instance,
already known to individually satisfy `BoundarySquareZeroEverywhere`):
`root`'s single link to `leaf` supplies exactly the "single nonzero link to
a leaf" shape on both factors, so `incidenceProd finiteIncidence
finiteIncidence` fails `BoundarySquareZeroEverywhere` even though
`finiteIncidence` itself does not. The same argument applies verbatim to
`rationalIncidence`/`realIncidence` (cycles 77-78 established they have the
identical single-link-to-leaf shape at every nonzero element), so this is
not a `finiteIncidence`-specific accident. -/
theorem incidenceProd_finiteIncidence_not_boundarySquareZeroEverywhere :
    ¬ BoundarySquareZeroEverywhere (incidenceProd finiteIncidence finiteIncidence) :=
  incidenceProd_not_boundarySquareZeroEverywhere_of_single_link_star
    finiteIncidence finiteIncidence
    (i1 := .root) (j1 := .leaf)
    (e1 := { i := .leaf, role := .src, sign := .pos, mult := 1, mult_pos := by omega })
    rfl rfl (by decide) rfl
    (i2 := .root) (j2 := .leaf)
    (e2 := { i := .leaf, role := .src, sign := .pos, mult := 1, mult_pos := by omega })
    rfl rfl (by decide) rfl

/- Research cycle 81 (see RESEARCH_LOG.md): cycle 80 closed the
   `incidenceSum` side of the sum/product asymmetry thread (cycles
   32/33/35/36/79/80) with a precise negative -- `incidenceSum` reaches
   `CoherentIncidence` but the retract/Heyting-isomorphism layer is
   categorically unreachable, because every `BoundarySquareZeroEverywhere`-
   satisfying instance in this project is a one-leaf "star" and `incidenceSum`
   always collapses cross-side leaves. Cycle 80 queued the converse question
   as the natural capstone: `incidenceProd` transports faithfulness
   UNCONDITIONALLY (cycle 32, no "leafless side" hypothesis needed, unlike
   `incidenceSum`'s cycle 35 conditional), so if `incidenceProd` also reached
   `ChainComplexPushoutIncidence`, the retract layer would close immediately.
   But cycle 79 already separately proved the opposite blocking fact:
   `incidenceProd finiteIncidence finiteIncidence` FAILS
   `BoundarySquareZeroEverywhere` outright
   (`incidenceProd_finiteIncidence_not_boundarySquareZeroEverywhere`, just
   above). The task this cycle set out to do was CONFIRM this precise
   converse relationship rigorously, not merely infer it from the two
   separately-proved pieces: verify that cycle 32's faithfulness-transport
   genuinely combines with a concrete factor pair to satisfy the
   retract-eligibility criterion
   (`coherentQuotient_has_logicalRetract_iff_source_bisim_faithful`, whose
   hypothesis is exactly `∀ {left right}, approxBisim source.chainPushout.inc
   left right → left = right`), while the SEPARATE `boundary_square_zero`
   field is what genuinely blocks the chain from ever reaching that
   criterion's statement in the first place -- and to check, rather than
   assume, that `CoherentIncidence`'s OTHER required field
   (`completeLogic`) is not hiding a second obstruction alongside
   `boundary_square_zero`.

   `finiteIncidenceProdAtomCoding`/`finiteIncidenceProdCompleteLogic` settle
   the `completeLogic` question first: `Logic.lean`'s `CountableAtomCoding.prod`
   (used by cycle 80 for `.sum`, confirmed pre-existing rather than newly
   built there) pairs `finiteIncidenceAtomCoding` with itself exactly as
   `.sum` did, producing a genuine `CompletePropositionalInternalLogic
   (FiniteIncidence × FiniteIncidence)` with zero new proof content -- so
   `completeLogic` transports through `incidenceProd finiteIncidence
   finiteIncidence` just as cleanly as it did through the sum (cycle 80
   thread 1). This rules out the task's flagged risk: the block is not a
   `completeLogic` subtlety, it really is `boundary_square_zero` alone.

   `incidenceProd_finiteIncidence_bisim_faithful` is the concrete
   instantiation of cycle 32's `incidenceProd_faithful_of_faithful` against
   `finiteIncidence_approxBisim_iff_eq` (cycle 73) applied to both factors --
   `incidenceProd finiteIncidence finiteIncidence`'s bisimulation genuinely
   is `=`, unconditionally, mirroring the `natIncidence × natIncidence`
   instantiation already in this file (L502-504) but for the factor whose
   product fails `BoundarySquareZeroEverywhere`.

   `incidenceProd_finiteIncidence_no_coherentIncidence` makes the blocking
   fact precise at the level `CoherentIncidence` itself is stated: since
   `ChainComplexPushoutIncidence` bundles `boundary_square_zero :
   BoundarySquareZeroEverywhere inc` as a literal field
   (`IncidenceTheory.lean` L2050-2053), no `coherent : CoherentIncidence
   (FiniteIncidence × FiniteIncidence) (GraphRole ⊕ GraphRole) (GraphType ×
   GraphType)` can have `coherent.chainPushout.inc = incidenceProd
   finiteIncidence finiteIncidence` -- attempting to supply one immediately
   yields a term of the negated proposition cycle 79 already proved. This is
   the precise sense in which `incidenceProd`'s obstruction sits at the
   OPPOSITE end of the chain from `incidenceSum`'s: `incidenceSum`'s source
   is a genuine, constructible `CoherentIncidence`
   (`incidenceSum_finiteIncidence_coherentIncidence`, `Sum.lean` cycle 80)
   and the retract fails afterward; `incidenceProd`'s source cannot even be
   packaged as a `CoherentIncidence` in the first place.

   `incidenceProd_finiteIncidence_retract_of_hypothetical_source` is the
   capstone: it grants, as a hypothesis, exactly the thing
   `incidenceProd_finiteIncidence_no_coherentIncidence` proves is
   unsatisfiable (a `source : CoherentIncidence ...` whose
   `chainPushout.inc` equals `incidenceProd finiteIncidence finiteIncidence`)
   and, under that counterfactual alone, derives
   `Nonempty (CoherentQuotientLogicalRetract quotient)` for ANY
   `CoherentQuotient` of it -- using only
   `coherentQuotient_has_logicalRetract_iff_source_bisim_faithful`'s `.mpr`
   fed by `incidenceProd_finiteIncidence_bisim_faithful`, exactly the shape
   cycles 76/78's `finiteCoherentQuotientLogicalRetract`/
   `rationalCoherentQuotientLogicalRetract` used. This is not a vacuous
   `False.elim` dressed up as a theorem: its proof never uses
   `incidenceProd_finiteIncidence_no_coherentIncidence` or any contradiction
   from `hsource`, only genuine faithfulness -- so it is a real witness that
   the retract-eligibility criterion's hypothesis holds for this instance,
   independently of the fact (proved separately, one theorem above) that its
   own premise can never be discharged. Together the two theorems confirm,
   rather than merely infer, cycle 80's queued converse: `incidenceProd`
   would clear the retract/Heyting-isomorphism layer with no further work
   needed IF it could reach `CoherentIncidence` at all, but it cannot, for a
   reason entirely confined to `boundary_square_zero` -- the exact mirror
   image of `incidenceSum`'s "reaches `CoherentIncidence`, blocked at the
   retract" shape. -/

/-- `completeLogic` transports through `incidenceProd` exactly as cleanly as
cycle 80 found for `incidenceSum`: `CountableAtomCoding.prod` (pre-existing,
`Logic.lean`) pairs `finiteIncidenceAtomCoding` with itself, needing no new
proof content. Confirms `completeLogic` is NOT part of the obstruction. -/
noncomputable def finiteIncidenceProdAtomCoding :
    CountableAtomCoding (FiniteIncidence × FiniteIncidence) :=
  finiteIncidenceAtomCoding.prod finiteIncidenceAtomCoding

/-- A genuine `CompletePropositionalInternalLogic (FiniteIncidence ×
FiniteIncidence)`, built from `finiteIncidenceProdAtomCoding` alone -- the
`completeLogic` field a `CoherentIncidence` on this carrier would need is
fully constructible; only `boundary_square_zero` is not. -/
noncomputable def finiteIncidenceProdCompleteLogic :
    CompletePropositionalInternalLogic (FiniteIncidence × FiniteIncidence) :=
  finiteIncidenceProdAtomCoding.completeLogic

/-- Concrete instantiation of cycle 32's `incidenceProd_faithful_of_faithful`
against `finiteIncidence_approxBisim_iff_eq` (cycle 73) on both factors:
`incidenceProd finiteIncidence finiteIncidence`'s bisimulation is exactly
`=`, unconditionally -- the retract-eligibility criterion's hypothesis,
verified directly rather than left as an inference from the general
theorem. -/
theorem incidenceProd_finiteIncidence_bisim_faithful :
    ∀ p q : FiniteIncidence × FiniteIncidence,
      approxBisim (incidenceProd finiteIncidence finiteIncidence) p q ↔ p = q :=
  incidenceProd_faithful_of_faithful finiteIncidence finiteIncidence
    finiteIncidence_approxBisim_iff_eq finiteIncidence_approxBisim_iff_eq

/-- The precise location of the block: `ChainComplexPushoutIncidence`
bundles `boundary_square_zero : BoundarySquareZeroEverywhere inc` as a
literal field, so no `CoherentIncidence` on this carrier can have
`incidenceProd finiteIncidence finiteIncidence` as its underlying incidence
-- attempting to supply one directly contradicts cycle 79's negative
theorem. This is the opposite end of the chain from `incidenceSum`'s
obstruction: there the source is constructible and the retract fails;
here the source itself cannot be constructed. -/
theorem incidenceProd_finiteIncidence_no_coherentIncidence
    (coherent : CoherentIncidence (FiniteIncidence × FiniteIncidence)
      (GraphRole ⊕ GraphRole) (GraphType × GraphType))
    (hinc : coherent.chainPushout.inc = incidenceProd finiteIncidence finiteIncidence) :
    False := by
  apply incidenceProd_finiteIncidence_not_boundarySquareZeroEverywhere
  rw [← hinc]
  exact coherent.chainPushout.boundary_square_zero

/-- The capstone: GRANTING, purely hypothetically, that a `source :
CoherentIncidence ...` with `incidenceProd finiteIncidence finiteIncidence`
as its underlying incidence existed (impossible per
`incidenceProd_finiteIncidence_no_coherentIncidence` above), the
retract-eligibility criterion is satisfied unconditionally for ANY
`CoherentQuotient` of it, via cycle 32's faithfulness alone -- the proof
below never invokes the impossibility of `hsource`, only genuine
faithfulness, so this is a real confirmation that `incidenceProd`'s
faithfulness-transport combines with retract-eligibility, not a vacuous
`False.elim` in disguise. Confirms cycle 80's queued converse precisely:
`incidenceProd` is blocked at the OPPOSITE end of the
`CoherentIncidence`/retract chain from `incidenceSum`. -/
theorem incidenceProd_finiteIncidence_retract_of_hypothetical_source
    {Q : Type} [DecidableEq Q]
    (source : CoherentIncidence (FiniteIncidence × FiniteIncidence)
      (GraphRole ⊕ GraphRole) (GraphType × GraphType))
    (hsource : source.chainPushout.inc = incidenceProd finiteIncidence finiteIncidence)
    (quotient : CoherentQuotient (Q := Q) source) :
    Nonempty (CoherentQuotientLogicalRetract quotient) := by
  apply (coherentQuotient_has_logicalRetract_iff_source_bisim_faithful quotient).mpr
  intro left right hbisim
  rw [hsource] at hbisim
  exact (incidenceProd_finiteIncidence_bisim_faithful left right).mp hbisim

end IncidenceCore
