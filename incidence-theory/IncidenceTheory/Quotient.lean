import IncidenceTheory.Cycle
import IncidenceTheory.Peano
import IncidenceTheory.Simplex

/- Merkle-ID: implementation.graph_model.quotient
   story.jsonnet → implementation.nodes.quotient
   Research cycle 38 (see RESEARCH_LOG.md): the third generic
   constructor thread queued since cycle 36/37 -- "a quotient
   construction using `approxBisim` itself as the identifying
   relation." Before attempting to build a full `Incidence` structure
   on the `≈`-quotient of an existing instance, this cycle checks the
   necessary PREREQUISITE first: does `Incidence`'s own data (`boundary`,
   `glue`) even respect `≈`, i.e. is it constant on `≈`-equivalence
   classes? This is exactly the well-definedness side condition
   `Quotient.lift` needs to turn a function on `I` into a function on
   `Quotient (approxBisimSetoid inc)`.

   Two findings, one positive and one negative. POSITIVE: `approxBisim`
   is already a genuine equivalence relation for ANY instance
   (`approxBisim_refl`/`_symm`/`_trans` all proven, root file) --
   `approxBisimSetoid` packages this as a real `Setoid I`,
   unconditionally, no caveats. NEGATIVE: `boundary` and `glue` do NOT
   respect `≈` in general -- `cycleIncidence` (cycle 26, the pre-fix,
   non-faithful instance where ALL FOUR elements collapse into one
   `≈`-class, `cycleIncidence_all_collapse`) is a ready-made
   counterexample: `cycleIncidence.boundary CycleId.c0` and
   `cycleIncidence.boundary CycleId.c1` are literally different lists
   (`[{i := c3, ...}]` vs. `[{i := c0, ...}]`), yet `c0 ≈ c1`. The same
   holds for `glue`. So `Quotient.lift inc.boundary` (and
   `Quotient.lift₂ inc.glue`) are simply not well-typed for this
   instance -- the naive "reuse the original data directly on the
   quotient" approach to a quotient-`Incidence` constructor is a dead
   end in general, not merely undischarged. -/

namespace IncidenceCore

/- The positive half is supplied by the core `approxBisimSetoid`: it packages
   every `Incidence`'s proved bisimilarity equivalence as a `Setoid`. -/

/- The concrete inequality underlying the negative result: `c0` and
   `c1`'s single boundary entries point to different predecessors
   (`c3` vs. `c0`), so the lists differ. `Endpoint` has no derived
   `DecidableEq` (only `Repr`), so this needs an explicit injection
   argument rather than `decide`. -/
theorem cycleBoundary_c0_ne_c1 :
  cycleIncidence.boundary CycleId.c0 ≠ cycleIncidence.boundary CycleId.c1 := by
  simp only [cycleIncidence, cycleBoundary, cyclePred]
  intro h
  injection h with h1 _
  injection h1 with hi _
  exact absurd hi (by decide)

/- The headline negative result: `boundary` is not constant on
   `≈`-classes -- the well-definedness hypothesis `Quotient.lift` would
   need to produce `Quotient (approxBisimSetoid cycleIncidence) →
   Boundary CycleId CycleRole` from `cycleIncidence.boundary` is simply
   false for this instance. -/
theorem cycleIncidence_boundary_not_approxBisim_invariant :
  ¬ (∀ i j : CycleId, approxBisim cycleIncidence i j →
      cycleIncidence.boundary i = cycleIncidence.boundary j) := by
  intro h
  exact absurd (h CycleId.c0 CycleId.c1 (cycleIncidence_all_collapse CycleId.c0 CycleId.c1))
    cycleBoundary_c0_ne_c1

/- Packaged generically: SOME instance in this project already
   witnesses the failure -- not a hypothetical worry, a concrete fact
   about an existing, previously-built structure. -/
theorem exists_incidence_boundary_not_approxBisim_congruent :
  ∃ (I R T : Type) (_ : DecidableEq I) (inc : Incidence I R T) (i j : I),
    approxBisim inc i j ∧ inc.boundary i ≠ inc.boundary j :=
  ⟨CycleId, CycleRole, GraphType, inferInstance, cycleIncidence, CycleId.c0, CycleId.c1,
    cycleIncidence_all_collapse CycleId.c0 CycleId.c1, cycleBoundary_c0_ne_c1⟩

/- Confirms the failure isn't isolated to `boundary` specifically:
   `glue` fails the identical well-definedness check. `cycleAdd c0 c0 =
   c0` but `cycleAdd c1 c0 = c1`, and `c0 ≈ c1`, so gluing against a
   fixed third element (`c0`) already distinguishes `c0`'s and `c1`'s
   `≈`-class-mates from each other -- `Quotient.lift₂ inc.glue` would
   need this to be false and it is not. Together with the boundary
   result, this indicates the phenomenon is general: `≈` is a
   genuinely coarser "behavioral" equivalence than any congruence
   `Incidence`'s own raw structural data satisfies, for at least this
   instance. -/
theorem cycleIncidence_glue_not_approxBisim_invariant :
  ¬ (∀ i j k : CycleId, approxBisim cycleIncidence i j →
      cycleIncidence.glue i k = cycleIncidence.glue j k) := by
  intro h
  have := h CycleId.c0 CycleId.c1 CycleId.c0 (cycleIncidence_all_collapse CycleId.c0 CycleId.c1)
  simp only [cycleIncidence] at this
  exact absurd this (by decide)

/- Research cycle 39 (see RESEARCH_LOG.md): option (a) queued from
   cycle 38 -- does the *canonical-representative* quotient variant
   (define the quotient's `boundary` via `inc.boundary` applied to a
   chosen class representative, rather than naively lifting
   `inc.boundary` directly) fare any better than the naive lift cycle
   38 refuted? Tested against `cycleIncidence` again, since
   `cycleIncidence_all_collapse` makes it the sharpest available case:
   ALL FOUR elements are already one `≈`-class, so `Quotient
   (approxBisimSetoid cycleIncidence)` is a *one-point type* -- and this
   turns out to force a much more general fact than "the representative
   construction happens to fail here": `well_founded` alone (`∀ i,
   ¬∃ e ∈ boundary i, e.i = i`) forces ANY `Incidence` structure on a
   `Subsingleton` carrier to have EMPTY boundary at every point,
   regardless of how `boundary` is defined -- if the carrier has only
   one point, every boundary entry's `.i` field is forced (by
   `Subsingleton.elim`) to equal the very point whose boundary it's
   in, which `well_founded` forbids outright unless the boundary list
   is empty. This is not specific to representative-choice mechanics at
   all -- it settles the *entire family* of possible quotient
   constructions on a fully-collapsed instance at once, not just the
   two variants (naive lift, cycle 38; canonical representative, this
   cycle) that were tried by hand. -/
theorem incidence_subsingleton_boundary_empty {I R T : Type u} [DecidableEq I] [Subsingleton I]
  (inc : Incidence I R T) (i : I) : inc.boundary i = [] := by
  match h : inc.boundary i with
  | [] => rfl
  | e :: rest =>
    exact absurd (inc.well_founded i ⟨e, by simp [h], Subsingleton.elim e.i i⟩) (by simp)

/- Confirms the general theorem actually applies here: `cycleIncidence`'s
   quotient by `≈` genuinely is a one-point type, since
   `cycleIncidence_all_collapse` makes the underlying relation total
   (every pair of elements is related), collapsing all of `CycleId`'s
   four elements into a single class. -/
instance cycleIncidence_quotient_subsingleton :
  Subsingleton (Quotient (approxBisimSetoid cycleIncidence)) := by
  constructor
  intro q1 q2
  induction q1 using Quotient.ind with
  | _ x =>
    induction q2 using Quotient.ind with
    | _ y =>
      exact Quotient.sound (cycleIncidence_all_collapse x y)

/- A concrete, hands-on complement to the abstract Subsingleton fact
   above: this project has no `mathlib` dependency, so no `Quotient.out`
   is available -- `quotOut` is the honest core-Lean substitute, built
   directly from `Quotient.exists_rep` (core) via `Classical.choice`,
   the same construction `Quotient.out` itself uses upstream. Reusable
   for any future instance, not just `cycleIncidence`. -/
noncomputable def quotOut {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
  Quotient (approxBisimSetoid inc) → I :=
  fun q => Classical.choose (Quotient.exists_rep q)

/- `cycleRep` factors through `Quotient.mk`, so it automatically only
   depends on `x`'s `≈`-class -- exactly the "representative function
   respecting classes" shape a real `Quotient.out ∘ Quotient.mk`
   construction would have. -/
noncomputable def cycleRep : CycleId → CycleId :=
  fun x => quotOut cycleIncidence (Quotient.mk (approxBisimSetoid cycleIncidence) x)

theorem cycleRep_respects_approxBisim (x y : CycleId) (h : approxBisim cycleIncidence x y) :
  cycleRep x = cycleRep y := by
  unfold cycleRep
  congr 1
  exact @Quotient.sound _ (approxBisimSetoid cycleIncidence) x y h

/- The concrete mechanism behind the abstract Subsingleton fact: for
   ANY function `rep` that respects `≈`-classes (not just `cycleRep`
   specifically), gluing `cycleIncidence`'s own boundary shape onto a
   chosen representative produces a boundary entry whose remapped
   target is the representative ITSELF -- a direct self-loop -- because
   `cycleIncidence_all_collapse` makes literally every pair of elements
   `≈`-related, so `rep` collapses `cyclePred (rep c0)` and `c0`
   together regardless of what `rep` otherwise does. -/
theorem cycleIncidence_rep_quotient_self_loop
  (rep : CycleId → CycleId) (hrep : ∀ x y, approxBisim cycleIncidence x y → rep x = rep y) :
  ∃ e ∈ cycleIncidence.boundary (rep CycleId.c0), rep e.i = rep CycleId.c0 := by
  refine ⟨{ i := cyclePred (rep CycleId.c0), role := CycleRole.chain, sign := Sign.neg, mult := 1 },
    ?_, ?_⟩
  · simp [cycleIncidence, cycleBoundary]
  · exact hrep (cyclePred (rep CycleId.c0)) CycleId.c0
      (cycleIncidence_all_collapse (cyclePred (rep CycleId.c0)) CycleId.c0)

/- Instantiated against the real `cycleRep`: not a hypothetical worry,
   a concrete self-loop that the actual core-Lean representative
   construction produces for this instance. -/
theorem cycleIncidence_real_quotient_self_loop :
  ∃ e ∈ cycleIncidence.boundary (cycleRep CycleId.c0), cycleRep e.i = cycleRep CycleId.c0 :=
  cycleIncidence_rep_quotient_self_loop cycleRep cycleRep_respects_approxBisim

/- Research cycle 40 (see RESEARCH_LOG.md): option (a) from cycle 39's
   queue -- the "opposite end" from cycle 38/39's Subsingleton finding.
   Cycles 38/39 settled the fully-collapsed case (`cycleIncidence`):
   ANY quotient-`Incidence` construction is a dead end there, forced
   into total triviality. What about the other extreme -- an already
   `≈`-*faithful* instance (`natIncidence`, `cycleIncidenceFixed`),
   where `≈` already coincides with `=`? There, every `≈`-class is a
   *singleton*, so the well-definedness question cycle 38 asked
   (does `boundary`/`glue` respect `≈`?) should be trivially `Yes` --
   and the deeper question is whether the quotient itself is anything
   more than a relabeling of `I`. -/

/- For a faithful instance, `Quotient.mk` is injective -- distinct
   elements can never share a class, since sharing a class would mean
   `≈`-related, which for a faithful instance means literally equal. -/
theorem quotient_mk_injective_of_faithful {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (hfaithful : ∀ x y : I, approxBisim inc x y ↔ x = y)
  {x y : I} (h : Quotient.mk (approxBisimSetoid inc) x = Quotient.mk (approxBisimSetoid inc) y) :
  x = y :=
  (hfaithful x y).mp (Quotient.exact h)

/- Surjectivity holds unconditionally for ANY instance (not just
   faithful ones) -- every quotient element is `Quotient.mk` of some
   representative, by `Quotient.ind`. Stated here rather than in the
   Subsingleton section above since it only becomes interesting
   combined with injectivity, which is where faithfulness matters. -/
theorem quotient_mk_surjective {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
  ∀ q : Quotient (approxBisimSetoid inc), ∃ x, Quotient.mk (approxBisimSetoid inc) x = q := by
  intro q
  induction q using Quotient.ind with
  | _ x => exact ⟨x, rfl⟩

/- Combined: for a faithful instance, `Quotient.mk` is a genuine
   bijection `I ≃ Quotient (approxBisimSetoid inc)`. The quotient adds
   no new identifications (injective) and loses no elements
   (surjective) -- it is, up to relabeling, the same carrier the
   instance already had. This is the precise sense in which faithful
   instances sit at the opposite end from `cycleIncidence`'s
   Subsingleton (one-point) quotient: one extreme collapses everything,
   the other collapses nothing at all. -/
theorem quotient_mk_bijective_of_faithful {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (hfaithful : ∀ x y : I, approxBisim inc x y ↔ x = y) :
  (∀ x y : I, Quotient.mk (approxBisimSetoid inc) x = Quotient.mk (approxBisimSetoid inc) y → x = y) ∧
  (∀ q : Quotient (approxBisimSetoid inc), ∃ x, Quotient.mk (approxBisimSetoid inc) x = q) :=
  ⟨fun _ _ => quotient_mk_injective_of_faithful inc hfaithful, quotient_mk_surjective inc⟩

theorem quotient_mk_injective_iff_bisimulationFaithful
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (∀ x y : I, Quotient.mk (approxBisimSetoid inc) x =
      Quotient.mk (approxBisimSetoid inc) y → x = y) ↔
      CompletenessTheory.BisimulationFaithful inc := by
  constructor
  · intro injective i j bisimilar
    exact injective i j (Quotient.sound bisimilar)
  · intro faithful x y classesEqual
    exact faithful (Quotient.exact classesEqual)

theorem quotient_mk_bijective_iff_bisimulationFaithful
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ((∀ x y : I, Quotient.mk (approxBisimSetoid inc) x =
        Quotient.mk (approxBisimSetoid inc) y → x = y) ∧
      (∀ q : Quotient (approxBisimSetoid inc),
        ∃ x, Quotient.mk (approxBisimSetoid inc) x = q)) ↔
      CompletenessTheory.BisimulationFaithful inc := by
  constructor
  · intro bijective
    exact (quotient_mk_injective_iff_bisimulationFaithful inc).mp
      bijective.left
  · intro faithful
    exact ⟨(quotient_mk_injective_iff_bisimulationFaithful inc).mpr faithful,
      quotient_mk_surjective inc⟩

def BisimulationQuotientMapCollapses
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop :=
  ∃ x y : I, x ≠ y ∧
    Quotient.mk (approxBisimSetoid inc) x =
      Quotient.mk (approxBisimSetoid inc) y

theorem bisimulationQuotientMapCollapses_iff_not_faithful
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BisimulationQuotientMapCollapses inc ↔
      ¬ CompletenessTheory.BisimulationFaithful inc := by
  constructor
  · rintro ⟨x, y, different, classesEqual⟩ faithful
    exact different (faithful (Quotient.exact classesEqual))
  · intro notFaithful
    classical
    exact Classical.byContradiction (fun noWitness => by
      apply notFaithful
      intro x y bisimilar
      exact Classical.byContradiction (fun different =>
        noWitness ⟨x, y, different, Quotient.sound bisimilar⟩))

theorem bisimulationQuotientMapDoesNotCollapse_iff_faithful
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (¬ BisimulationQuotientMapCollapses inc) ↔
      CompletenessTheory.BisimulationFaithful inc := by
  classical
  constructor
  · intro noCollapse
    intro x y bisimilar
    exact Classical.byContradiction (fun different =>
      noCollapse ⟨x, y, different, Quotient.sound bisimilar⟩)
  · intro faithful collapse
    exact (bisimulationQuotientMapCollapses_iff_not_faithful inc).mp collapse
      faithful

/- Concrete confirmation against both faithful instances built so far
   in this project (`natIncidence`, cycle 4; `cycleIncidenceFixed`,
   cycle 27) -- not vacuous, two genuinely different faithful instances
   both confirm the bijection. -/
example : ∀ x y : Nat, Quotient.mk (approxBisimSetoid natIncidence) x =
    Quotient.mk (approxBisimSetoid natIncidence) y → x = y :=
  fun _ _ => quotient_mk_injective_of_faithful natIncidence natIncidence_approxBisim_iff

example : ∀ x y : CycleId, Quotient.mk (approxBisimSetoid cycleIncidenceFixed) x =
    Quotient.mk (approxBisimSetoid cycleIncidenceFixed) y → x = y :=
  fun _ _ => quotient_mk_injective_of_faithful cycleIncidenceFixed cycleIncidenceFixed_approxBisim_iff

/- Research cycle 41 (see RESEARCH_LOG.md): item (b) from cycle 40's
   queue -- does any EXISTING instance in this project have a
   `≈`-quotient in the genuinely interesting middle ground (more than
   one class, fewer than all)? The answer was hiding in plain sight:
   `simplexIncidence`'s `≈`-partition was already FULLY characterized
   across cycles 12/18/21/22/23, long before this project's "third
   generic constructor" thread (cycles 36-40) even started --
   `simplexToShape_iff_approxBisim` proves `≈` is EXACTLY
   `simplexToShape`-agreement, giving exactly THREE classes out of
   SEVEN elements: `{v0,v1,v2}`, `{e01,e02,e12}`, `{face}`. This cycle
   revisits that old result through the new quotient-construction lens
   cycles 38-40 built, rather than reproving anything about
   `simplexIncidence` itself. -/

/- Unlike `cycleIncidence`'s `boundary`/`glue` (cycle 38), which failed
   the well-definedness check `Quotient.lift` needs, `simplexToShape`
   PASSES it -- this is exactly what `simplexToShape_distinguishes`
   (cycle 23) already established (`approxBisim → shape-equal`, the
   precise hypothesis `Quotient.lift` requires). No new proof needed,
   only recognizing the old theorem already had this shape. -/
def simplexBisimulationQuotientClassification :
    BisimulationQuotientClassification (Q := SimplexShape) simplexIncidence where
  classify := simplexToShape
  respects := fun h => simplexToShape_distinguishes _ _ h
  reflects := fun h => simplexToShape_reflects _ _ h
  surjective := by
    intro shape
    cases shape with
    | vertex => exact ⟨SimplexId.v0, rfl⟩
    | edgeShape => exact ⟨SimplexId.e01, rfl⟩
    | faceShape => exact ⟨SimplexId.face, rfl⟩

noncomputable def simplexQuotientToShape :
  Quotient (approxBisimSetoid simplexIncidence) → SimplexShape :=
  Quotient.lift simplexToShape simplexToShape_distinguishes

theorem simplexBisimulationQuotientClassification_exact :
    simplexBisimulationQuotientClassification.lift = simplexQuotientToShape := by
  funext quotient
  induction quotient using Quotient.ind with
  | _ simplex => rfl

/- Injective: `simplexToShape`-agreement implies `≈` too
   (`simplexToShape_reflects`, cycle 22), so two quotient classes
   mapping to the same shape must already have been the same class. -/
theorem simplexQuotientToShape_injective (q1 q2 : Quotient (approxBisimSetoid simplexIncidence))
  (h : simplexQuotientToShape q1 = simplexQuotientToShape q2) : q1 = q2 := by
  induction q1 using Quotient.ind with
  | _ x =>
    induction q2 using Quotient.ind with
    | _ y =>
      unfold simplexQuotientToShape at h
      simp only [Quotient.lift] at h
      exact Quotient.sound (simplexToShape_reflects x y h)

/- Surjective: all three shapes are hit by a concrete element. -/
theorem simplexQuotientToShape_surjective (s : SimplexShape) :
  ∃ q : Quotient (approxBisimSetoid simplexIncidence), simplexQuotientToShape q = s := by
  cases s with
  | vertex => exact ⟨Quotient.mk _ SimplexId.v0, rfl⟩
  | edgeShape => exact ⟨Quotient.mk _ SimplexId.e01, rfl⟩
  | faceShape => exact ⟨Quotient.mk _ SimplexId.face, rfl⟩

/- The headline positive result: a genuine `Incidence SimplexShape
   SimplexRole GraphType` structure on the (isomorphic image of the)
   quotient carrier, hand-built by collapsing each shape's boundary
   entries' targets through `simplexToShape`. Crucially, `well_founded`
   is NOT violated here the way it was for `cycleIncidence`'s
   Subsingleton quotient (cycles 38/39): `vertex`'s boundary is empty,
   `edgeShape`'s entries point only to `vertex` (≠ `edgeShape`), and
   `faceShape`'s entries point only to `edgeShape` (≠ `faceShape`) --
   the shape-grading (0-cells ← 1-cells ← 2-cells) is itself a
   well-founded structure, so collapsing WITHIN each grade never
   creates the kind of self-loop a total collapse (cycleIncidence)
   forces. This is the project's first successful "quotient-shaped"
   `Incidence` construction, a genuine contrast to cycles 38/39's
   negative result -- the middle ground really is different from both
   extremes, not just in how many classes it has. -/
def shapeBoundary : SimplexShape → Boundary SimplexShape SimplexRole
  | .vertex => []
  | .edgeShape =>
    [ { i := .vertex, role := SimplexRole.src, sign := Sign.neg, mult := 1 }
    , { i := .vertex, role := SimplexRole.dst, sign := Sign.pos, mult := 1 } ]
  | .faceShape =>
    [ { i := .edgeShape, role := SimplexRole.src, sign := Sign.pos, mult := 1 }
    , { i := .edgeShape, role := SimplexRole.dst, sign := Sign.neg, mult := 1 }
    , { i := .edgeShape, role := SimplexRole.dst, sign := Sign.pos, mult := 1 } ]

def shapeIncidence : Incidence SimplexShape SimplexRole GraphType where
  boundary := shapeBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = SimplexShape.vertex then some j else some i
  unit     := SimplexShape.vertex
  guards   := Guards.permissive SimplexShape
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [shapeBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  multiplicities := by
    intro i e h
    cases i <;> simp [shapeBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [shapeBoundary] at he <;>
      first
        | (rcases he with he | he | he <;> subst he <;> simp_all)
        | (rcases he with he | he <;> subst he <;> simp_all)
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = SimplexShape.vertex <;> simp [h]
  type_preserve := fun _ _ => rfl

/- An honest limitation, checked rather than assumed: `simplexToShape`
   is NOT a `glue`-homomorphism between `simplexIncidence` and
   `shapeIncidence` -- unlike cycle 28's `cycleToNat_glue_hom` or cycle
   34's `natToFiniteSet_glue_hom`, both of which succeeded. Concrete
   witness: `simplexIncidence.glue v1 face = some v1` (since `v1 ≠
   v0`), which maps to `some vertex`; but `shapeIncidence.glue vertex
   faceShape = some faceShape` (since `vertex = vertex`) -- a genuine
   mismatch. This is consistent with, and a more interesting instance
   of, cycle 38's general finding that `glue` does not respect `≈`:
   `shapeIncidence` is A valid `Incidence` structure living on the
   quotient's carrier, hand-built independently, not one *derived* from
   `simplexIncidence`'s own `glue` via any structure-preserving
   transport. -/
theorem simplexToShape_not_glue_hom :
  (simplexIncidence.glue SimplexId.v1 SimplexId.face).map simplexToShape ≠
    shapeIncidence.glue (simplexToShape SimplexId.v1) (simplexToShape SimplexId.face) := by
  decide

end IncidenceCore
