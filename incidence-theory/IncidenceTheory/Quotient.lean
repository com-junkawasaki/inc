import IncidenceTheory.Cycle
import IncidenceTheory.Peano
import IncidenceTheory.PathComplex
import IncidenceTheory.Product
import IncidenceTheory.Simplex
import IncidenceTheory.Tree

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

def BisimulationInvariantMap
    {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q) : Prop :=
  ∀ ⦃x y⦄, approxBisim inc x y → map x = map y

theorem factors_through_bisimulationQuotient_iff_invariant
    {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q) :
    (∃ lift : Quotient (approxBisimSetoid inc) → Q,
      ∀ x, lift (Quotient.mk (approxBisimSetoid inc) x) = map x) ↔
      BisimulationInvariantMap inc map := by
  constructor
  · rintro ⟨lift, factors⟩ x y bisimilar
    rw [← factors x, ← factors y, Quotient.sound bisimilar]
  · intro invariant
    exact ⟨Quotient.lift map (fun _ _ bisimilar => invariant bisimilar),
      fun _ => rfl⟩

theorem bisimulationQuotient_factorization_unique
    {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q)
    (first second : Quotient (approxBisimSetoid inc) → Q)
    (firstFactors : ∀ x,
      first (Quotient.mk (approxBisimSetoid inc) x) = map x)
    (secondFactors : ∀ x,
      second (Quotient.mk (approxBisimSetoid inc) x) = map x) :
    first = second := by
  funext quotient
  induction quotient using Quotient.ind with
  | _ representative =>
      exact (firstFactors representative).trans
        (secondFactors representative).symm

theorem bisimulationQuotient_universal_property
    {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q)
    (invariant : BisimulationInvariantMap inc map) :
    ∃ lift : Quotient (approxBisimSetoid inc) → Q,
      (∀ x, lift (Quotient.mk (approxBisimSetoid inc) x) = map x) ∧
      ∀ candidate : Quotient (approxBisimSetoid inc) → Q,
        (∀ x, candidate (Quotient.mk (approxBisimSetoid inc) x) = map x) →
        candidate = lift := by
  refine ⟨Quotient.lift map (fun _ _ bisimilar => invariant bisimilar),
    fun _ => rfl, ?_⟩
  intro candidate candidateFactors
  exact bisimulationQuotient_factorization_unique inc map candidate _
    candidateFactors (fun _ => rfl)

def bisimulationQuotientLift
    {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q)
    (invariant : BisimulationInvariantMap inc map) :
    Quotient (approxBisimSetoid inc) → Q :=
  Quotient.lift map (fun _ _ bisimilar => invariant bisimilar)

theorem bisimulationQuotientLift_mk
    {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q)
    (invariant : BisimulationInvariantMap inc map) (x : I) :
    bisimulationQuotientLift inc map invariant
      (Quotient.mk (approxBisimSetoid inc) x) = map x := rfl

theorem bisimulationQuotientLift_unique
    {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q)
    (invariant : BisimulationInvariantMap inc map)
    (candidate : Quotient (approxBisimSetoid inc) → Q)
    (candidateFactors : ∀ x,
      candidate (Quotient.mk (approxBisimSetoid inc) x) = map x) :
    candidate = bisimulationQuotientLift inc map invariant :=
  bisimulationQuotient_factorization_unique inc map candidate _
    candidateFactors (bisimulationQuotientLift_mk inc map invariant)

theorem bisimulationQuotientLift_mk_eq_identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    bisimulationQuotientLift inc
      (Quotient.mk (approxBisimSetoid inc))
      (fun _ _ bisimilar => Quotient.sound bisimilar) = id := by
  apply bisimulationQuotient_factorization_unique inc
    (Quotient.mk (approxBisimSetoid inc))
  · intro x
    rfl
  · intro x
    rfl

theorem bisimulationQuotientLift_comp
    {I R T Q P : Type u} [DecidableEq I]
    (inc : Incidence I R T) (map : I → Q)
    (invariant : BisimulationInvariantMap inc map) (after : Q → P) :
    bisimulationQuotientLift inc (after ∘ map)
      (fun _ _ bisimilar => congrArg after (invariant bisimilar)) =
      after ∘ bisimulationQuotientLift inc map invariant := by
  apply bisimulationQuotient_factorization_unique inc (after ∘ map)
  · intro x
    rfl
  · intro x
    rfl

theorem BisimulationQuotientClassification.lift_eq_bisimulationQuotientLift
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    classification.lift = bisimulationQuotientLift inc
      classification.classify
      (fun _ _ bisimilar => classification.respects bisimilar) := by
  apply bisimulationQuotient_factorization_unique inc classification.classify
  · intro x
    rfl
  · intro x
    rfl

noncomputable def BisimulationQuotientClassification.equivalence
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    IncTypeEquivalence (IncidenceQuotient inc) Q where
  forward := classification.lift
  inverse := fun q => Classical.choose (classification.lift_surjective q)
  inverse_forward := by
    intro quotient
    apply classification.lift_injective
    exact Classical.choose_spec
      (classification.lift_surjective (classification.lift quotient))
  forward_inverse := by
    intro q
    exact Classical.choose_spec (classification.lift_surjective q)

theorem BisimulationQuotientClassification.equivalence_forward
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    classification.equivalence.forward = classification.lift := rfl

def BisimulationQuotientClassification.mappedSourceBoundary
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (x : I) : Boundary Q R :=
  (inc.boundary x).map fun endpoint =>
    { endpoint with i := classification.classify endpoint.i }

def BisimulationQuotientClassification.BoundaryInvariant
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) : Prop :=
  BisimulationInvariantMap inc classification.mappedSourceBoundary

def BisimulationQuotientClassification.BoundaryRealization
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) : Prop :=
  ∃ boundary : Q → Boundary Q R,
    ∀ x, boundary (classification.classify x) =
      classification.mappedSourceBoundary x

noncomputable def BisimulationQuotientClassification.canonicalBoundary
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.BoundaryInvariant) : Q → Boundary Q R :=
  bisimulationQuotientLift inc classification.mappedSourceBoundary invariant ∘
    classification.equivalence.inverse

theorem BisimulationQuotientClassification.canonicalBoundary_classify
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.BoundaryInvariant) (x : I) :
    classification.canonicalBoundary invariant (classification.classify x) =
      classification.mappedSourceBoundary x := by
  unfold canonicalBoundary
  change bisimulationQuotientLift inc classification.mappedSourceBoundary invariant
      (classification.equivalence.inverse (classification.classify x)) = _
  have inverseClassify := classification.equivalence.inverse_forward
    (Quotient.mk (approxBisimSetoid inc) x)
  change classification.equivalence.inverse (classification.classify x) =
    Quotient.mk (approxBisimSetoid inc) x at inverseClassify
  rw [inverseClassify]
  rfl

theorem BisimulationQuotientClassification.boundaryRealization_iff_invariant
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    classification.BoundaryRealization ↔ classification.BoundaryInvariant := by
  constructor
  · rintro ⟨boundary, realizes⟩ x y bisimilar
    rw [← realizes x, ← realizes y, classification.respects bisimilar]
  · intro invariant
    exact ⟨classification.canonicalBoundary invariant,
      classification.canonicalBoundary_classify invariant⟩

theorem BisimulationQuotientClassification.canonicalBoundary_unique
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.BoundaryInvariant)
    (candidate : Q → Boundary Q R)
    (realizes : ∀ x, candidate (classification.classify x) =
      classification.mappedSourceBoundary x) :
    candidate = classification.canonicalBoundary invariant := by
  funext q
  rcases classification.surjective q with ⟨x, rfl⟩
  rw [realizes, classification.canonicalBoundary_classify]

theorem approxBisim_typeFunc_eq
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {x y : I} (bisimilar : approxBisim inc x y) :
    inc.typeFunc x = inc.typeFunc y := by
  rcases bisimilar with ⟨relation, isBisimulation, related⟩
  exact (isBisimulation x y related).left

def BisimulationQuotientClassification.typeInvariant
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (_classification : BisimulationQuotientClassification (Q := Q) inc) :
    BisimulationInvariantMap inc inc.typeFunc :=
  fun _ _ bisimilar => approxBisim_typeFunc_eq bisimilar

noncomputable def BisimulationQuotientClassification.canonicalType
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    Q → T :=
  bisimulationQuotientLift inc inc.typeFunc classification.typeInvariant ∘
    classification.equivalence.inverse

theorem BisimulationQuotientClassification.canonicalType_classify
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (x : I) :
    classification.canonicalType (classification.classify x) =
      inc.typeFunc x := by
  unfold canonicalType
  change bisimulationQuotientLift inc inc.typeFunc classification.typeInvariant
      (classification.equivalence.inverse (classification.classify x)) = _
  have inverseClassify := classification.equivalence.inverse_forward
    (Quotient.mk (approxBisimSetoid inc) x)
  change classification.equivalence.inverse (classification.classify x) =
    Quotient.mk (approxBisimSetoid inc) x at inverseClassify
  rw [inverseClassify]
  rfl

theorem BisimulationQuotientClassification.canonicalType_unique
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (candidate : Q → T)
    (realizes : ∀ x, candidate (classification.classify x) = inc.typeFunc x) :
    candidate = classification.canonicalType := by
  funext q
  rcases classification.surjective q with ⟨x, rfl⟩
  rw [realizes, classification.canonicalType_classify]

theorem BisimulationQuotientClassification.canonicalBoundary_type_consistent
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (boundaryInvariant : classification.BoundaryInvariant) :
    ∀ (q : Q) (e : Endpoint Q R),
      e ∈ classification.canonicalBoundary boundaryInvariant q →
      classification.canonicalType e.i = classification.canonicalType q := by
  intro q e member
  rcases classification.surjective q with ⟨x, rfl⟩
  rw [classification.canonicalBoundary_classify] at member
  rcases List.mem_map.mp member with ⟨sourceEndpoint, sourceMember, endpointEq⟩
  subst e
  simp only [BisimulationQuotientClassification.canonicalType_classify]
  exact inc.type_consistent x sourceEndpoint sourceMember

theorem BisimulationQuotientClassification.canonicalBoundary_sign_rules
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (boundaryInvariant : classification.BoundaryInvariant) :
    ∀ (q : Q) (e : Endpoint Q R),
      e ∈ classification.canonicalBoundary boundaryInvariant q →
      e.sign = Sign.neg ∨ e.sign = Sign.zero ∨ e.sign = Sign.pos := by
  intro q e member
  rcases classification.surjective q with ⟨x, rfl⟩
  rw [classification.canonicalBoundary_classify] at member
  rcases List.mem_map.mp member with ⟨sourceEndpoint, sourceMember, endpointEq⟩
  subst e
  exact inc.sign_rules x sourceEndpoint sourceMember

theorem BisimulationQuotientClassification.canonicalBoundary_multiplicities
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (boundaryInvariant : classification.BoundaryInvariant) :
    ∀ (q : Q) (e : Endpoint Q R),
      e ∈ classification.canonicalBoundary boundaryInvariant q → e.mult ≥ 1 := by
  intro q e member
  rcases classification.surjective q with ⟨x, rfl⟩
  rw [classification.canonicalBoundary_classify] at member
  rcases List.mem_map.mp member with ⟨sourceEndpoint, sourceMember, endpointEq⟩
  subst e
  exact inc.multiplicities x sourceEndpoint sourceMember

def BisimulationQuotientClassification.mappedSourceGlue
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (x y : I) : Option Q :=
  (inc.glue x y).map classification.classify

def BisimulationQuotientClassification.GlueInvariant
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) : Prop :=
  ∀ ⦃x x' y y'⦄, approxBisim inc x x' → approxBisim inc y y' →
    classification.mappedSourceGlue x y =
      classification.mappedSourceGlue x' y'

def BisimulationQuotientClassification.GlueRealization
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) : Prop :=
  ∃ glue : Q → Q → Option Q,
    ∀ x y, glue (classification.classify x) (classification.classify y) =
      classification.mappedSourceGlue x y

noncomputable def BisimulationQuotientClassification.representative
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (q : Q) : I :=
  Classical.choose (classification.surjective q)

theorem BisimulationQuotientClassification.classify_representative
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (q : Q) :
    classification.classify (classification.representative q) = q :=
  Classical.choose_spec (classification.surjective q)

noncomputable def BisimulationQuotientClassification.canonicalGlue
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (_invariant : classification.GlueInvariant) : Q → Q → Option Q :=
  fun q r => classification.mappedSourceGlue
    (classification.representative q) (classification.representative r)

theorem BisimulationQuotientClassification.canonicalGlue_classify
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.GlueInvariant) (x y : I) :
    classification.canonicalGlue invariant
        (classification.classify x) (classification.classify y) =
      classification.mappedSourceGlue x y := by
  apply invariant
  · apply classification.reflects
    exact classification.classify_representative (classification.classify x)
  · apply classification.reflects
    exact classification.classify_representative (classification.classify y)

theorem BisimulationQuotientClassification.glueRealization_iff_invariant
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    classification.GlueRealization ↔ classification.GlueInvariant := by
  constructor
  · rintro ⟨glue, realizes⟩ x x' y y' hx hy
    rw [← realizes x y, ← realizes x' y', classification.respects hx,
      classification.respects hy]
  · intro invariant
    exact ⟨classification.canonicalGlue invariant,
      classification.canonicalGlue_classify invariant⟩

theorem BisimulationQuotientClassification.canonicalGlue_unique
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.GlueInvariant)
    (candidate : Q → Q → Option Q)
    (realizes : ∀ x y,
      candidate (classification.classify x) (classification.classify y) =
        classification.mappedSourceGlue x y) :
    candidate = classification.canonicalGlue invariant := by
  funext q r
  rcases classification.surjective q with ⟨x, rfl⟩
  rcases classification.surjective r with ⟨y, rfl⟩
  rw [realizes, classification.canonicalGlue_classify]

theorem BisimulationQuotientClassification.canonicalGlue_unit_left
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.GlueInvariant) (q : Q) :
    classification.canonicalGlue invariant
        (classification.classify inc.unit) q = some q := by
  rcases classification.surjective q with ⟨x, rfl⟩
  rw [classification.canonicalGlue_classify]
  simp [BisimulationQuotientClassification.mappedSourceGlue, inc.unit_left]

theorem BisimulationQuotientClassification.canonicalGlue_unit_right
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.GlueInvariant) (q : Q) :
    classification.canonicalGlue invariant
        q (classification.classify inc.unit) = some q := by
  rcases classification.surjective q with ⟨x, rfl⟩
  rw [classification.canonicalGlue_classify]
  simp [BisimulationQuotientClassification.mappedSourceGlue, inc.unit_right]

def BisimulationQuotientClassification.GuardInvariant
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (_classification : BisimulationQuotientClassification (Q := Q) inc) : Prop :=
  ∀ ⦃x x' y y'⦄, approxBisim inc x x' → approxBisim inc y y' →
    inc.guards.allow x y = inc.guards.allow x' y'

def BisimulationQuotientClassification.GuardRealization
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) : Prop :=
  ∃ guards : Guards Q,
    ∀ x y, guards.allow (classification.classify x) (classification.classify y) =
      inc.guards.allow x y

noncomputable def BisimulationQuotientClassification.canonicalGuards
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (_invariant : classification.GuardInvariant) : Guards Q where
  allow := fun q r => inc.guards.allow
    (classification.representative q) (classification.representative r)

theorem BisimulationQuotientClassification.canonicalGuards_allow_classify
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.GuardInvariant) (x y : I) :
    (classification.canonicalGuards invariant).allow
        (classification.classify x) (classification.classify y) =
      inc.guards.allow x y := by
  apply invariant
  · apply classification.reflects
    exact classification.classify_representative (classification.classify x)
  · apply classification.reflects
    exact classification.classify_representative (classification.classify y)

theorem BisimulationQuotientClassification.guardRealization_iff_invariant
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    classification.GuardRealization ↔ classification.GuardInvariant := by
  constructor
  · rintro ⟨guards, realizes⟩ x x' y y' hx hy
    rw [← realizes x y, ← realizes x' y', classification.respects hx,
      classification.respects hy]
  · intro invariant
    exact ⟨classification.canonicalGuards invariant,
      classification.canonicalGuards_allow_classify invariant⟩

theorem BisimulationQuotientClassification.canonicalGuards_unique
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.GuardInvariant)
    (candidate : Guards Q)
    (realizes : ∀ x y,
      candidate.allow (classification.classify x) (classification.classify y) =
        inc.guards.allow x y) :
    candidate = classification.canonicalGuards invariant := by
  cases candidate with
  | mk allow =>
      apply congrArg Guards.mk
      funext q r
      rcases classification.surjective q with ⟨x, rfl⟩
      rcases classification.surjective r with ⟨y, rfl⟩
      calc
        allow (classification.classify x) (classification.classify y) =
            inc.guards.allow x y := realizes x y
        _ = (classification.canonicalGuards invariant).allow
            (classification.classify x) (classification.classify y) :=
          (classification.canonicalGuards_allow_classify invariant x y).symm


noncomputable def BisimulationQuotientClassification.targetEquivalence
    {I R T Q₁ Q₂ : Type u} [DecidableEq I] {inc : Incidence I R T}
    (first : BisimulationQuotientClassification (Q := Q₁) inc)
    (second : BisimulationQuotientClassification (Q := Q₂) inc) :
    IncTypeEquivalence Q₁ Q₂ :=
  second.equivalence.trans first.equivalence.symm

theorem BisimulationQuotientClassification.targetEquivalence_classify
    {I R T Q₁ Q₂ : Type u} [DecidableEq I] {inc : Incidence I R T}
    (first : BisimulationQuotientClassification (Q := Q₁) inc)
    (second : BisimulationQuotientClassification (Q := Q₂) inc)
    (x : I) :
    (first.targetEquivalence second).forward (first.classify x) =
      second.classify x := by
  change second.lift (first.equivalence.inverse (first.classify x)) =
    second.classify x
  have inverseClassify := first.equivalence.inverse_forward
    (Quotient.mk (approxBisimSetoid inc) x)
  change first.equivalence.inverse (first.classify x) =
    Quotient.mk (approxBisimSetoid inc) x at inverseClassify
  rw [inverseClassify]
  rfl

theorem BisimulationQuotientClassification.targetEquivalence_unique
    {I R T Q₁ Q₂ : Type u} [DecidableEq I] {inc : Incidence I R T}
    (first : BisimulationQuotientClassification (Q := Q₁) inc)
    (second : BisimulationQuotientClassification (Q := Q₂) inc)
    (candidate : Q₁ → Q₂)
    (commutes : ∀ x, candidate (first.classify x) = second.classify x) :
    candidate = (first.targetEquivalence second).forward := by
  funext q
  rcases first.surjective q with ⟨x, rfl⟩
  rw [commutes,
    BisimulationQuotientClassification.targetEquivalence_classify]

theorem BisimulationQuotientClassification.targetEquivalence_self
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    classification.targetEquivalence classification =
      IncTypeEquivalence.refl Q := by
  apply IncTypeEquivalence.ext_forward
  exact (classification.targetEquivalence_unique classification id
    (fun _ => rfl)).symm

theorem BisimulationQuotientClassification.targetEquivalence_comp
    {I R T Q₁ Q₂ Q₃ : Type u} [DecidableEq I]
    {inc : Incidence I R T}
    (first : BisimulationQuotientClassification (Q := Q₁) inc)
    (second : BisimulationQuotientClassification (Q := Q₂) inc)
    (third : BisimulationQuotientClassification (Q := Q₃) inc) :
    (second.targetEquivalence third).trans
        (first.targetEquivalence second) =
      first.targetEquivalence third := by
  apply IncTypeEquivalence.ext_forward
  apply first.targetEquivalence_unique third
  intro x
  change (second.targetEquivalence third).forward
      ((first.targetEquivalence second).forward (first.classify x)) =
    third.classify x
  rw [first.targetEquivalence_classify second,
    second.targetEquivalence_classify third]

theorem BisimulationQuotientClassification.targetEquivalence_symm
    {I R T Q₁ Q₂ : Type u} [DecidableEq I]
    {inc : Incidence I R T}
    (first : BisimulationQuotientClassification (Q := Q₁) inc)
    (second : BisimulationQuotientClassification (Q := Q₂) inc) :
    (first.targetEquivalence second).symm =
      second.targetEquivalence first := by
  apply IncTypeEquivalence.ext_forward
  apply second.targetEquivalence_unique first
  intro x
  have inverseForward := (first.targetEquivalence second).inverse_forward
    (first.classify x)
  rw [first.targetEquivalence_classify second] at inverseForward
  exact inverseForward

noncomputable def BisimulationQuotientClassification.transportTarget
    {I R T Q Q' : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (equivalence : IncTypeEquivalence Q Q') :
    BisimulationQuotientClassification (Q := Q') inc where
  classify := equivalence.forward ∘ classification.classify
  respects := by
    intro x y bisimilar
    exact congrArg equivalence.forward (classification.respects bisimilar)
  reflects := by
    intro x y imagesEqual
    apply classification.reflects
    have inverseImages := congrArg equivalence.inverse imagesEqual
    simpa [Function.comp_apply, equivalence.inverse_forward] using inverseImages
  surjective := by
    intro q'
    rcases classification.surjective (equivalence.inverse q') with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change equivalence.forward (classification.classify x) = q'
    rw [hx, equivalence.forward_inverse]

theorem BisimulationQuotientClassification.ext
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second : BisimulationQuotientClassification (Q := Q) inc}
    (classifyEq : first.classify = second.classify) : first = second := by
  cases first
  cases second
  cases classifyEq
  rfl

theorem BisimulationQuotientClassification.transportTarget_classify
    {I R T Q Q' : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (equivalence : IncTypeEquivalence Q Q') (x : I) :
    (classification.transportTarget equivalence).classify x =
      equivalence.forward (classification.classify x) := rfl

theorem BisimulationQuotientClassification.targetEquivalence_transportTarget
    {I R T Q Q' : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (equivalence : IncTypeEquivalence Q Q') :
    classification.targetEquivalence
        (classification.transportTarget equivalence) = equivalence := by
  apply IncTypeEquivalence.ext_forward
  exact (classification.targetEquivalence_unique
    (classification.transportTarget equivalence) equivalence.forward
    (fun _ => rfl)).symm

theorem BisimulationQuotientClassification.transportTarget_refl
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    classification.transportTarget (IncTypeEquivalence.refl Q) =
      classification := by
  apply BisimulationQuotientClassification.ext
  funext x
  rfl

theorem BisimulationQuotientClassification.transportTarget_comp
    {I R T Q₁ Q₂ Q₃ : Type u} [DecidableEq I]
    {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q₁) inc)
    (first : IncTypeEquivalence Q₁ Q₂)
    (second : IncTypeEquivalence Q₂ Q₃) :
    (classification.transportTarget first).transportTarget second =
      classification.transportTarget (second.trans first) := by
  apply BisimulationQuotientClassification.ext
  funext x
  rfl

theorem BisimulationQuotientClassification.transportTarget_symm
    {I R T Q Q' : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (equivalence : IncTypeEquivalence Q Q') :
    (classification.transportTarget equivalence).transportTarget
        equivalence.symm = classification := by
  rw [classification.transportTarget_comp equivalence equivalence.symm,
    IncTypeEquivalence.symm_trans_self,
    classification.transportTarget_refl]

def bisimulationQuotientClassificationOfKernel
    {I R T Q : Type u} [DecidableEq I] (inc : Incidence I R T)
    (classify : I → Q)
    (kernel : ∀ x y, classify x = classify y ↔ approxBisim inc x y)
    (surjective : ∀ q : Q, ∃ x, classify x = q) :
    BisimulationQuotientClassification (Q := Q) inc where
  classify := classify
  respects := by
    intro x y bisimilar
    exact (kernel x y).mpr bisimilar
  reflects := by
    intro x y equal
    exact (kernel x y).mp equal
  surjective := surjective

theorem BisimulationQuotientClassification.kernel_iff
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (x y : I) :
    classification.classify x = classification.classify y ↔
      approxBisim inc x y :=
  ⟨classification.reflects, classification.respects⟩

theorem bisimulationQuotientClassification_exists_with_map_iff
    {I R T Q : Type u} [DecidableEq I] (inc : Incidence I R T)
    (classify : I → Q) :
    (∃ classification : BisimulationQuotientClassification (Q := Q) inc,
      classification.classify = classify) ↔
      (∀ x y, classify x = classify y ↔ approxBisim inc x y) ∧
      ∀ q : Q, ∃ x, classify x = q := by
  constructor
  · rintro ⟨classification, rfl⟩
    exact ⟨classification.kernel_iff, classification.surjective⟩
  · rintro ⟨kernel, surjective⟩
    exact ⟨bisimulationQuotientClassificationOfKernel inc classify
      kernel surjective, rfl⟩

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

structure BisimulationQuotientIncidencePresentation
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    (source : Incidence I R T) where
  classification : BisimulationQuotientClassification (Q := Q) source
  target : Incidence Q QR QT
  boundary_iff : ∀ atom,
    IncidenceBoundaryValuation target (classification.classify atom) ↔
      IncidenceBoundaryValuation source atom

/- A reusable sufficient condition for constructing the target Incidence of a
   quotient presentation.  The only structurally difficult Incidence
   obligation on a collapsed carrier is absence of boundary self-loops.  A
   natural-number grading which strictly decreases along every boundary edge
   discharges that obligation uniformly. -/
structure GradedIncidenceData (Q QR QT : Type u) [DecidableEq Q] where
  boundary : Q → Boundary Q QR
  typeFunc : Q → QT
  glue : Q → Q → Option Q
  unit : Q
  guards : Guards Q
  grade : Q → Nat
  boundary_decreases : ∀ (q : Q) (e : Endpoint Q QR),
    e ∈ boundary q → grade e.i < grade q
  type_consistent : ∀ (q : Q) (e : Endpoint Q QR),
    e ∈ boundary q → typeFunc e.i = typeFunc q
  sign_rules : ∀ (q : Q) (e : Endpoint Q QR), e ∈ boundary q →
    e.sign = Sign.neg ∨ e.sign = Sign.zero ∨ e.sign = Sign.pos
  multiplicities : ∀ (q : Q) (e : Endpoint Q QR),
    e ∈ boundary q → e.mult ≥ 1
  unit_left : ∀ q, glue unit q = some q
  unit_right : ∀ q, glue q unit = some q
  type_preserve : ∀ {i j k}, guards.allow i j →
    glue i j = some k → typeFunc k = typeFunc i

/- Raw target data with every Incidence law except `well_founded`.  This
   separates the exact obstruction to putting an Incidence on a quotient
   carrier from the independent typing, sign, multiplicity, and gluing laws. -/
structure IncidenceCandidateData (Q QR QT : Type u) [DecidableEq Q] where
  boundary : Q → Boundary Q QR
  typeFunc : Q → QT
  glue : Q → Q → Option Q
  unit : Q
  guards : Guards Q
  type_consistent : ∀ (q : Q) (e : Endpoint Q QR),
    e ∈ boundary q → typeFunc e.i = typeFunc q
  sign_rules : ∀ (q : Q) (e : Endpoint Q QR), e ∈ boundary q →
    e.sign = Sign.neg ∨ e.sign = Sign.zero ∨ e.sign = Sign.pos
  multiplicities : ∀ (q : Q) (e : Endpoint Q QR),
    e ∈ boundary q → e.mult ≥ 1
  unit_left : ∀ q, glue unit q = some q
  unit_right : ∀ q, glue q unit = some q
  type_preserve : ∀ {i j k}, guards.allow i j →
    glue i j = some k → typeFunc k = typeFunc i

def IncidenceCandidateData.HasNoBoundarySelfLoop
    {Q QR QT : Type u} [DecidableEq Q]
    (data : IncidenceCandidateData Q QR QT) : Prop :=
  ∀ q, ¬ ∃ e ∈ data.boundary q, e.i = q

def IncidenceCandidateData.toIncidence
    {Q QR QT : Type u} [DecidableEq Q]
    (data : IncidenceCandidateData Q QR QT)
    (wellFounded : data.HasNoBoundarySelfLoop) : Incidence Q QR QT where
  boundary := data.boundary
  typeFunc := data.typeFunc
  glue := data.glue
  unit := data.unit
  guards := data.guards
  type_consistent := data.type_consistent
  sign_rules := data.sign_rules
  multiplicities := data.multiplicities
  well_founded := wellFounded
  unit_left := data.unit_left
  unit_right := data.unit_right
  type_preserve := data.type_preserve

def IncidenceCandidateData.RealizedBy
    {Q QR QT : Type u} [DecidableEq Q]
    (data : IncidenceCandidateData Q QR QT) : Prop :=
  ∃ target : Incidence Q QR QT,
    target.boundary = data.boundary ∧
    target.typeFunc = data.typeFunc ∧
    target.glue = data.glue ∧
    target.unit = data.unit ∧
    target.guards = data.guards

theorem IncidenceCandidateData.realizedBy_iff_noBoundarySelfLoop
    {Q QR QT : Type u} [DecidableEq Q]
    (data : IncidenceCandidateData Q QR QT) :
    data.RealizedBy ↔ data.HasNoBoundarySelfLoop := by
  constructor
  · rintro ⟨target, boundaryEq, _, _, _, _⟩ q selfLoop
    apply target.well_founded q
    simpa [boundaryEq] using selfLoop
  · intro noSelfLoop
    exact ⟨data.toIncidence noSelfLoop, rfl, rfl, rfl, rfl, rfl⟩

structure CanonicalQuotientIncidenceCoherence
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) where
  boundaryInvariant : classification.BoundaryInvariant
  glueInvariant : classification.GlueInvariant
  boundary_no_self : ∀ q,
    ¬ ∃ e ∈ classification.canonicalBoundary boundaryInvariant q, e.i = q
  glue_type_preserve : ∀ x y q,
    classification.mappedSourceGlue x y = some q →
      classification.canonicalType q = inc.typeFunc x

noncomputable def CanonicalQuotientIncidenceCoherence.candidate
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalQuotientIncidenceCoherence classification) :
    IncidenceCandidateData Q R T where
  boundary := classification.canonicalBoundary coherence.boundaryInvariant
  typeFunc := classification.canonicalType
  glue := classification.canonicalGlue coherence.glueInvariant
  unit := classification.classify inc.unit
  guards := Guards.permissive Q
  type_consistent :=
    classification.canonicalBoundary_type_consistent coherence.boundaryInvariant
  sign_rules :=
    classification.canonicalBoundary_sign_rules coherence.boundaryInvariant
  multiplicities :=
    classification.canonicalBoundary_multiplicities coherence.boundaryInvariant
  unit_left := classification.canonicalGlue_unit_left coherence.glueInvariant
  unit_right := classification.canonicalGlue_unit_right coherence.glueInvariant
  type_preserve := by
    intro q r k _ glueEq
    rcases classification.surjective q with ⟨x, rfl⟩
    rcases classification.surjective r with ⟨y, rfl⟩
    rw [classification.canonicalGlue_classify] at glueEq
    exact (coherence.glue_type_preserve x y k glueEq).trans
      (classification.canonicalType_classify x).symm

theorem CanonicalQuotientIncidenceCoherence.candidate_noBoundarySelfLoop
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalQuotientIncidenceCoherence classification) :
    coherence.candidate.HasNoBoundarySelfLoop :=
  coherence.boundary_no_self

noncomputable def CanonicalQuotientIncidenceCoherence.toIncidence
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalQuotientIncidenceCoherence classification) :
    Incidence Q R T :=
  coherence.candidate.toIncidence coherence.candidate_noBoundarySelfLoop

theorem CanonicalQuotientIncidenceCoherence.toIncidence_boundary_classify
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalQuotientIncidenceCoherence classification) (x : I) :
    coherence.toIncidence.boundary (classification.classify x) =
      classification.mappedSourceBoundary x :=
  classification.canonicalBoundary_classify coherence.boundaryInvariant x

theorem CanonicalQuotientIncidenceCoherence.toIncidence_glue_classify
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalQuotientIncidenceCoherence classification) (x y : I) :
    coherence.toIncidence.glue
        (classification.classify x) (classification.classify y) =
      classification.mappedSourceGlue x y :=
  classification.canonicalGlue_classify coherence.glueInvariant x y

structure CanonicalGuardedQuotientIncidenceCoherence
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    extends CanonicalQuotientIncidenceCoherence classification where
  guardInvariant : classification.GuardInvariant

noncomputable def CanonicalGuardedQuotientIncidenceCoherence.candidate
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalGuardedQuotientIncidenceCoherence classification) :
    IncidenceCandidateData Q R T where
  boundary := classification.canonicalBoundary coherence.boundaryInvariant
  typeFunc := classification.canonicalType
  glue := classification.canonicalGlue coherence.glueInvariant
  unit := classification.classify inc.unit
  guards := classification.canonicalGuards coherence.guardInvariant
  type_consistent :=
    classification.canonicalBoundary_type_consistent coherence.boundaryInvariant
  sign_rules :=
    classification.canonicalBoundary_sign_rules coherence.boundaryInvariant
  multiplicities :=
    classification.canonicalBoundary_multiplicities coherence.boundaryInvariant
  unit_left := classification.canonicalGlue_unit_left coherence.glueInvariant
  unit_right := classification.canonicalGlue_unit_right coherence.glueInvariant
  type_preserve := by
    intro q r k _ glueEq
    rcases classification.surjective q with ⟨x, rfl⟩
    rcases classification.surjective r with ⟨y, rfl⟩
    rw [classification.canonicalGlue_classify] at glueEq
    exact (coherence.glue_type_preserve x y k glueEq).trans
      (classification.canonicalType_classify x).symm

theorem CanonicalGuardedQuotientIncidenceCoherence.candidate_noBoundarySelfLoop
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalGuardedQuotientIncidenceCoherence classification) :
    coherence.candidate.HasNoBoundarySelfLoop :=
  coherence.boundary_no_self

noncomputable def CanonicalGuardedQuotientIncidenceCoherence.toIncidence
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalGuardedQuotientIncidenceCoherence classification) :
    Incidence Q R T :=
  coherence.candidate.toIncidence coherence.candidate_noBoundarySelfLoop

theorem CanonicalGuardedQuotientIncidenceCoherence.toIncidence_guard_classify
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q]
    {inc : Incidence I R T}
    {classification : BisimulationQuotientClassification (Q := Q) inc}
    (coherence : CanonicalGuardedQuotientIncidenceCoherence classification)
    (x y : I) :
    coherence.toIncidence.guards.allow
        (classification.classify x) (classification.classify y) =
      inc.guards.allow x y :=
  classification.canonicalGuards_allow_classify coherence.guardInvariant x y

def GradedIncidenceData.candidate
    {Q QR QT : Type u} [DecidableEq Q]
    (data : GradedIncidenceData Q QR QT) :
    IncidenceCandidateData Q QR QT where
  boundary := data.boundary
  typeFunc := data.typeFunc
  glue := data.glue
  unit := data.unit
  guards := data.guards
  type_consistent := data.type_consistent
  sign_rules := data.sign_rules
  multiplicities := data.multiplicities
  unit_left := data.unit_left
  unit_right := data.unit_right
  type_preserve := data.type_preserve

theorem GradedIncidenceData.hasNoBoundarySelfLoop
    {Q QR QT : Type u} [DecidableEq Q]
    (data : GradedIncidenceData Q QR QT) :
    data.candidate.HasNoBoundarySelfLoop := by
  rintro q ⟨e, member, self⟩
  have decreases := data.boundary_decreases q e member
  rw [self] at decreases
  exact Nat.lt_irrefl _ decreases

def GradedIncidenceData.toIncidence
    {Q QR QT : Type u} [DecidableEq Q]
    (data : GradedIncidenceData Q QR QT) : Incidence Q QR QT where
  boundary := data.boundary
  typeFunc := data.typeFunc
  glue := data.glue
  unit := data.unit
  guards := data.guards
  type_consistent := data.type_consistent
  sign_rules := data.sign_rules
  multiplicities := data.multiplicities
  well_founded := data.hasNoBoundarySelfLoop
  unit_left := data.unit_left
  unit_right := data.unit_right
  type_preserve := data.type_preserve

structure GradedBisimulationQuotientPresentation
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    (source : Incidence I R T) where
  classification : BisimulationQuotientClassification (Q := Q) source
  data : GradedIncidenceData Q QR QT
  boundary_iff : ∀ atom,
    IncidenceBoundaryValuation data.toIncidence (classification.classify atom) ↔
      IncidenceBoundaryValuation source atom

def GradedBisimulationQuotientPresentation.toPresentation
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (graded : GradedBisimulationQuotientPresentation
      (Q := Q) (QR := QR) (QT := QT) source) :
    BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source where
  classification := graded.classification
  target := graded.data.toIncidence
  boundary_iff := graded.boundary_iff

noncomputable def BisimulationQuotientIncidencePresentation.quotientEquivalence
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source) :
    IncTypeEquivalence (IncidenceQuotient source) Q :=
  presentation.classification.equivalence

def BisimulationQuotientIncidencePresentation.observationEmbedding
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source) :
    IncidenceBoundaryObservationEmbedding source presentation.target where
  map := presentation.classification.classify
  boundary_iff := presentation.boundary_iff

theorem BisimulationQuotientIncidencePresentation.satisfies_iff
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source)
    (formula : Formula I) :
    IncidenceBoundarySatisfies presentation.target
        (formula.map presentation.classification.classify) ↔
      IncidenceBoundarySatisfies source formula :=
  presentation.observationEmbedding.satisfies_iff formula

theorem BisimulationQuotientIncidencePresentation.entails_iff
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source)
    (context : List (Formula I)) (formula : Formula I) :
    IncidenceBoundaryEntails presentation.target
        (Formula.mapContext presentation.classification.classify context)
        (formula.map presentation.classification.classify) ↔
      IncidenceBoundaryEntails source context formula :=
  presentation.observationEmbedding.entails_iff context formula

theorem BisimulationQuotientIncidencePresentation.leafSatisfies_iff
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source)
    (formula : Formula I) :
    IncidenceLeafSatisfies presentation.target
        (formula.map presentation.classification.classify) ↔
      IncidenceLeafSatisfies source formula :=
  presentation.observationEmbedding.leafSatisfies_iff formula

theorem BisimulationQuotientIncidencePresentation.leafEntails_iff
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source)
    (context : List (Formula I)) (formula : Formula I) :
    IncidenceLeafEntails presentation.target
        (Formula.mapContext presentation.classification.classify context)
        (formula.map presentation.classification.classify) ↔
      IncidenceLeafEntails source context formula :=
  presentation.observationEmbedding.leafEntails_iff context formula

noncomputable def BisimulationQuotientIncidencePresentation.targetObservationEmbedding
    {I R T Q₁ QR₁ QT₁ Q₂ QR₂ QT₂ : Type u}
    [DecidableEq I] [DecidableEq Q₁] [DecidableEq Q₂]
    {source : Incidence I R T}
    (first : BisimulationQuotientIncidencePresentation
      (Q := Q₁) (QR := QR₁) (QT := QT₁) source)
    (second : BisimulationQuotientIncidencePresentation
      (Q := Q₂) (QR := QR₂) (QT := QT₂) source) :
    IncidenceBoundaryObservationEmbedding first.target second.target where
  map := (first.classification.targetEquivalence second.classification).forward
  boundary_iff := by
    intro targetAtom
    rcases first.classification.surjective targetAtom with ⟨sourceAtom, rfl⟩
    rw [BisimulationQuotientClassification.targetEquivalence_classify]
    exact (second.boundary_iff sourceAtom).trans (first.boundary_iff sourceAtom).symm

theorem BisimulationQuotientIncidencePresentation.targetSatisfies_iff
    {I R T Q₁ QR₁ QT₁ Q₂ QR₂ QT₂ : Type u}
    [DecidableEq I] [DecidableEq Q₁] [DecidableEq Q₂]
    {source : Incidence I R T}
    (first : BisimulationQuotientIncidencePresentation
      (Q := Q₁) (QR := QR₁) (QT := QT₁) source)
    (second : BisimulationQuotientIncidencePresentation
      (Q := Q₂) (QR := QR₂) (QT := QT₂) source)
    (formula : Formula Q₁) :
    IncidenceBoundarySatisfies second.target
        (formula.map (first.targetObservationEmbedding second).map) ↔
      IncidenceBoundarySatisfies first.target formula :=
  (first.targetObservationEmbedding second).satisfies_iff formula

theorem BisimulationQuotientIncidencePresentation.targetLeafSatisfies_iff
    {I R T Q₁ QR₁ QT₁ Q₂ QR₂ QT₂ : Type u}
    [DecidableEq I] [DecidableEq Q₁] [DecidableEq Q₂]
    {source : Incidence I R T}
    (first : BisimulationQuotientIncidencePresentation
      (Q := Q₁) (QR := QR₁) (QT := QT₁) source)
    (second : BisimulationQuotientIncidencePresentation
      (Q := Q₂) (QR := QR₂) (QT := QT₂) source)
    (formula : Formula Q₁) :
    IncidenceLeafSatisfies second.target
        (formula.map (first.targetObservationEmbedding second).map) ↔
      IncidenceLeafSatisfies first.target formula :=
  (first.targetObservationEmbedding second).leafSatisfies_iff formula

theorem BisimulationQuotientIncidencePresentation.targetEntails_iff
    {I R T Q₁ QR₁ QT₁ Q₂ QR₂ QT₂ : Type u}
    [DecidableEq I] [DecidableEq Q₁] [DecidableEq Q₂]
    {source : Incidence I R T}
    (first : BisimulationQuotientIncidencePresentation
      (Q := Q₁) (QR := QR₁) (QT := QT₁) source)
    (second : BisimulationQuotientIncidencePresentation
      (Q := Q₂) (QR := QR₂) (QT := QT₂) source)
    (context : List (Formula Q₁)) (formula : Formula Q₁) :
    IncidenceBoundaryEntails second.target
        (Formula.mapContext (first.targetObservationEmbedding second).map context)
        (formula.map (first.targetObservationEmbedding second).map) ↔
      IncidenceBoundaryEntails first.target context formula :=
  (first.targetObservationEmbedding second).entails_iff context formula

theorem BisimulationQuotientIncidencePresentation.targetLeafEntails_iff
    {I R T Q₁ QR₁ QT₁ Q₂ QR₂ QT₂ : Type u}
    [DecidableEq I] [DecidableEq Q₁] [DecidableEq Q₂]
    {source : Incidence I R T}
    (first : BisimulationQuotientIncidencePresentation
      (Q := Q₁) (QR := QR₁) (QT := QT₁) source)
    (second : BisimulationQuotientIncidencePresentation
      (Q := Q₂) (QR := QR₂) (QT := QT₂) source)
    (context : List (Formula Q₁)) (formula : Formula Q₁) :
    IncidenceLeafEntails second.target
        (Formula.mapContext (first.targetObservationEmbedding second).map context)
        (formula.map (first.targetObservationEmbedding second).map) ↔
      IncidenceLeafEntails first.target context formula :=
  (first.targetObservationEmbedding second).leafEntails_iff context formula

theorem BisimulationQuotientIncidencePresentation.target_nontrivial_of_source_boundary
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source)
    {atom : I} (sourceHasBoundary : IncidenceBoundaryValuation source atom) :
    ∃ first second : Q, first ≠ second := by
  have targetHasBoundary := (presentation.boundary_iff atom).mpr sourceHasBoundary
  rcases targetHasBoundary with ⟨endpoint, member⟩
  refine ⟨endpoint.i, presentation.classification.classify atom, ?_⟩
  intro equal
  exact presentation.target.well_founded
    (presentation.classification.classify atom) ⟨endpoint, member, equal⟩

theorem BisimulationQuotientIncidencePresentation.quotient_nontrivial_of_source_boundary
    {I R T Q QR QT : Type u} [DecidableEq I] [DecidableEq Q]
    {source : Incidence I R T}
    (presentation : BisimulationQuotientIncidencePresentation
      (Q := Q) (QR := QR) (QT := QT) source)
    {atom : I} (sourceHasBoundary : IncidenceBoundaryValuation source atom) :
    ∃ first second : IncidenceQuotient source, first ≠ second := by
  rcases presentation.target_nontrivial_of_source_boundary sourceHasBoundary with
    ⟨firstTarget, secondTarget, different⟩
  rcases presentation.classification.lift_surjective firstTarget with
    ⟨first, firstValue⟩
  rcases presentation.classification.lift_surjective secondTarget with
    ⟨second, secondValue⟩
  refine ⟨first, second, ?_⟩
  intro equal
  apply different
  rw [← firstValue, ← secondValue, equal]

theorem cycleIncidence_no_bisimulationQuotientIncidencePresentation
    {Q QR QT : Type} [DecidableEq Q] :
    ¬ Nonempty (BisimulationQuotientIncidencePresentation
      (I := CycleId) (R := CycleRole) (T := GraphType)
      (Q := Q) (QR := QR) (QT := QT) cycleIncidence) := by
  rintro ⟨presentation⟩
  letI : Subsingleton Q := ⟨by
    intro left right
    rcases presentation.classification.surjective left with ⟨leftSource, rfl⟩
    rcases presentation.classification.surjective right with ⟨rightSource, rfl⟩
    exact presentation.classification.respects
      (cycleIncidence_all_collapse leftSource rightSource)⟩
  have sourceHasBoundary :
      IncidenceBoundaryValuation cycleIncidence CycleId.c0 := by
    simp [IncidenceBoundaryValuation, cycleIncidence, cycleBoundary, cyclePred]
  have targetHasBoundary :=
    (presentation.boundary_iff CycleId.c0).mpr sourceHasBoundary
  rcases targetHasBoundary with ⟨endpoint, member⟩
  rw [incidence_subsingleton_boundary_empty presentation.target] at member
  simp at member

abbrev NatBoolProductIncidence :
    Incidence (Nat × Bool) (PeanoRole ⊕ GraphRole) (GraphType × GraphType) :=
  incidenceProd natIncidence
    (trivialIncidence : Incidence Bool GraphRole GraphType)

def natBoolProductClassification :
    BisimulationQuotientClassification (Q := Nat) NatBoolProductIncidence :=
  bisimulationQuotientClassificationOfKernel NatBoolProductIncidence Prod.fst
    (by
      intro x y
      rw [incidenceProd_approxBisim_iff, natIncidence_approxBisim_iff]
      constructor
      · intro equal
        exact ⟨equal, trivial_approxBisim_total x.2 y.2⟩
      · exact fun related => related.left)
    (by intro n; exact ⟨(n, false), rfl⟩)

theorem natBoolProductClassification_nonfaithful :
    natBoolProductClassification.classify (0, false) =
      natBoolProductClassification.classify (0, true) ∧
      (0, false) ≠ (0, true) := by
  exact ⟨rfl, by decide⟩

theorem natBoolProductClassification_boundaryInvariant :
    natBoolProductClassification.BoundaryInvariant := by
  intro x y bisimilar
  have firstEqual : x.1 = y.1 :=
    (incidenceProd_approxBisim_iff natIncidence
      (trivialIncidence : Incidence Bool GraphRole GraphType)
      x.1 y.1 x.2 y.2).mp bisimilar |>.left |>
      (natIncidence_approxBisim_iff x.1 y.1).mp
  rcases x with ⟨x, xb⟩
  rcases y with ⟨y, yb⟩
  simp only at firstEqual
  subst y
  cases x <;>
    simp [BisimulationQuotientClassification.mappedSourceBoundary,
      natBoolProductClassification, NatBoolProductIncidence, incidenceProd,
      prodBoundary, natIncidence, peanoBoundary, trivialIncidence,
      bisimulationQuotientClassificationOfKernel]

theorem natBoolProductClassification_glueInvariant :
    natBoolProductClassification.GlueInvariant := by
  intro x x' y y' hx hy
  have firstX : x.1 = x'.1 :=
    (incidenceProd_approxBisim_iff natIncidence
      (trivialIncidence : Incidence Bool GraphRole GraphType)
      x.1 x'.1 x.2 x'.2).mp hx |>.left |>
      (natIncidence_approxBisim_iff x.1 x'.1).mp
  have firstY : y.1 = y'.1 :=
    (incidenceProd_approxBisim_iff natIncidence
      (trivialIncidence : Incidence Bool GraphRole GraphType)
      y.1 y'.1 y.2 y'.2).mp hy |>.left |>
      (natIncidence_approxBisim_iff y.1 y'.1).mp
  rcases x with ⟨x, xb⟩
  rcases x' with ⟨x', xb'⟩
  rcases y with ⟨y, yb⟩
  rcases y' with ⟨y', yb'⟩
  simp only at firstX firstY
  subst x'
  subst y'
  cases xb <;> cases xb' <;> cases yb <;> cases yb' <;>
  simp [BisimulationQuotientClassification.mappedSourceGlue,
    natBoolProductClassification, NatBoolProductIncidence, incidenceProd,
    prodGlue, natIncidence, trivialIncidence,
    bisimulationQuotientClassificationOfKernel]

theorem natBoolProductClassification_guardInvariant :
    natBoolProductClassification.GuardInvariant := by
  intro x x' y y' hx hy
  simp [NatBoolProductIncidence, incidenceProd, prodGuards, trivialIncidence,
    natIncidence, Guards.permissive]

noncomputable def natBoolProductCanonicalCoherence :
    CanonicalGuardedQuotientIncidenceCoherence natBoolProductClassification where
  boundaryInvariant := natBoolProductClassification_boundaryInvariant
  glueInvariant := natBoolProductClassification_glueInvariant
  guardInvariant := natBoolProductClassification_guardInvariant
  boundary_no_self := by
    intro q selfLoop
    rcases natBoolProductClassification.surjective q with ⟨x, rfl⟩
    rw [natBoolProductClassification.canonicalBoundary_classify] at selfLoop
    rcases x with ⟨n, bit⟩
    cases n <;>
      simp [BisimulationQuotientClassification.mappedSourceBoundary,
        natBoolProductClassification, NatBoolProductIncidence, incidenceProd,
        prodBoundary, natIncidence, peanoBoundary, trivialIncidence,
        bisimulationQuotientClassificationOfKernel] at selfLoop
  glue_type_preserve := by
    intro x y q mapped
    rcases natBoolProductClassification.surjective q with ⟨z, rfl⟩
    rw [natBoolProductClassification.canonicalType_classify]
    rcases x with ⟨xn, xb⟩
    rcases z with ⟨zn, zb⟩
    rfl

noncomputable def natBoolProductCanonicalQuotientIncidence :
    Incidence Nat (PeanoRole ⊕ GraphRole) (GraphType × GraphType) :=
  natBoolProductCanonicalCoherence.toIncidence

theorem natBoolProductCanonicalQuotient_glue (m n : Nat) :
    natBoolProductCanonicalQuotientIncidence.glue m n = some (m + n) := by
  have beta := natBoolProductCanonicalCoherence.toIncidence_glue_classify
    (m, false) (n, false)
  simpa [natBoolProductCanonicalQuotientIncidence,
    natBoolProductClassification, BisimulationQuotientClassification.mappedSourceGlue,
    NatBoolProductIncidence, incidenceProd, prodGlue, natIncidence,
    trivialIncidence, bisimulationQuotientClassificationOfKernel] using beta

theorem natBoolProductCanonicalQuotient_guard (m n : Nat) :
    natBoolProductCanonicalQuotientIncidence.guards.allow m n = true := by
  have beta := natBoolProductCanonicalCoherence.toIncidence_guard_classify
    (m, false) (n, false)
  simpa [natBoolProductCanonicalQuotientIncidence, natBoolProductClassification,
    NatBoolProductIncidence, incidenceProd, prodGuards, natIncidence,
    trivialIncidence, Guards.permissive,
    bisimulationQuotientClassificationOfKernel] using beta

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

noncomputable def simplexQuotientShapeEquivalence :
    IncTypeEquivalence
      (Quotient (approxBisimSetoid simplexIncidence)) SimplexShape :=
  simplexBisimulationQuotientClassification.equivalence

theorem simplexQuotientShapeEquivalence_forward :
    simplexQuotientShapeEquivalence.forward = simplexQuotientToShape := by
  change simplexBisimulationQuotientClassification.lift =
    simplexQuotientToShape
  exact simplexBisimulationQuotientClassification_exact

theorem simplexQuotientShapeEquivalence_inverse_vertex :
    simplexQuotientShapeEquivalence.inverse SimplexShape.vertex =
      Quotient.mk (approxBisimSetoid simplexIncidence) SimplexId.v0 := by
  have inverseForward := simplexQuotientShapeEquivalence.inverse_forward
    (Quotient.mk (approxBisimSetoid simplexIncidence) SimplexId.v0)
  simpa [simplexQuotientShapeEquivalence_forward] using inverseForward

theorem simplexQuotientShapeEquivalence_inverse_edge :
    simplexQuotientShapeEquivalence.inverse SimplexShape.edgeShape =
      Quotient.mk (approxBisimSetoid simplexIncidence) SimplexId.e01 := by
  have inverseForward := simplexQuotientShapeEquivalence.inverse_forward
    (Quotient.mk (approxBisimSetoid simplexIncidence) SimplexId.e01)
  simpa [simplexQuotientShapeEquivalence_forward] using inverseForward

theorem simplexQuotientShapeEquivalence_inverse_face :
    simplexQuotientShapeEquivalence.inverse SimplexShape.faceShape =
      Quotient.mk (approxBisimSetoid simplexIncidence) SimplexId.face := by
  have inverseForward := simplexQuotientShapeEquivalence.inverse_forward
    (Quotient.mk (approxBisimSetoid simplexIncidence) SimplexId.face)
  simpa [simplexQuotientShapeEquivalence_forward] using inverseForward

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

theorem simplexClassification_boundaryRealization :
    simplexBisimulationQuotientClassification.BoundaryRealization := by
  refine ⟨shapeBoundary, ?_⟩
  intro atom
  cases atom <;>
    simp [shapeBoundary,
      BisimulationQuotientClassification.mappedSourceBoundary,
      simplexBisimulationQuotientClassification, simplexToShape,
      simplexIncidence, simplexBoundary]

theorem simplexClassification_boundaryInvariant :
    simplexBisimulationQuotientClassification.BoundaryInvariant :=
  (simplexBisimulationQuotientClassification.boundaryRealization_iff_invariant).mp
    simplexClassification_boundaryRealization

theorem simplexClassification_canonicalBoundary_eq_shapeBoundary :
    simplexBisimulationQuotientClassification.canonicalBoundary
      simplexClassification_boundaryInvariant = shapeBoundary := by
  symm
  apply simplexBisimulationQuotientClassification.canonicalBoundary_unique
  intro atom
  cases atom <;>
    simp [shapeBoundary,
      BisimulationQuotientClassification.mappedSourceBoundary,
      simplexBisimulationQuotientClassification, simplexToShape,
      simplexIncidence, simplexBoundary]

def simplexShapeGrade : SimplexShape → Nat
  | .vertex => 0
  | .edgeShape => 1
  | .faceShape => 2

def shapeGradedIncidenceData :
    GradedIncidenceData SimplexShape SimplexRole GraphType where
  boundary := shapeBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = SimplexShape.vertex then some j else some i
  unit     := SimplexShape.vertex
  guards   := Guards.permissive SimplexShape
  grade := simplexShapeGrade
  boundary_decreases := by
    intro i e h
    cases i <;> simp [shapeBoundary] at h <;>
      first
        | (rcases h with h | h | h <;> subst h <;> simp [simplexShapeGrade])
        | (rcases h with h | h <;> subst h <;> simp [simplexShapeGrade])
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [shapeBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  multiplicities := by
    intro i e h
    cases i <;> simp [shapeBoundary] at h <;>
      first | (rcases h with h | h | h <;> subst h <;> simp) | (rcases h with h | h <;> subst h <;> simp)
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = SimplexShape.vertex <;> simp [h]
  type_preserve := fun _ _ => rfl

def shapeIncidence : Incidence SimplexShape SimplexRole GraphType :=
  shapeGradedIncidenceData.toIncidence

def simplexGradedQuotientPresentation :
    GradedBisimulationQuotientPresentation
      (Q := SimplexShape) (QR := SimplexRole) (QT := GraphType)
      simplexIncidence where
  classification := simplexBisimulationQuotientClassification
  data := shapeGradedIncidenceData
  boundary_iff := by
    intro atom
    cases atom <;>
      simp [IncidenceBoundaryValuation, simplexBisimulationQuotientClassification,
        simplexToShape, simplexIncidence, simplexBoundary,
        shapeGradedIncidenceData, GradedIncidenceData.toIncidence, shapeBoundary]

def simplexQuotientIncidencePresentation :
    BisimulationQuotientIncidencePresentation
      (Q := SimplexShape) (QR := SimplexRole) (QT := GraphType)
      simplexIncidence :=
  simplexGradedQuotientPresentation.toPresentation

theorem simplexToShape_boundaryLogic_satisfies_iff
    (formula : Formula SimplexId) :
    IncidenceBoundarySatisfies shapeIncidence (formula.map simplexToShape) ↔
      IncidenceBoundarySatisfies simplexIncidence formula :=
  simplexQuotientIncidencePresentation.satisfies_iff formula

theorem simplexToShape_boundaryLogic_entails_iff
    (context : List (Formula SimplexId)) (formula : Formula SimplexId) :
    IncidenceBoundaryEntails shapeIncidence
        (Formula.mapContext simplexToShape context) (formula.map simplexToShape) ↔
      IncidenceBoundaryEntails simplexIncidence context formula :=
  simplexQuotientIncidencePresentation.entails_iff context formula

theorem simplexToShape_leafLogic_satisfies_iff
    (formula : Formula SimplexId) :
    IncidenceLeafSatisfies shapeIncidence (formula.map simplexToShape) ↔
      IncidenceLeafSatisfies simplexIncidence formula :=
  simplexQuotientIncidencePresentation.leafSatisfies_iff formula

theorem simplexToShape_leafLogic_entails_iff
    (context : List (Formula SimplexId)) (formula : Formula SimplexId) :
    IncidenceLeafEntails shapeIncidence
        (Formula.mapContext simplexToShape context) (formula.map simplexToShape) ↔
      IncidenceLeafEntails simplexIncidence context formula :=
  simplexQuotientIncidencePresentation.leafEntails_iff context formula

theorem simplexQuotientPresentation_equivalence :
    Nonempty (IncTypeEquivalence
      (IncidenceQuotient simplexIncidence) SimplexShape) :=
  ⟨simplexQuotientIncidencePresentation.quotientEquivalence⟩

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

theorem simplexClassification_glue_not_invariant :
    ¬ simplexBisimulationQuotientClassification.GlueInvariant := by
  intro invariant
  have verticesBisimilar :
      approxBisim simplexIncidence SimplexId.v0 SimplexId.v1 :=
    (simplexToShape_iff_approxBisim SimplexId.v0 SimplexId.v1).mp rfl
  have equalMappedGlue := invariant verticesBisimilar
    (approxBisim_refl simplexIncidence SimplexId.face)
  simp [BisimulationQuotientClassification.mappedSourceGlue,
    simplexBisimulationQuotientClassification, simplexToShape,
    simplexIncidence] at equalMappedGlue

/- Cycle 45: `simplexToShape_not_glue_hom` (cycle 41) only ruled out
   the ONE particular `shapeIncidence.glue` this project happened to
   build there (cycle 41's own "direct copy" of `simplexIncidence`'s
   unit-absorbing pattern, not derived from anything). Cycle 41's
   queue asked the strictly stronger question, repeated unattempted
   through cycles 42/43/44: is there ANY OTHER well-typed
   `glue : SimplexShape → SimplexShape → Option SimplexShape` for
   which `simplexToShape` IS a genuine glue-homomorphism -- or is that
   structurally impossible?

   `BisimulationQuotientClassification.glueRealization_iff_invariant`
   (built out in the generalized quotient-classification development
   that followed cycle 41, well before cycles 42-44's analysis-thread
   detour) already supplies the exact necessary-and-sufficient
   criterion this question needs: a `Q`-valued glue realizing
   `classify` as a homomorphism exists (`GlueRealization`) iff
   `inc.glue` is `≈`-invariant in both arguments (`GlueInvariant`).
   And `simplexClassification_glue_not_invariant`, proved immediately
   above as part of that same development, already establishes
   `¬ GlueInvariant` for EXACTLY this classification
   (`simplexBisimulationQuotientClassification`, whose `classify`
   field is `simplexToShape` itself). No prior cycle had drawn these
   two already-proved facts together into the closing statement the
   open question actually asks for -- doing so is this cycle's entire
   contribution: a clean, GENERAL negative closure, ruling out every
   possible choice of glue at once rather than just the one candidate
   cycle 41 happened to build. -/
theorem simplexShape_glue_not_realizable :
    ¬ simplexBisimulationQuotientClassification.GlueRealization :=
  fun realization =>
    simplexClassification_glue_not_invariant
      ((BisimulationQuotientClassification.glueRealization_iff_invariant
        simplexBisimulationQuotientClassification).mp realization)

/- The same fact, unfolded out of the classification abstraction into
   plain function language matching the open question's own phrasing:
   no total function `SimplexShape → SimplexShape → Option
   SimplexShape` whatsoever -- `shapeIncidence.glue` or any other
   well-typed candidate -- can make `simplexToShape` a
   glue-homomorphism out of `simplexIncidence`. This is the structural
   impossibility cycle 41's queue asked to confirm or refute; it is
   confirmed. -/
theorem simplexToShape_no_glue_homomorphism_exists :
    ¬ ∃ glue' : SimplexShape → SimplexShape → Option SimplexShape,
      ∀ x y : SimplexId,
        glue' (simplexToShape x) (simplexToShape y) =
          (simplexIncidence.glue x y).map simplexToShape :=
  simplexShape_glue_not_realizable

/- Research cycle 51 (see RESEARCH_LOG.md): cycle 50's queue (option
   (ii), preferred over option (i) by the task's own diversification
   choice) asks whether cycle 41's finding -- a quotient construction can
   succeed exactly when the collapse respects some well-founded grading
   already present in the instance -- generalizes to ANOTHER graded
   instance, or was an accident of `simplexIncidence`'s specific shape.
   `pathIncidence` (`PathComplex.lean`, cycle 10) is the natural second
   candidate flagged in the task briefing: a 2-graded structure (nodes =
   grade 0 / leaves, edges = grade 1), already known since cycle 13
   (`pathIncidence_nodes_collapse`) to have its nodes collapse under `≈`.
   The open question genuinely new to this cycle: do `pathIncidence`'s
   edges ALSO collapse among themselves (the way `simplexIncidence`'s
   edges did, cycle 18), giving exactly two `≈`-classes over an INFINITE
   carrier (unlike `simplexIncidence`'s finite 7-element carrier) -- a
   meaningfully different data point (unbounded multiplicity per grade,
   not just finitely many grades), not a restatement of the simplex case. -/

inductive PathShape where | nodeShape | edgeShape
deriving DecidableEq, Repr

def pathToShape : PathId → PathShape
  | .node _ => .nodeShape
  | .edge _ => .edgeShape

/- The bisimulation relation witnessing both collapses at once, in
   exactly `simplexEdgeVertexRel`'s style (cycle 18): any two nodes are
   related, and any two edges are related, generalized here to ARBITRARY
   indices (cycle 13's own relation was already stated generally enough
   internally, just never packaged as a reusable named lemma over
   arbitrary `m`/`n` -- done here since the shape-classification below
   needs it for every pair, not one representative). -/
def pathNodeEdgeRel (x y : PathId) : Prop :=
  (∃ m, x = PathId.node m) ∧ (∃ n, y = PathId.node n) ∨
  (∃ m, x = PathId.edge m) ∧ (∃ n, y = PathId.edge n)

theorem pathNodeEdgeRel_symm : ∀ a b, pathNodeEdgeRel a b → pathNodeEdgeRel b a := by
  intro a b h
  unfold pathNodeEdgeRel at h ⊢
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨hb, ha⟩
  · exact Or.inr ⟨hb, ha⟩

theorem pathCompat_refl (e : Endpoint PathId PeanoRole) :
  boundaryCompatible pathIncidence e e := ⟨rfl, rfl, rfl⟩

/- Method note: unlike `simplexEdgeVertexRel_isBisimulation` (cycle 18),
   which needed nine case-split arms (three vertices × three vertices,
   etc.) because `SimplexId` has finitely many named constructors per
   grade, `pathIncidence`'s two grades each have INFINITELY many elements
   (`node n`/`edge n` for every `n : Nat`) but are structurally uniform in
   `n` -- so a single generic argument per grade suffices, no per-index
   case split needed. This is the first concrete evidence that the
   "grading" pattern cycle 41 identified does not depend on the grades
   being finite. -/
theorem pathNodeEdgeRel_isBisimulation :
  IsBisimulation pathIncidence pathNodeEdgeRel := by
  intro i j hij
  refine ⟨rfl, ?_⟩
  rcases hij with ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ | ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  · subst hm; subst hn
    simp [boundaryMatched, pathIncidence, pathBoundary]
  · subst hm; subst hn
    exact boundaryMatched_of_two_entries pathIncidence pathNodeEdgeRel
      (PathId.edge m) (PathId.edge n)
      { i := PathId.node m, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
      { i := PathId.node (m + 1), role := PeanoRole.pred, sign := Sign.pos, mult := 1 }
      { i := PathId.node n, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
      { i := PathId.node (n + 1), role := PeanoRole.pred, sign := Sign.pos, mult := 1 }
      rfl rfl (pathCompat_refl _) (Or.inl ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩)
      (pathCompat_refl _) (Or.inl ⟨⟨m + 1, rfl⟩, ⟨n + 1, rfl⟩⟩)

/- The general leaf-vs-nonleaf separator: EVERY `node n` is a leaf
   (`pathBoundary` matches `node _` uniformly, unlike `simplexIncidence`
   where only three of seven constructors are leaves) -- so this single
   lemma, over an arbitrary `n`, does the job `simplexIncidence_nonempty_
   not_vertex` (cycle 22) needed three enumerated cases for. -/
theorem pathIncidence_nonempty_not_node (i : PathId)
  (hi : pathIncidence.boundary i ≠ []) (n : Nat) :
  ¬ approxBisim pathIncidence i (PathId.node n) := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hi
  exact not_approxBisim_empty_nonempty pathIncidence i (PathId.node n) rfl e he

theorem pathToShape_reflects (x y : PathId) (h : pathToShape x = pathToShape y) :
  approxBisim pathIncidence x y := by
  cases x with
  | node m => cases y with
    | node n => exact ⟨pathNodeEdgeRel, pathNodeEdgeRel_isBisimulation, Or.inl ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩⟩
    | edge n => simp [pathToShape] at h
  | edge m => cases y with
    | node n => simp [pathToShape] at h
    | edge n => exact ⟨pathNodeEdgeRel, pathNodeEdgeRel_isBisimulation, Or.inr ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩⟩

/- The converse, over all four constructor-shape combinations at once
   (again, no per-index enumeration needed -- contrast
   `simplexToShape_distinguishes`'s 49 explicit arms, cycle 23). -/
theorem pathToShape_distinguishes (x y : PathId) (h : approxBisim pathIncidence x y) :
  pathToShape x = pathToShape y := by
  cases x with
  | node m => cases y with
    | node n => rfl
    | edge n =>
      exact absurd (approxBisim_symm h)
        (pathIncidence_nonempty_not_node (PathId.edge n) (by simp [pathIncidence, pathBoundary]) m)
  | edge m => cases y with
    | node n =>
      exact absurd h
        (pathIncidence_nonempty_not_node (PathId.edge m) (by simp [pathIncidence, pathBoundary]) n)
    | edge n => rfl

/- The exhaustive characterization: `pathIncidence`'s `≈` is exactly
   `pathToShape`-agreement -- exactly two classes over an infinite
   carrier, confirming the open question above. -/
theorem pathToShape_iff_approxBisim (x y : PathId) :
  pathToShape x = pathToShape y ↔ approxBisim pathIncidence x y :=
  ⟨pathToShape_reflects x y, pathToShape_distinguishes x y⟩

def pathBisimulationQuotientClassification :
    BisimulationQuotientClassification (Q := PathShape) pathIncidence where
  classify := pathToShape
  respects := fun h => pathToShape_distinguishes _ _ h
  reflects := fun h => pathToShape_reflects _ _ h
  surjective := by
    intro shape
    cases shape with
    | nodeShape => exact ⟨PathId.node 0, rfl⟩
    | edgeShape => exact ⟨PathId.edge 0, rfl⟩

noncomputable def pathQuotientToShape :
  Quotient (approxBisimSetoid pathIncidence) → PathShape :=
  Quotient.lift pathToShape pathToShape_distinguishes

theorem pathQuotientToShape_injective (q1 q2 : Quotient (approxBisimSetoid pathIncidence))
  (h : pathQuotientToShape q1 = pathQuotientToShape q2) : q1 = q2 := by
  induction q1 using Quotient.ind with
  | _ x =>
    induction q2 using Quotient.ind with
    | _ y =>
      unfold pathQuotientToShape at h
      simp only [Quotient.lift] at h
      exact Quotient.sound (pathToShape_reflects x y h)

theorem pathQuotientToShape_surjective (s : PathShape) :
  ∃ q : Quotient (approxBisimSetoid pathIncidence), pathQuotientToShape q = s := by
  cases s with
  | nodeShape => exact ⟨Quotient.mk _ (PathId.node 0), rfl⟩
  | edgeShape => exact ⟨Quotient.mk _ (PathId.edge 0), rfl⟩

noncomputable def pathQuotientShapeEquivalence :
    IncTypeEquivalence
      (Quotient (approxBisimSetoid pathIncidence)) PathShape :=
  pathBisimulationQuotientClassification.equivalence

/- The genuine fresh `Incidence PathShape` structure, built the SAME way
   cycle 41 built `shapeIncidence` -- but this time using the
   `GradedIncidenceData` machinery that was generalized (as reusable
   infrastructure) sometime after cycle 41's own bespoke construction,
   making the `well_founded` obligation fall out of a single `Nat`-valued
   grade rather than a hand-written case split. `nodeShape` is grade 0
   (empty boundary); `edgeShape` is grade 1, its two entries both
   pointing to `nodeShape` -- exactly `simplexIncidence`'s vertex/edge
   two-level grading, one level shallower than its vertex/edge/face
   three-level grading (there is no `face`-analogue here, since
   `pathIncidence` has no third grade). -/
def pathShapeBoundary : PathShape → Boundary PathShape PeanoRole
  | .nodeShape => []
  | .edgeShape =>
    [ { i := .nodeShape, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
    , { i := .nodeShape, role := PeanoRole.pred, sign := Sign.pos, mult := 1 } ]

theorem pathClassification_boundaryRealization :
    pathBisimulationQuotientClassification.BoundaryRealization := by
  refine ⟨pathShapeBoundary, ?_⟩
  intro atom
  cases atom <;>
    simp [pathShapeBoundary,
      BisimulationQuotientClassification.mappedSourceBoundary,
      pathBisimulationQuotientClassification, pathToShape,
      pathIncidence, pathBoundary]

theorem pathClassification_boundaryInvariant :
    pathBisimulationQuotientClassification.BoundaryInvariant :=
  (pathBisimulationQuotientClassification.boundaryRealization_iff_invariant).mp
    pathClassification_boundaryRealization

def pathShapeGrade : PathShape → Nat
  | .nodeShape => 0
  | .edgeShape => 1

def pathShapeGradedIncidenceData :
    GradedIncidenceData PathShape PeanoRole GraphType where
  boundary := pathShapeBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = PathShape.nodeShape then some j else some i
  unit     := PathShape.nodeShape
  guards   := Guards.permissive PathShape
  grade := pathShapeGrade
  boundary_decreases := by
    intro i e h
    cases i <;> simp [pathShapeBoundary] at h <;>
      (rcases h with h | h <;> subst h <;> simp [pathShapeGrade])
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [pathShapeBoundary] at h <;>
      (rcases h with h | h <;> subst h <;> simp)
  multiplicities := by
    intro i e h
    cases i <;> simp [pathShapeBoundary] at h <;>
      (rcases h with h | h <;> subst h <;> simp)
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = PathShape.nodeShape <;> simp [h]
  type_preserve := fun _ _ => rfl

def pathShapeIncidence : Incidence PathShape PeanoRole GraphType :=
  pathShapeGradedIncidenceData.toIncidence

def pathGradedQuotientPresentation :
    GradedBisimulationQuotientPresentation
      (Q := PathShape) (QR := PeanoRole) (QT := GraphType)
      pathIncidence where
  classification := pathBisimulationQuotientClassification
  data := pathShapeGradedIncidenceData
  boundary_iff := by
    intro atom
    cases atom <;>
      simp [IncidenceBoundaryValuation, pathBisimulationQuotientClassification,
        pathToShape, pathIncidence, pathBoundary,
        pathShapeGradedIncidenceData, GradedIncidenceData.toIncidence, pathShapeBoundary]

def pathQuotientIncidencePresentation :
    BisimulationQuotientIncidencePresentation
      (Q := PathShape) (QR := PeanoRole) (QT := GraphType)
      pathIncidence :=
  pathGradedQuotientPresentation.toPresentation

theorem pathQuotientPresentation_equivalence :
    Nonempty (IncTypeEquivalence
      (IncidenceQuotient pathIncidence) PathShape) :=
  ⟨pathQuotientIncidencePresentation.quotientEquivalence⟩

/- Honest check (task step (d), not assumed): is `pathToShape` a
   `glue`-homomorphism between `pathIncidence` and `pathShapeIncidence`?
   Both `glue`s share the identical "absorb at the unit" shape
   (`if i = unit then some j else some i`), but the unit-check happens on
   the SOURCE type against ONE specific representative (`PathId.node 0`)
   while every OTHER node (`node 1`, `node 3`, ...) is also `≈ node 0`
   yet is treated as "not the unit" by `pathIncidence.glue` itself --
   exactly the same mismatch cycle 41 found for `simplexIncidence`, now
   confirmed in a second, differently-shaped instance: `node 0` and
   `node 1` collapse to the same class, but gluing each against a fixed
   edge produces different SHAPES, not just different underlying
   elements. -/
theorem pathClassification_glue_not_invariant :
    ¬ pathBisimulationQuotientClassification.GlueInvariant := by
  intro invariant
  have nodesBisimilar : approxBisim pathIncidence (PathId.node 0) (PathId.node 1) :=
    (pathToShape_iff_approxBisim (PathId.node 0) (PathId.node 1)).mp rfl
  have equalMappedGlue := invariant nodesBisimilar (approxBisim_refl pathIncidence (PathId.edge 0))
  have hlhs : pathBisimulationQuotientClassification.mappedSourceGlue
      (PathId.node 0) (PathId.edge 0) = some PathShape.edgeShape := by
    simp [BisimulationQuotientClassification.mappedSourceGlue,
      pathBisimulationQuotientClassification, pathToShape, pathIncidence]
  have hrhs : pathBisimulationQuotientClassification.mappedSourceGlue
      (PathId.node 1) (PathId.edge 0) = some PathShape.nodeShape := by
    simp [BisimulationQuotientClassification.mappedSourceGlue,
      pathBisimulationQuotientClassification, pathToShape, pathIncidence]
  rw [hlhs, hrhs] at equalMappedGlue
  exact absurd equalMappedGlue (by decide)

/- The strictly stronger, "no escape hatch" closure -- reusing the
   ALREADY GENERALIZED `glueRealization_iff_invariant` (built after
   cycle 41, first spent on `simplexIncidence` only in cycle 45, one
   cycle after its own quotient was built) to get the full closure in
   the SAME cycle the quotient itself was constructed, rather than
   needing a separate follow-up cycle the way `simplexIncidence` did
   (cycle 41 → cycle 45). No well-typed
   `glue' : PathShape → PathShape → Option PathShape` whatsoever can
   make `pathToShape` a glue-homomorphism out of `pathIncidence`. -/
theorem pathShape_glue_not_realizable :
    ¬ pathBisimulationQuotientClassification.GlueRealization :=
  fun realization =>
    pathClassification_glue_not_invariant
      ((BisimulationQuotientClassification.glueRealization_iff_invariant
        pathBisimulationQuotientClassification).mp realization)

theorem pathToShape_no_glue_homomorphism_exists :
    ¬ ∃ glue' : PathShape → PathShape → Option PathShape,
      ∀ x y : PathId,
        glue' (pathToShape x) (pathToShape y) =
          (pathIncidence.glue x y).map pathToShape :=
  pathShape_glue_not_realizable

/- Research cycle 52 (see RESEARCH_LOG.md): cycle 51's own queued primary
   next-hypothesis -- `treeIncidence` (Tree.lean, cycle 29), the ONE
   graded instance cycle 51 explicitly declined to attempt because its
   carrier (`TreeId`) nests recursively WITHOUT BOUND (`node a b c`'s
   children can themselves be nodes, to arbitrary depth), unlike
   `simplexIncidence`'s fixed 3-level grading (cycle 41) or
   `pathIncidence`'s fixed 2-level grading with unbounded per-grade
   multiplicity (cycle 51). Does the "collapse survives exactly when it
   respects a well-founded grading" mechanism ALSO survive when the
   grading itself comes from unbounded recursive depth? -/

/- The quotient target: `TreeId` with leaf labels erased but the full
   recursive branching structure retained. Unlike `PathShape`/`SimplexShape`
   (finite types with 2/3 named constructors), `TreeShape` is ITSELF an
   unboundedly recursive inductive type -- any single value has finite
   depth, but there is no bound across all values, mirroring `TreeId`'s own
   shape one level up (after erasing `Nat` leaf labels). -/
inductive TreeShape where
  | leaf
  | node (a b c : TreeShape)
deriving DecidableEq, Repr

def treeToShape : TreeId → TreeShape
  | .leaf _ => .leaf
  | .node a b c => .node (treeToShape a) (treeToShape b) (treeToShape c)

/- The natural candidate bisimulation: "same `TreeShape`". Unlike
   `pathNodeEdgeRel`/`simplexEdgeVertexRel` (flat relations stated
   directly on the two grades), this one is defined VIA the recursive
   classifying map itself -- there is no flat, non-recursive way to state
   "these two trees have the same branching shape" for an unboundedly deep
   type. -/
def treeShapeRel (x y : TreeId) : Prop := treeToShape x = treeToShape y

/- `treeShapeRel` is a bisimulation via a SINGLE level of case analysis
   (using `boundaryMatched_of_three_entries` above) -- no induction needed
   here, since the relation already *assumes* shape-equality of the
   children (`TreeShape.node.injEq` unpacks it), it does not need to
   RE-DERIVE it. This mirrors `pathNodeEdgeRel_isBisimulation`'s
   one-level-suffices shape, not `simplexEdgeVertexRel_isBisimulation`'s
   per-constructor enumeration. -/
theorem treeShapeRel_isBisimulation :
  IsBisimulation treeIncidence treeShapeRel := by
  intro i j hij
  refine ⟨rfl, ?_⟩
  cases i with
  | leaf n =>
    cases j with
    | leaf m => simp [boundaryMatched, treeIncidence, treeBoundary]
    | node a' b' c' => exact absurd hij (by simp [treeShapeRel, treeToShape])
  | node a b c =>
    cases j with
    | leaf m => exact absurd hij (by simp [treeShapeRel, treeToShape])
    | node a' b' c' =>
      have heq : treeToShape a = treeToShape a' ∧ treeToShape b = treeToShape b' ∧
          treeToShape c = treeToShape c' := by
        simpa [treeShapeRel, treeToShape, TreeShape.node.injEq] using hij
      exact boundaryMatched_of_three_entries treeIncidence treeShapeRel
        (TreeId.node a b c) (TreeId.node a' b' c')
        { i := a, role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
        { i := b, role := TernaryRole.c2, sign := Sign.pos, mult := 1 }
        { i := c, role := TernaryRole.c3, sign := Sign.pos, mult := 1 }
        { i := a', role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
        { i := b', role := TernaryRole.c2, sign := Sign.pos, mult := 1 }
        { i := c', role := TernaryRole.c3, sign := Sign.pos, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ heq.1 ⟨rfl, rfl, rfl⟩ heq.2.1 ⟨rfl, rfl, rfl⟩ heq.2.2

theorem treeToShape_reflects (x y : TreeId) (h : treeToShape x = treeToShape y) :
  approxBisim treeIncidence x y :=
  ⟨treeShapeRel, treeShapeRel_isBisimulation, h⟩

/- Method note: `TernaryRole`'s pairwise constructor-distinctness facts
   are proved as standalone, fully closed lemmas FIRST (no ambient free
   variables at all), rather than inlining `by decide` at the point of use
   below. The inline version hit a genuine, reproducible Lean elaboration
   snag: even under an explicit type ascription, `by decide` run inside a
   context with unrelated free variables in scope (`a`, `b'`, etc., bound
   by the enclosing theorem/case-split, entirely unmentioned by the target
   proposition itself) is rejected with "Expected type must not contain
   free variables" -- `decide`'s closed-term precondition looks at the
   ambient elaboration context, not just the stated goal. Proving the
   disequalities in total isolation and then merely *applying* them via
   `absurd` (a defeq check, not a fresh `decide` elaboration) sidesteps
   this entirely. -/
theorem ternaryRole_c1_ne_c2 : TernaryRole.c1 ≠ TernaryRole.c2 := by decide
theorem ternaryRole_c1_ne_c3 : TernaryRole.c1 ≠ TernaryRole.c3 := by decide
theorem ternaryRole_c2_ne_c1 : TernaryRole.c2 ≠ TernaryRole.c1 := by decide
theorem ternaryRole_c2_ne_c3 : TernaryRole.c2 ≠ TernaryRole.c3 := by decide
theorem ternaryRole_c3_ne_c1 : TernaryRole.c3 ≠ TernaryRole.c1 := by decide
theorem ternaryRole_c3_ne_c2 : TernaryRole.c3 ≠ TernaryRole.c2 := by decide

/- The extraction lemma the converse direction needs: unpacking
   `boundaryMatched` at a *specific known pair* of ternary nodes into the
   three positional `rel` facts, using that the three roles `c1`/`c2`/`c3`
   are pairwise distinct to rule out the two "wrong slot" matches per
   entry. This is the general shape `treeIncidence_node_x_boundary`
   (Tree.lean, cycle 30) already exploited for `boundaryMatrix`; here it's
   extracted directly for an arbitrary `rel` via `boundaryMatched`, not
   specialized to `=`. -/
theorem treeIncidence_node_node_boundaryMatched_rel
    {rel : TreeId → TreeId → Prop} {a b c a' b' c' : TreeId}
    (h : boundaryMatched treeIncidence rel (TreeId.node a b c) (TreeId.node a' b' c')) :
    rel a a' ∧ rel b b' ∧ rel c c' := by
  obtain ⟨hforward, _⟩ := h
  have ha := hforward { i := a, role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
    (by simp [treeIncidence, treeBoundary])
  have hb := hforward { i := b, role := TernaryRole.c2, sign := Sign.pos, mult := 1 }
    (by simp [treeIncidence, treeBoundary])
  have hc := hforward { i := c, role := TernaryRole.c3, sign := Sign.pos, mult := 1 }
    (by simp [treeIncidence, treeBoundary])
  obtain ⟨e1', he1', hcompat1, hr1⟩ := ha
  obtain ⟨e2', he2', hcompat2, hr2⟩ := hb
  obtain ⟨e3', he3', hcompat3, hr3⟩ := hc
  simp only [treeIncidence, treeBoundary, List.mem_cons, List.not_mem_nil, or_false]
    at he1' he2' he3'
  refine ⟨?_, ?_, ?_⟩
  · rcases he1' with he1' | he1' | he1' <;> subst he1'
    · exact hr1
    · exact absurd hcompat1.1 ternaryRole_c1_ne_c2
    · exact absurd hcompat1.1 ternaryRole_c1_ne_c3
  · rcases he2' with he2' | he2' | he2' <;> subst he2'
    · exact absurd hcompat2.1 ternaryRole_c2_ne_c1
    · exact hr2
    · exact absurd hcompat2.1 ternaryRole_c2_ne_c3
  · rcases he3' with he3' | he3' | he3' <;> subst he3'
    · exact absurd hcompat3.1 ternaryRole_c3_ne_c1
    · exact absurd hcompat3.1 ternaryRole_c3_ne_c2
    · exact hr3

/- The genuinely NEW proof-technique requirement this cycle surfaces: the
   converse direction (`approxBisim → shape-equal`) cannot be a flat,
   uniform-in-index argument the way `pathToShape_distinguishes` was
   (`pathIncidence`'s grades are flat -- one level, uniform in `n`) nor a
   finite-enumeration one the way `simplexToShape_distinguishes` was
   (`simplexIncidence` has only 7 elements total). Because `TreeId` nests
   without bound, this needs GENUINE STRUCTURAL INDUCTION over the tree --
   the first time this project's quotient-construction thread (cycles
   38-51) has needed induction rather than direct case-splitting or finite
   enumeration to establish a classifying map's converse direction. The
   induction is over an arbitrary witnessing bisimulation `rel`, not just
   `treeShapeRel` itself (mirroring `incidence_bisim_faithful`'s structure,
   cycle 4, but with a shape-classification conclusion instead of literal
   equality, and structural recursion on `TreeId` instead of a `Nat`-valued
   well-founded measure -- `TreeId`'s own recursor already IS a
   well-founded measure). -/
theorem treeToShape_distinguishes_of_bisimulation
    {rel : TreeId → TreeId → Prop} (isBisim : IsBisimulation treeIncidence rel) :
    ∀ x y, rel x y → treeToShape x = treeToShape y := by
  intro x
  induction x with
  | leaf n =>
    intro y hxy
    cases y with
    | leaf m => rfl
    | node a' b' c' =>
      have hb : approxBisim treeIncidence (TreeId.node a' b' c') (TreeId.leaf n) :=
        approxBisim_symm ⟨rel, isBisim, hxy⟩
      exact absurd hb (not_approxBisim_empty_nonempty treeIncidence
        (TreeId.node a' b' c') (TreeId.leaf n) rfl
        { i := a', role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
        (by simp [treeIncidence, treeBoundary]))
  | node a b c ih_a ih_b ih_c =>
    intro y hxy
    cases y with
    | leaf m =>
      exact absurd (⟨rel, isBisim, hxy⟩ : approxBisim treeIncidence (TreeId.node a b c) (TreeId.leaf m))
        (not_approxBisim_empty_nonempty treeIncidence (TreeId.node a b c) (TreeId.leaf m) rfl
          { i := a, role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
          (by simp [treeIncidence, treeBoundary]))
    | node a' b' c' =>
      obtain ⟨_, hmatch⟩ := isBisim (TreeId.node a b c) (TreeId.node a' b' c') hxy
      obtain ⟨hra, hrb, hrc⟩ := treeIncidence_node_node_boundaryMatched_rel hmatch
      simp only [treeToShape]
      rw [ih_a a' hra, ih_b b' hrb, ih_c c' hrc]

theorem treeToShape_distinguishes (x y : TreeId) (h : approxBisim treeIncidence x y) :
  treeToShape x = treeToShape y := by
  obtain ⟨rel, isBisim, hxy⟩ := h
  exact treeToShape_distinguishes_of_bisimulation isBisim x y hxy

/- The exhaustive characterization, closing the loop cycle 51 left open:
   `treeIncidence`'s `≈` is exactly `treeToShape`-agreement -- a genuine
   middle-ground quotient (more than one class: distinct branching shapes
   remain distinct; fewer than all: every `leaf n` collapses to one class
   regardless of `n`) even though the grading now comes from unbounded
   recursive depth, not a fixed handful of levels. -/
theorem treeToShape_iff_approxBisim (x y : TreeId) :
  treeToShape x = treeToShape y ↔ approxBisim treeIncidence x y :=
  ⟨treeToShape_reflects x y, treeToShape_distinguishes x y⟩

def treeBisimulationQuotientClassification :
    BisimulationQuotientClassification (Q := TreeShape) treeIncidence where
  classify := treeToShape
  respects := fun h => treeToShape_distinguishes _ _ h
  reflects := fun h => treeToShape_reflects _ _ h
  surjective := by
    intro shape
    induction shape with
    | leaf => exact ⟨TreeId.leaf 0, rfl⟩
    | node a b c ih_a ih_b ih_c =>
      obtain ⟨ta, hta⟩ := ih_a
      obtain ⟨tb, htb⟩ := ih_b
      obtain ⟨tc, htc⟩ := ih_c
      exact ⟨TreeId.node ta tb tc, by simp [treeToShape, hta, htb, htc]⟩

noncomputable def treeQuotientToShape :
  Quotient (approxBisimSetoid treeIncidence) → TreeShape :=
  Quotient.lift treeToShape treeToShape_distinguishes

theorem treeQuotientToShape_injective (q1 q2 : Quotient (approxBisimSetoid treeIncidence))
  (h : treeQuotientToShape q1 = treeQuotientToShape q2) : q1 = q2 := by
  induction q1 using Quotient.ind with
  | _ x =>
    induction q2 using Quotient.ind with
    | _ y =>
      unfold treeQuotientToShape at h
      simp only [Quotient.lift] at h
      exact Quotient.sound (treeToShape_reflects x y h)

theorem treeQuotientToShape_surjective (s : TreeShape) :
  ∃ q : Quotient (approxBisimSetoid treeIncidence), treeQuotientToShape q = s := by
  obtain ⟨x, hx⟩ := treeBisimulationQuotientClassification.surjective s
  exact ⟨Quotient.mk _ x, hx⟩

noncomputable def treeQuotientShapeEquivalence :
    IncTypeEquivalence
      (Quotient (approxBisimSetoid treeIncidence)) TreeShape :=
  treeBisimulationQuotientClassification.equivalence

/- The genuine fresh `Incidence TreeShape` structure, built via the SAME
   `GradedIncidenceData` machinery cycles 41/51 used -- but now with a
   grading function that is genuinely UNBOUNDED (not 0/1/2-valued): subtree
   size. Method note, an incidental but real finding: the FIRST attempt
   used `grade := sizeOf` directly, reusing `TreeShape`'s auto-derived
   `SizeOf` instance the same way `treeIncidence.well_founded` itself
   (`Tree.lean`, cycle 29) reuses `TreeId`'s. That failed to COMPILE --
   not a proof failure, a compilation one: `lake build` rejected
   `treeShapeGradedIncidenceData` with "depends on declaration
   `TreeShape._sizeOf_inst`, which has no executable code; consider
   marking definition as `noncomputable`" -- `TreeShape`'s auto-derived
   `SizeOf` instance is itself noncomputable (unlike `TreeId`'s, which
   compiles fine and is only ever consumed inside `Prop`-valued proofs,
   where computability never matters). Since `GradedIncidenceData` is a
   plain, executable `def` (its `grade` field is real run-time data, not
   proof-irrelevant), this forces a choice between marking the whole
   presentation `noncomputable` or avoiding `sizeOf`. Chose the latter:
   `treeShapeGrade` below is a hand-written, structurally-recursive `Nat`
   function (subtree size) in exactly `pathShapeGrade`/`simplexShapeGrade`'s
   style (an explicit `Q → Nat` map, cycles 41/51) generalized from a
   finite lookup table to genuine structural recursion -- fully computable,
   and its `boundary_decreases` proof is the same shape `treeIncidence`'s
   own `well_founded` proof uses (a strict decrease across one constructor
   application), just stated for an explicit sum-of-children measure
   instead of via `sizeOf_spec`. -/
def treeShapeGrade : TreeShape → Nat
  | .leaf => 0
  | .node a b c => treeShapeGrade a + treeShapeGrade b + treeShapeGrade c + 1

def treeShapeBoundary : TreeShape → Boundary TreeShape TernaryRole
  | .leaf => []
  | .node a b c =>
    [ { i := a, role := TernaryRole.c1, sign := Sign.pos, mult := 1 }
    , { i := b, role := TernaryRole.c2, sign := Sign.pos, mult := 1 }
    , { i := c, role := TernaryRole.c3, sign := Sign.pos, mult := 1 } ]

theorem treeClassification_boundaryRealization :
    treeBisimulationQuotientClassification.BoundaryRealization := by
  refine ⟨treeShapeBoundary, ?_⟩
  intro atom
  cases atom <;>
    simp [treeShapeBoundary, BisimulationQuotientClassification.mappedSourceBoundary,
      treeBisimulationQuotientClassification, treeToShape, treeIncidence, treeBoundary]

theorem treeClassification_boundaryInvariant :
    treeBisimulationQuotientClassification.BoundaryInvariant :=
  (treeBisimulationQuotientClassification.boundaryRealization_iff_invariant).mp
    treeClassification_boundaryRealization

def treeShapeGradedIncidenceData :
    GradedIncidenceData TreeShape TernaryRole GraphType where
  boundary := treeShapeBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = TreeShape.leaf then some j else some i
  unit     := TreeShape.leaf
  guards   := Guards.permissive TreeShape
  grade    := treeShapeGrade
  boundary_decreases := by
    intro q e h
    cases q with
    | leaf => simp [treeShapeBoundary] at h
    | node a b c =>
      simp only [treeShapeBoundary, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> subst h <;>
        simp only [treeShapeGrade] <;> omega
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro q e h
    cases q with
    | leaf => simp [treeShapeBoundary] at h
    | node a b c =>
      simp only [treeShapeBoundary, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> subst h <;> simp
  multiplicities := by
    intro q e h
    cases q with
    | leaf => simp [treeShapeBoundary] at h
    | node a b c =>
      simp only [treeShapeBoundary, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> subst h <;> simp
  unit_left := by intro q; simp
  unit_right := by intro q; by_cases h : q = TreeShape.leaf <;> simp [h]
  type_preserve := fun _ _ => rfl

def treeShapeIncidence : Incidence TreeShape TernaryRole GraphType :=
  treeShapeGradedIncidenceData.toIncidence

def treeGradedQuotientPresentation :
    GradedBisimulationQuotientPresentation
      (Q := TreeShape) (QR := TernaryRole) (QT := GraphType)
      treeIncidence where
  classification := treeBisimulationQuotientClassification
  data := treeShapeGradedIncidenceData
  boundary_iff := by
    intro atom
    cases atom <;>
      simp [IncidenceBoundaryValuation, treeBisimulationQuotientClassification,
        treeToShape, treeIncidence, treeBoundary,
        treeShapeGradedIncidenceData, GradedIncidenceData.toIncidence, treeShapeBoundary]

def treeQuotientIncidencePresentation :
    BisimulationQuotientIncidencePresentation
      (Q := TreeShape) (QR := TernaryRole) (QT := GraphType)
      treeIncidence :=
  treeGradedQuotientPresentation.toPresentation

theorem treeQuotientPresentation_equivalence :
    Nonempty (IncTypeEquivalence
      (IncidenceQuotient treeIncidence) TreeShape) :=
  ⟨treeQuotientIncidencePresentation.quotientEquivalence⟩

/- Honest check (task step (d), not assumed): is `treeToShape` a
   `glue`-homomorphism between `treeIncidence` and `treeShapeIncidence`?
   Exactly the same mismatch cycles 41/51 found for `simplexIncidence`/
   `pathIncidence`: both `glue`s share the "absorb at the unit" shape
   (`if i = unit then some j else some i`), but `treeIncidence.glue`
   special-cases the literal representative `leaf 0`, not the whole
   `≈`-class of leaves -- `leaf 0 ≈ leaf 1` (same class), yet gluing each
   against a fixed non-leaf node produces different shapes. -/
theorem treeClassification_glue_not_invariant :
    ¬ treeBisimulationQuotientClassification.GlueInvariant := by
  intro invariant
  have leavesBisimilar : approxBisim treeIncidence (TreeId.leaf 0) (TreeId.leaf 1) :=
    (treeToShape_iff_approxBisim (TreeId.leaf 0) (TreeId.leaf 1)).mp rfl
  have equalMappedGlue := invariant leavesBisimilar
    (approxBisim_refl treeIncidence
      (TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2)))
  have hlhs : treeBisimulationQuotientClassification.mappedSourceGlue
      (TreeId.leaf 0) (TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2)) =
      some (TreeShape.node TreeShape.leaf TreeShape.leaf TreeShape.leaf) := by
    simp [BisimulationQuotientClassification.mappedSourceGlue,
      treeBisimulationQuotientClassification, treeToShape, treeIncidence]
  have hrhs : treeBisimulationQuotientClassification.mappedSourceGlue
      (TreeId.leaf 1) (TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2)) =
      some TreeShape.leaf := by
    simp [BisimulationQuotientClassification.mappedSourceGlue,
      treeBisimulationQuotientClassification, treeToShape, treeIncidence]
  rw [hlhs, hrhs] at equalMappedGlue
  exact absurd equalMappedGlue (by decide)

/- The strictly stronger, "no escape hatch" closure -- available in the
   SAME cycle the quotient itself was constructed (as for `pathIncidence`,
   cycle 51), since `glueRealization_iff_invariant` was already generic
   reusable infrastructure by the time this cycle started. -/
theorem treeShape_glue_not_realizable :
    ¬ treeBisimulationQuotientClassification.GlueRealization :=
  fun realization =>
    treeClassification_glue_not_invariant
      ((BisimulationQuotientClassification.glueRealization_iff_invariant
        treeBisimulationQuotientClassification).mp realization)

theorem treeToShape_no_glue_homomorphism_exists :
    ¬ ∃ glue' : TreeShape → TreeShape → Option TreeShape,
      ∀ x y : TreeId,
        glue' (treeToShape x) (treeToShape y) =
          (treeIncidence.glue x y).map treeToShape :=
  treeShape_glue_not_realizable

/- Research cycle 53 (see RESEARCH_LOG.md): cycle 52's own queued primary
   next-hypothesis -- with THREE separately hand-derived negative results
   now on record (`simplexClassification_glue_not_invariant`, cycle 41/45;
   `pathClassification_glue_not_invariant`, cycle 51;
   `treeClassification_glue_not_invariant`, cycle 52), is there ONE general
   theorem subsuming the repeated instance-by-instance pattern, rather than
   a fourth graded instance re-deriving the same shape of argument by hand a
   fourth time?

   Read all three counterexample proofs side by side (not assumed in
   advance) plus `simplexIncidence`/`pathIncidence`/`treeIncidence`'s own
   `glue`/`unit` fields in `Simplex.lean`/`PathComplex.lean`/`Tree.lean`.
   The literal shared mechanism: EVERY `Incidence`'s `unit_left` law
   (`glue unit i = some i`, an obligation of ALL instances, not
   instance-specific) already pins down `mappedSourceGlue inc.unit j = some
   (classify j)` for free, for any `j`. Each of the three counterexamples
   then supplies exactly one further, genuinely instance-specific fact: some
   OTHER element `x` in `inc.unit`'s own `≈`-class (`x ≠ unit`, `x ≈ unit` --
   `v1 ≈ v0`, `node 1 ≈ node 0`, `leaf 1 ≈ leaf 0` respectively) satisfies
   `glue x j = some x` for some `j` OUTSIDE that class (`classify j ≠
   classify unit` -- `face`, `edge 0`, a `node`/`node` respectively) --
   i.e. `x` is treated as "absorbing/self-fixed" by `glue`, in flat
   contradiction with `unit`'s own law, even though `classify` cannot tell
   `x` and `unit` apart. This holds for all three because
   `simplexIncidence.glue`/`pathIncidence.glue`/`treeIncidence.glue` are
   ALL LITERALLY the identical formula `fun i j => if i = unit then some j
   else some i` (confirmed by reading `Simplex.lean:63`,
   `PathComplex.lean:40`, `Tree.lean:51` directly, not by memory), differing
   only in which concrete element is chosen as `unit`. The theorem below is
   stated in two layers: a primitive lemma needing only the one behavioral
   fact (`glue x j = some x`), then a corollary specializing to the literal
   "absorbing-unit" formula shape all three sources share, from which all
   three concrete instances are re-derived below as one-line applications
   (`rfl` for the formula match, `decide` for the finite disequalities,
   the existing `_iff_approxBisim` characterization for the bisimilarity
   witness) -- no new case analysis on `SimplexId`/`PathId`/`TreeId` at all. -/
theorem glueInvariant_fails_of_unit_class_witness
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {x : I} (xBisimUnit : approxBisim inc x inc.unit)
    {j : I} (jOutsideUnitClass :
      classification.classify j ≠ classification.classify inc.unit)
    (xAbsorbs : inc.glue x j = some x) :
    ¬ classification.GlueInvariant := by
  intro invariant
  have equalMappedGlue := invariant xBisimUnit (approxBisim_refl inc j)
  have hunit : classification.mappedSourceGlue inc.unit j =
      some (classification.classify j) := by
    simp [BisimulationQuotientClassification.mappedSourceGlue, inc.unit_left]
  have hx : classification.mappedSourceGlue x j =
      some (classification.classify x) := by
    simp [BisimulationQuotientClassification.mappedSourceGlue, xAbsorbs]
  rw [hx, hunit] at equalMappedGlue
  have classifyEq : classification.classify j = classification.classify inc.unit :=
    ((classification.respects xBisimUnit).symm.trans
      (Option.some.inj equalMappedGlue)).symm
  exact jOutsideUnitClass classifyEq

theorem glueRealization_fails_of_unit_class_witness
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {x : I} (xBisimUnit : approxBisim inc x inc.unit)
    {j : I} (jOutsideUnitClass :
      classification.classify j ≠ classification.classify inc.unit)
    (xAbsorbs : inc.glue x j = some x) :
    ¬ classification.GlueRealization :=
  fun realization =>
    glueInvariant_fails_of_unit_class_witness classification xBisimUnit
      jOutsideUnitClass xAbsorbs
      ((classification.glueRealization_iff_invariant).mp realization)

/- The specialization matching cycle 52's own phrasing of the open question
   ("any `GradedIncidenceData`-presentable quotient of an instance whose
   `glue` has the `if i = unit then some j else some i`-style fixed-
   representative shape"): once `inc.glue` is LITERALLY that formula, the
   one behavioral fact `glueInvariant_fails_of_unit_class_witness` needs
   (`glue x j = some x`) is automatic from `x ≠ inc.unit` alone -- no
   per-instance glue computation required at all. -/
theorem glueInvariant_fails_of_absorbingUnitGlue
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (absorbing : inc.glue = fun i j => if i = inc.unit then some j else some i)
    {x : I} (xNeUnit : x ≠ inc.unit) (xBisimUnit : approxBisim inc x inc.unit)
    {j : I} (jOutsideUnitClass :
      classification.classify j ≠ classification.classify inc.unit) :
    ¬ classification.GlueInvariant :=
  glueInvariant_fails_of_unit_class_witness classification xBisimUnit jOutsideUnitClass
    (by rw [absorbing]; simp [xNeUnit])

theorem glueRealization_fails_of_absorbingUnitGlue
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (absorbing : inc.glue = fun i j => if i = inc.unit then some j else some i)
    {x : I} (xNeUnit : x ≠ inc.unit) (xBisimUnit : approxBisim inc x inc.unit)
    {j : I} (jOutsideUnitClass :
      classification.classify j ≠ classification.classify inc.unit) :
    ¬ classification.GlueRealization :=
  fun realization =>
    glueInvariant_fails_of_absorbingUnitGlue classification absorbing xNeUnit xBisimUnit
      jOutsideUnitClass
      ((classification.glueRealization_iff_invariant).mp realization)

/- The three corollaries: cycles 41/45, 51, 52's separately hand-derived
   negative results, all re-obtained here as one-line applications of the
   SAME general theorem, at the strongest (`GlueRealization`, "no possible
   glue whatsoever") level directly -- confirming the criterion really does
   subsume all three, not merely resemble them. -/
theorem simplexShape_glue_not_realizable_of_general :
    ¬ simplexBisimulationQuotientClassification.GlueRealization :=
  glueRealization_fails_of_absorbingUnitGlue simplexBisimulationQuotientClassification
    (absorbing := rfl) (x := SimplexId.v1) (xNeUnit := by decide)
    (xBisimUnit := (simplexToShape_iff_approxBisim SimplexId.v1 SimplexId.v0).mp rfl)
    (j := SimplexId.face) (jOutsideUnitClass := by decide)

theorem pathShape_glue_not_realizable_of_general :
    ¬ pathBisimulationQuotientClassification.GlueRealization :=
  glueRealization_fails_of_absorbingUnitGlue pathBisimulationQuotientClassification
    (absorbing := rfl) (x := PathId.node 1) (xNeUnit := by decide)
    (xBisimUnit := (pathToShape_iff_approxBisim (PathId.node 1) (PathId.node 0)).mp rfl)
    (j := PathId.edge 0) (jOutsideUnitClass := by decide)

theorem treeShape_glue_not_realizable_of_general :
    ¬ treeBisimulationQuotientClassification.GlueRealization :=
  glueRealization_fails_of_absorbingUnitGlue treeBisimulationQuotientClassification
    (absorbing := rfl) (x := TreeId.leaf 1) (xNeUnit := by decide)
    (xBisimUnit := (treeToShape_iff_approxBisim (TreeId.leaf 1) (TreeId.leaf 0)).mp rfl)
    (j := TreeId.node (TreeId.leaf 0) (TreeId.leaf 1) (TreeId.leaf 2))
    (jOutsideUnitClass := by decide)

/- Research cycle 54 (see RESEARCH_LOG.md): cycle 53's own queued primary
   next-hypothesis -- does the SAME mechanism that explains
   simplex/path/tree's `GlueInvariant` failure (`glueInvariant_fails_of_unit_class_witness`,
   cycle 53: one universal `Incidence` law, `unit_left`, plus a
   non-singleton `≈`-class containing `unit` witnessed against some `j`
   OUTSIDE that class) ALSO explain `cycleIncidence`'s ORIGINAL
   `boundary`-failure (cycle 38, `cycleIncidence_boundary_not_approxBisim_invariant`)?

   Read cycle 38's raw finding, `cycleIncidence`'s definition
   (`Cycle.lean`, `cycleIncidence_all_collapse`: ALL FOUR elements
   `≈`-related, the total-collapse extreme), and `BoundaryInvariant`'s
   definition (`mappedSourceBoundary` above, which -- unlike cycle 38's
   raw `∀ i j, i ≈ j → inc.boundary i = inc.boundary j` -- only asks for
   agreement AFTER remapping indices through `classify`) side by side,
   rather than assuming either answer.

   The two turn out to be OPPOSITES, not the same mechanism in different
   clothes. Cycle 53's argument needs a witness `j` with `classify j ≠
   classify unit` -- i.e. the classification must have AT LEAST TWO
   distinguishable classes for the statement to even be satisfiable.
   `cycleIncidence`'s quotient is the opposite extreme: `≈` relates
   EVERY pair (`cycleIncidence_all_collapse`), so ANY classification
   target is forced `Subsingleton` -- no `j` "outside" any class can
   exist, `jOutsideUnitClass` is unsatisfiable by construction, not
   merely false in this instance. Checked this isn't a vacuous-hypothesis
   technicality but a genuine semantic fact by building the concrete
   classification the cycle 38-53 framework never instantiated for
   `cycleIncidence` (`cycleBisimulationQuotientClassification`, target
   `Unit`, via `bisimulationQuotientClassificationOfKernel` +
   `cycleIncidence_all_collapse`) and checking `BoundaryInvariant`/
   `GlueInvariant` directly against it. -/

/- The instance this project's `BisimulationQuotientClassification`
   framework never built for `cycleIncidence`: since every pair is `≈`-
   related, the only possible (up to `IncTypeEquivalence`) target is a
   one-point type, `Unit`. The kernel condition is exactly
   `cycleIncidence_all_collapse`, already proven in cycle 26. -/
def cycleBisimulationQuotientClassification :
    BisimulationQuotientClassification (Q := Unit) cycleIncidence :=
  bisimulationQuotientClassificationOfKernel cycleIncidence (fun _ => ())
    (fun x y => ⟨fun _ => cycleIncidence_all_collapse x y, fun _ => rfl⟩)
    (fun q => ⟨CycleId.c0, by cases q; rfl⟩)

/- `BoundaryInvariant` HOLDS here -- the opposite of simplex/path/tree's
   `GlueInvariant`. `classify` is constant (`Unit` has one point), so
   `mappedSourceBoundary x` collapses every element's boundary-entry
   index to that same point regardless of `x`; since `cycleBoundary`
   gives every element the identical `role`/`sign`/`mult` shape
   (cycle 26's own "uniform boundary" observation), the two sides are
   syntactically identical -- no case split on `x`/`y` needed at all. -/
theorem cycleBisimulationQuotientClassification_boundaryInvariant :
    cycleBisimulationQuotientClassification.BoundaryInvariant :=
  fun _ _ _ => rfl

/- `GlueInvariant` HOLDS too, for the identical reason: `cycleIncidence.glue`
   is total (`fun i j => some (cycleAdd i j)`, cycle 26), so
   `mappedSourceGlue x y` is `some ()` for EVERY `x y` once mapped
   through the constant `classify` -- there is no "absorbing element"
   phenomenon to even test, since the target has no room for a second
   class to be absorbing *against*. -/
theorem cycleBisimulationQuotientClassification_glueInvariant :
    cycleBisimulationQuotientClassification.GlueInvariant :=
  fun _ _ _ _ _ _ => rfl

/- Both realizations follow immediately from the already-generic
   `_iff_invariant` lemmas (cycle 51/53's reusable infrastructure). -/
theorem cycleBisimulationQuotientClassification_boundaryRealization :
    cycleBisimulationQuotientClassification.BoundaryRealization :=
  (cycleBisimulationQuotientClassification.boundaryRealization_iff_invariant).mpr
    cycleBisimulationQuotientClassification_boundaryInvariant

theorem cycleBisimulationQuotientClassification_glueRealization :
    cycleBisimulationQuotientClassification.GlueRealization :=
  (cycleBisimulationQuotientClassification.glueRealization_iff_invariant).mpr
    cycleBisimulationQuotientClassification_glueInvariant

/- The general, instance-independent confirmation that cycle 53's
   negative mechanism cannot fire at total collapse: whenever the target
   `Q` is a `Subsingleton`, `jOutsideUnitClass` (cycle 53's key
   hypothesis) is unsatisfiable for ANY classification, by
   `Subsingleton.elim` alone -- no fact about `inc` is needed. This is
   the precise, formal sense in which the two mechanisms are opposites
   rather than instances of one general theorem. -/
theorem no_jOutsideUnitClass_of_subsingleton
    {I R T Q : Type u} [DecidableEq I] [Subsingleton Q] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    ¬ ∃ j : I, classification.classify j ≠ classification.classify inc.unit :=
  fun ⟨_, hne⟩ => hne (Subsingleton.elim _ _)

theorem cycleBisimulationQuotientClassification_unit_class_witness_vacuous :
    ¬ ∃ j : CycleId, cycleBisimulationQuotientClassification.classify j ≠
      cycleBisimulationQuotientClassification.classify cycleIncidence.unit :=
  no_jOutsideUnitClass_of_subsingleton cycleBisimulationQuotientClassification

/- The genuinely different obstruction, stated at the same level of
   generality as cycle 53's theorems (general lemma, then a
   `cycleIncidence`-specific corollary): whenever the target is a
   `Subsingleton` AND the source has *some* point with nonempty
   boundary, `canonicalBoundary` is forced into a literal self-loop at
   EVERY point of the quotient -- not because `BoundaryInvariant` fails
   (it doesn't -- proven above), but because `Subsingleton` collapses
   every boundary entry's remapped index onto the very point whose
   boundary it is attached to. This is the exact obstruction
   `incidence_subsingleton_boundary_empty` (cycle 39) rules out for any
   *well-founded* boundary -- so it is a fact about `well_founded`
   specifically, a law with no analogue in `GlueInvariant`/
   `BoundaryInvariant` at all (those only ever ask for congruence across
   `≈`-classes, never for self-loop-freeness). -/
theorem canonicalBoundary_self_loop_of_subsingleton
    {I R T Q : Type u} [DecidableEq I] [Subsingleton Q] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.BoundaryInvariant)
    {x : I} (nonempty : inc.boundary x ≠ []) (q : Q) :
    ∃ e ∈ classification.canonicalBoundary invariant q, e.i = q := by
  have hq : q = classification.classify x := Subsingleton.elim _ _
  subst hq
  rw [classification.canonicalBoundary_classify]
  match h : inc.boundary x, nonempty with
  | e :: rest, _ =>
    refine ⟨{ e with i := classification.classify e.i }, ?_, Subsingleton.elim _ _⟩
    simp [BisimulationQuotientClassification.mappedSourceBoundary, h]

/- Consequently, NO `CanonicalQuotientIncidenceCoherence` -- the
   congruence-respecting route this project's quotient constructor
   (cycles 41-53) uses to actually assemble a target `Incidence` --
   can ever be completed for a totally-collapsed classification whose
   source has nonempty boundary anywhere, regardless of whether
   `BoundaryInvariant`/`GlueInvariant` hold. -/
theorem no_canonicalQuotientIncidenceCoherence_of_subsingleton_target
    {I R T Q : Type u} [DecidableEq I] [DecidableEq Q] [Subsingleton Q]
    {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {x : I} (nonempty : inc.boundary x ≠ []) :
    ¬ Nonempty (CanonicalQuotientIncidenceCoherence classification) := by
  rintro ⟨coherence⟩
  exact coherence.boundary_no_self (classification.classify x)
    (canonicalBoundary_self_loop_of_subsingleton classification
      coherence.boundaryInvariant nonempty _)

/- Cycle 38's original finding, re-derived: `cycleIncidence`'s
   `boundary`-obstruction is not the `unit_left`/absorbing-element
   mechanism (cycle 53) applied to a new instance -- it is this dual,
   `well_founded`-anchored mechanism, here specialized to the concrete
   classification built above with a one-line application, exactly
   mirroring cycle 53's own specialization pattern
   (`glueRealization_fails_of_absorbingUnitGlue` applied to
   `simplexBisimulationQuotientClassification` etc.). Confirms, rather
   than contradicts, cycle 39's synthesis that the fully-collapsed
   (Subsingleton) case is a qualitatively different regime from the
   partial, "middle-ground" collapse simplex/path/tree exhibit --
   `well_founded` is the load-bearing law here, not any congruence law
   `GlueInvariant`/`BoundaryInvariant` police. -/
theorem cycleBisimulationQuotientClassification_no_coherence :
    ¬ Nonempty (CanonicalQuotientIncidenceCoherence
      cycleBisimulationQuotientClassification) :=
  no_canonicalQuotientIncidenceCoherence_of_subsingleton_target
    cycleBisimulationQuotientClassification
    (x := CycleId.c0) (by simp [cycleIncidence, cycleBoundary])

/- Research cycle 55 (see RESEARCH_LOG.md): cycle 53's queued item (c),
   restated as thread (a) by cycle 54's synthesis -- does any EXISTING
   `Guards` value this project actually attaches to a classified
   `Incidence` have an "absorbing"-style shape parallel to `glue`'s
   (cycle 53), so the same two-layer criterion (general behavioral
   lemma, then a literal-formula specialization) transfers to
   `GuardInvariant`/`GuardRealization`?

   First surprise, checked by `grep`, not assumed: `GuardInvariant`/
   `GuardRealization` (lines ~675-740 above) and
   `CanonicalGuardedQuotientIncidenceCoherence` (~1133-1192) already
   existed BEFORE this cycle, built alongside `GlueInvariant`/
   `GlueRealization` in the same generic infrastructure, complete with
   `canonicalGuards`/`canonicalGuards_unique` and one concrete instance
   already discharged, `natBoolProductClassification_guardInvariant`
   (~1512-1516, over `NatBoolProductIncidence := incidenceProd natIncidence
   trivialIncidence`, whose `guards := prodGuards natIncidence
   trivialIncidence`). So cycle 53's parenthetical ("worth checking
   whether any EXISTING guard definition... before assuming the analogy
   transfers") was answered in one direction already, just not for
   `simplexBisimulationQuotientClassification`/`pathBisimulationQuotientClassification`/
   `treeBisimulationQuotientClassification` (cycle 53's own three glue
   sources) nor `cycleBisimulationQuotientClassification` (cycle 54's
   Subsingleton instance) -- those four were the genuinely untouched
   gap.

   Read `simplexIncidence`'s/`pathIncidence`'s/`treeIncidence`'s/
   `cycleIncidence`'s own `guards` fields directly (`Simplex.lean:65`,
   `PathComplex.lean:42`, `Tree.lean:53`, `Cycle.lean:61`) rather than
   trusting cycle 54's tentative "`Guards.permissive`... looks trivially
   total" phrasing: all FOUR are literally `Guards.permissive`, the exact
   same closed term (not merely similar in spirit, the way cycle 53 first
   had to confirm for `glue`'s absorbing-unit formula). Combined with the
   pre-existing `NatBoolProductIncidence` instance (`prodGuards` of two
   `Guards.permissive`-carrying factors, `natIncidence`/`trivialIncidence`,
   confirmed by reading `natIncidence`'s and `trivialIncidence`'s own
   `guards` fields -- `natIncidence.guards = Guards.permissive Nat`
   literally, `trivialIncidence.guards = { allow := fun _ _ => true }`
   structurally identical to it though spelled out inline rather than via
   the `Guards.permissive` name), EVERY `Guards` value this project has
   ever attached
   to an actually-classified `Incidence` -- all five existing
   `BisimulationQuotientClassification`s in the codebase, no exceptions --
   reduces to a function that ignores BOTH its arguments. This is the
   exact polar opposite of `glue`'s absorbing-unit formula (cycle 53),
   which is essential-argument-dependent by construction (that dependence
   is precisely what broke `GlueInvariant`). So the criterion does not
   "transfer" in the sense of finding a parallel counterexample -- there
   is structurally no room for one, since none of this project's guard
   definitions ever make `allow` depend on its arguments in the first
   place. Proved as one theorem needing NOTHING about `inc`'s laws (no
   `unit_left`-style obligation, no fact about `approxBisim` beyond it
   being some relation, not even `DecidableEq`): constancy of `allow`
   alone forces `GuardInvariant`, full stop, generalizing beyond
   `Guards.permissive` specifically (e.g. it covers `Guards.never`
   (cycle 50) too, were any classification ever built over an instance
   using it -- none currently is, `finiteIncidenceNeverGuards` in
   `Sum.lean` is used only for the unrelated `sumGuardsExpected`
   divergence work, not attached to a `BisimulationQuotientClassification`). -/
theorem guardInvariant_of_constantGuards
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (b : Bool) (constant : ∀ i j, inc.guards.allow i j = b) :
    classification.GuardInvariant :=
  fun x x' y y' _ _ => (constant x y).trans (constant x' y').symm

theorem guardRealization_of_constantGuards
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (b : Bool) (constant : ∀ i j, inc.guards.allow i j = b) :
    classification.GuardRealization :=
  (classification.guardRealization_iff_invariant).mpr
    (guardInvariant_of_constantGuards classification b constant)

/- The specialization matching every concrete instance actually built in
   this project so far: `Guards.permissive`'s `allow` is the constant
   `true`, so the `constant` hypothesis above discharges by `rfl` once
   `inc.guards` is known equal to `Guards.permissive I`. -/
theorem guardInvariant_of_permissive
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (permissive : inc.guards = Guards.permissive I) :
    classification.GuardInvariant :=
  guardInvariant_of_constantGuards classification true
    (fun i j => by simp [permissive, Guards.permissive])

theorem guardRealization_of_permissive
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (permissive : inc.guards = Guards.permissive I) :
    classification.GuardRealization :=
  (classification.guardRealization_iff_invariant).mpr
    (guardInvariant_of_permissive classification permissive)

/- The four corollaries: simplex/path/tree (cycle 53's own three `glue`
   sources, `GuardInvariant` untouched by name until now) plus
   `cycleIncidence` (cycle 54's Subsingleton instance), each a one-line
   application of the general theorem with `permissive := rfl` -- every
   one of these sources' `guards` field literally IS `Guards.permissive`
   (confirmed above by reading the field, not inferred from the name),
   so no case analysis on `SimplexId`/`PathId`/`TreeId`/`CycleId` is
   needed anywhere, mirroring cycle 53's own "zero new casework" corollary
   pattern but for a positive rather than a negative conclusion. -/
theorem simplexClassification_guardInvariant :
    simplexBisimulationQuotientClassification.GuardInvariant :=
  guardInvariant_of_permissive simplexBisimulationQuotientClassification rfl

theorem simplexClassification_guardRealization :
    simplexBisimulationQuotientClassification.GuardRealization :=
  guardRealization_of_permissive simplexBisimulationQuotientClassification rfl

theorem pathClassification_guardInvariant :
    pathBisimulationQuotientClassification.GuardInvariant :=
  guardInvariant_of_permissive pathBisimulationQuotientClassification rfl

theorem pathClassification_guardRealization :
    pathBisimulationQuotientClassification.GuardRealization :=
  guardRealization_of_permissive pathBisimulationQuotientClassification rfl

theorem treeClassification_guardInvariant :
    treeBisimulationQuotientClassification.GuardInvariant :=
  guardInvariant_of_permissive treeBisimulationQuotientClassification rfl

theorem treeClassification_guardRealization :
    treeBisimulationQuotientClassification.GuardRealization :=
  guardRealization_of_permissive treeBisimulationQuotientClassification rfl

theorem cycleBisimulationQuotientClassification_guardInvariant :
    cycleBisimulationQuotientClassification.GuardInvariant :=
  guardInvariant_of_permissive cycleBisimulationQuotientClassification rfl

theorem cycleBisimulationQuotientClassification_guardRealization :
    cycleBisimulationQuotientClassification.GuardRealization :=
  guardRealization_of_permissive cycleBisimulationQuotientClassification rfl

/- Research cycle 56 (see RESEARCH_LOG.md): cycle 54's queued item (c) /
   cycle 55's item (b) -- is there a genuinely THIRD collapse regime,
   distinct from both (i) cycles 41/51/52's "well-founded grading
   survives collapse-within-grade" (simplex/path/tree -- the quotient's
   `Incidence` succeeds, only `glue` realization fails) and (ii) cycles
   38/39/54's "total collapse forces a Subsingleton, `well_founded` fails
   EVERYWHERE" (`cycleIncidence`)? Concretely: a PARTIAL quotient (more
   than one class, fewer than all elements) where the source's grading
   itself degenerates -- develops a genuine `canonicalBoundary` self-loop
   -- but confined to ONE class, while every OTHER class stays perfectly
   well-founded.

   First isolated the mechanism at the right level of generality, rather
   than building an instance first and hoping: `canonicalBoundary_self_
   loop_of_subsingleton` (cycle 54) is really the "every point" special
   case of a sharper LOCAL fact -- whenever some single source element
   `x` has a boundary entry whose target `z` lands in `x`'s OWN `≈`-class
   (whether `z = x`, forced trivially by Subsingleton, or a genuinely
   DISTINCT bisimilar partner `z ≠ x`), `canonicalBoundary` self-loops
   specifically at `classify x` -- regardless of how many OTHER classes
   the quotient has. Cycle 54's theorem is the "holds for every x" case
   forced by Subsingleton; this cycle asks whether "holds for SOME x but
   not all" is separately witnessable, i.e. whether the self-loop
   mechanism can be genuinely PARTIAL.

   Confirmed it can, via a new minimal instance built for exactly this
   question (checked, per the task's own instruction, that no existing
   graded instance -- `simplexIncidence`/`pathIncidence`/`treeIncidence`
   -- could exhibit this: `BisimulationQuotientClassification.reflects`
   forces `classify`'s kernel to equal `≈` EXACTLY for a given source, so
   there is no "different, coarser bisimulation collapse" of an EXISTING
   instance to try -- `≈` (`approxBisim`) is already, by its own
   definition as `∃ rel, IsBisimulation rel ∧ rel i j`, the union of every
   bisimulation on that source, hence the unique coarsest one; a genuinely
   new source had to be built instead). `MirrorId := m0 | m1 | u`:
   `m0`/`m1` mutually reference each other (a 2-element closed cycle,
   cycle 26's 4-cycle mechanism scaled down to its minimal case), while
   `u` is a genuine, structurally disjoint leaf (empty boundary).
   `mirrorIncidence.well_founded` holds (`m0 ≠ m1`, no *literal* self-
   loop at either element) -- but exactly as cycle 26 already observed
   for the 4-cycle, that raw field only forbids DIRECT self-reference,
   not a 2-cycle; checked directly (not assumed) that `{m0, m1}` admits
   NO valid `Nat`-valued strictly-decreasing grading at all (any such
   grading needs `grade m1 < grade m0` from `m0`'s boundary AND
   `grade m0 < grade m1` from `m1`'s -- immediate contradiction), so this
   really is a genuinely UNGRADED sub-structure, unlike simplex/path/
   tree's uniformly graded carriers. -/

inductive MirrorRole where | link
deriving DecidableEq, Repr

inductive MirrorId where | m0 | m1 | u
deriving DecidableEq, Repr

def mirrorBoundary : MirrorId → Boundary MirrorId MirrorRole
  | .m0 => [{ i := .m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 }]
  | .m1 => [{ i := .m0, role := MirrorRole.link, sign := Sign.neg, mult := 1 }]
  | .u  => []

/- Same "absorb at a fixed literal unit representative" `glue` shape
   every prior instance in this project uses (cycle 53's `absorbing`
   formula) -- not load-bearing for this cycle's finding (which is about
   `boundary`/`well_founded`, not `glue`), kept only for consistency with
   the rest of the project's style. -/
def mirrorIncidence : Incidence MirrorId MirrorRole GraphType where
  boundary := mirrorBoundary
  typeFunc := fun _ => GraphType.unit
  glue := fun i j => if i = MirrorId.u then some j else some i
  unit := MirrorId.u
  guards := Guards.permissive MirrorId
  type_consistent := fun _ _ _ => rfl
  sign_rules := fun _ e _ => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [mirrorBoundary] at he <;> subst he <;> simp_all
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = MirrorId.u <;> simp [h]
  type_preserve := fun _ _ => rfl

/- Confirms the `{m0, m1}` sub-structure genuinely has no valid
   `Nat`-valued strictly-decreasing grading -- unlike `simplexIncidence`/
   `pathIncidence`/`treeIncidence`, `GradedIncidenceData`'s
   `boundary_decreases` obligation could never be discharged for
   `mirrorIncidence` even restricted to just these two elements, since it
   would demand `grade m1 < grade m0` and `grade m0 < grade m1`
   simultaneously. This is the formal confirmation of cycle 26's
   informal observation (the 4-cycle "has no base case") sharpened into
   an actual non-existence theorem, and the precise sense in which this
   instance's `well_founded` field (satisfied) and genuine well-
   foundedness (Nat-gradeable, NOT satisfied) come apart. -/
theorem mirrorIncidence_no_valid_grading :
    ¬ ∃ grade : MirrorId → Nat,
      ∀ q e, e ∈ mirrorBoundary q → grade e.i < grade q := by
  rintro ⟨grade, decreases⟩
  have h01 : grade MirrorId.m1 < grade MirrorId.m0 :=
    decreases MirrorId.m0 { i := MirrorId.m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
      (by simp [mirrorBoundary])
  have h10 : grade MirrorId.m0 < grade MirrorId.m1 :=
    decreases MirrorId.m1 { i := MirrorId.m0, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
      (by simp [mirrorBoundary])
  exact absurd (Nat.lt_trans h01 h10) (Nat.lt_irrefl _)

/- The bisimulation relation witnessing the partial collapse: `m0`/`m1`
   are mutually related (both directions, both "self" pairs), `u` is
   related only to itself -- exactly the shape `mirrorToShape` (below)
   is meant to characterize. -/
abbrev mirrorRel (a b : MirrorId) : Prop :=
  (a = MirrorId.m0 ∨ a = MirrorId.m1) ∧ (b = MirrorId.m0 ∨ b = MirrorId.m1) ∨
  (a = MirrorId.u ∧ b = MirrorId.u)

theorem mirrorRel_isBisimulation : IsBisimulation mirrorIncidence mirrorRel := by
  intro i j hij
  refine ⟨rfl, ?_⟩
  rcases hij with ⟨hi, hj⟩ | ⟨hu, hu'⟩
  · rcases hi with hi | hi <;> subst hi <;> rcases hj with hj | hj <;> subst hj
    · exact boundaryMatched_of_one_entry mirrorIncidence mirrorRel MirrorId.m0 MirrorId.m0
        { i := MirrorId.m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        { i := MirrorId.m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
    · exact boundaryMatched_of_one_entry mirrorIncidence mirrorRel MirrorId.m0 MirrorId.m1
        { i := MirrorId.m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        { i := MirrorId.m0, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
    · exact boundaryMatched_of_one_entry mirrorIncidence mirrorRel MirrorId.m1 MirrorId.m0
        { i := MirrorId.m0, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        { i := MirrorId.m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
    · exact boundaryMatched_of_one_entry mirrorIncidence mirrorRel MirrorId.m1 MirrorId.m1
        { i := MirrorId.m0, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        { i := MirrorId.m0, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
  · subst hu; subst hu'
    simp [boundaryMatched, mirrorIncidence, mirrorBoundary]

theorem mirrorIncidence_m0_not_bisim_u : ¬ approxBisim mirrorIncidence MirrorId.m0 MirrorId.u :=
  not_approxBisim_empty_nonempty mirrorIncidence MirrorId.m0 MirrorId.u rfl
    { i := MirrorId.m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
    (by simp [mirrorIncidence, mirrorBoundary])

theorem mirrorIncidence_m1_not_bisim_u : ¬ approxBisim mirrorIncidence MirrorId.m1 MirrorId.u :=
  not_approxBisim_empty_nonempty mirrorIncidence MirrorId.m1 MirrorId.u rfl
    { i := MirrorId.m0, role := MirrorRole.link, sign := Sign.neg, mult := 1 }
    (by simp [mirrorIncidence, mirrorBoundary])

inductive MirrorShape where | pairShape | leafShape
deriving DecidableEq, Repr

def mirrorToShape : MirrorId → MirrorShape
  | .m0 => .pairShape
  | .m1 => .pairShape
  | .u  => .leafShape

theorem mirrorToShape_reflects (x y : MirrorId) (h : mirrorToShape x = mirrorToShape y) :
    approxBisim mirrorIncidence x y := by
  cases x <;> cases y <;> simp [mirrorToShape] at h <;>
    exact ⟨mirrorRel, mirrorRel_isBisimulation, by decide⟩

theorem mirrorToShape_distinguishes (x y : MirrorId) (h : approxBisim mirrorIncidence x y) :
    mirrorToShape x = mirrorToShape y := by
  cases x <;> cases y <;> simp only [mirrorToShape] <;>
    first
    | rfl
    | exact absurd h mirrorIncidence_m0_not_bisim_u
    | exact absurd h mirrorIncidence_m1_not_bisim_u
    | exact absurd (approxBisim_symm h) mirrorIncidence_m0_not_bisim_u
    | exact absurd (approxBisim_symm h) mirrorIncidence_m1_not_bisim_u

/- The exhaustive characterization: exactly two classes over three
   elements -- `{m0, m1}` and `{u}` -- a genuinely PARTIAL quotient
   (more than one class, fewer than all elements), matching cycle
   41/51/52's simplex/path/tree cardinality profile in COUNT, but built
   from a source with no valid grading at all rather than a well-founded
   one. -/
theorem mirrorToShape_iff_approxBisim (x y : MirrorId) :
    mirrorToShape x = mirrorToShape y ↔ approxBisim mirrorIncidence x y :=
  ⟨mirrorToShape_reflects x y, mirrorToShape_distinguishes x y⟩

def mirrorBisimulationQuotientClassification :
    BisimulationQuotientClassification (Q := MirrorShape) mirrorIncidence :=
  bisimulationQuotientClassificationOfKernel mirrorIncidence mirrorToShape
    mirrorToShape_iff_approxBisim
    (fun shape => by
      cases shape with
      | pairShape => exact ⟨MirrorId.m0, rfl⟩
      | leafShape => exact ⟨MirrorId.u, rfl⟩)

/- `BoundaryInvariant` HOLDS -- `mappedSourceBoundary` is well-defined on
   both classes (`{m0, m1}`'s two elements produce syntactically the same
   remapped boundary, `[{i := pairShape, ...}]`, since `classify m0 =
   classify m1 = pairShape`; `{u}` trivially has none). This is exactly
   the prerequisite cycle 41/51/52's positive constructions needed, and
   it holds here too -- the obstruction this cycle finds is NOT a
   `BoundaryInvariant` failure (unlike cycle 38's raw, unindexed
   `cycleIncidence` finding), it is what happens ONE LEVEL UP, at
   `well_founded`, exactly mirroring cycle 54's contrast with cycle 53. -/
theorem mirrorBisimulationQuotientClassification_boundaryInvariant :
    mirrorBisimulationQuotientClassification.BoundaryInvariant := by
  intro x y hxy
  cases x <;> cases y <;>
    first
    | rfl
    | exact absurd hxy mirrorIncidence_m0_not_bisim_u
    | exact absurd hxy mirrorIncidence_m1_not_bisim_u
    | exact absurd (approxBisim_symm hxy) mirrorIncidence_m0_not_bisim_u
    | exact absurd (approxBisim_symm hxy) mirrorIncidence_m1_not_bisim_u

/- The general, instance-independent mechanism this cycle isolates:
   `canonicalBoundary_self_loop_of_subsingleton` (cycle 54) is the
   "holds at EVERY point" special case, forced by `Subsingleton`, of this
   sharper LOCAL fact -- whenever some single source element `x` has a
   boundary entry `e` whose target `e.i` lands in `x`'s OWN `≈`-class
   (`classify e.i = classify x`, whether because `e.i = x` literally or
   because `e.i` is merely a DISTINCT bisimilar partner of `x`),
   `canonicalBoundary` self-loops specifically at `classify x` --
   regardless of how many OTHER classes the quotient has, and regardless
   of whether `classify` is (as here) genuinely non-injective on other
   elements too. This is the key structural difference from cycle 54's
   theorem: THAT theorem quantifies over every `q` (forced, since
   `Subsingleton` makes every `q` equal); THIS theorem is local to
   whichever single class the witnessing `x` happens to land in. -/
theorem canonicalBoundary_self_loop_of_boundary_within_class
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.BoundaryInvariant)
    {x : I} {e : Endpoint I R} (member : e ∈ inc.boundary x)
    (within : classification.classify e.i = classification.classify x) :
    ∃ e' ∈ classification.canonicalBoundary invariant (classification.classify x),
      e'.i = classification.classify x := by
  refine ⟨{ e with i := classification.classify e.i }, ?_, within⟩
  rw [classification.canonicalBoundary_classify]
  exact List.mem_map.mpr ⟨e, member, rfl⟩

/- Cycle 54's own theorem re-derived as a special case of the general
   local fact above, confirming this cycle's generalization is genuine
   (not merely analogous in spirit): `Subsingleton` forces `within` to
   hold trivially (`Subsingleton.elim`) for EVERY `x`/`q` pair at once,
   recovering the "self-loop everywhere" conclusion cycle 54 proved by a
   direct, instance-shaped argument. -/
theorem canonicalBoundary_self_loop_of_subsingleton_via_local
    {I R T Q : Type u} [DecidableEq I] [Subsingleton Q] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    (invariant : classification.BoundaryInvariant)
    {x : I} (nonempty : inc.boundary x ≠ []) (q : Q) :
    ∃ e ∈ classification.canonicalBoundary invariant q, e.i = q := by
  have hq : q = classification.classify x := Subsingleton.elim _ _
  subst hq
  match h : inc.boundary x, nonempty with
  | e :: _, _ =>
    exact canonicalBoundary_self_loop_of_boundary_within_class classification invariant
      (e := e) (by simp [h]) (Subsingleton.elim _ _)

/- The concrete witness: `m0`'s single boundary entry points to `m1`,
   and `m1 ≈ m0` (same `pairShape` class) -- `within` holds via `rfl`,
   since `mirrorToShape m1 = mirrorToShape m0 = pairShape` definitionally.
   This produces a genuine self-loop AT THE `pairShape` CLASS SPECIFICALLY
   -- `leafShape` (the OTHER class, `{u}`) is untouched, still perfectly
   well-founded (`canonicalBoundary leafShape = []`, no entries at all).
   This is the genuinely PARTIAL analogue of cycle 39/54's total-collapse
   self-loop: the obstruction is confined to exactly the class descending
   from the source's ungraded `{m0, m1}` sub-structure. -/
theorem mirrorPairShape_canonicalBoundary_self_loop
    (invariant : mirrorBisimulationQuotientClassification.BoundaryInvariant) :
    ∃ e ∈ mirrorBisimulationQuotientClassification.canonicalBoundary invariant
        (mirrorBisimulationQuotientClassification.classify MirrorId.m0),
      e.i = mirrorBisimulationQuotientClassification.classify MirrorId.m0 :=
  canonicalBoundary_self_loop_of_boundary_within_class
    mirrorBisimulationQuotientClassification invariant
    (x := MirrorId.m0)
    (e := { i := MirrorId.m1, role := MirrorRole.link, sign := Sign.neg, mult := 1 })
    (by simp [mirrorIncidence, mirrorBoundary]) rfl

/- Consequently, NO `CanonicalQuotientIncidenceCoherence` can ever be
   completed for `mirrorBisimulationQuotientClassification`, exactly
   mirroring cycle 54's closing theorem for `cycleIncidence` -- but this
   time the classification is genuinely PARTIAL (two classes, `pairShape`
   and `leafShape`, over three elements), not a `Subsingleton`. The
   obstruction is confined to `pairShape`; `boundary_no_self` still has to
   hold at EVERY class for a `CanonicalQuotientIncidenceCoherence` to
   exist at all, so failing at just one class is already enough to rule
   out the whole structure -- the third regime this cycle's task asked
   about. -/
theorem mirrorBisimulationQuotientClassification_no_coherence :
    ¬ Nonempty (CanonicalQuotientIncidenceCoherence
      mirrorBisimulationQuotientClassification) := by
  rintro ⟨coherence⟩
  obtain ⟨e', mem, heq⟩ :=
    mirrorPairShape_canonicalBoundary_self_loop coherence.boundaryInvariant
  exact coherence.boundary_no_self
    (mirrorBisimulationQuotientClassification.classify MirrorId.m0) ⟨e', mem, heq⟩

/- Research cycle 57 (see RESEARCH_LOG.md): the last remaining item from
   cycle 53's original three-item queue, deferred through cycles 54
   (Subsingleton `well_founded`), 55 (`GuardInvariant`'s constancy
   mechanism), and 56 (the third, local-collapse regime) -- each of
   which picked a DIFFERENT item off that queue. Cycle 55's own
   next-hypothesis states it precisely: `prodGuards` (`Product.lean`,
   cycle 31) of two CONSTANT-guards factors was shown to stay constant
   (hence trivially `GuardInvariant`-respecting, via
   `guardInvariant_of_constantGuards`), but "never constructed or
   audited a `prodGuards` instance built from a NON-constant factor
   guard" -- and cycle 55 also confirmed, by reading every `guards :=`
   field in the project, that EVERY existing classified instance's
   guards is constant (`Guards.permissive` or equivalent), so this is a
   genuinely untested case, not a re-derivation.

   Read `Product.lean`'s `prodGuards` directly first (not assumed):
   `allow := fun (i1, i2) (j1, j2) => inc1.guards.allow i1 j1 &&
   inc2.guards.allow i2 j2` -- a literal, unconditional componentwise
   `Bool.and`, already the "naive expected" definition itself (unlike
   `incidenceSum`'s guards, cycle 46/47/50's finding, which is the
   CONSTANT `Guards.permissive` regardless of either factor -- the
   asymmetry cycle 47 first named). So there is no scope, even in
   principle, for `prodGuards`'s TOP-LEVEL `allow` value to diverge from
   componentwise `&&` the way `incidenceSum`'s diverges from
   `sumGuardsExpected` -- that question was already closed by cycle 47's
   reading of the source. The genuinely open question, per cycle 55's
   framing, is one level up: does this componentwise `&&` correctly
   TRANSPORT `GuardInvariant` (guards respecting `≈`) from the factors to
   the product, for a factor whose own guards is NOT constant -- or does
   the combination introduce some new blind spot of its own?

   Built the required non-constant witness fresh, per cycle 55's own
   audit (no existing instance qualifies): `Guards.diag`, `allow i j :=
   decide (i = j)`, and `mirrorDiagGuards` -- cycle 56's `mirrorIncidence`
   with ONLY the `guards` field swapped, everything else (including
   `type_preserve := fun _ _ => rfl`) copied verbatim, exactly cycle 50's
   `finiteIncidenceNeverGuards` recipe: `mirrorIncidence.typeFunc` is the
   constant `GraphType.unit`, so `type_preserve` never actually depended
   on its `guards.allow` hypothesis, and the same proof term typechecks
   unchanged against ANY replacement `guards`. Picked `mirrorIncidence`
   deliberately over a fresh from-scratch instance because it is the
   project's only carrier with a genuinely NON-TRIVIAL `≈` collapse
   (`m0 ≈ m1`, cycle 56) -- `natIncidence`/`finiteIncidence`-style fully
   faithful carriers (`≈ ↔ =`) would make the guard-invariance question
   VACUOUS (any function of two arguments trivially respects `=`), so
   they cannot exercise the property being tested at all. -/

def Guards.diag (I : Type u) [DecidableEq I] : Guards I :=
  { allow := fun i j => decide (i = j) }

/- `mirrorIncidence` (cycle 56) with only `guards` replaced -- `boundary`/
   `typeFunc`/`glue`/`unit` copied verbatim, so `IsBisimulation`/
   `approxBisim` (defined in `IncidenceTheory.lean` purely in terms of
   `typeFunc`/`boundary`, never `guards`) are UNCHANGED by the swap. -/
def mirrorDiagGuards : Incidence MirrorId MirrorRole GraphType where
  boundary := mirrorBoundary
  typeFunc := fun _ => GraphType.unit
  glue := fun i j => if i = MirrorId.u then some j else some i
  unit := MirrorId.u
  guards := Guards.diag MirrorId
  type_consistent := fun _ _ _ => rfl
  sign_rules := fun _ e _ => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [mirrorBoundary] at he <;> subst he <;> simp_all
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = MirrorId.u <;> simp [h]
  type_preserve := fun _ _ => rfl

/- `mirrorRel_isBisimulation` (cycle 56) typechecks directly at
   `mirrorDiagGuards` with no new proof at all -- confirming, not merely
   asserting, that the guards swap leaves `IsBisimulation`/`mirrorRel`
   completely untouched (`IsBisimulation`'s definition never mentions
   `guards`, so the exact same proof term is accepted against either
   incidence). -/
theorem mirrorRel_isBisimulation_diag : IsBisimulation mirrorDiagGuards mirrorRel :=
  mirrorRel_isBisimulation

theorem approxBisim_mirrorDiagGuards_m0_m1 :
    approxBisim mirrorDiagGuards MirrorId.m0 MirrorId.m1 :=
  ⟨mirrorRel, mirrorRel_isBisimulation_diag, by decide⟩

/- The concrete failure: `mirrorDiagGuards`'s OWN guards do not respect
   its OWN `≈` -- `m0 ≈ m1` (just above), yet `allow m0 m0 ≠ allow m1 m0`,
   `decide`-checked directly against the computed `Bool` values. This is
   the first hand-built `GuardInvariant` FAILURE in this project's
   history: cycle 55 showed every existing classified instance's guards
   trivially satisfies `GuardInvariant` because every one is constant;
   this confirms a genuinely non-constant guards value is not merely a
   definitional curiosity but can actually break the property, PROVIDED
   the underlying `≈` is non-trivial (a fully faithful carrier could
   never witness this, as noted above). -/
theorem mirrorDiagGuards_not_guardInvariant :
    mirrorDiagGuards.guards.allow MirrorId.m0 MirrorId.m0 = true ∧
      mirrorDiagGuards.guards.allow MirrorId.m1 MirrorId.m0 = false ∧
      approxBisim mirrorDiagGuards MirrorId.m0 MirrorId.m1 :=
  ⟨by decide, by decide, approxBisim_mirrorDiagGuards_m0_m1⟩

/- The headline generic theorem answering cycle 55's queued question:
   `prodGuards`'s componentwise `&&`, combined with
   `incidenceProd_approxBisim_iff` (cycle 32: `≈` on the product is
   EXACTLY componentwise `≈`, no more and no less), transports
   `GuardInvariant` from the two factors to the product UNCONDITIONALLY
   -- no constancy hypothesis on either factor's `guards` at all. This is
   strictly more general than cycle 55's `guardInvariant_of_constantGuards`
   (which only covers the special case where each factor's `allow`
   ignores its arguments entirely; a constant function trivially
   satisfies the hypotheses `h1`/`h2` below, so that theorem is the
   special case of this one, not an alternative to it). -/
theorem incidenceProd_guardInvariant_of_factors
    {I1 R1 T1 I2 R2 T2 Q : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (classification :
      BisimulationQuotientClassification (Q := Q) (incidenceProd inc1 inc2))
    (h1 : ∀ ⦃x x' y y' : I1⦄, approxBisim inc1 x x' → approxBisim inc1 y y' →
        inc1.guards.allow x y = inc1.guards.allow x' y')
    (h2 : ∀ ⦃x x' y y' : I2⦄, approxBisim inc2 x x' → approxBisim inc2 y y' →
        inc2.guards.allow x y = inc2.guards.allow x' y') :
    classification.GuardInvariant := by
  rintro ⟨p1, p2⟩ ⟨p1', p2'⟩ ⟨q1, q2⟩ ⟨q1', q2'⟩ hp hq
  rw [incidenceProd_approxBisim_iff] at hp hq
  simp only [incidenceProd, prodGuards]
  rw [h1 hp.1 hq.1, h2 hp.2 hq.2]

/- The concrete confirmation, mirroring cycle 50's `_diverges_concrete`
   pattern: `incidenceProd mirrorDiagGuards natIncidence`'s ACTUAL guards
   (the literal `&&` computed from `mirrorDiagGuards`'s own
   `GuardInvariant`-violating guards, cycle 50's `Guards.permissive`
   right factor contributing nothing but `true`) diverges on exactly the
   pair the theorem above predicts it must -- `prodGuards` neither hides
   nor amplifies the factor's own blind spot, it PROPAGATES it exactly,
   with no independent defect of its own. This is the honest converse of
   `incidenceProd_guardInvariant_of_factors`: since `mirrorDiagGuards`
   fails hypothesis `h1`, the product's `GuardInvariant` fails too, and
   both failures are the SAME divergence (`allow m0 m0 = true`,
   `allow m1 m0 = false`, `m0 ≈ m1`), witnessed here componentwise via
   `natIncidence`'s permissive right factor contributing a constant
   `true` that changes nothing. -/
theorem incidenceProd_mirrorDiagGuards_nat_guardInvariant_fails :
    approxBisim (incidenceProd mirrorDiagGuards natIncidence)
        (MirrorId.m0, (0 : Nat)) (MirrorId.m0, (0 : Nat)) ∧
      approxBisim (incidenceProd mirrorDiagGuards natIncidence)
        (MirrorId.m0, (0 : Nat)) (MirrorId.m1, (0 : Nat)) ∧
      (incidenceProd mirrorDiagGuards natIncidence).guards.allow
          (MirrorId.m0, (0 : Nat)) (MirrorId.m0, (0 : Nat)) = true ∧
      (incidenceProd mirrorDiagGuards natIncidence).guards.allow
          (MirrorId.m1, (0 : Nat)) (MirrorId.m0, (0 : Nat)) = false := by
  refine ⟨approxBisim_refl _ _, ?_, by decide, by decide⟩
  rw [incidenceProd_approxBisim_iff]
  exact ⟨approxBisim_mirrorDiagGuards_m0_m1, approxBisim_refl _ _⟩

/- Synthesis recorded here rather than only in RESEARCH_LOG.md, matching
   this file's convention of stating the closing contrast alongside the
   theorems: `prodGuards` has NO blind spot of its own, in sharp asymmetry
   with `incidenceSum` (cycles 46/47/50) -- `incidenceSum`'s guards
   DISCARD both factors' guards entirely (a constant `Guards.permissive`
   regardless of what `inc1`/`inc2` supply), while `prodGuards`'s literal
   componentwise `&&` transports `GuardInvariant` faithfully from the
   factors, PROVEN generically (`incidenceProd_guardInvariant_of_factors`)
   and confirmed against the first genuinely non-constant guards witness
   this project has built (`mirrorDiagGuards`), not merely against the
   constant guards every prior instance happened to use. -/


/- Research cycle 58 (see RESEARCH_LOG.md): the one remaining item from
   cycle 56's queue -- does cycle 53's `GlueInvariant`-failure mechanism
   (`glueInvariant_fails_of_unit_class_witness`, keyed on the specific
   distinguished `inc.unit` element and its universal `unit_left` law)
   admit a class-LOCAL refinement, the way cycle 56's
   `canonicalBoundary_self_loop_of_boundary_within_class` refined cycle
   54's GLOBAL `Subsingleton` theorem? Cycle 57 flagged a precise reason
   to be skeptical rather than assume the pattern transfers mechanically:
   `GlueInvariant` compares `glue x y` across a PAIR of `≈`-related
   inputs (two-argument, congruence-shaped), unlike `BoundaryInvariant`'s
   single-argument, shape-shaped obligation that cycle 56 localized.

   Read cycle 53's proof of `glueInvariant_fails_of_unit_class_witness`
   again with this question specifically in mind: which of its hypotheses
   is doing the "global" work cycle 56 found a way to remove? The answer
   is NOT the two-argument/congruence shape cycle 57 worried about --
   `GlueInvariant`'s NEGATION was already existential/pointwise from the
   moment cycle 53 stated it (needing just ONE witnessing `x`/`j` pair,
   nothing about "every class"), so there was never a cardinality-style
   global hypothesis analogous to cycle 54's `Subsingleton` to remove in
   the first place. The actual global dependency is different: the proof
   uses `inc.unit_left`, a law quantified `∀ j` but ANCHORED at the one
   element `inc.unit` -- and the proof only ever INSTANTIATES that law at
   the single `j` already fixed by the `xAbsorbs` hypothesis. So the
   `∀ j` quantification is never load-bearing; only the one-point fact
   `inc.glue inc.unit j = some j` (for THAT `j`) is used. This is the
   real localization axis: replace "the ∀-quantified law, which only
   `inc.unit` can supply" with "the one-point behavioral fact, which any
   element could in principle supply at that one `j`" -- a DIFFERENT axis
   from cycle 56's "how many classes does the hypothesis quantify over."

   Before building anything, checked directly (not assumed) whether
   `inc.unit` is the ONLY element that could ever supply even the FULL
   `∀ j` version of this fact, since if some other element could always
   do so too, the "generalization" would be vacuous. `unit_unique_full_
   left_identity` below proves it in two lines from `unit_right` alone,
   for EVERY `Incidence`: an element with `∀ j, glue e j = some j` is
   forced to equal `inc.unit`. So the full-law form of the property really
   is unit-exclusive -- confirming any genuine generalization has to work
   at the strictly weaker ONE-POINT level cycle 53's own proof actually
   uses, not by finding a second element with the full law.

   Built `glueInvariant_fails_of_class_witness`: the primitive lemma with
   `inc.unit`/`unit_left` replaced by an arbitrary `e`/a one-point
   hypothesis `inc.glue e j = some j`. `glueInvariant_fails_of_unit_
   class_witness_via_local` re-derives cycle 53's exact original theorem
   as the special case `e := inc.unit`, `inc.unit_left j` -- confirming
   the generalization is genuine, not merely a relabeling, exactly
   mirroring cycle 56's own re-derivation of cycle 54's theorem.

   To confirm this is exercised at a genuinely NEW point (not just
   re-provable via cycle 53's own criterion under a different name, the
   way `Guards.never` turned out to be a dead end for cycle 57), built
   `glueLocalIncidence`: a fresh 4-element carrier (`GlueLocalId := core |
   e | x | out`) where `core` is `inc.unit` with a genuine SINGLETON
   `≈`-class (`glueLocalIncidence_unit_class_singleton` proves this, so
   cycle 53's own criterion is PROVABLY inapplicable here, exactly
   mirroring cycle 54's `no_jOutsideUnitClass_of_subsingleton` vacuity
   check but for the opposite reason -- there unit's class was
   the WHOLE space; here it is a singleton within a partial quotient),
   while `e`/`x` form a separate NON-singleton class (mutual boundary
   reference, cycle 56's `mirrorIncidence` recipe) at which the new
   one-point identity fact holds (`glue e out = some out`) alongside the
   conflicting absorbing behavior of its classmate (`glue x out = some
   x`) -- witnessing `glueInvariant_fails_of_class_witness`'s hypotheses
   at `e ≠ inc.unit` for the first time in this project. `out`'s boundary
   entry uses a DIFFERENT role (`GlueLocalRole.anchor` vs `e`/`x`'s
   `.link`) specifically so `out`'s non-bisimilarity to `e`/`x` is a
   one-step `boundaryCompatible` mismatch rather than requiring a deeper
   argument about what `out`'s target itself bisimulates with. -/

inductive GlueLocalRole where | link | anchor
deriving DecidableEq, Repr

inductive GlueLocalId where | core | e | x | out
deriving DecidableEq, Repr

def glueLocalBoundary : GlueLocalId → Boundary GlueLocalId GlueLocalRole
  | .e    => [{ i := .x, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }]
  | .x    => [{ i := .e, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }]
  | .core => []
  | .out  => [{ i := .core, role := GlueLocalRole.anchor, sign := Sign.neg, mult := 1 }]

/- `glue` deliberately keeps the project's usual "absorb at a fixed
   representative" shape at `core` (= `unit`), matching `unit_left`/
   `unit_right`, but ALSO carries a second, purely LOCAL exception at
   `(e, out)` -- `e` behaves like an identity specifically toward `out`,
   even though `e ≠ inc.unit` and `e`'s own class is non-singleton. `x`
   (`e`'s classmate) keeps the ordinary "absorb self" behavior at `out`,
   producing the same clash cycle 53's mechanism needs, just anchored at
   `e` instead of `inc.unit`. -/
def glueLocalIncidence : Incidence GlueLocalId GlueLocalRole GraphType where
  boundary := glueLocalBoundary
  typeFunc := fun _ => GraphType.unit
  glue := fun i k =>
    if i = GlueLocalId.e ∧ k = GlueLocalId.out then some k
    else if i = GlueLocalId.core then some k
    else some i
  unit := GlueLocalId.core
  guards := Guards.permissive GlueLocalId
  type_consistent := fun _ _ _ => rfl
  sign_rules := fun _ e _ => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [glueLocalBoundary] at he <;> subst he <;> simp_all
  unit_left := by intro i; simp
  unit_right := by
    intro i
    cases i <;> simp
  type_preserve := fun _ _ => rfl

abbrev glueLocalRel (a b : GlueLocalId) : Prop :=
  (a = GlueLocalId.e ∨ a = GlueLocalId.x) ∧ (b = GlueLocalId.e ∨ b = GlueLocalId.x) ∨
  (a = GlueLocalId.core ∧ b = GlueLocalId.core) ∨
  (a = GlueLocalId.out ∧ b = GlueLocalId.out)

theorem glueLocalRel_isBisimulation : IsBisimulation glueLocalIncidence glueLocalRel := by
  intro i j hij
  refine ⟨rfl, ?_⟩
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rcases hi with hi | hi <;> subst hi <;> rcases hj with hj | hj <;> subst hj
    · exact boundaryMatched_of_one_entry glueLocalIncidence glueLocalRel GlueLocalId.e GlueLocalId.e
        { i := GlueLocalId.x, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        { i := GlueLocalId.x, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
    · exact boundaryMatched_of_one_entry glueLocalIncidence glueLocalRel GlueLocalId.e GlueLocalId.x
        { i := GlueLocalId.x, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        { i := GlueLocalId.e, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
    · exact boundaryMatched_of_one_entry glueLocalIncidence glueLocalRel GlueLocalId.x GlueLocalId.e
        { i := GlueLocalId.e, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        { i := GlueLocalId.x, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
    · exact boundaryMatched_of_one_entry glueLocalIncidence glueLocalRel GlueLocalId.x GlueLocalId.x
        { i := GlueLocalId.e, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        { i := GlueLocalId.e, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
        rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)
  · subst hi; subst hj
    simp [boundaryMatched, glueLocalIncidence, glueLocalBoundary]
  · subst hi; subst hj
    exact boundaryMatched_of_one_entry glueLocalIncidence glueLocalRel GlueLocalId.out GlueLocalId.out
      { i := GlueLocalId.core, role := GlueLocalRole.anchor, sign := Sign.neg, mult := 1 }
      { i := GlueLocalId.core, role := GlueLocalRole.anchor, sign := Sign.neg, mult := 1 }
      rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)

theorem glueLocalIncidence_e_not_bisim_core :
    ¬ approxBisim glueLocalIncidence GlueLocalId.e GlueLocalId.core :=
  not_approxBisim_empty_nonempty glueLocalIncidence GlueLocalId.e GlueLocalId.core rfl
    { i := GlueLocalId.x, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
    (by simp [glueLocalIncidence, glueLocalBoundary])

theorem glueLocalIncidence_x_not_bisim_core :
    ¬ approxBisim glueLocalIncidence GlueLocalId.x GlueLocalId.core :=
  not_approxBisim_empty_nonempty glueLocalIncidence GlueLocalId.x GlueLocalId.core rfl
    { i := GlueLocalId.e, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
    (by simp [glueLocalIncidence, glueLocalBoundary])

theorem glueLocalIncidence_core_not_bisim_out :
    ¬ approxBisim glueLocalIncidence GlueLocalId.core GlueLocalId.out := by
  intro h
  exact not_approxBisim_empty_nonempty glueLocalIncidence GlueLocalId.out GlueLocalId.core rfl
    { i := GlueLocalId.core, role := GlueLocalRole.anchor, sign := Sign.neg, mult := 1 }
    (by simp [glueLocalIncidence, glueLocalBoundary])
    (approxBisim_symm h)

theorem glueLocalIncidence_e_not_bisim_out :
    ¬ approxBisim glueLocalIncidence GlueLocalId.e GlueLocalId.out := by
  apply not_approxBisim_of_boundary_mismatch glueLocalIncidence GlueLocalId.e GlueLocalId.out
    { i := GlueLocalId.x, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
    (by simp [glueLocalIncidence, glueLocalBoundary])
  intro e' he'
  simp [glueLocalIncidence, glueLocalBoundary] at he'
  subst he'
  simp [boundaryCompatible]

theorem glueLocalIncidence_x_not_bisim_out :
    ¬ approxBisim glueLocalIncidence GlueLocalId.x GlueLocalId.out := by
  apply not_approxBisim_of_boundary_mismatch glueLocalIncidence GlueLocalId.x GlueLocalId.out
    { i := GlueLocalId.e, role := GlueLocalRole.link, sign := Sign.neg, mult := 1 }
    (by simp [glueLocalIncidence, glueLocalBoundary])
  intro e' he'
  simp [glueLocalIncidence, glueLocalBoundary] at he'
  subst he'
  simp [boundaryCompatible]

inductive GlueLocalShape where | pairShape | coreShape | outShape
deriving DecidableEq, Repr

def glueLocalToShape : GlueLocalId → GlueLocalShape
  | .e    => .pairShape
  | .x    => .pairShape
  | .core => .coreShape
  | .out  => .outShape

theorem glueLocalToShape_reflects (a b : GlueLocalId) (h : glueLocalToShape a = glueLocalToShape b) :
    approxBisim glueLocalIncidence a b := by
  cases a <;> cases b <;> simp [glueLocalToShape] at h <;>
    exact ⟨glueLocalRel, glueLocalRel_isBisimulation, by decide⟩

theorem glueLocalToShape_distinguishes (a b : GlueLocalId) (h : approxBisim glueLocalIncidence a b) :
    glueLocalToShape a = glueLocalToShape b := by
  cases a <;> cases b <;> simp only [glueLocalToShape] <;>
    first
    | rfl
    | exact absurd h glueLocalIncidence_e_not_bisim_core
    | exact absurd h glueLocalIncidence_x_not_bisim_core
    | exact absurd h glueLocalIncidence_e_not_bisim_out
    | exact absurd h glueLocalIncidence_x_not_bisim_out
    | exact absurd h glueLocalIncidence_core_not_bisim_out
    | exact absurd (approxBisim_symm h) glueLocalIncidence_e_not_bisim_core
    | exact absurd (approxBisim_symm h) glueLocalIncidence_x_not_bisim_core
    | exact absurd (approxBisim_symm h) glueLocalIncidence_e_not_bisim_out
    | exact absurd (approxBisim_symm h) glueLocalIncidence_x_not_bisim_out
    | exact absurd (approxBisim_symm h) glueLocalIncidence_core_not_bisim_out

theorem glueLocalToShape_iff_approxBisim (a b : GlueLocalId) :
    glueLocalToShape a = glueLocalToShape b ↔ approxBisim glueLocalIncidence a b :=
  ⟨glueLocalToShape_reflects a b, glueLocalToShape_distinguishes a b⟩

def glueLocalBisimulationQuotientClassification :
    BisimulationQuotientClassification (Q := GlueLocalShape) glueLocalIncidence :=
  bisimulationQuotientClassificationOfKernel glueLocalIncidence glueLocalToShape
    glueLocalToShape_iff_approxBisim
    (fun shape => by
      cases shape with
      | pairShape => exact ⟨GlueLocalId.e, rfl⟩
      | coreShape => exact ⟨GlueLocalId.core, rfl⟩
      | outShape => exact ⟨GlueLocalId.out, rfl⟩)

/- `inc.unit` (= `core`)'s `≈`-class here is a genuine SINGLETON -- so
   cycle 53's own criterion (`glueInvariant_fails_of_unit_class_witness`,
   which needs some `x ≈ inc.unit` with `x` behaving differently from
   `inc.unit`) is PROVABLY inapplicable to this instance: there is no
   witness for it to use. Confirms `glueLocalIncidence` genuinely
   exercises NEW content, not a relabeled instance of cycle 53's own
   already-covered ground -- the failure below can ONLY be explained via
   the local mechanism anchored at `e`. -/
theorem glueLocalIncidence_unit_class_singleton {y : GlueLocalId}
    (hy : approxBisim glueLocalIncidence y GlueLocalId.core) : y = GlueLocalId.core := by
  have hshape := (glueLocalToShape_iff_approxBisim y GlueLocalId.core).mpr hy
  cases y <;> first | rfl | simp [glueLocalToShape] at hshape

/- The general theorem: `unit`'s role in cycle 53's mechanism is
   replaceable by ANY element `e`, provided the one-point behavioral fact
   `unit_left` supplied at `inc.unit` is instead supplied directly at
   `e`/`j` -- no reference to `inc.unit`, `unit_left`, or any global
   cardinality condition on the classification's target at all. This is
   the class-LOCAL refinement of cycle 53's mechanism, in exact parallel
   to how cycle 56 refined cycle 54's `Subsingleton` theorem, but along a
   different axis: cycle 56 removed a hypothesis about how many classes
   the WHOLE quotient has; this removes a hypothesis about WHICH element
   supplies the identity law, weakening `unit_left`'s `∀ j` universal
   guarantee (available only at `inc.unit`, `unit_unique_full_left_
   identity` below) down to the single instantiated fact cycle 53's own
   proof actually used. -/
theorem glueInvariant_fails_of_class_witness
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {e x : I} (xBisimE : approxBisim inc x e)
    {j : I} (jOutsideEClass :
      classification.classify j ≠ classification.classify e)
    (eIdentityAt : inc.glue e j = some j)
    (xAbsorbs : inc.glue x j = some x) :
    ¬ classification.GlueInvariant := by
  intro invariant
  have equalMappedGlue := invariant xBisimE (approxBisim_refl inc j)
  have he : classification.mappedSourceGlue e j =
      some (classification.classify j) := by
    simp [BisimulationQuotientClassification.mappedSourceGlue, eIdentityAt]
  have hx : classification.mappedSourceGlue x j =
      some (classification.classify x) := by
    simp [BisimulationQuotientClassification.mappedSourceGlue, xAbsorbs]
  rw [hx, he] at equalMappedGlue
  have classifyEq : classification.classify j = classification.classify e :=
    ((classification.respects xBisimE).symm.trans
      (Option.some.inj equalMappedGlue)).symm
  exact jOutsideEClass classifyEq

theorem glueRealization_fails_of_class_witness
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {e x : I} (xBisimE : approxBisim inc x e)
    {j : I} (jOutsideEClass :
      classification.classify j ≠ classification.classify e)
    (eIdentityAt : inc.glue e j = some j)
    (xAbsorbs : inc.glue x j = some x) :
    ¬ classification.GlueRealization :=
  fun realization =>
    glueInvariant_fails_of_class_witness classification xBisimE jOutsideEClass
      eIdentityAt xAbsorbs
      ((classification.glueRealization_iff_invariant).mp realization)

/- Cycle 53's own theorem, re-derived here as the special case `e :=
   inc.unit`, confirming the generalization is genuine (not merely
   analogous in spirit) -- exactly mirroring cycle 56's `canonicalBoundary_
   self_loop_of_subsingleton_via_local`. -/
theorem glueInvariant_fails_of_unit_class_witness_via_local
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {x : I} (xBisimUnit : approxBisim inc x inc.unit)
    {j : I} (jOutsideUnitClass :
      classification.classify j ≠ classification.classify inc.unit)
    (xAbsorbs : inc.glue x j = some x) :
    ¬ classification.GlueInvariant :=
  glueInvariant_fails_of_class_witness classification xBisimUnit jOutsideUnitClass
    (inc.unit_left j) xAbsorbs

/- The concrete witness, exercising `glueInvariant_fails_of_class_witness`
   at `e := GlueLocalId.e ≠ inc.unit` -- the first `GlueInvariant` failure
   in this project's history NOT explainable by cycle 53's own criterion
   (`glueLocalIncidence_unit_class_singleton` above rules that out
   directly). -/
theorem glueLocalIncidence_not_glueInvariant :
    ¬ glueLocalBisimulationQuotientClassification.GlueInvariant :=
  glueInvariant_fails_of_class_witness glueLocalBisimulationQuotientClassification
    (e := GlueLocalId.e) (x := GlueLocalId.x)
    (xBisimE := (glueLocalToShape_iff_approxBisim GlueLocalId.x GlueLocalId.e).mp rfl)
    (j := GlueLocalId.out)
    (jOutsideEClass := by decide)
    (eIdentityAt := by decide)
    (xAbsorbs := by decide)

theorem glueLocalIncidence_not_glueRealization :
    ¬ glueLocalBisimulationQuotientClassification.GlueRealization :=
  glueRealization_fails_of_class_witness glueLocalBisimulationQuotientClassification
    (e := GlueLocalId.e) (x := GlueLocalId.x)
    (xBisimE := (glueLocalToShape_iff_approxBisim GlueLocalId.x GlueLocalId.e).mp rfl)
    (j := GlueLocalId.out)
    (jOutsideEClass := by decide)
    (eIdentityAt := by decide)
    (xAbsorbs := by decide)

/- The precise limit on the generalization, checked rather than assumed
   per this cycle's own brief: the FULL `∀ j` form of the identity
   property (`unit_left`'s exact shape) is unique to `inc.unit` in EVERY
   `Incidence`, not just in the three known glue-formula instances --
   proved directly from `unit_right` alone, no reference to `glue`'s
   shape in any specific instance. This is why the generalization above
   only succeeds at the strictly weaker ONE-POINT level cycle 53's own
   proof already used (`eIdentityAt` fixed at one `j`), not by exhibiting
   a second element with the full law: no such second element can ever
   exist. -/
theorem unit_unique_full_left_identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    {e : I} (hident : ∀ j, inc.glue e j = some j) : e = inc.unit := by
  have h1 : inc.glue e inc.unit = some inc.unit := hident inc.unit
  have h2 : inc.glue e inc.unit = some e := inc.unit_right e
  exact (Option.some.inj (h1.symm.trans h2)).symm

/- Synthesis recorded here alongside the theorems, matching this file's
   convention (cycles 53/56/57): cycle 57's flagged caveat -- that
   `GlueInvariant`'s two-argument, congruence shape might block the same
   "global -> local" move cycle 56 made for `BoundaryInvariant`'s
   single-argument, shape-shaped obligation -- turns out not to be the
   operative obstruction at all. `GlueInvariant`'s NEGATION was already
   pointwise/existential from cycle 53's first statement of it (one
   witnessing pair, not "every class"), so there was never a
   `Subsingleton`-style cardinality hypothesis to relax in the first
   place; the two-argument shape is orthogonal to the axis this cycle
   actually generalizes along. The real global dependency cycle 53's
   proof had was on WHICH element could supply the needed identity fact
   -- `inc.unit` via its universally-quantified `unit_left` law -- and
   `unit_unique_full_left_identity` confirms that dependency is not a
   proof artifact but a real theorem (unit is the UNIQUE full-law
   holder, in every `Incidence`, via `unit_right` alone). The
   generalization this cycle proves succeeds precisely because cycle
   53's own proof never actually needed the full `∀ j` law -- only the
   one instantiated fact at the one `j` already fixed by `xAbsorbs` --
   so weakening the hypothesis to that one point (rather than trying to
   find a second element with the full law, which `unit_unique_full_
   left_identity` shows is impossible) is where the genuine slack was.
   `glueLocalIncidence` confirms this is not vacuous reshuffling: its
   `inc.unit`'s class is a proved singleton
   (`glueLocalIncidence_unit_class_singleton`), so cycle 53's own
   criterion cannot explain `glueLocalIncidence_not_glueInvariant` at
   all -- only the local criterion anchored at `e ≠ inc.unit` can. -/

/- Research cycle 59 (see RESEARCH_LOG.md): cycle 58's own queued option (a),
   the last cheap confirmatory check on the glue/boundary/guards/quotient-
   invariant thread (cycles 45-58) before treating it as closed -- does
   `GuardInvariant`'s failure mechanism (cycle 57's `mirrorDiagGuards_not_
   guardInvariant`) have ANY "which element supplies the behavior" dependency
   analogous to `GlueInvariant`'s `inc.unit`-anchored mechanism (cycle 53) and
   its class-local generalization (cycle 58), or is it -- as cycle 58's own
   synthesis speculated -- vacuous, because `guards.allow` has no law
   analogous to `unit_left`/`unit_right` binding it to a specific element?

   Checked directly, not assumed: read the base `Incidence` structure
   (`Axioms.lean` L17-58) field by field. `guards : Guards I`, and `Guards I`
   itself (`A9_A13.lean` L9-10) is a BARE one-field wrapper (`allow : I → I →
   Bool`) carrying ZERO structural laws of its own -- unlike `glue`, which is
   directly pinned down by two unconditional, unit-anchored laws (`unit_left`/
   `unit_right : ∀ i, glue unit i = some i` / `glue i unit = some i`). The
   ONLY place `guards.allow` appears in any law of the full `Incidence`
   structure at all is `type_preserve : guards.allow i j → glue i j = some k →
   typeFunc k = typeFunc i` (`Axioms.lean` L58) -- but this is a CONDITIONAL
   constraint relating three different fields at matching triples, not a
   value-forcing law like `unit_left` (which states, unconditionally, for
   EVERY `i`, exactly what `glue unit i` equals). It never singles out any
   distinguished element the way `unit_left`/`unit_right` single out `unit`,
   and it places no constraint whatsoever on `guards.allow` at any point
   where its own hypothesis is false. So `guards.allow` is free to be ANY
   `I → I → Bool` function subject only to this one global implication --
   confirming cycle 58's speculation for a PRECISE, STRUCTURAL reason (no
   analogous law exists in the structure), not merely because no
   counterexample had been checked yet.

   Went one level deeper, in this thread's established style of preferring a
   general theorem over an instance-by-instance audit: `IsBisimulation`/
   `boundaryMatched`/`boundaryCompatible` (`IncidenceTheory.lean` L36-66) are
   defined using ONLY `inc.typeFunc` and `inc.boundary` -- `guards` (and
   `glue`/`unit`) never appear in their definitions at all. This is stronger
   than "guards has no `unit_left`-analog law": `≈` itself is STRUCTURALLY
   BLIND to `guards` (and to `glue`/`unit`) in EVERY `Incidence`, not merely
   in the instances this project happens to have built. -/

theorem isBisimulation_eq_of_typeFunc_boundary_eq
    {I R T : Type u} [DecidableEq I] (inc1 inc2 : Incidence I R T)
    (htype : inc1.typeFunc = inc2.typeFunc) (hbound : inc1.boundary = inc2.boundary)
    (rel : I → I → Prop) :
    IsBisimulation inc1 rel ↔ IsBisimulation inc2 rel := by
  unfold IsBisimulation boundaryMatched boundaryCompatible
  rw [htype, hbound]

theorem approxBisim_eq_of_typeFunc_boundary_eq
    {I R T : Type u} [DecidableEq I] (inc1 inc2 : Incidence I R T)
    (htype : inc1.typeFunc = inc2.typeFunc) (hbound : inc1.boundary = inc2.boundary)
    (x y : I) :
    approxBisim inc1 x y ↔ approxBisim inc2 x y := by
  unfold approxBisim
  constructor
  · rintro ⟨rel, hbisim, hxy⟩
    exact ⟨rel,
      (isBisimulation_eq_of_typeFunc_boundary_eq inc1 inc2 htype hbound rel).mp hbisim, hxy⟩
  · rintro ⟨rel, hbisim, hxy⟩
    exact ⟨rel,
      (isBisimulation_eq_of_typeFunc_boundary_eq inc1 inc2 htype hbound rel).mpr hbisim, hxy⟩

/- The direct consequence for `GuardInvariant`: unlike `glueInvariant_fails_of_
   class_witness` (cycle 58), which needed a genuine one-point BEHAVIORAL fact
   about `glue` (`eIdentityAt`/`xAbsorbs`), a `GuardInvariant` failure needs
   NOTHING beyond unfolding its own definition -- any bisimilar pair plus any
   guards disagreement at a shared third point. There is no analogous "which
   element can supply this fact" question to even ask, because
   `GuardInvariant`'s hypotheses are not routed through any law of `Incidence`
   at all -- this lemma's proof is a one-liner, in sharp contrast to
   `glueInvariant_fails_of_class_witness`'s multi-step `mappedSourceGlue`
   argument. -/
theorem guardInvariant_fails_of_pair_witness
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {p p' y : I} (hpp' : approxBisim inc p p')
    (hdiff : inc.guards.allow p y ≠ inc.guards.allow p' y) :
    ¬ classification.GuardInvariant :=
  fun invariant => hdiff (invariant hpp' (approxBisim_refl inc y))

/- Concrete confirmation, reusing cycle 58's OWN unit-class-singleton instance
   `glueLocalIncidence` rather than building a fresh carrier from scratch --
   this both economizes the construction and gives the strongest possible
   witness: cycle 58 already proved `glueLocalIncidence`'s `unit` (= `core`)
   class is a genuine singleton (`glueLocalIncidence_unit_class_singleton`),
   so ANY `GuardInvariant` failure exhibited on this exact carrier is, by
   construction, provably unrelated to `unit`. Everything except `guards` is
   copied verbatim from `glueLocalIncidence`; `type_preserve := fun _ _ =>
   rfl` carries over unchanged because `typeFunc` is the constant
   `GraphType.unit` there, so the hypothesis is never actually used --
   exactly cycle 57's `mirrorDiagGuards` recipe, applied here to a different
   existing instance instead of `mirrorIncidence`. -/
def glueLocalDiagGuards : Incidence GlueLocalId GlueLocalRole GraphType where
  boundary := glueLocalBoundary
  typeFunc := fun _ => GraphType.unit
  glue := fun i k =>
    if i = GlueLocalId.e ∧ k = GlueLocalId.out then some k
    else if i = GlueLocalId.core then some k
    else some i
  unit := GlueLocalId.core
  guards := Guards.diag GlueLocalId
  type_consistent := fun _ _ _ => rfl
  sign_rules := fun _ e _ => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [glueLocalBoundary] at he <;> subst he <;> simp_all
  unit_left := by intro i; simp
  unit_right := by
    intro i
    cases i <;> simp
  type_preserve := fun _ _ => rfl

theorem glueLocalDiagGuards_typeFunc_eq :
    glueLocalDiagGuards.typeFunc = glueLocalIncidence.typeFunc := rfl

theorem glueLocalDiagGuards_boundary_eq :
    glueLocalDiagGuards.boundary = glueLocalIncidence.boundary := rfl

/- The guards swap is completely invisible to `≈` on this carrier, an instance
   of the general fact above rather than a fresh bisimulation argument. -/
theorem glueLocalDiagGuards_approxBisim_iff (a b : GlueLocalId) :
    approxBisim glueLocalDiagGuards a b ↔ approxBisim glueLocalIncidence a b :=
  approxBisim_eq_of_typeFunc_boundary_eq glueLocalDiagGuards glueLocalIncidence
    glueLocalDiagGuards_typeFunc_eq glueLocalDiagGuards_boundary_eq a b

/- `unit`'s (= `core`'s) `≈`-class is STILL a genuine singleton on this
   carrier -- transferred directly from cycle 58's `glueLocalIncidence_unit_
   class_singleton` via the iff above, with no new bisimulation argument
   needed, confirming the guards swap really is invisible to `≈` here, not
   merely in the abstract. -/
theorem glueLocalDiagGuards_unit_class_singleton {y : GlueLocalId}
    (hy : approxBisim glueLocalDiagGuards y GlueLocalId.core) : y = GlueLocalId.core :=
  glueLocalIncidence_unit_class_singleton
    ((glueLocalDiagGuards_approxBisim_iff y GlueLocalId.core).mp hy)

def glueLocalDiagGuardsBisimulationQuotientClassification :
    BisimulationQuotientClassification (Q := GlueLocalShape) glueLocalDiagGuards :=
  bisimulationQuotientClassificationOfKernel glueLocalDiagGuards glueLocalToShape
    (fun a b => by
      rw [glueLocalDiagGuards_approxBisim_iff]
      exact glueLocalToShape_iff_approxBisim a b)
    (fun shape => by
      cases shape with
      | pairShape => exact ⟨GlueLocalId.e, rfl⟩
      | coreShape => exact ⟨GlueLocalId.core, rfl⟩
      | outShape => exact ⟨GlueLocalId.out, rfl⟩)

theorem approxBisim_glueLocalDiagGuards_e_x :
    approxBisim glueLocalDiagGuards GlueLocalId.e GlueLocalId.x :=
  (glueLocalDiagGuards_approxBisim_iff GlueLocalId.e GlueLocalId.x).mpr
    ((glueLocalToShape_iff_approxBisim GlueLocalId.e GlueLocalId.x).mp rfl)

/- The failure itself: `e ≈ x` (just above, on a carrier where `unit`'s class
   is PROVABLY a singleton), yet `allow e e ≠ allow x e` -- `Guards.diag`'s
   argument-dependence bites at `e`/`x`, exactly as it bit at `m0`/`m1` in
   cycle 57's `mirrorDiagGuards`, but this time anchored at a point cycle
   53/58's own unit-anchored criterion cannot reach. This is the closing
   confirmation: `GuardInvariant`'s failure needs no distinguished element at
   all, not even the weakened one-point kind `GlueInvariant`'s local
   refinement (cycle 58) still required. -/
theorem glueLocalDiagGuards_not_guardInvariant :
    ¬ glueLocalDiagGuardsBisimulationQuotientClassification.GuardInvariant :=
  guardInvariant_fails_of_pair_witness glueLocalDiagGuardsBisimulationQuotientClassification
    (y := GlueLocalId.e) approxBisim_glueLocalDiagGuards_e_x (by decide)

/- Synthesis recorded here alongside the theorems, matching this file's
   convention (cycles 53/56/57/58): the question cycle 58 flagged is now
   closed definitively rather than left as speculation. `GuardInvariant`'s
   failure mechanism is STRICTLY simpler than `GlueInvariant`'s, along two
   independent axes proven above rather than merely observed in one instance.
   (1) Source-level: `Guards I` has no law at all, let alone one anchored at a
   distinguished element -- `type_preserve` is the only law mentioning
   `guards.allow`, and it is a conditional cross-field constraint, not a
   value-forcing law in `unit_left`/`unit_right`'s shape. (2) Semantic-level,
   strictly stronger: `≈` (`IsBisimulation`/`approxBisim`) is defined purely
   from `typeFunc`/`boundary` and is PROVABLY INSENSITIVE to `guards` (and to
   `glue`/`unit`) in every `Incidence` (`approxBisim_eq_of_typeFunc_boundary_
   eq`), so no future instance -- however its `glue`/`unit` are shaped -- could
   ever manufacture a hidden guards/unit coupling through `≈` either. The
   concrete witness (`glueLocalDiagGuards`, reusing cycle 58's own `unit`-
   class-singleton carrier `glueLocalIncidence` with only `guards` swapped)
   confirms this is not vacuous reshuffling: a genuine `GuardInvariant`
   failure exists at `e`/`x`, on a carrier where `unit`'s class is proved to
   contain nothing else, so cycle 53/58's own unit-anchored/class-local
   criteria are structurally unable to explain it -- only the fact that
   `guards` carries no law at all can. With this check complete, all threads
   cycle 56/57/58 queued from the original cycle 53 three-item list, plus
   cycle 58's own queued option (a), are now closed; see RESEARCH_LOG.md
   cycle 59 for the resulting scouting recommendation for cycle 60. -/

end IncidenceCore
