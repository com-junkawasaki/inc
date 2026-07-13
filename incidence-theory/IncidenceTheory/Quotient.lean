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

end IncidenceCore
