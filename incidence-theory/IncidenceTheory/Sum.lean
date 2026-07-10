import IncidenceTheory.Peano
import IncidenceTheory.Cycle

/- Merkle-ID: implementation.graph_model.sum
   story.jsonnet → implementation.nodes.sum
   Research cycle 33 (see RESEARCH_LOG.md): the second generic
   constructor internal to Inc, after `incidenceProd` (cycle 31) --
   `incidenceSum`, the disjoint-union analogue, `I1 ⊕ I2`. Chosen over
   the T5-translation option queued alongside it because building this
   surfaced a genuine design question the product never had to answer:
   a product's two-sided identity is simply `(inc1.unit, inc2.unit)`
   (every element of `I1 × I2` genuinely has both components), but a
   disjoint union has no element belonging to *both* sides, so there is
   no way to define `glue` purely componentwise and still satisfy
   `unit_left`/`unit_right` (gluing the unit against an element from the
   *other* side would need to produce *that* element, which componentwise
   gluing can't do at all). Resolved the same way essentially every
   prior hand-built instance in this project resolved a similar
   tension: a single designated unit that "absorbs" trivially
   (`glue x y := if y = unit then some x else if x = unit then some y
   else <componentwise, same side only>`), falling back to `none` for
   any genuine cross-side pair. Unlike the product, this also forces a
   *constant* `typeFunc` (`GraphType.unit`, the same trivial type every
   pre-cycle-31 instance in this project already used) -- a genuinely
   non-trivial `T1 ⊕ T2` typeFunc would make `type_preserve` fail for
   the unit-absorption case (gluing the unit against `y` produces `y`,
   whose type need not match the unit's).

   The main finding: **faithfulness does NOT transport through
   `incidenceSum` the way it did through `incidenceProd` (cycle 32).**
   Any two leaves (empty-boundary elements), from *either* side,
   necessarily become bisimilar in the sum -- `boundaryMatched` is
   vacuously satisfied for two elements with no boundary entries at
   all, regardless of which side they came from, the exact same
   mechanism as the "flat leaves collapse" pattern (cycles 2/12/13/18/26)
   but now demonstrated as a structural consequence of the *sum
   construction itself*, not of any one instance's design. Concretely:
   `Sum.inl 0 ≈ Sum.inr 0` in `incidenceSum natIncidence natIncidence`,
   even though `natIncidence` is individually fully faithful and
   `Sum.inl 0 ≠ Sum.inr 0` as elements of `Nat ⊕ Nat`. -/

namespace IncidenceCore

def sumInlEndpoint {I1 R1 I2 R2 : Type u} (e : Endpoint I1 R1) :
    Endpoint (I1 ⊕ I2) (R1 ⊕ R2) :=
  { i := Sum.inl e.i, role := Sum.inl e.role, sign := e.sign, mult := e.mult,
    mult_pos := e.mult_pos }

def sumInrEndpoint {I1 R1 I2 R2 : Type u} (e : Endpoint I2 R2) :
    Endpoint (I1 ⊕ I2) (R1 ⊕ R2) :=
  { i := Sum.inr e.i, role := Sum.inr e.role, sign := e.sign, mult := e.mult,
    mult_pos := e.mult_pos }

def sumBoundary {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
  (I1 ⊕ I2) → Boundary (I1 ⊕ I2) (R1 ⊕ R2)
  | Sum.inl i1 =>
    (inc1.boundary i1).map sumInlEndpoint
  | Sum.inr i2 =>
    (inc2.boundary i2).map sumInrEndpoint

/- Unit-absorbing, then componentwise same-side, else `none` -- the
   only shape that can satisfy `unit_left`/`unit_right` given a
   disjoint union has no element in both `I1` and `I2`. -/
def sumGlue {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (unit : I1 ⊕ I2) :
  (I1 ⊕ I2) → (I1 ⊕ I2) → Option (I1 ⊕ I2)
  | x, y =>
    if y = unit then some x
    else if x = unit then some y
    else match x, y with
      | Sum.inl x1, Sum.inl y1 => (inc1.glue x1 y1).map Sum.inl
      | Sum.inr x2, Sum.inr y2 => (inc2.glue x2 y2).map Sum.inr
      | _, _ => none

def incidenceSum {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
  Incidence (I1 ⊕ I2) (R1 ⊕ R2) GraphType where
  boundary := sumBoundary inc1 inc2
  typeFunc := fun _ => GraphType.unit
  glue := sumGlue inc1 inc2 (Sum.inl inc1.unit)
  unit := Sum.inl inc1.unit
  guards := Guards.permissive (I1 ⊕ I2)
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e he
    cases i with
    | inl i1 =>
      simp only [sumBoundary, List.mem_map] at he
      obtain ⟨e1, he1, heq⟩ := he
      subst heq
      exact inc1.sign_rules i1 e1 he1
    | inr i2 =>
      simp only [sumBoundary, List.mem_map] at he
      obtain ⟨e2, he2, heq⟩ := he
      subst heq
      exact inc2.sign_rules i2 e2 he2
  multiplicities := by
    intro i e he
    cases i with
    | inl i1 =>
      simp only [sumBoundary, List.mem_map] at he
      obtain ⟨e1, he1, heq⟩ := he
      subst heq
      exact inc1.multiplicities i1 e1 he1
    | inr i2 =>
      simp only [sumBoundary, List.mem_map] at he
      obtain ⟨e2, he2, heq⟩ := he
      subst heq
      exact inc2.multiplicities i2 e2 he2
  well_founded := by
    intro i hex
    obtain ⟨e, he, hei⟩ := hex
    cases i with
    | inl i1 =>
      simp only [sumBoundary, List.mem_map] at he
      obtain ⟨e1, he1, heq⟩ := he
      subst heq
      simp [sumInlEndpoint] at hei
      exact inc1.well_founded i1 ⟨e1, he1, hei⟩
    | inr i2 =>
      simp only [sumBoundary, List.mem_map] at he
      obtain ⟨e2, he2, heq⟩ := he
      subst heq
      simp [sumInrEndpoint] at hei
      exact inc2.well_founded i2 ⟨e2, he2, hei⟩
  unit_left := by
    intro i
    simp only [sumGlue]
    by_cases h : i = Sum.inl inc1.unit
    · simp [h]
    · simp [h]
  unit_right := by
    intro i
    simp only [sumGlue]
    simp
  type_preserve := fun _ _ => rfl

/- Is `x` a leaf (empty boundary), regardless of which side it's on? -/
def sumIsLeaf {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) : (I1 ⊕ I2) → Prop
  | Sum.inl a => inc1.boundary a = []
  | Sum.inr b => inc2.boundary b = []

/- The headline finding: any two leaves are `≈`-related in the sum, no
   matter which side they come from -- `boundaryMatched` is vacuously
   satisfied when both elements have empty boundary, so the standard
   "everything related to everything" relation (cycles 2/12/13/18/26,
   here restricted to leaves) is trivially a bisimulation regardless of
   the `Sum.inl`/`Sum.inr` tag. -/
theorem incidenceSum_leaves_collapse
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {x y : I1 ⊕ I2} (hx : sumIsLeaf inc1 inc2 x) (hy : sumIsLeaf inc1 inc2 y) :
  approxBisim (incidenceSum inc1 inc2) x y := by
  refine ⟨fun a b => sumIsLeaf inc1 inc2 a ∧ sumIsLeaf inc1 inc2 b, ?_, hx, hy⟩
  intro a b ⟨ha, hb⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro e he
    exfalso
    cases a with
    | inl a1 =>
      simp only [sumIsLeaf] at ha
      simp only [incidenceSum, sumBoundary, ha, List.map_nil] at he
      simp at he
    | inr a2 =>
      simp only [sumIsLeaf] at ha
      simp only [incidenceSum, sumBoundary, ha, List.map_nil] at he
      simp at he
  · intro e he
    exfalso
    cases b with
    | inl b1 =>
      simp only [sumIsLeaf] at hb
      simp only [incidenceSum, sumBoundary, hb, List.map_nil] at he
      simp at he
    | inr b2 =>
      simp only [sumIsLeaf] at hb
      simp only [incidenceSum, sumBoundary, hb, List.map_nil] at he
      simp at he

/- Concrete confirmation, not just abstract: even though `natIncidence`
   is individually FULLY faithful (`≈ ↔ =`, cycle 4), the sum of
   `natIncidence` with itself is NOT -- `Sum.inl 0` and `Sum.inr 0` are
   two genuinely distinct elements of `Nat ⊕ Nat` (different
   constructors) that nonetheless become `≈`-related, purely because
   both happen to be `natIncidence`'s unique leaf. -/
theorem incidenceSum_leaves_cross_natIncidence :
  approxBisim (incidenceSum natIncidence natIncidence) (Sum.inl 0) (Sum.inr 0) :=
  incidenceSum_leaves_collapse natIncidence natIncidence rfl rfl

theorem incidenceSum_inl0_ne_inr0 :
  (Sum.inl (0 : Nat) : Nat ⊕ Nat) ≠ Sum.inr (0 : Nat) := by simp

/- Research cycle 35 (see RESEARCH_LOG.md): does `incidenceSum` have a
   *conditional* faithfulness result, given cycle 33 showed it fails in
   general? The cross-side collapse mechanism (cycle 33) needs *both*
   sides to supply a leaf for the SAME pair -- so if just one side has
   *no* leaves at all, no cross-side collapse can ever happen, for
   *any* pair. `cycleIncidenceFixed` (cycle 27) is the perfect witness:
   it's fully faithful AND has zero leaves whatsoever (every element
   has exactly one boundary entry, cyclically) -- the first instance in
   this project with that property. -/

/- If `inc1`'s element has *any* boundary entry, it can never be
   cross-side bisimilar to anything on the other side -- the same
   argument cycle 33's collapse fact needed the ABSENCE of, now used in
   the presence of a boundary entry via `not_approxBisim_of_boundary_mismatch`
   (cycle 21) directly. -/
theorem incidenceSum_cross_not_bisim_of_not_leaf_left
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {a : I1} {b : I2} (ha : inc1.boundary a ≠ []) :
  ¬ approxBisim (incidenceSum inc1 inc2) (Sum.inl a) (Sum.inr b) := by
  obtain ⟨e1, he1⟩ := List.exists_mem_of_ne_nil _ ha
  apply not_approxBisim_of_boundary_mismatch (incidenceSum inc1 inc2) (Sum.inl a) (Sum.inr b)
    (sumInlEndpoint e1)
  · simp only [incidenceSum, sumBoundary, List.mem_map]
    exact ⟨e1, he1, rfl⟩
  · intro e' he'
    simp only [incidenceSum, sumBoundary, List.mem_map] at he'
    obtain ⟨e2, he2, heq⟩ := he'
    subst heq
    simp [sumInlEndpoint, sumInrEndpoint, boundaryCompatible]

/- Symmetric: if `inc2`'s element has any boundary entry, same
   conclusion, via `approxBisim_symm` applied to the mirror-image
   argument. -/
theorem incidenceSum_cross_not_bisim_of_not_leaf_right
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {a : I1} {b : I2} (hb : inc2.boundary b ≠ []) :
  ¬ approxBisim (incidenceSum inc1 inc2) (Sum.inl a) (Sum.inr b) := by
  intro h
  have h' : approxBisim (incidenceSum inc1 inc2) (Sum.inr b) (Sum.inl a) := approxBisim_symm h
  obtain ⟨e2, he2⟩ := List.exists_mem_of_ne_nil _ hb
  exact not_approxBisim_of_boundary_mismatch (incidenceSum inc1 inc2) (Sum.inr b) (Sum.inl a)
    (sumInrEndpoint e2)
    (by simp only [incidenceSum, sumBoundary, List.mem_map]; exact ⟨e2, he2, rfl⟩)
    (by
      intro e' he'
      simp only [incidenceSum, sumBoundary, List.mem_map] at he'
      obtain ⟨e1, he1, heq⟩ := he'
      subst heq
      simp [sumInlEndpoint, sumInrEndpoint, boundaryCompatible])
    h'

/- Same-side `≈` in the sum reduces to `≈` in `inc1` alone -- the
   `incidenceProd_project`-style projection (cycle 32), simpler here
   since there's nothing to combine, only to isolate. One genuine
   subtlety `incidenceProd_project` didn't have: `incidenceSum`'s
   `typeFunc` is *forced* constant (the design tension noted above), so
   `IsBisimulation`'s type-preservation obligation can't be derived for
   free the way it could for the product's genuine `T1×T2` typing --
   resolved by baking `inc1.typeFunc x = inc1.typeFunc y` directly into
   the projected relation, then propagating it along boundary edges via
   `inc1`'s own `type_consistent` obligation (already guaranteed by the
   `Incidence` structure, not an extra assumption). -/
theorem incidenceSum_project_left
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {a b : I1} (h : approxBisim (incidenceSum inc1 inc2) (Sum.inl a) (Sum.inl b))
  (htype : inc1.typeFunc a = inc1.typeFunc b) :
  approxBisim inc1 a b := by
  obtain ⟨rel, hbisim, hab⟩ := h
  refine ⟨fun x y => rel (Sum.inl x) (Sum.inl y) ∧ inc1.typeFunc x = inc1.typeFunc y,
    ?_, hab, htype⟩
  intro x y ⟨hr, htype'⟩
  obtain ⟨_, hmatch⟩ := hbisim (Sum.inl x) (Sum.inl y) hr
  refine ⟨htype', ?_, ?_⟩
  · intro e he
    have heS : sumInlEndpoint e ∈ (incidenceSum inc1 inc2).boundary (Sum.inl x) := by
      simp only [incidenceSum, sumBoundary, List.mem_map]
      exact ⟨e, he, rfl⟩
    obtain ⟨e', he', hcompat, hrel'⟩ := hmatch.left _ heS
    simp only [incidenceSum, sumBoundary, List.mem_map] at he'
    obtain ⟨e1', he1', heq⟩ := he'
    subst heq
    refine ⟨e1', he1', ⟨(Sum.inl.injEq _ _).mp hcompat.1, hcompat.2⟩, hrel', ?_⟩
    rw [inc1.type_consistent x e he, inc1.type_consistent y e1' he1', htype']
  · intro e' he'
    have heS : sumInlEndpoint e' ∈ (incidenceSum inc1 inc2).boundary (Sum.inl y) := by
      simp only [incidenceSum, sumBoundary, List.mem_map]
      exact ⟨e', he', rfl⟩
    obtain ⟨e, he, hcompat, hrel'⟩ := hmatch.right _ heS
    simp only [incidenceSum, sumBoundary, List.mem_map] at he
    obtain ⟨e1, he1, heq⟩ := he
    subst heq
    refine ⟨e1, he1, ⟨(Sum.inl.injEq _ _).mp hcompat.1, hcompat.2⟩, hrel', ?_⟩
    rw [inc1.type_consistent x e1 he1, inc1.type_consistent y e' he', htype']

theorem incidenceSum_project_right
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {a b : I2} (h : approxBisim (incidenceSum inc1 inc2) (Sum.inr a) (Sum.inr b))
  (htype : inc2.typeFunc a = inc2.typeFunc b) :
  approxBisim inc2 a b := by
  obtain ⟨rel, hbisim, hab⟩ := h
  refine ⟨fun x y => rel (Sum.inr x) (Sum.inr y) ∧ inc2.typeFunc x = inc2.typeFunc y,
    ?_, hab, htype⟩
  intro x y ⟨hr, htype'⟩
  obtain ⟨_, hmatch⟩ := hbisim (Sum.inr x) (Sum.inr y) hr
  refine ⟨htype', ?_, ?_⟩
  · intro e he
    have heS : sumInrEndpoint e ∈ (incidenceSum inc1 inc2).boundary (Sum.inr x) := by
      simp only [incidenceSum, sumBoundary, List.mem_map]
      exact ⟨e, he, rfl⟩
    obtain ⟨e', he', hcompat, hrel'⟩ := hmatch.left _ heS
    simp only [incidenceSum, sumBoundary, List.mem_map] at he'
    obtain ⟨e2', he2', heq⟩ := he'
    subst heq
    refine ⟨e2', he2', ⟨(Sum.inr.injEq _ _).mp hcompat.1, hcompat.2⟩, hrel', ?_⟩
    rw [inc2.type_consistent x e he, inc2.type_consistent y e2' he2', htype']
  · intro e' he'
    have heS : sumInrEndpoint e' ∈ (incidenceSum inc1 inc2).boundary (Sum.inr y) := by
      simp only [incidenceSum, sumBoundary, List.mem_map]
      exact ⟨e', he', rfl⟩
    obtain ⟨e, he, hcompat, hrel'⟩ := hmatch.right _ heS
    simp only [incidenceSum, sumBoundary, List.mem_map] at he
    obtain ⟨e2, he2, heq⟩ := he
    subst heq
    refine ⟨e2, he2, ⟨(Sum.inr.injEq _ _).mp hcompat.1, hcompat.2⟩, hrel', ?_⟩
    rw [inc2.type_consistent x e2 he2, inc2.type_consistent y e' he', htype']

/- The payoff: full faithfulness for the sum whenever both factors are
   individually faithful AND at least one side has no leaves at all.
   Restricted to `GraphType`-typed instances (every concrete instance in
   this project, matching the design tension noted above) so `htype`
   discharges trivially via `rfl` at the call sites. -/
theorem incidenceSum_faithful_of_faithful_no_shared_leaves
  {I1 R1 I2 R2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 GraphType) (inc2 : Incidence I2 R2 GraphType)
  (hf1 : ∀ x y : I1, approxBisim inc1 x y ↔ x = y)
  (hf2 : ∀ x y : I2, approxBisim inc2 x y ↔ x = y)
  (hleafless2 : ∀ b, inc2.boundary b ≠ []) :
  ∀ p q : I1 ⊕ I2, approxBisim (incidenceSum inc1 inc2) p q ↔ p = q := by
  intro p q
  cases p with
  | inl a =>
    cases q with
    | inl b =>
      constructor
      · intro h
        have := incidenceSum_project_left inc1 inc2 h rfl
        rw [hf1] at this
        rw [this]
      · rintro h
        cases h
        exact approxBisim_refl _ _
    | inr b =>
      constructor
      · intro h
        exact absurd h (incidenceSum_cross_not_bisim_of_not_leaf_right inc1 inc2 (hleafless2 b))
      · intro h
        cases h
  | inr a =>
    cases q with
    | inl b =>
      constructor
      · intro h
        exact absurd (approxBisim_symm h)
          (incidenceSum_cross_not_bisim_of_not_leaf_right inc1 inc2 (hleafless2 a))
      · intro h
        cases h
    | inr b =>
      constructor
      · intro h
        have := incidenceSum_project_right inc1 inc2 h rfl
        rw [hf2] at this
        rw [this]
      · rintro h
        cases h
        exact approxBisim_refl _ _

/- Concrete confirmation: `natIncidence ⊕ cycleIncidenceFixed` is fully
   faithful -- `cycleIncidenceFixed` (cycle 27) is the first instance in
   this project with NO leaves at all, so no cross-side collapse can
   happen despite `natIncidence` itself having exactly one leaf (`0`). -/
example : ∀ p q : Nat ⊕ CycleId,
    approxBisim (incidenceSum natIncidence cycleIncidenceFixed) p q ↔ p = q :=
  incidenceSum_faithful_of_faithful_no_shared_leaves natIncidence cycleIncidenceFixed
    natIncidence_approxBisim_iff cycleIncidenceFixed_approxBisim_iff
    (fun b => by cases b <;> simp [cycleIncidenceFixed, cycleBoundaryFixed])

/- Research cycle 36 (see RESEARCH_LOG.md), part 1 (audit): is
   `cycleIncidenceFixed` unique among every instance built so far in
   this project in being *both* fully faithful *and* leafless (the two
   properties `incidenceSum_faithful_of_faithful_no_shared_leaves`
   needs on at least one side)? Audited every named instance: `natIncidence`
   is faithful but has exactly one leaf (`0`); `cycleIncidence` (the
   pre-fix version, cycle 26) is leafless but NOT faithful (that's the
   whole point of cycle 26); `incidenceProd`/`incidenceSum` themselves
   are constructors, not base instances, and inherit leaves from
   whichever factors have them. `cycleIncidenceFixed` remains the only
   witness -- confirming this project has so far produced exactly one
   instance combining both properties, so the corollary below is not
   yet reusable with a *different* right-hand witness. -/

/- Research cycle 36, part 2: does `incidenceSum` have a generic
   translation-pairing result, mirroring cycle 34's
   `incidenceProd_translation_reflects`? Cycle 35 showed plain
   faithfulness-transport for the sum is conditional (needs a leafless
   side), so the naive guess is that any sum-translation result
   inherits the same side-condition. It does NOT: using `Sum.map t1 t2
   : I1 ⊕ I2 → S1 ⊕ S2` (landing in a genuinely disjoint target,
   unlike `Sum.elim t1 t2 : I1 ⊕ I2 → S` which shares a single target
   and would reproduce cycle 33's collapse) makes CROSS-side
   translate-equality `Sum.map t1 t2 p = Sum.map t1 t2 q` for `p, q` on
   opposite sides *type-theoretically impossible*
   (`Sum.inl _ ≠ Sum.inr _`, unconditionally) rather than merely false
   for a specific instance. So the only cases the theorem must handle
   are the two SAME-side cases, and those close via the unconditional
   "lift" lemmas below -- the converse direction of cycle 35's
   `incidenceSum_project_left`/`_right`, and, unlike those, needing NO
   extra `typeFunc`-equality hypothesis: `incidenceSum`'s `typeFunc` is
   *constant*, so in the LIFT direction (produce a `IsBisimulation` for
   the sum from one for a factor) type-preservation is trivially `rfl`
   with nothing to derive from `inc1`/`inc2`'s own typing -- the
   asymmetry is specific to which direction of implication is being
   proved, not an inconsistency with cycle 35's approach. Net result:
   **the sum's translation-reflects property is unconditional**, in
   direct contrast to cycle 35's conditional faithfulness-transport --
   the two properties (faithfulness-transport vs. translation-pairing)
   genuinely diverge in what side-conditions they need, even for the
   same constructor. -/
theorem incidenceSum_lift_left
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {a b : I1} (h : approxBisim inc1 a b) :
  approxBisim (incidenceSum inc1 inc2) (Sum.inl a) (Sum.inl b) := by
  obtain ⟨rel1, hbisim1, hab⟩ := h
  refine ⟨fun x y => match x, y with
    | Sum.inl x1, Sum.inl y1 => rel1 x1 y1
    | _, _ => False, ?_, hab⟩
  intro x y hr
  cases x with
  | inl x1 =>
    cases y with
    | inl y1 =>
      simp only at hr
      obtain ⟨htype, hmatch⟩ := hbisim1 x1 y1 hr
      refine ⟨by simp [incidenceSum], ?_, ?_⟩
      · intro e he
        simp only [incidenceSum, sumBoundary, List.mem_map] at he
        obtain ⟨e1, he1, heq⟩ := he
        subst heq
        obtain ⟨e1', he1', hcompat, hrel'⟩ := hmatch.left e1 he1
        exact ⟨sumInlEndpoint e1',
          by simp only [incidenceSum, sumBoundary, List.mem_map]; exact ⟨e1', he1', rfl⟩,
          ⟨congrArg Sum.inl hcompat.1, hcompat.2⟩, hrel'⟩
      · intro e' he'
        simp only [incidenceSum, sumBoundary, List.mem_map] at he'
        obtain ⟨e1', he1', heq⟩ := he'
        subst heq
        obtain ⟨e1, he1, hcompat, hrel'⟩ := hmatch.right e1' he1'
        exact ⟨sumInlEndpoint e1,
          by simp only [incidenceSum, sumBoundary, List.mem_map]; exact ⟨e1, he1, rfl⟩,
          ⟨congrArg Sum.inl hcompat.1, hcompat.2⟩, hrel'⟩
    | inr y2 => simp at hr
  | inr x2 => simp at hr

theorem incidenceSum_lift_right
  {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  {a b : I2} (h : approxBisim inc2 a b) :
  approxBisim (incidenceSum inc1 inc2) (Sum.inr a) (Sum.inr b) := by
  obtain ⟨rel2, hbisim2, hab⟩ := h
  refine ⟨fun x y => match x, y with
    | Sum.inr x2, Sum.inr y2 => rel2 x2 y2
    | _, _ => False, ?_, hab⟩
  intro x y hr
  cases x with
  | inr x2 =>
    cases y with
    | inr y2 =>
      simp only at hr
      obtain ⟨htype, hmatch⟩ := hbisim2 x2 y2 hr
      refine ⟨by simp [incidenceSum], ?_, ?_⟩
      · intro e he
        simp only [incidenceSum, sumBoundary, List.mem_map] at he
        obtain ⟨e2, he2, heq⟩ := he
        subst heq
        obtain ⟨e2', he2', hcompat, hrel'⟩ := hmatch.left e2 he2
        exact ⟨sumInrEndpoint e2',
          by simp only [incidenceSum, sumBoundary, List.mem_map]; exact ⟨e2', he2', rfl⟩,
          ⟨congrArg Sum.inr hcompat.1, hcompat.2⟩, hrel'⟩
      · intro e' he'
        simp only [incidenceSum, sumBoundary, List.mem_map] at he'
        obtain ⟨e2', he2', heq⟩ := he'
        subst heq
        obtain ⟨e2, he2, hcompat, hrel'⟩ := hmatch.right e2' he2'
        exact ⟨sumInrEndpoint e2,
          by simp only [incidenceSum, sumBoundary, List.mem_map]; exact ⟨e2, he2, rfl⟩,
          ⟨congrArg Sum.inr hcompat.1, hcompat.2⟩, hrel'⟩
    | inl y1 => simp at hr
  | inl x1 => simp at hr

/- The main pairing result, combining both lifts with the cross-side
   impossibility argument: `Sum.map`-translate-equality reflects to `≈`
   in the sum, UNCONDITIONALLY -- no faithfulness or leaflessness
   hypotheses on `inc1`/`inc2` at all, only that `t1`/`t2` individually
   reflect translate-equality to `≈` in their own factor (the same
   hypothesis shape as cycle 34's `incidenceProd_translation_reflects`
   and the original `natToFiniteSet_reflects_approxBisim`). -/
theorem incidenceSum_translation_reflects
  {I1 S1 I2 S2 : Type u} [DecidableEq I1] [DecidableEq I2] {R1 T1 R2 T2 : Type u}
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
  (t1 : I1 → S1) (t2 : I2 → S2)
  (ht1 : ∀ x y, t1 x = t1 y → approxBisim inc1 x y)
  (ht2 : ∀ x y, t2 x = t2 y → approxBisim inc2 x y)
  {p q : I1 ⊕ I2} (h : Sum.map t1 t2 p = Sum.map t1 t2 q) :
  approxBisim (incidenceSum inc1 inc2) p q := by
  cases p with
  | inl a =>
    cases q with
    | inl b =>
      simp only [Sum.map_inl, Sum.inl.injEq] at h
      exact incidenceSum_lift_left inc1 inc2 (ht1 a b h)
    | inr b => simp at h
  | inr a =>
    cases q with
    | inl b => simp at h
    | inr b =>
      simp only [Sum.map_inr, Sum.inr.injEq] at h
      exact incidenceSum_lift_right inc1 inc2 (ht2 a b h)

/- Concrete confirmation: pairing `natToFiniteSet` (cycle 5, itself now
   known to be a `glue`-homomorphism, cycle 34) on both sides of a
   `natIncidence ⊕ natIncidence` sum, translate-equality still reflects
   to `≈` in the sum -- despite `incidenceSum natIncidence natIncidence`
   itself NOT being faithful (cycle 33's `incidenceSum_leaves_cross_natIncidence`). -/
example {a b : Nat ⊕ Nat}
    (h : Sum.map natToFiniteSet natToFiniteSet a = Sum.map natToFiniteSet natToFiniteSet b) :
    approxBisim (incidenceSum natIncidence natIncidence) a b :=
  incidenceSum_translation_reflects natIncidence natIncidence natToFiniteSet natToFiniteSet
    (fun _ _ => natToFiniteSet_reflects_approxBisim) (fun _ _ => natToFiniteSet_reflects_approxBisim) h

end IncidenceCore
