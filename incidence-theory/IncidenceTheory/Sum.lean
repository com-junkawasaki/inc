import IncidenceTheory.Peano
import IncidenceTheory.Cycle
import IncidenceTheory.Product

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

def sumResonance {I1 R1 T1 I2 R2 T2 : Type u}
    [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (unit : I1 ⊕ I2) : (I1 ⊕ I2) → (I1 ⊕ I2) → (I1 ⊕ I2) → Prop :=
  fun x y k =>
    (x = unit ∧ k = y) ∨ (y = unit ∧ k = x) ∨
      match x, y, k with
      | .inl x1, .inl y1, .inl k1 => inc1.resonance x1 y1 k1
      | .inr x2, .inr y2, .inr k2 => inc2.resonance x2 y2 k2
      | _, _, _ => False

def incidenceSum {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
  Incidence (I1 ⊕ I2) (R1 ⊕ R2) GraphType where
  boundary := sumBoundary inc1 inc2
  typeFunc := fun _ => GraphType.unit
  resonance := sumResonance inc1 inc2 (Sum.inl inc1.unit)
  glue := sumGlue inc1 inc2 (Sum.inl inc1.unit)
  selected_resonates := by
    intro x y k selected
    simp only [sumGlue] at selected
    split at selected
    next hy =>
      have hk : k = x := by simpa using selected.symm
      exact Or.inr (Or.inl ⟨hy, hk⟩)
    next hy =>
      split at selected
      next hx =>
        have hk : k = y := by simpa using selected.symm
        exact Or.inl ⟨hx, hk⟩
      next hx =>
        cases x with
        | inl x1 =>
          cases y with
          | inl y1 =>
            cases glueEq : inc1.glue x1 y1 with
            | none => simp [glueEq] at selected
            | some k1 =>
              simp [glueEq] at selected
              subst k
              exact Or.inr (Or.inr (inc1.selected_resonates glueEq))
          | inr y2 => simp at selected
        | inr x2 =>
          cases y with
          | inl y1 => simp at selected
          | inr y2 =>
            cases glueEq : inc2.glue x2 y2 with
            | none => simp [glueEq] at selected
            | some k2 =>
              simp [glueEq] at selected
              subst k
              exact Or.inr (Or.inr (inc2.selected_resonates glueEq))
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

theorem incidenceSum_preserves_unselected_resonance_mode :
    finiteIncidence.resonance .root .root .leaf ∧
      (incidenceSum finiteIncidence finiteIncidence).resonance
        (Sum.inl .root) (Sum.inl .root) (Sum.inl .leaf) := by
  constructor
  · trivial
  · exact Or.inr (Or.inr True.intro)

def resonanceSumSpec
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (first : ResonanceSpec inc1) (second : ResonanceSpec inc2) :
    ResonanceSpec (incidenceSum inc1 inc2) where
  symmetric := by
    intro x y k resonant
    rcases resonant with unitLeft | unitRight | sameSide
    · exact Or.inr (Or.inl unitLeft)
    · exact Or.inl unitRight
    · rcases x with x1 | x2 <;> rcases y with y1 | y2 <;>
        rcases k with k1 | k2
      all_goals simp only at sameSide ⊢
      · exact Or.inr (Or.inr (first.symmetric sameSide))
      · exact Or.inr (Or.inr (second.symmetric sameSide))
  unit_left := by
    intro i
    exact Or.inl ⟨rfl, rfl⟩
  unit_right := by
    intro i
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  type_compatible := by
    intro i j k resonant
    exact ⟨rfl, rfl⟩

theorem finiteIncidenceSum_not_associativeResonance :
    ¬ Nonempty (AssociativeResonanceSpec
      (incidenceSum finiteIncidence finiteIncidence)) := by
  rintro ⟨associative⟩
  have reassociated := associative.reassociate
    (i := Sum.inl FiniteIncidence.root)
    (j := Sum.inl FiniteIncidence.root)
    (k := Sum.inr FiniteIncidence.root)
    (out := Sum.inr FiniteIncidence.root)
  have leftReachable :
      ∃ ij,
        (incidenceSum finiteIncidence finiteIncidence).resonance
          (Sum.inl .root) (Sum.inl .root) ij ∧
        (incidenceSum finiteIncidence finiteIncidence).resonance
          ij (Sum.inr .root) (Sum.inr .root) := by
    exact ⟨Sum.inl FiniteIncidence.leaf,
      Or.inr (Or.inr True.intro), Or.inl ⟨rfl, rfl⟩⟩
  rcases reassociated.mp leftReachable with ⟨jk, hjk, hout⟩
  rcases jk with jk1 | jk2
  · simp [incidenceSum, sumResonance, finiteIncidence] at hjk
  · simp [incidenceSum, sumResonance, finiteIncidence] at hjk

noncomputable def countablyPresentedIncidenceSum
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : CountablyPresentedIncidence I1 R1 T1)
    (right : CountablyPresentedIncidence I2 R2 T2) :
    CountablyPresentedIncidence (I1 ⊕ I2) (R1 ⊕ R2) GraphType where
  incidence := incidenceSum left.incidence right.incidence
  atoms := left.atoms.sum right.atoms

theorem countablyPresentedIncidenceSum_internalLogic_complete
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : CountablyPresentedIncidence I1 R1 T1)
    (right : CountablyPresentedIncidence I2 R2 T2)
    (context : List (Formula (I1 ⊕ I2))) (formula : Formula (I1 ⊕ I2)) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  (countablyPresentedIncidenceSum left right).internalLogic_complete context formula

theorem incidenceSum_boundaryValuation_inl_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (atom : I1) :
    IncidenceBoundaryValuation (incidenceSum left right) (Sum.inl atom) ↔
      IncidenceBoundaryValuation left atom := by
  simp only [IncidenceBoundaryValuation, incidenceSum, sumBoundary, List.mem_map]
  constructor
  · rintro ⟨_, source, member, rfl⟩
    exact ⟨source, member⟩
  · rintro ⟨source, member⟩
    exact ⟨_, source, member, rfl⟩

theorem incidenceSum_boundaryValuation_inr_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (atom : I2) :
    IncidenceBoundaryValuation (incidenceSum left right) (Sum.inr atom) ↔
      IncidenceBoundaryValuation right atom := by
  simp only [IncidenceBoundaryValuation, incidenceSum, sumBoundary, List.mem_map]
  constructor
  · rintro ⟨_, source, member, rfl⟩
    exact ⟨source, member⟩
  · rintro ⟨source, member⟩
    exact ⟨_, source, member, rfl⟩

theorem incidenceSum_leafValuation_inl_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (atom : I1) :
    IncidenceLeafValuation (incidenceSum left right) (Sum.inl atom) ↔
      IncidenceLeafValuation left atom := by
  simp [IncidenceLeafValuation, incidenceSum, sumBoundary]

theorem incidenceSum_leafValuation_inr_iff
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (left : Incidence I1 R1 T1) (right : Incidence I2 R2 T2)
    (atom : I2) :
    IncidenceLeafValuation (incidenceSum left right) (Sum.inr atom) ↔
      IncidenceLeafValuation right atom := by
  simp [IncidenceLeafValuation, incidenceSum, sumBoundary]

noncomputable def natSumCountablyPresentedIncidence :
    CountablyPresentedIncidence (Nat ⊕ Nat) (PeanoRole ⊕ PeanoRole) GraphType :=
  countablyPresentedIncidenceSum natCountablyPresentedIncidence
    natCountablyPresentedIncidence

theorem natSum_internalLogic_consistent_iff_model
    (context : List (Formula (Nat ⊕ Nat))) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  natSumCountablyPresentedIncidence.internalLogic_consistent_iff_model context

theorem natSum_internalLogic_countermodel
    {context : List (Formula (Nat ⊕ Nat))} {formula : Formula (Nat ⊕ Nat)}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory (Nat ⊕ Nat),
      KripkeContextForces (canonicalKripkeModel (Nat ⊕ Nat)) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel (Nat ⊕ Nat)) theory formula :=
  natSumCountablyPresentedIncidence.internalLogic_countermodel hnot

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

theorem incidenceSum_nat_not_quotientResonanceCongruent :
    ¬ QuotientResonanceCongruent
      (incidenceSum natIncidence natIncidence) := by
  intro congruent
  have preserved := (congruent
    incidenceSum_leaves_cross_natIncidence
    (approxBisim_refl _ (Sum.inl 1))
    (approxBisim_refl _ (Sum.inl 1))).mp
    (show (incidenceSum natIncidence natIncidence).resonance
      (Sum.inl 0) (Sum.inl 1) (Sum.inl 1) from
      Or.inl ⟨rfl, rfl⟩)
  simp [incidenceSum, sumResonance, natIncidence] at preserved

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

theorem incidenceSum_quotientResonanceCongruent_of_faithful_no_shared_leaves
    {I1 R1 I2 R2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 GraphType) (inc2 : Incidence I2 R2 GraphType)
    (hf1 : ∀ x y : I1, approxBisim inc1 x y ↔ x = y)
    (hf2 : ∀ x y : I2, approxBisim inc2 x y ↔ x = y)
    (hleafless2 : ∀ b, inc2.boundary b ≠ []) :
    QuotientResonanceCongruent (incidenceSum inc1 inc2) :=
  quotientResonanceCongruent_of_faithful _
    (incidenceSum_faithful_of_faithful_no_shared_leaves
      inc1 inc2 hf1 hf2 hleafless2)

theorem natCycleSum_quotientResonanceCongruent :
    QuotientResonanceCongruent
      (incidenceSum natIncidence cycleIncidenceFixed) :=
  incidenceSum_quotientResonanceCongruent_of_faithful_no_shared_leaves
    natIncidence cycleIncidenceFixed natIncidence_approxBisim_iff
    cycleIncidenceFixed_approxBisim_iff
    (fun b => by cases b <;> simp [cycleIncidenceFixed, cycleBoundaryFixed])

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

/- Cycle 46 (see RESEARCH_LOG.md): cycle 41's queue (= cycle 37's own
   queue item (b), restated through cycles 39/42/44/45) named the
   remaining largest open thread as "the internal-logic distributivity
   direction relating `incidenceProd`/`incidenceSum`" and, since cycle
   37, has repeatedly flagged it as needing a scope-down FIRST STEP
   before any bisimulation/homomorphism/distributivity attempt: does a
   natural, well-typed map exist at all between `incidenceProd inc1
   inc2`'s carrier (`I1 × I2`, `Product.lean`'s `incidenceProd`) and
   `incidenceSum inc1 inc2`'s carrier (`I1 ⊕ I2`, this file's
   `incidenceSum`) for the SAME `inc1 : Incidence I1 R1 T1`,
   `inc2 : Incidence I2 R2 T2`? Both constructors are stated fully
   generically over `{I1 R1 T1 I2 R2 T2 : Type u}` with NO cardinality
   hypothesis on `I1`/`I2` at all -- so a *generic* carrier-comparison
   combinator, usable for every `incidenceProd`/`incidenceSum` pair this
   project could ever build (not only the specific instances already
   used elsewhere, e.g. `natIncidence`/`finiteIncidence`/
   `trivialIncidence` via `NatBoolProductIncidence` in `Quotient.lean`),
   would itself need to typecheck for every possible `I1`, `I2` -- the
   same discipline cycle 37 used when testing `prodCollapseTrivial`
   against a deliberately adversarial case rather than trusting a
   structural argument by inspection alone.

   Finding, in three parts. (1) `I1 × I2 → I1 ⊕ I2` exists
   unconditionally and generically (no hypothesis on `I1`/`I2` needed),
   but is NOT canonical: there are at least two equally well-typed,
   provably DISTINCT candidates (`prodToSumCarrier`/
   `prodToSumCarrier'` below, projecting then injecting on either
   side), and nothing in either `Incidence` structure singles one out;
   both discard one whole component's worth of data. (2)
   `I1 ⊕ I2 → I1 × I2` does NOT exist generically at all --
   `sum_to_prod_carrier_map_impossible_in_general` proves this
   concretely by instantiating `I1 := Empty`: any
   `Empty ⊕ Unit → Empty × Unit` would have to conjure an `Empty` value
   out of `Sum.inr ()`, which is impossible regardless of classical
   choice (there is no term of an uninhabited type to return; choice
   only selects among already-existing witnesses). (3) Restricting to
   this project's actual concrete, non-`Empty` carriers (e.g. `Nat`,
   via `natIncidence`) does make an AD HOC `I1 ⊕ I2 → I1 × I2` possible,
   but `sumToProdNatCarrier_basepoint_dependent` shows it is genuinely
   basepoint-dependent, not canonical: two equally reasonable defaults
   (`0` vs `1`) disagree on the very same input.

   Conclusion for the scope-down question: NO natural/canonical map
   exists between `incidenceProd A B`'s carrier and `incidenceSum A B`'s
   carrier, for the same `A`, `B`, in EITHER direction, that could serve
   as a non-arbitrary basis for a subsequent bisimulation/homomorphism/
   distributivity claim comparing the two constructors directly. This
   is a clean negative scope-down result, in this project's established
   style (cycles 38-40): it closes this particular framing of the
   question rather than opening new ground.

   Recorded separately for cycle 47 (out of scope to pursue this
   cycle): the ORIGINAL cycle 37 phrasing of this thread's underlying
   motivation was not this same-`(A,B)` comparison at all, but the
   *distributive-law* shape `incidenceProd inc1 (incidenceSum inc2
   inc3)` vs `incidenceSum (incidenceProd inc1 inc2)
   (incidenceProd inc1 inc3)` -- a genuinely different comparison, over
   THREE incidence structures, whose underlying carrier types
   (`I1 × (I2 ⊕ I3)` vs `(I1 × I2) ⊕ (I1 × I3)`) DO have a standard,
   canonical, natural bijection (`Type`/`Set` is a distributive
   category: pairing distributes over disjoint union, unlike the
   reverse direction). That comparison was never actually tested here
   (this cycle deliberately tested only the same-`(A,B)` framing, per
   cycle 45's own next-hypothesis and this cycle's task scope) and
   remains open -- and is a much more promising candidate for an actual
   positive carrier-level map than the question this cycle answered. -/

def prodToSumCarrier {I1 I2 : Type u} (p : I1 × I2) : I1 ⊕ I2 := Sum.inl p.1

def prodToSumCarrier' {I1 I2 : Type u} (p : I1 × I2) : I1 ⊕ I2 := Sum.inr p.2

theorem prodToSumCarrier_ne_prodToSumCarrier' :
    prodToSumCarrier (I1 := Nat) (I2 := Bool) (5, true) ≠
      prodToSumCarrier' (I1 := Nat) (I2 := Bool) (5, true) :=
  fun h => Sum.noConfusion h

theorem sum_to_prod_carrier_map_impossible_in_general :
    ¬ Nonempty ((Empty ⊕ Unit) → (Empty × Unit)) := by
  rintro ⟨f⟩
  exact (f (Sum.inr ())).1.elim

def sumToProdNatCarrier (basepoint : Nat) : Nat ⊕ Nat → Nat × Nat
  | Sum.inl n => (n, basepoint)
  | Sum.inr n => (basepoint, n)

theorem sumToProdNatCarrier_basepoint_dependent :
    sumToProdNatCarrier 0 (Sum.inl 7) ≠ sumToProdNatCarrier 1 (Sum.inl 7) := by
  simp [sumToProdNatCarrier]

/- Cycle 47 (see RESEARCH_LOG.md): cycle 46's own next-hypothesis, re-scoping
   the distributivity thread to the shape cycle 37 ORIGINALLY asked for (not
   the same-`(A,B)` carrier-map comparison cycle 46 closed negatively, which
   was a drift cycle 46 itself identified and explicitly set aside for this
   cycle): does the canonical `I1 × (I2 ⊕ I3) ≃ (I1 × I2) ⊕ (I1 × I3)`
   bijection -- `Type`/`Set` genuinely IS a distributive category, unlike the
   carrier-map question cycle 46 closed -- align the `boundary`/`glue`/
   `guards` structure of `incidenceProd inc1 (incidenceSum inc2 inc3)` with
   `incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)`,
   definitionally, for concrete already-existing instances? Per the task's
   explicit scope-down: construct the bijection first, then check
   definitionally -- no bisimulation/homomorphism/general-distributivity
   theorem attempted this cycle.

   Concrete instances reused (per cycle 46's own asymmetry finding --
   `incidenceProd` has three applied instances in this codebase,
   `incidenceSum` has none outside its own file's header example): `inc1 :=
   natIncidence`, `inc2 := inc3 := finiteIncidence` -- `incidenceSum
   finiteIncidence finiteIncidence` is literally this file's own header
   example (`incidenceSum_preserves_unselected_resonance_mode`, above), and
   `incidenceProd natIncidence finiteIncidence` is `CrossInstance.lean`'s
   `natFiniteProdNormalizedResonanceCompletion`'s underlying instance -- no
   new instance invented.

   Finding, in three parts, mirroring the task's structure exactly.

   (1) `boundary` ALIGNS, generically (not just for these instances): both
   composite structures' boundary at corresponding elements have the SAME
   LENGTH (`prodBoundary_sum_{left,right}_length` /
   `sumBoundary_prod_{left,right}_length`, combined into
   `incidenceProd_incidenceSum_boundary_length_aligned_{left,right}`) --
   `prodBoundary`'s `++`/`List.map` shape and `sumBoundary`'s `List.map`
   shape compose the same way regardless of which constructor sits on the
   outside, because `List.length` is a `List.map`/`List.append`
   congruence, not a fact needing `inc1`/`inc2`/`inc3`'s internals at all.
   (A full ENTRY-level correspondence -- not just length -- also holds by
   direct unfolding of `prodBoundary`/`sumBoundary`/`sumInlEndpoint`/
   `sumInrEndpoint`, but is not separately stated as a theorem here, per the
   task's explicit "definitionally first, no homomorphism proof yet" scope;
   the length results are the concrete, decidable-in-principle witness the
   task asked for.)

   (2) `glue` does NOT align -- a concrete, decidable counterexample,
   `incidenceProd_incidenceSum_distrib_glue_misaligned` below. The
   mechanism: `incidenceSum`'s `glue` (cycle 33) absorbs against its OWN
   designated unit exactly (`Sum.inl inc2.unit` for the inner sum inside
   `incidenceProd inc1 (incidenceSum inc2 inc3)`; `Sum.inl
   (incidenceProd inc1 inc2).unit = Sum.inl (inc1.unit, inc2.unit)` for the
   outer sum in `incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1
   inc3)`). On the LHS, the inner sum's absorption test only inspects the
   `I2 ⊕ I3` component (`x`/`y`), completely independent of `i1` -- so it can
   fire (returning the OTHER side's element unchanged) even when `i1 ≠
   inc1.unit`, provided `inc1.glue i1 j1` still succeeds (as it always does
   for `natIncidence`, whose `glue` is total addition). On the RHS, the
   outer sum's absorption test requires the FULL pair `(i1, i2)` to equal
   `(inc1.unit, inc2.unit)` -- strictly narrower, since it also demands
   `i1 = inc1.unit`. When `i1 ≠ inc1.unit` and the two arguments land on
   OPPOSITE `I2 ⊕ I3` sides, the LHS still glues successfully (via the inner
   absorption) while the RHS's same-side/cross-side match falls through to
   `none` (opposite tags, neither side is the exact designated unit).
   Verified concretely: at `i1 := 2`, `j1 := 3` (both `≠ 0 = natIncidence.unit`),
   `x := Sum.inl FiniteIncidence.leaf` (`= finiteIncidence.unit`, so the inner
   sum's absorption fires), `y := Sum.inr FiniteIncidence.root` (opposite
   side) -- `#eval` first (scratch, not committed), then transcribed as a
   `decide`-checked theorem: LHS glue maps to `some (Sum.inr (5, root))`
   (`5 = 2 + 3` via `natIncidence.glue`'s addition, passed through cleanly),
   RHS glue is `none`. Genuinely different Lean values, not merely
   non-obviously-equal.

   (3) `guards`: not concretely counterexampled (every applied concrete
   instance in this project -- `natIncidence`, `finiteIncidence`,
   `trivialIncidence` -- uses `Guards.permissive`, i.e. always `true`, so no
   existing instance can concretely witness a disagreement without
   inventing a new one, which the task's tractability scope disallows).
   But the STRUCTURAL asymmetry is real and provable generically:
   `incidenceSum`'s `guards` field (cycle 33) is unconditionally
   `Guards.permissive`, discarding whatever guards its two arguments
   actually carry (`incidenceSum_prod_guards_always_permissive`: the RHS's
   top-level `guards.allow` is `true` for every pair, full stop) -- whereas
   `incidenceProd`'s `guards` (cycle 31) genuinely conjoins its two factors'
   guards (`incidenceProd_sum_guards_depends_on_inc1_only`: the LHS's
   top-level `guards.allow (i1,x) (j1,y)` reduces to exactly
   `inc1.guards.allow i1 j1`, since the inner sum's own guards are
   permissive and cancel out of the `&&`). For this project's actual
   instances `inc1.guards.allow i1 j1` is always `true` too, so no
   observable disagreement exists YET -- but the two formulas are not the
   same function in general, and would diverge the moment any future
   instance in this project used a non-trivial `Guards`.
   `lake build`: 62/62 jobs (`lake clean && lake build`, matching
   `verify.sh`). `#print axioms` (scratch file, deleted after use, exactly
   cycles 45/46's method) on the new theorems: `prodSumDistrib_left_inverse`/
   `prodSumDistrib_right_inverse` need no axioms at all (pure `rfl`/`cases`);
   the four boundary-length lemmas and both guards lemmas need only
   `propext`/`Quot.sound`; `incidenceProd_incidenceSum_distrib_glue_misaligned`
   needs `propext`/`Classical.choice`/`Quot.sound` -- but this is
   `natIncidence`'s OWN standing baseline, not something this cycle's proof
   introduces: even `theorem t : natIncidence.glue 2 3 = some 5 := rfl`
   alone (checked in the same scratch file, with none of this cycle's new
   code) already carries `Classical.choice`, consistent with cycle 37's own
   note that `natIncidence`-involving facts have carried it since cycle 4. -/

/- The canonical distributive-law bijection at the carrier level -- always
   well-typed for ANY `I1`, `I2`, `I3` (no instance/cardinality hypothesis),
   unlike cycle 46's same-`(A,B)` carrier-map question which had none in
   either direction. Both directions given explicitly, plus round-trip
   lemmas, in place of `Equiv` (this project has no existing `Equiv`-style
   bundled-bijection abstraction to reuse -- checked by grep -- so this
   follows the plainer "explicit forward/backward plus round-trip lemmas"
   convention the task itself suggested). -/
def prodSumDistribForward {I1 I2 I3 : Type u} (p : I1 × (I2 ⊕ I3)) :
    (I1 × I2) ⊕ (I1 × I3) :=
  match p with
  | (i1, Sum.inl i2) => Sum.inl (i1, i2)
  | (i1, Sum.inr i3) => Sum.inr (i1, i3)

def prodSumDistribBackward {I1 I2 I3 : Type u} (q : (I1 × I2) ⊕ (I1 × I3)) :
    I1 × (I2 ⊕ I3) :=
  match q with
  | Sum.inl (i1, i2) => (i1, Sum.inl i2)
  | Sum.inr (i1, i3) => (i1, Sum.inr i3)

theorem prodSumDistrib_left_inverse {I1 I2 I3 : Type u}
    (p : I1 × (I2 ⊕ I3)) :
    prodSumDistribBackward (prodSumDistribForward p) = p := by
  obtain ⟨i1, x⟩ := p
  cases x <;> rfl

theorem prodSumDistrib_right_inverse {I1 I2 I3 : Type u}
    (q : (I1 × I2) ⊕ (I1 × I3)) :
    prodSumDistribForward (prodSumDistribBackward q) = q := by
  cases q with
  | inl a => obtain ⟨i1, i2⟩ := a; rfl
  | inr a => obtain ⟨i1, i3⟩ := a; rfl

/- Part (1): `boundary` aligns, generically, in the sense of matching
   cardinality under the bijection -- proved directly from `prodBoundary`'s
   `++`/`List.map` shape and `sumBoundary`'s `List.map` shape, needing
   nothing about `inc1`/`inc2`/`inc3` beyond their existence. -/
theorem prodBoundary_sum_left_length
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 : I1) (i2 : I2) :
    (prodBoundary inc1 (incidenceSum inc2 inc3) (i1, Sum.inl i2)).length =
      (inc1.boundary i1).length + (inc2.boundary i2).length := by
  simp [prodBoundary, incidenceSum, sumBoundary]

theorem prodBoundary_sum_right_length
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 : I1) (i3 : I3) :
    (prodBoundary inc1 (incidenceSum inc2 inc3) (i1, Sum.inr i3)).length =
      (inc1.boundary i1).length + (inc3.boundary i3).length := by
  simp [prodBoundary, incidenceSum, sumBoundary]

theorem sumBoundary_prod_left_length
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 : I1) (i2 : I2) :
    (sumBoundary (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)
      (Sum.inl (i1, i2))).length =
      (inc1.boundary i1).length + (inc2.boundary i2).length := by
  simp [sumBoundary, incidenceProd, prodBoundary]

theorem sumBoundary_prod_right_length
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 : I1) (i3 : I3) :
    (sumBoundary (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)
      (Sum.inr (i1, i3))).length =
      (inc1.boundary i1).length + (inc3.boundary i3).length := by
  simp [sumBoundary, incidenceProd, prodBoundary]

/- The headline alignment statement, stated directly in terms of the two
   composite `Incidence` structures' own `.boundary` field (not the raw
   `prodBoundary`/`sumBoundary` helpers) and the bijection itself, matching
   exactly the shape the task posed the question in. -/
theorem incidenceProd_incidenceSum_boundary_length_aligned_left
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 : I1) (i2 : I2) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).boundary (i1, Sum.inl i2)).length =
      ((incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).boundary
        (prodSumDistribForward (i1, Sum.inl i2))).length := by
  simp [incidenceProd, incidenceSum, prodBoundary, sumBoundary, prodSumDistribForward]

theorem incidenceProd_incidenceSum_boundary_length_aligned_right
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 : I1) (i3 : I3) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).boundary (i1, Sum.inr i3)).length =
      ((incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).boundary
        (prodSumDistribForward (i1, Sum.inr i3))).length := by
  simp [incidenceProd, incidenceSum, prodBoundary, sumBoundary, prodSumDistribForward]

/- Part (2): `glue` does NOT align -- a concrete, decidable counterexample
   using this project's own existing `natIncidence`/`finiteIncidence`
   instances (no new instance invented). See the doc comment above for the
   mechanism (inner-sum absorption ignoring `i1` vs. outer-sum absorption
   requiring the full pair to match its unit). -/
theorem incidenceProd_incidenceSum_distrib_glue_misaligned :
    ((incidenceProd natIncidence (incidenceSum finiteIncidence finiteIncidence)).glue
        (2, Sum.inl FiniteIncidence.leaf) (3, Sum.inr FiniteIncidence.root)).map
      (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)) ≠
    (incidenceSum (incidenceProd natIncidence finiteIncidence)
        (incidenceProd natIncidence finiteIncidence)).glue
      (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)
        (2, Sum.inl FiniteIncidence.leaf))
      (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)
        (3, Sum.inr FiniteIncidence.root)) := by decide

/- Part (3): the structural (not concretely-witnessed) `guards` asymmetry --
   `incidenceSum`'s top-level guards are unconditionally permissive,
   `incidenceProd`'s genuinely depend on `inc1`. See the doc comment above. -/
theorem incidenceSum_prod_guards_always_permissive
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (p q : (I1 × I2) ⊕ (I1 × I3)) :
    (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).guards.allow p q =
      true := by
  simp [incidenceSum, Guards.permissive]

theorem incidenceProd_sum_guards_depends_on_inc1_only
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (x y : I2 ⊕ I3) :
    (incidenceProd inc1 (incidenceSum inc2 inc3)).guards.allow (i1, x) (j1, y) =
      inc1.guards.allow i1 j1 := by
  simp [incidenceProd, prodGuards, incidenceSum, Guards.permissive]

/- Research cycle 48 (see RESEARCH_LOG.md): cycle 47's own next-hypothesis
   (a) -- given cycle 47's concrete counterexample turned on ON-THE-NOSE
   equality after the bijection (LHS glues to `some (Sum.inr (5, root))`,
   RHS to `none`), does the WEAKER claim -- agreement up to `≈`
   (`approxBisim`) rather than exact equality -- rescue it, or hold in
   general?

   Finding, in two parts, exactly mirroring the task's own anticipated
   shape. (1) The specific counterexample is NOT rescued by weakening to
   `≈`, for a structural reason cycle 47 itself flagged as a live
   possibility: `approxBisim` (`IncidenceTheory.lean`) is a relation
   `I → I → Prop` on the CARRIER of a single `Incidence`, never on
   `Option I` -- there is no established notion of a `none` outcome being
   "`≈`-related" to a `some x` outcome at all, and this project's own
   existing vocabulary for "gluing respects `≈`" (`GlueRespects`,
   `IncidenceTheory.lean`, used since `trivial_glue_respects_approxBisim`
   and `BisimulationNormalizationSpec`) is ITSELF only ever quantified
   over the case both sides' `glue` produce a `some` -- it says nothing
   about a `none` outcome. Formalized directly below via
   `OptionApproxBisim`, the canonical lift of `≈` to `Option` (mirroring
   how `=` lifts to `Option` -- `none ≈ none`, `some a ≈ some b ↔ a ≈ b`,
   and `none` is NEVER related to any `some _`, by construction, not by a
   deep argument): `not_optionApproxBisim_some_none` shows `some a` is
   never `OptionApproxBisim`-related to `none`, for ANY relation and ANY
   `a` -- so cycle 47's specific counterexample (LHS `some _`, RHS `none`)
   remains a counterexample even under this weakening;
   `incidenceProd_incidenceSum_distrib_glue_misaligned_not_bisim_rescued`
   confirms this concretely for cycle 47's own instances and values. This
   is the scoping resolution the task itself anticipated as a live
   possibility, not a strained proof.

   (2) But investigating WHY led to a stronger and more informative
   result than the bisimulation question itself: `glue` agreement between
   the two composite structures turns out to be EXACT (not merely `≈`)
   whenever the RHS succeeds at all --
   `incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some` proves,
   fully generically over ANY `inc1`/`inc2`/`inc3` (no instance
   hypothesis, unlike cycle 47's concrete-instance-only counterexample):
   if `incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)`'s
   glue succeeds (`some w`), then `incidenceProd inc1 (incidenceSum inc2
   inc3)`'s glue ALSO succeeds and, transported through
   `prodSumDistribForward`, equals `w` EXACTLY. The proof works by cases
   on which side of `I2 ⊕ I3` each argument's tag falls on (four cases,
   `incidenceProd_incidenceSum_distrib_glue_agree_{inl_inl,inr_inr,
   inl_inr,inr_inl}`), using only `inc1`/`inc2`/`inc3`'s own
   `unit_left`/`unit_right` structural obligations -- no instance-specific
   facts about `natIncidence`/`finiteIncidence` at all. Two reusable
   general facts about `incidenceSum` fell out along the way and are
   recorded as their own theorems (`incidenceSum_glue_same_left`/
   `_same_right`/`_cross_left`/`_cross_right`): critically,
   `incidenceSum`'s absorbing unit is ALWAYS `Sum.inl inc1.unit` (the
   FIRST factor's unit, tagged left) -- so a same-side pair on the
   SECOND factor (`Sum.inr`/`Sum.inr`) can NEVER hit an absorption
   branch at all and reduces unconditionally to the plain componentwise
   glue (`incidenceSum_glue_same_right`), whereas a same-side pair on the
   FIRST factor genuinely can (`incidenceSum_glue_same_left`) -- the two
   "symmetric-looking" same-side cases are secretly asymmetric in proof
   difficulty, a subtlety an initial by-hand derivation (assuming naive
   left/right symmetry) got wrong on the first pass before the Lean
   compiler forced the correction.

   Corollary,
   `incidenceProd_incidenceSum_distrib_glue_no_disagreement_when_both_some`:
   there is consequently NO possible case, for ANY `inc1`/`inc2`/`inc3`
   whatsoever (not merely none yet witnessed in this codebase's concrete
   instances), where both sides' `glue` succeed but disagree -- ruling
   out the task's suggested "look for a both-succeed-but-differ case"
   avenue entirely, by proof rather than by exhaustive search of this
   project's few concrete instances.
   `incidenceProd_incidenceSum_distrib_glue_approxBisim_of_both_some`
   restates this in the `≈` vocabulary the task asked about (trivially,
   via `approxBisim_refl`, since literal equality is always `≈`-related):
   whenever both sides succeed, they are not just `≈`-related but
   IDENTICAL.

   Net picture: the misalignment cycle 47 found is exactly and only a
   "RHS fails, LHS may still succeed" phenomenon (never the reverse, and
   never a same-side disagreement), and no rescue exists by weakening
   the FAILING case to `≈` -- because comparing a defined outcome to an
   undefined one is not what `≈` (or this project's own `GlueRespects`)
   was ever built to express. `lake build`: 66/66 jobs. `#print axioms`
   (scratch, deleted after use): every new theorem in this cycle needs at
   most `propext`/`Classical.choice`/`Quot.sound` -- the two `decide`d
   concrete facts about `natIncidence`/`finiteIncidence` carry
   `Classical.choice` for the same standing reason cycle 37/47 already
   documented (`natIncidence`-involving facts have carried it since cycle
   4); the fully generic theorems (`_agrees_of_rhs_some` and its case
   lemmas, `_no_disagreement_when_both_some`,
   `_approxBisim_of_both_some`, `not_optionApproxBisim_some_none`) need
   only `propext`/`Quot.sound`. Full `./verify.sh` passes end to end. -/

/- `incidenceSum`'s absorbing unit is always `Sum.inl inc1.unit` -- the
   FIRST factor's unit only. A same-side pair on the first factor can
   therefore still hit an absorption branch (if either argument happens
   to equal the unit exactly), but by `inc1`'s own `unit_left`/
   `unit_right` laws, whichever branch fires is forced to agree with the
   plain componentwise `glue` anyway -- so the result is unconditionally
   `some (Sum.inl k1)` whenever the componentwise glue itself succeeds,
   regardless of which (if any) absorption branch actually fired. -/
theorem incidenceSum_glue_same_left
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    {i1 j1 : I1} {k1 : I1} (hk1 : inc1.glue i1 j1 = some k1) :
    (incidenceSum inc1 inc2).glue (Sum.inl i1) (Sum.inl j1) = some (Sum.inl k1) := by
  simp only [incidenceSum, sumGlue]
  by_cases hj : j1 = inc1.unit
  · subst hj
    have hu := inc1.unit_right i1
    rw [hu] at hk1
    simp only [Option.some.injEq] at hk1
    subst hk1
    simp
  · by_cases hi : i1 = inc1.unit
    · subst hi
      have hu := inc1.unit_left j1
      rw [hu] at hk1
      simp only [Option.some.injEq] at hk1
      subst hk1
      simp [hj]
    · simp [hj, hi, hk1]

/- Unlike `incidenceSum_glue_same_left`, the SECOND factor never hits the
   absorption tests at all -- the designated unit is always
   `Sum.inl inc1.unit`, which can never equal a `Sum.inr`-tagged value --
   so this reduces unconditionally to the plain componentwise `inc2.glue`,
   with no case split on `inc2.unit` needed. This asymmetry (only the
   FIRST factor's same-side case needs the unit-law argument above) is
   itself the main proof-engineering finding of this cycle. -/
theorem incidenceSum_glue_same_right
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    {i2 j2 : I2} {k2 : I2} (hk2 : inc2.glue i2 j2 = some k2) :
    (incidenceSum inc1 inc2).glue (Sum.inr i2) (Sum.inr j2) = some (Sum.inr k2) := by
  simp [incidenceSum, sumGlue, hk2]

/- Cross-side (first factor on the left, second on the right): succeeds
   exactly when the left argument is the first factor's unit (absorbing
   the right argument unchanged), else fails outright -- there is no
   componentwise fallback for a genuinely cross-side pair. -/
theorem incidenceSum_glue_cross_left
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (i1 : I1) (j2 : I2) :
    (incidenceSum inc1 inc2).glue (Sum.inl i1) (Sum.inr j2) =
      if i1 = inc1.unit then some (Sum.inr j2) else none := by
  simp only [incidenceSum, sumGlue]
  by_cases hi : i1 = inc1.unit
  · simp [hi]
  · simp [hi]

/- Symmetric cross-side case (second factor on the left, first on the
   right): the absorption test is on the RIGHT argument here (it must be
   the first factor's unit, tagged left), since `incidenceSum`'s unit
   test is always `y = unit` first. -/
theorem incidenceSum_glue_cross_right
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (i2 : I2) (j1 : I1) :
    (incidenceSum inc1 inc2).glue (Sum.inr i2) (Sum.inl j1) =
      if j1 = inc1.unit then some (Sum.inr i2) else none := by
  simp only [incidenceSum, sumGlue]
  by_cases hj : j1 = inc1.unit
  · simp [hj]
  · simp [hj]

theorem incidenceProd_incidenceSum_distrib_glue_agree_inl_inl
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i2 j2 : I2) (w : (I1 × I2) ⊕ (I1 × I3))
    (hRHS : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (Sum.inl (i1, i2)) (Sum.inl (j1, j2)) = some w) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inl i2) (j1, Sum.inl j2)).map
      prodSumDistribForward = some w := by
  by_cases hj : (j1, j2) = (inc1.unit, inc2.unit)
  · injection hj with hj1 hj2
    subst hj1; subst hj2
    have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
        (Sum.inl (i1, i2)) (Sum.inl (inc1.unit, inc2.unit)) = some (Sum.inl (i1, i2)) := by
      simp [incidenceSum, sumGlue, incidenceProd]
    rw [hval] at hRHS
    simp only [Option.some.injEq] at hRHS
    subst hRHS
    simp only [incidenceProd, prodGlue, inc1.unit_right,
      incidenceSum_glue_same_left inc2 inc3 (inc2.unit_right i2), prodSumDistribForward,
      Option.map_some]
  · by_cases hi : (i1, i2) = (inc1.unit, inc2.unit)
    · injection hi with hi1 hi2
      subst hi1; subst hi2
      have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
          (Sum.inl (inc1.unit, inc2.unit)) (Sum.inl (j1, j2)) = some (Sum.inl (j1, j2)) := by
        simp [incidenceSum, sumGlue, hj, incidenceProd]
      rw [hval] at hRHS
      simp only [Option.some.injEq] at hRHS
      subst hRHS
      simp only [incidenceProd, prodGlue, inc1.unit_left,
        incidenceSum_glue_same_left inc2 inc3 (inc2.unit_left j2), prodSumDistribForward,
        Option.map_some]
    · rcases hk1 : inc1.glue i1 j1 with _ | k1
      · exfalso
        have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
            (Sum.inl (i1, i2)) (Sum.inl (j1, j2)) = none := by
          simp [incidenceSum, sumGlue, hj, hi, incidenceProd, prodGlue, hk1]
        rw [hval] at hRHS; exact absurd hRHS (by simp)
      · rcases hk2 : inc2.glue i2 j2 with _ | k2
        · exfalso
          have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (Sum.inl (i1, i2)) (Sum.inl (j1, j2)) = none := by
            simp [incidenceSum, sumGlue, hj, hi, incidenceProd, prodGlue, hk1, hk2]
          rw [hval] at hRHS; exact absurd hRHS (by simp)
        · have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (Sum.inl (i1, i2)) (Sum.inl (j1, j2)) = some (Sum.inl (k1, k2)) := by
            simp [incidenceSum, sumGlue, hj, hi, incidenceProd, prodGlue, hk1, hk2]
          rw [hval] at hRHS
          simp only [Option.some.injEq] at hRHS
          subst hRHS
          simp only [incidenceProd, prodGlue, hk1,
            incidenceSum_glue_same_left inc2 inc3 hk2, prodSumDistribForward, Option.map_some]

theorem incidenceProd_incidenceSum_distrib_glue_agree_inr_inr
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i3 j3 : I3) (w : (I1 × I2) ⊕ (I1 × I3))
    (hRHS : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (Sum.inr (i1, i3)) (Sum.inr (j1, j3)) = some w) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inr i3) (j1, Sum.inr j3)).map
      prodSumDistribForward = some w := by
  rcases hk1 : inc1.glue i1 j1 with _ | k1
  · exfalso
    have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
        (Sum.inr (i1, i3)) (Sum.inr (j1, j3)) = none := by
      simp [incidenceSum, sumGlue, incidenceProd, prodGlue, hk1]
    rw [hval] at hRHS; exact absurd hRHS (by simp)
  · rcases hk3 : inc3.glue i3 j3 with _ | k3
    · exfalso
      have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
          (Sum.inr (i1, i3)) (Sum.inr (j1, j3)) = none := by
        simp [incidenceSum, sumGlue, incidenceProd, prodGlue, hk1, hk3]
      rw [hval] at hRHS; exact absurd hRHS (by simp)
    · have hval : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
          (Sum.inr (i1, i3)) (Sum.inr (j1, j3)) = some (Sum.inr (k1, k3)) := by
        simp [incidenceSum, sumGlue, incidenceProd, prodGlue, hk1, hk3]
      rw [hval] at hRHS
      simp only [Option.some.injEq] at hRHS
      subst hRHS
      simp only [incidenceProd, prodGlue, hk1,
        incidenceSum_glue_same_right inc2 inc3 hk3, prodSumDistribForward, Option.map_some]

theorem incidenceProd_incidenceSum_distrib_glue_agree_inl_inr
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i2 : I2) (j3 : I3) (w : (I1 × I2) ⊕ (I1 × I3))
    (hRHS : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (Sum.inl (i1, i2)) (Sum.inr (j1, j3)) = some w) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inl i2) (j1, Sum.inr j3)).map
      prodSumDistribForward = some w := by
  rw [incidenceSum_glue_cross_left] at hRHS
  simp only [incidenceProd] at hRHS
  by_cases hcombo : (i1, i2) = (inc1.unit, inc2.unit)
  · simp only [hcombo, if_true] at hRHS
    injection hcombo with hi1 hi2
    subst hi1; subst hi2
    simp only [Option.some.injEq] at hRHS
    subst hRHS
    simp only [incidenceProd, prodGlue, inc1.unit_left, incidenceSum_glue_cross_left,
      if_true, prodSumDistribForward, Option.map_some]
  · simp [hcombo] at hRHS

theorem incidenceProd_incidenceSum_distrib_glue_agree_inr_inl
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i3 : I3) (j2 : I2) (w : (I1 × I2) ⊕ (I1 × I3))
    (hRHS : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (Sum.inr (i1, i3)) (Sum.inl (j1, j2)) = some w) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inr i3) (j1, Sum.inl j2)).map
      prodSumDistribForward = some w := by
  rw [incidenceSum_glue_cross_right] at hRHS
  simp only [incidenceProd] at hRHS
  by_cases hcombo : (j1, j2) = (inc1.unit, inc2.unit)
  · simp only [hcombo, if_true] at hRHS
    injection hcombo with hj1 hj2
    subst hj1; subst hj2
    simp only [Option.some.injEq] at hRHS
    subst hRHS
    simp only [incidenceProd, prodGlue, inc1.unit_right, incidenceSum_glue_cross_right,
      if_true, prodSumDistribForward, Option.map_some]
  · simp [hcombo] at hRHS

/- The main theorem: fully general over ANY `inc1`/`inc2`/`inc3` (no
   instance hypothesis at all), whenever the RHS's glue succeeds, the
   LHS's glue also succeeds and, transported through the bijection,
   agrees EXACTLY -- not merely up to `≈`. Combines the four tag-combo
   cases above. -/
theorem incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (x y : I2 ⊕ I3) (w : (I1 × I2) ⊕ (I1 × I3))
    (hRHS : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (prodSumDistribForward (i1, x)) (prodSumDistribForward (j1, y)) = some w) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, x) (j1, y)).map
      prodSumDistribForward = some w := by
  cases x with
  | inl i2 =>
    cases y with
    | inl j2 =>
      exact incidenceProd_incidenceSum_distrib_glue_agree_inl_inl inc1 inc2 inc3 i1 j1 i2 j2 w hRHS
    | inr j3 =>
      exact incidenceProd_incidenceSum_distrib_glue_agree_inl_inr inc1 inc2 inc3 i1 j1 i2 j3 w hRHS
  | inr i3 =>
    cases y with
    | inl j2 =>
      exact incidenceProd_incidenceSum_distrib_glue_agree_inr_inl inc1 inc2 inc3 i1 j1 i3 j2 w hRHS
    | inr j3 =>
      exact incidenceProd_incidenceSum_distrib_glue_agree_inr_inr inc1 inc2 inc3 i1 j1 i3 j3 w hRHS

/- Corollary: there is no possible case, for ANY `inc1`/`inc2`/`inc3`
   whatsoever, where both sides' `glue` succeed but literally disagree --
   the "look for a both-succeed-but-differ counterexample" avenue the
   task suggested as a fallback is provably empty, not merely unwitnessed
   among this project's few concrete instances. -/
theorem incidenceProd_incidenceSum_distrib_glue_no_disagreement_when_both_some
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (x y : I2 ⊕ I3) (v : I1 × (I2 ⊕ I3)) (w : (I1 × I2) ⊕ (I1 × I3))
    (hLHS : (incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, x) (j1, y) = some v)
    (hRHS : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (prodSumDistribForward (i1, x)) (prodSumDistribForward (j1, y)) = some w) :
    prodSumDistribForward v = w := by
  have hforward := incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some
    inc1 inc2 inc3 i1 j1 x y w hRHS
  rw [hLHS] at hforward
  simpa using hforward

/- Restated in the `≈` vocabulary the task itself asked about: whenever
   both sides succeed, they are not just `≈`-related but IDENTICAL
   (literal equality is always `≈`-related, via `approxBisim_refl`). This
   is the positive half of this cycle's answer to cycle 47's hypothesis
   (a) -- the "both succeed" case was never actually in doubt; only the
   "RHS fails" case (part (1) above) resists any `≈`-level rescue, for a
   reason unrelated to bisimulation strength (a category mismatch, not a
   failure of the bisimulation itself). -/
theorem incidenceProd_incidenceSum_distrib_glue_approxBisim_of_both_some
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (x y : I2 ⊕ I3) (v : I1 × (I2 ⊕ I3)) (w : (I1 × I2) ⊕ (I1 × I3))
    (hLHS : (incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, x) (j1, y) = some v)
    (hRHS : (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
              (prodSumDistribForward (i1, x)) (prodSumDistribForward (j1, y)) = some w) :
    approxBisim (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3))
      (prodSumDistribForward v) w := by
  rw [incidenceProd_incidenceSum_distrib_glue_no_disagreement_when_both_some
    inc1 inc2 inc3 i1 j1 x y v w hLHS hRHS]
  exact approxBisim_refl _ w

/- The canonical lift of `≈` to `Option` -- mirroring how `=` itself
   lifts to `Option` (`none` only equals `none`; `some a` only equals
   `some b` when `a = b`): `none` is related only to `none`, `some a` to
   `some b` exactly when `a ≈ b`, and a `none`/`some _` mismatch is NEVER
   related. This is the natural, non-strained meaning of "the two glue
   outcomes agree up to `≈`" for a PARTIAL operation -- and it settles,
   by construction rather than by a deep argument, whether cycle 47's
   `none`-vs-`some` counterexample could be rescued by weakening to `≈`. -/
def OptionApproxBisim {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    Option I → Option I → Prop
  | none, none => True
  | some a, some b => approxBisim inc a b
  | _, _ => False

theorem not_optionApproxBisim_some_none {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (a : I) : ¬ OptionApproxBisim inc (some a) none := by
  simp [OptionApproxBisim]

/- The concrete values from cycle 47's counterexample, transcribed as
   named facts (cycle 47 itself only proved the two sides `≠`, without
   naming either value separately). -/
theorem incidenceProd_incidenceSum_distrib_glue_lhs_some :
    ((incidenceProd natIncidence (incidenceSum finiteIncidence finiteIncidence)).glue
        (2, Sum.inl FiniteIncidence.leaf) (3, Sum.inr FiniteIncidence.root)).map
      (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)) =
    some (Sum.inr (5, FiniteIncidence.root)) := by decide

theorem incidenceProd_incidenceSum_distrib_glue_rhs_none :
    (incidenceSum (incidenceProd natIncidence finiteIncidence)
        (incidenceProd natIncidence finiteIncidence)).glue
      (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)
        (2, Sum.inl FiniteIncidence.leaf))
      (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)
        (3, Sum.inr FiniteIncidence.root)) = none := by decide

/- Closes cycle 47's hypothesis (a) concretely: the specific
   counterexample is NOT rescued by weakening to `≈` -- not because the
   bisimulation fails to relate the two sides in some subtle way, but
   because `OptionApproxBisim` (the canonical, non-strained lift of `≈`
   to a partial operation's outcomes) never relates a `some _` to a
   `none` in the first place, for any relation whatsoever. -/
theorem incidenceProd_incidenceSum_distrib_glue_misaligned_not_bisim_rescued :
    ¬ OptionApproxBisim
      (incidenceSum (incidenceProd natIncidence finiteIncidence)
        (incidenceProd natIncidence finiteIncidence))
      (((incidenceProd natIncidence (incidenceSum finiteIncidence finiteIncidence)).glue
          (2, Sum.inl FiniteIncidence.leaf) (3, Sum.inr FiniteIncidence.root)).map
        (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)))
      ((incidenceSum (incidenceProd natIncidence finiteIncidence)
          (incidenceProd natIncidence finiteIncidence)).glue
        (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)
          (2, Sum.inl FiniteIncidence.leaf))
        (prodSumDistribForward (I1 := Nat) (I2 := FiniteIncidence) (I3 := FiniteIncidence)
          (3, Sum.inr FiniteIncidence.root))) := by
  rw [incidenceProd_incidenceSum_distrib_glue_lhs_some,
    incidenceProd_incidenceSum_distrib_glue_rhs_none]
  exact not_optionApproxBisim_some_none _ _

/- Research cycle 49 (see RESEARCH_LOG.md): cycle 48's own next-hypothesis (a)
   -- cycle 48 proved `incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some`
   (RHS some -> LHS some, exactly equal) but explicitly left its CONVERSE
   uncharacterized: does the LHS glue ever succeed while the RHS glue is
   `none`, and if so, exactly when? Cycle 47's single concrete witness
   showed this CAN happen; this cycle characterizes EVERY case where it
   does, as a clean `iff`, fully generically over any `inc1`/`inc2`/`inc3`.

   First strengthens two of cycle 48's own lemmas
   (`incidenceSum_glue_same_left`/`_same_right`, each proved only under a
   "componentwise glue succeeds" hypothesis) into unconditional EQUALITIES:
   neither same-side case can ever differ from the plain componentwise
   glue, not even when the componentwise glue itself is `none` -- the same
   unit-law argument cycle 48 used for the `some` case works verbatim for
   `none` (if the componentwise glue is `none`, neither argument can be the
   absorbing unit, since the unit laws would force a `some` result if it
   were). This in turn gives FULL, unconditional equalities (not merely
   "if RHS succeeds") for the distributive law's two SAME-side tag
   combinations (`inl_inl`/`inr_inr`) -- proving, as a new fact this
   project's log has not stated before, that same-side pairs can NEVER
   misalign at all (misalignment is possible ONLY for genuinely
   cross-side pairs, exactly the shape of cycle 47's own counterexample).

   For the two CROSS-side combinations, derives closed `if`-`then`-`else`
   forms for both the LHS and the (already-known) RHS glue directly from
   cycle 48's `incidenceSum_glue_cross_left`/`_cross_right`, then reads
   off the precise misalignment condition by comparing the two closed
   forms: for `inl_inr` (`i1`/`i2` on the left, `j1`/`j3` on the right),
   LHS succeeds iff `i2 = inc2.unit` AND `inc1.glue i1 j1` succeeds (at
   ANY value), while RHS succeeds iff `i1 = inc1.unit` AND
   `i2 = inc2.unit` -- strictly narrower because it also demands `i1`
   itself be the unit, not merely that `inc1.glue i1 j1` succeed. So
   "LHS some, RHS none" happens exactly when `i2 = inc2.unit`,
   `i1 ≠ inc1.unit`, and `inc1.glue i1 j1` succeeds anyway (as it always
   does for `natIncidence`, cycle 47's own instance choice) -- confirming
   cycle 47's counterexample was not an isolated accident but the generic
   shape of the ENTIRE misalignment phenomenon for this tag combination.
   `inr_inl` is the mirror image, with the roles of `i1`/`j1` swapped
   (the unit-test lands on `j1` instead, since `incidenceSum`'s cross
   glue always tests whichever argument is tagged `Sum.inl`). Combines
   both cross cases with the (now-proved-impossible) same-side cases into
   one master `iff` over arbitrary `x y : I2 ⊕ I3`, completing the
   picture cycle 48 left open. -/

/- Strengthens `incidenceSum_glue_same_left` (cycle 48) to an unconditional
   equality: the sum's same-left glue is ALWAYS exactly the componentwise
   `inc1.glue` result (lifted through `Sum.inl`), whether or not that
   componentwise glue succeeds. -/
theorem incidenceSum_glue_same_left_eq
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (i1 j1 : I1) :
    (incidenceSum inc1 inc2).glue (Sum.inl i1) (Sum.inl j1) = (inc1.glue i1 j1).map Sum.inl := by
  simp only [incidenceSum, sumGlue]
  by_cases hj : j1 = inc1.unit
  · subst hj
    simp [inc1.unit_right i1]
  · by_cases hi : i1 = inc1.unit
    · subst hi
      simp [hj, inc1.unit_left j1]
    · simp [hj, hi]

/- Strengthens `incidenceSum_glue_same_right` (cycle 48) to an unconditional
   equality, mirroring `incidenceSum_glue_same_left_eq` -- the second
   factor's same-side pair never hits an absorption branch at all
   (`incidenceSum`'s designated unit is always `Sum.inl inc1.unit`), so
   this reduces unconditionally to the componentwise `inc2.glue`, no case
   split needed. -/
theorem incidenceSum_glue_same_right_eq
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (i2 j2 : I2) :
    (incidenceSum inc1 inc2).glue (Sum.inr i2) (Sum.inr j2) = (inc2.glue i2 j2).map Sum.inr := by
  simp [incidenceSum, sumGlue]

/- New fact: the `inl_inl` distributive-law combination can NEVER misalign
   -- a full, unconditional equality (not merely "if RHS succeeds"),
   strictly stronger than cycle 48's `incidenceProd_incidenceSum_distrib_glue_agree_inl_inl`. -/
theorem incidenceProd_incidenceSum_distrib_glue_inl_inl_eq
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i2 j2 : I2) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inl i2) (j1, Sum.inl j2)).map
      prodSumDistribForward =
    (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
      (Sum.inl (i1, i2)) (Sum.inl (j1, j2)) := by
  rw [incidenceSum_glue_same_left_eq (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)
    (i1, i2) (j1, j2)]
  simp only [incidenceProd, prodGlue, incidenceSum_glue_same_left_eq inc2 inc3 i2 j2]
  rcases inc1.glue i1 j1 with _ | k1 <;> rcases inc2.glue i2 j2 with _ | k2 <;>
    simp [prodSumDistribForward]

/- Mirror for `inr_inr`: also can NEVER misalign. -/
theorem incidenceProd_incidenceSum_distrib_glue_inr_inr_eq
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i3 j3 : I3) :
    ((incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inr i3) (j1, Sum.inr j3)).map
      prodSumDistribForward =
    (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
      (Sum.inr (i1, i3)) (Sum.inr (j1, j3)) := by
  rw [incidenceSum_glue_same_right_eq (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)
    (i1, i3) (j1, j3)]
  simp only [incidenceProd, prodGlue, incidenceSum_glue_same_right_eq inc2 inc3 i3 j3]
  rcases inc1.glue i1 j1 with _ | k1 <;> rcases inc3.glue i3 j3 with _ | k3 <;>
    simp [prodSumDistribForward]

/- Closed form for the LHS glue at the `inl_inr` cross combination, derived
   directly from `incidenceSum_glue_cross_left` (cycle 48): succeeds
   exactly when `i2 = inc2.unit` AND the outer `inc1.glue i1 j1` succeeds
   (at whatever value it happens to produce). -/
theorem incidenceProd_incidenceSum_distrib_glue_inl_inr_lhs_eq
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i2 : I2) (j3 : I3) :
    (incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inl i2) (j1, Sum.inr j3) =
      if i2 = inc2.unit then (inc1.glue i1 j1).map (fun k1 => (k1, Sum.inr j3)) else none := by
  simp only [incidenceProd, prodGlue, incidenceSum_glue_cross_left inc2 inc3 i2 j3]
  by_cases h : i2 = inc2.unit
  · subst h
    rcases inc1.glue i1 j1 with _ | k1 <;> simp
  · simp [h]

/- Closed form for the RHS glue at the `inl_inr` combination, derived from
   `incidenceSum_glue_cross_left` applied to the OUTER sum: succeeds
   exactly when the FULL pair `(i1, i2)` is `((incidenceProd inc1 inc2).unit`
   `= (inc1.unit, inc2.unit)` -- strictly narrower than the LHS's condition. -/
theorem incidenceSum_incidenceProd_distrib_glue_inl_inr_rhs_eq
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i2 : I2) (j3 : I3) :
    (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
      (Sum.inl (i1, i2)) (Sum.inr (j1, j3)) =
      if i1 = inc1.unit ∧ i2 = inc2.unit then some (Sum.inr (j1, j3)) else none := by
  rw [incidenceSum_glue_cross_left (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)
    (i1, i2) (j1, j3)]
  simp [incidenceProd, Prod.ext_iff]

/- The headline `inl_inr` characterization: LHS succeeds while RHS is
   `none` EXACTLY when `i2 = inc2.unit`, `i1 ≠ inc1.unit`, and
   `inc1.glue i1 j1` succeeds anyway -- the precise generic shape of
   cycle 47's concrete counterexample (`i1 := 2`, `j1 := 3`, both
   `≠ 0 = natIncidence.unit`, `inc1.glue i1 j1` total for `natIncidence`). -/
theorem incidenceProd_incidenceSum_distrib_glue_lhs_some_rhs_none_iff_inl_inr
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i2 : I2) (j3 : I3) :
    ((∃ v, (incidenceProd inc1 (incidenceSum inc2 inc3)).glue
        (i1, Sum.inl i2) (j1, Sum.inr j3) = some v) ∧
     (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
       (Sum.inl (i1, i2)) (Sum.inr (j1, j3)) = none)
    ↔ i2 = inc2.unit ∧ i1 ≠ inc1.unit ∧ ∃ k1, inc1.glue i1 j1 = some k1 := by
  rw [incidenceProd_incidenceSum_distrib_glue_inl_inr_lhs_eq inc1 inc2 inc3 i1 j1 i2 j3,
    incidenceSum_incidenceProd_distrib_glue_inl_inr_rhs_eq inc1 inc2 inc3 i1 j1 i2 j3]
  constructor
  · rintro ⟨⟨v, hv⟩, hnone⟩
    by_cases h2 : i2 = inc2.unit
    · refine ⟨h2, ?_, ?_⟩
      · intro h1
        rw [if_pos ⟨h1, h2⟩] at hnone
        exact absurd hnone (by simp)
      · rcases hk1 : inc1.glue i1 j1 with _ | k1
        · rw [if_pos h2, hk1] at hv
          exact absurd hv (by simp)
        · exact ⟨k1, rfl⟩
    · rw [if_neg h2] at hv
      exact absurd hv (by simp)
  · rintro ⟨h2, h1, k1, hk1⟩
    refine ⟨⟨(k1, Sum.inr j3), ?_⟩, ?_⟩
    · rw [if_pos h2, hk1]; rfl
    · rw [if_neg (fun h => h1 h.1)]

/- Closed forms and the headline characterization for the mirror `inr_inl`
   combination -- same mechanism, with the unit-test landing on `j1`
   instead of `i1` (since `incidenceSum`'s cross glue always tests
   whichever argument is tagged `Sum.inl`, and here that is the `j`
   argument). -/
theorem incidenceProd_incidenceSum_distrib_glue_inr_inl_lhs_eq
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i3 : I3) (j2 : I2) :
    (incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, Sum.inr i3) (j1, Sum.inl j2) =
      if j2 = inc2.unit then (inc1.glue i1 j1).map (fun k1 => (k1, Sum.inr i3)) else none := by
  simp only [incidenceProd, prodGlue, incidenceSum_glue_cross_right inc2 inc3 i3 j2]
  by_cases h : j2 = inc2.unit
  · subst h
    rcases inc1.glue i1 j1 with _ | k1 <;> simp
  · simp [h]

theorem incidenceSum_incidenceProd_distrib_glue_inr_inl_rhs_eq
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i3 : I3) (j2 : I2) :
    (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
      (Sum.inr (i1, i3)) (Sum.inl (j1, j2)) =
      if j1 = inc1.unit ∧ j2 = inc2.unit then some (Sum.inr (i1, i3)) else none := by
  rw [incidenceSum_glue_cross_right (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)
    (i1, i3) (j1, j2)]
  simp [incidenceProd, Prod.ext_iff]

theorem incidenceProd_incidenceSum_distrib_glue_lhs_some_rhs_none_iff_inr_inl
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (i3 : I3) (j2 : I2) :
    ((∃ v, (incidenceProd inc1 (incidenceSum inc2 inc3)).glue
        (i1, Sum.inr i3) (j1, Sum.inl j2) = some v) ∧
     (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
       (Sum.inr (i1, i3)) (Sum.inl (j1, j2)) = none)
    ↔ j2 = inc2.unit ∧ j1 ≠ inc1.unit ∧ ∃ k1, inc1.glue i1 j1 = some k1 := by
  rw [incidenceProd_incidenceSum_distrib_glue_inr_inl_lhs_eq inc1 inc2 inc3 i1 j1 i3 j2,
    incidenceSum_incidenceProd_distrib_glue_inr_inl_rhs_eq inc1 inc2 inc3 i1 j1 i3 j2]
  constructor
  · rintro ⟨⟨v, hv⟩, hnone⟩
    by_cases h2 : j2 = inc2.unit
    · refine ⟨h2, ?_, ?_⟩
      · intro h1
        rw [if_pos ⟨h1, h2⟩] at hnone
        exact absurd hnone (by simp)
      · rcases hk1 : inc1.glue i1 j1 with _ | k1
        · rw [if_pos h2, hk1] at hv
          exact absurd hv (by simp)
        · exact ⟨k1, rfl⟩
    · rw [if_neg h2] at hv
      exact absurd hv (by simp)
  · rintro ⟨h2, h1, k1, hk1⟩
    refine ⟨⟨(k1, Sum.inr i3), ?_⟩, ?_⟩
    · rw [if_pos h2, hk1]; rfl
    · rw [if_neg (fun h => h1 h.1)]

/- The master theorem: combines all four tag combinations into one clean
   `iff`, fully answering cycle 48's queued converse question. The
   same-side cases contribute nothing (shown impossible via the `_eq`
   lemmas above), so the only way "LHS some, RHS none" can happen at all
   is one of the two cross-side conditions above. -/
theorem incidenceProd_incidenceSum_distrib_glue_lhs_some_rhs_none_iff
    {I1 R1 T1 I2 R2 T2 I3 R3 T3 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq I3]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) (inc3 : Incidence I3 R3 T3)
    (i1 j1 : I1) (x y : I2 ⊕ I3) :
    ((∃ v, (incidenceProd inc1 (incidenceSum inc2 inc3)).glue (i1, x) (j1, y) = some v) ∧
     (incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)).glue
       (prodSumDistribForward (i1, x)) (prodSumDistribForward (j1, y)) = none)
    ↔ (∃ i2 j3, x = Sum.inl i2 ∧ y = Sum.inr j3 ∧
         i2 = inc2.unit ∧ i1 ≠ inc1.unit ∧ ∃ k1, inc1.glue i1 j1 = some k1) ∨
       (∃ i3 j2, x = Sum.inr i3 ∧ y = Sum.inl j2 ∧
         j2 = inc2.unit ∧ j1 ≠ inc1.unit ∧ ∃ k1, inc1.glue i1 j1 = some k1) := by
  cases x with
  | inl i2 =>
    cases y with
    | inl j2 =>
      constructor
      · rintro ⟨⟨v, hv⟩, hnone⟩
        have heq := incidenceProd_incidenceSum_distrib_glue_inl_inl_eq inc1 inc2 inc3 i1 j1 i2 j2
        simp only [prodSumDistribForward] at hnone
        rw [hv, hnone] at heq
        simp at heq
      · rintro (⟨_, _, _, hy, _⟩ | ⟨_, _, hx, _⟩)
        · exact absurd hy (by simp)
        · exact absurd hx (by simp)
    | inr j3 =>
      simp only [prodSumDistribForward]
      rw [incidenceProd_incidenceSum_distrib_glue_lhs_some_rhs_none_iff_inl_inr
        inc1 inc2 inc3 i1 j1 i2 j3]
      constructor
      · intro h
        exact Or.inl ⟨i2, j3, rfl, rfl, h⟩
      · rintro (⟨i2', j3', hi2, hj3, h⟩ | ⟨_, _, hx, _⟩)
        · rw [Sum.inl.injEq] at hi2
          rw [Sum.inr.injEq] at hj3
          subst hi2
          subst hj3
          exact h
        · exact absurd hx (by simp)
  | inr i3 =>
    cases y with
    | inl j2 =>
      simp only [prodSumDistribForward]
      rw [incidenceProd_incidenceSum_distrib_glue_lhs_some_rhs_none_iff_inr_inl
        inc1 inc2 inc3 i1 j1 i3 j2]
      constructor
      · intro h
        exact Or.inr ⟨i3, j2, rfl, rfl, h⟩
      · rintro (⟨_, _, hx, _⟩ | ⟨i3', j2', hi3, hj2, h⟩)
        · exact absurd hx (by simp)
        · rw [Sum.inr.injEq] at hi3
          rw [Sum.inl.injEq] at hj2
          subst hi3
          subst hj2
          exact h
    | inr j3 =>
      constructor
      · rintro ⟨⟨v, hv⟩, hnone⟩
        have heq := incidenceProd_incidenceSum_distrib_glue_inr_inr_eq inc1 inc2 inc3 i1 j1 i3 j3
        simp only [prodSumDistribForward] at hnone
        rw [hv, hnone] at heq
        simp at heq
      · rintro (⟨_, _, hx, _⟩ | ⟨_, _, _, hy, _⟩)
        · exact absurd hx (by simp)
        · exact absurd hy (by simp)

end IncidenceCore
