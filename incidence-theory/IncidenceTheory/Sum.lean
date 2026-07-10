import IncidenceTheory.Peano

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

def sumBoundary {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
  (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
  (I1 ⊕ I2) → Boundary (I1 ⊕ I2) (R1 ⊕ R2)
  | Sum.inl i1 =>
    (inc1.boundary i1).map (fun e =>
      ({ i := Sum.inl e.i, role := Sum.inl e.role, sign := e.sign, mult := e.mult } :
        Endpoint (I1 ⊕ I2) (R1 ⊕ R2)))
  | Sum.inr i2 =>
    (inc2.boundary i2).map (fun e =>
      ({ i := Sum.inr e.i, role := Sum.inr e.role, sign := e.sign, mult := e.mult } :
        Endpoint (I1 ⊕ I2) (R1 ⊕ R2)))

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
      simp at hei
      exact inc1.well_founded i1 ⟨e1, he1, hei⟩
    | inr i2 =>
      simp only [sumBoundary, List.mem_map] at he
      obtain ⟨e2, he2, heq⟩ := he
      subst heq
      simp at hei
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

end IncidenceCore
