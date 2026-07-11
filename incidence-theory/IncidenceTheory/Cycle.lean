import IncidenceTheory.GraphModel

/- Merkle-ID: implementation.graph_model.cycle
   story.jsonnet → implementation.nodes.cycle
   Research cycle 26 (see RESEARCH_LOG.md): every prior instance
   (`natIncidence`, `pairIncidenceChained`, `pathIncidenceChained`,
   `simplexIncidence`) is fundamentally *acyclic* -- a well-founded chain
   or a finite tree/simplex with at least one empty-boundary leaf. This
   file tests a genuinely different shape: a closed 4-cycle, `c0 → c3 →
   c2 → c1 → c0`, where *every* element has exactly one boundary entry
   and *none* has an empty one. `Incidence`'s own `well_founded` field
   (`∀ i, ¬∃ e ∈ boundary i, e.i = i`) only forbids a *direct* self-loop,
   not a longer cycle, so this is a legitimate, buildable instance, not
   a workaround.

   Two things this instance is built to test that no prior instance
   could: (1) does the "flat leaves collapse" pattern (cycles 2/12/13/18
   -- multiple elements sharing *identical* boundary structure become
   `≈`-related) generalize beyond *shared emptiness* specifically, to
   *any* uniform boundary shape lacking a well-founded anchor? (2) `glue`
   here is genuine `Z/4Z` addition -- the first *group*-structured `glue`
   in this project (commutative, every element invertible), unlike
   `natIncidence`'s infinite monoid or the left-biased *non-group*
   selection every other instance used. -/

namespace IncidenceCore

inductive CycleRole where | chain
deriving DecidableEq, Repr

inductive CycleId where | c0 | c1 | c2 | c3
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.cycle.boundary
   Every element points to its cyclic predecessor -- no base case,
   unlike every prior chain-shaped instance. -/
def cyclePred : CycleId → CycleId
  | .c0 => .c3
  | .c1 => .c0
  | .c2 => .c1
  | .c3 => .c2

def cycleBoundary : CycleId → Boundary CycleId CycleRole
  | ci => [{ i := cyclePred ci, role := CycleRole.chain, sign := Sign.neg, mult := 1 }]

def cycleToNat : CycleId → Nat
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3

def cycleOfNat : Nat → CycleId
  | 0 => .c0 | 1 => .c1 | 2 => .c2 | _ => .c3

/- `Z/4Z` addition -- a genuine finite group, the first `glue` in this
   project with inverses (see `cycleIncidence_glue_has_inverse` below). -/
def cycleAdd (x y : CycleId) : CycleId := cycleOfNat ((cycleToNat x + cycleToNat y) % 4)

def cycleIncidence : Incidence CycleId CycleRole GraphType where
  boundary := cycleBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => some (cycleAdd i j)
  unit     := CycleId.c0
  guards   := Guards.permissive CycleId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [cycleBoundary] at h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i <;> simp [cycleBoundary] at h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [cycleBoundary, cyclePred] at he <;> subst he <;> simp_all
  unit_left := by intro i; cases i <;> simp [cycleAdd, cycleToNat, cycleOfNat]
  unit_right := by intro i; cases i <;> simp [cycleAdd, cycleToNat, cycleOfNat]
  type_preserve := fun _ _ => rfl

def cycleIdx : List CycleId := [CycleId.c0, CycleId.c1, CycleId.c2, CycleId.c3]

/- ∂² still fails here, exactly as `single_link_composition_ne_zero`
   (cycle 9) predicts for any single-link chain -- the general theorem
   applies "for free" to a cyclic instance too, not just linear ones
   (`natIncidence`, `pathIncidenceChained`'s nodes, `pairIncidenceChained`'s
   atoms). Not a new phenomenon, but worth confirming the theorem's
   reach isn't accidentally tied to acyclicity. -/
theorem cycleIncidence_c0_composition_ne_zero (idx : List CycleId) (hmem : CycleId.c3 ∈ idx) :
  boundary_composition cycleIncidence idx CycleId.c0 CycleId.c2 ≠ 0 :=
  single_link_composition_ne_zero cycleIncidence idx CycleId.c0 CycleId.c3 CycleId.c2
    { i := CycleId.c3, role := CycleRole.chain, sign := Sign.neg, mult := 1 }
    { i := CycleId.c2, role := CycleRole.chain, sign := Sign.neg, mult := 1 }
    rfl rfl (by simp)
    rfl rfl (by simp)
    hmem

theorem cycleIncidence_not_boundary_square_zero :
  verify_boundary_composition cycleIncidence cycleIdx = false := by decide

/- The genuinely new finding: the SAME "everything related to
   everything" relation cycles 2/12/13/18 used to collapse elements
   sharing *empty* boundary also witnesses a bisimulation here, where
   *no* element has empty boundary at all -- every element's single
   boundary entry has an identical shape (`chain`, `neg`, `1`), and that
   uniformity alone is enough: `boundaryMatched` only needs *some*
   compatible, related counterpart to exist, and the fully-related
   relation trivially supplies one regardless of which specific element
   it is. The "flat leaves collapse" pattern was never really about
   *emptiness* -- it's about *lacking a well-founded, distinguishing
   measure*, and a uniform cycle is a second, structurally different way
   to lack one. -/
theorem cycleIncidence_isBisimulation_full : IsBisimulation cycleIncidence (fun _ _ => True) := by
  intro i j _
  refine ⟨rfl, ?_, ?_⟩
  · intro e he
    cases i <;> simp [cycleIncidence, cycleBoundary] at he <;> subst he <;>
      exact ⟨{ i := cyclePred j, role := CycleRole.chain, sign := Sign.neg, mult := 1 },
        by simp [cycleIncidence, cycleBoundary], ⟨rfl, rfl, rfl⟩, trivial⟩
  · intro e he
    cases j <;> simp [cycleIncidence, cycleBoundary] at he <;> subst he <;>
      exact ⟨{ i := cyclePred i, role := CycleRole.chain, sign := Sign.neg, mult := 1 },
        by simp [cycleIncidence, cycleBoundary], ⟨rfl, rfl, rfl⟩, trivial⟩

/- ALL FOUR elements collapse into a single `≈`-class -- not merely
   "some pair", the strongest form of this pattern seen yet, since
   there's no substructure here at all (unlike `simplexIncidence`, where
   vertices/edges/face stayed separated by differing boundary shapes). -/
theorem cycleIncidence_all_collapse (x y : CycleId) : approxBisim cycleIncidence x y :=
  ⟨fun _ _ => True, cycleIncidence_isBisimulation_full, trivial⟩

theorem cycleIncidence_c0_ne_c1 : (CycleId.c0 : CycleId) ≠ CycleId.c1 := by simp

theorem cycleIncidence_not_bisimulationFaithful :
    ¬ CompletenessTheory.BisimulationFaithful cycleIncidence := by
  intro faithful
  exact cycleIncidence_c0_ne_c1
    (faithful (cycleIncidence_all_collapse CycleId.c0 CycleId.c1))

theorem cycleIncidence_complete_language_has_unsoundness_witness
    (language : CompletenessTheory.LinearObservationLanguage
      cycleIncidence cycleIdx)
    (complete : CompletenessTheory.ContainsLinearIndicators
      cycleIncidence cycleIdx language) :
    ∃ i j : CycleId, approxBisim cycleIncidence i j ∧
      ∃ observation, language observation ∧
        (observation.boundary_matrix i ≠ observation.boundary_matrix j ∨
         observation.laplacian i ≠ observation.laplacian j) :=
  CompletenessTheory.nonfaithful_has_bisimilar_observational_counterexample
    cycleIncidence cycleIdx language complete
      cycleIncidence_not_bisimulationFaithful

theorem incidence_axioms_do_not_force_bisimulation_extensionality :
    ¬ (∀ inc : Incidence CycleId CycleRole GraphType,
      ∀ first second : CycleId,
        approxBisim inc first second → first = second) := by
  intro forcesExtensionality
  exact cycleIncidence_c0_ne_c1
    (forcesExtensionality cycleIncidence .c0 .c1
      (cycleIncidence_all_collapse .c0 .c1))

/- `glue` is commutative (`Z/4Z` addition) -- checked as a `decide`,
   the same way `natIncidence`'s commutativity was checked in cycle 1. -/
theorem cycleIncidence_glue_comm (x y : CycleId) :
  cycleIncidence.glue x y = cycleIncidence.glue y x := by
  cases x <;> cases y <;> decide

/- The genuinely new algebraic property: every element has an inverse
   (sums to `unit = c0`) -- no prior `glue` in this project had this
   (`natIncidence`'s addition has no inverses in `Nat`; every other
   instance's `glue` was left-biased selection, not a group operation at
   all). -/
theorem cycleIncidence_glue_has_inverse (x : CycleId) :
  ∃ y, cycleIncidence.glue x y = some CycleId.c0 := by
  cases x
  · exact ⟨CycleId.c0, by decide⟩
  · exact ⟨CycleId.c3, by decide⟩
  · exact ⟨CycleId.c2, by decide⟩
  · exact ⟨CycleId.c1, by decide⟩

/- Research cycle 27 (see RESEARCH_LOG.md): does `cycleIncidence` admit a
   faithfulness-recovering "fixed" variant, the way `pairIncidence` →
   `pairIncidenceChained` (cycle 3) and `pathIncidence` →
   `pathIncidenceChained` (cycle 14) did? The established fix
   (cycles 3/13/14) was "give elements a well-founded distinguishing
   predecessor chain reaching a base case" -- but a *cycle* has no base
   case at all, so that fix doesn't directly transplant. This tests a
   genuinely different mechanism instead: give each of the four
   positions its *own*, structurally distinct `role`, rather than
   reusing one uniform role everywhere. -/
inductive CycleRoleFixed where | r0 | r1 | r2 | r3
deriving DecidableEq, Repr

def cycleRoleOf : CycleId → CycleRoleFixed
  | .c0 => .r0 | .c1 => .r1 | .c2 => .r2 | .c3 => .r3

def cycleBoundaryFixed : CycleId → Boundary CycleId CycleRoleFixed
  | ci => [{ i := cyclePred ci, role := cycleRoleOf ci, sign := Sign.neg, mult := 1 }]

def cycleIncidenceFixed : Incidence CycleId CycleRoleFixed GraphType where
  boundary := cycleBoundaryFixed
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => some (cycleAdd i j)
  unit     := CycleId.c0
  guards   := Guards.permissive CycleId
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i <;> simp [cycleBoundaryFixed] at h <;> subst h <;> simp
  multiplicities := by
    intro i e h
    cases i <;> simp [cycleBoundaryFixed] at h <;> subst h <;> simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i <;> simp [cycleBoundaryFixed, cyclePred] at he <;> subst he <;> simp_all
  unit_left := by intro i; cases i <;> simp [cycleAdd, cycleToNat, cycleOfNat]
  unit_right := by intro i; cases i <;> simp [cycleAdd, cycleToNat, cycleOfNat]
  type_preserve := fun _ _ => rfl

/- The fix works, but via a **genuinely new proof route**: not
   `incidence_bisim_faithful` (cycle 4, which needs a well-founded
   *measure* -- something a closed cycle structurally cannot have,
   since nothing ever "decreases" around a loop) but
   `not_approxBisim_of_boundary_mismatch` (cycle 21) directly. Distinct
   elements' boundary entries now carry *distinct* roles
   (`cycleRoleOf` is injective by construction), so no relation can ever
   match them -- faithfulness follows from role-discrimination alone,
   with no induction and no measure needed at all. Every ordinary role
   in every other instance in this project only ever needed 1-3
   constructors; this is the first fix whose entire mechanism *is* the
   role type's cardinality matching the carrier's. -/
theorem cycleIncidenceFixed_not_bisim_of_ne (x y : CycleId) (hne : x ≠ y) :
  ¬ approxBisim cycleIncidenceFixed x y := by
  apply not_approxBisim_of_boundary_mismatch cycleIncidenceFixed x y
    { i := cyclePred x, role := cycleRoleOf x, sign := Sign.neg, mult := 1 }
    (by simp [cycleIncidenceFixed, cycleBoundaryFixed])
  intro e' he'
  cases y <;> simp [cycleIncidenceFixed, cycleBoundaryFixed] at he' <;> subst he' <;>
    cases x <;> simp_all [boundaryCompatible, cycleRoleOf]

/- Full faithfulness (`≈ ↔ =`), proved via role-discrimination rather
   than well-founded induction -- and, notably, with only `propext`, no
   `Classical.choice` at all (checked, not assumed): a genuinely
   constructive alternative to the well-founded-measure route for
   instances where no such measure can exist. -/
theorem cycleIncidenceFixed_approxBisim_iff (x y : CycleId) :
  approxBisim cycleIncidenceFixed x y ↔ x = y := by
  constructor
  · intro h
    by_cases hne : x = y
    · exact hne
    · exact absurd h (cycleIncidenceFixed_not_bisim_of_ne x y hne)
  · intro h
    subst h
    exact approxBisim_refl cycleIncidenceFixed x


def cycleIdxFixed : List CycleId := [CycleId.c0, CycleId.c1, CycleId.c2, CycleId.c3]

theorem cycleIncidenceFixed_bisimulationFaithful :
    CompletenessTheory.BisimulationFaithful cycleIncidenceFixed := by
  intro x y bisimilar
  exact (cycleIncidenceFixed_approxBisim_iff x y).mp bisimilar

theorem cycleIncidenceFixed_complete_language_sound
    (language : CompletenessTheory.LinearObservationLanguage
      cycleIncidenceFixed cycleIdxFixed)
    (complete : CompletenessTheory.ContainsLinearIndicators
      cycleIncidenceFixed cycleIdxFixed language) :
    CompletenessTheory.CompleteLanguageBisimulationSound
      cycleIncidenceFixed cycleIdxFixed language :=
  (CompletenessTheory.complete_language_bisimulation_sound_iff_faithful
    cycleIncidenceFixed cycleIdxFixed language complete).mpr
      cycleIncidenceFixed_bisimulationFaithful

theorem cycleIncidenceFixed_complete_observational_iff_bisimulation
    (language : CompletenessTheory.LinearObservationLanguage
      cycleIncidenceFixed cycleIdxFixed)
    (complete : CompletenessTheory.ContainsLinearIndicators
      cycleIncidenceFixed cycleIdxFixed language)
    (x y : CycleId) :
    CompletenessTheory.AgreeOnLinearObservationLanguage
        cycleIncidenceFixed cycleIdxFixed language x y ↔
      approxBisim cycleIncidenceFixed x y :=
  CompletenessTheory.complete_language_observational_iff_bisimulation_of_faithful
    cycleIncidenceFixed cycleIdxFixed language complete
      cycleIncidenceFixed_bisimulationFaithful x y

def cycleIncidenceFixed_completeLanguageQuotientEquivalence
    (language : CompletenessTheory.LinearObservationLanguage
      cycleIncidenceFixed cycleIdxFixed)
    (complete : CompletenessTheory.ContainsLinearIndicators
      cycleIncidenceFixed cycleIdxFixed language) :
    IncTypeEquivalence
      (CompletenessTheory.LanguageObservationQuotient
        cycleIncidenceFixed cycleIdxFixed language complete)
      (IncidenceQuotient cycleIncidenceFixed) :=
  CompletenessTheory.completeLanguageBisimulationQuotientEquivalence
    cycleIncidenceFixed cycleIdxFixed language complete
      cycleIncidenceFixed_bisimulationFaithful

def cycleToFixedBoundaryShapeEquivalence :
    TranslationPreservation.BoundaryShapeEquivalence
      cycleIncidence cycleIncidenceFixed :=
  TranslationPreservation.boundaryShapeEquivalenceOfCodeEquivalence
    (IncTypeEquivalence.refl CycleId) (by
      intro i
      cases i <;> rfl)

theorem boundaryShapeEquivalence_does_not_preserve_bisimulation :
    ¬ (∀ {I J R₁ T₁ R₂ T₂ : Type}
      [DecidableEq I] [DecidableEq J]
      (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
      (equivalence : TranslationPreservation.BoundaryShapeEquivalence
        source target) {i j : I},
      approxBisim source i j →
        approxBisim target (equivalence.hom.map i) (equivalence.hom.map j)) := by
  intro universallyPreserves
  have fixedBisimilar := universallyPreserves cycleIncidence cycleIncidenceFixed
    cycleToFixedBoundaryShapeEquivalence
    (cycleIncidence_all_collapse CycleId.c0 CycleId.c1)
  exact cycleIncidenceFixed_not_bisim_of_ne CycleId.c0 CycleId.c1
    cycleIncidence_c0_ne_c1 fixedBisimilar

theorem cycleIncidenceFixed_not_boundary_square_zero :
  verify_boundary_composition cycleIncidenceFixed cycleIdxFixed = false := by decide

/- The predicted price, confirmed a fourth time (after `natIncidence`/
   `pairIncidenceChained`, cycle 8; `pathIncidenceChained`, cycle 16):
   the faithfulness fix breaks `∂² = 0` here too -- via the *same*
   general theorem (`single_link_composition_ne_zero`, cycle 9), which
   never cared about roles, only about the single-link *shape*. This
   sharpens the tension further: it isn't specific to "chain reaching a
   base case" fixes -- ANY fix keeping the single-link shape pays the
   same price, regardless of how the distinguishing information is
   encoded (a predecessor chain, or unique role tags on a closed
   cycle). -/
theorem cycleIncidenceFixed_c0_composition_ne_zero (idx : List CycleId) (hmem : CycleId.c3 ∈ idx) :
  boundary_composition cycleIncidenceFixed idx CycleId.c0 CycleId.c2 ≠ 0 :=
  single_link_composition_ne_zero cycleIncidenceFixed idx CycleId.c0 CycleId.c3 CycleId.c2
    { i := CycleId.c3, role := cycleRoleOf CycleId.c0, sign := Sign.neg, mult := 1 }
    { i := CycleId.c2, role := cycleRoleOf CycleId.c3, sign := Sign.neg, mult := 1 }
    rfl rfl (by simp)
    rfl rfl (by simp)
    hmem

/- Research cycle 28 (see RESEARCH_LOG.md): every prior T5 translation
   (`natToFiniteSet`/`pairToShape`/`pathToNatBool`) only ever needed
   *injectivity* -- none of their targets, and none of the source
   `glue`s (an infinite monoid, or non-group left-biased selection), had
   algebraic structure worth checking a translation against. `Z/4Z`
   (cycle 26) is different: it's the first *invertible* `glue` in this
   project. Does `cycleToNat` (already used internally to define
   `cycleAdd`) also happen to be a genuine `glue`-*homomorphism* into
   `(Nat, (· + ·) % 4)`, not just an injective map? Checked empirically
   first (`#eval`, all 16 pairs `(m, n) ∈ {0..3}²`): every pair agrees.
   Unsurprising once stated -- `cycleAdd` was *defined* via exactly this
   formula wrapped in `cycleOfNat`/`cycleToNat` -- but worth confirming
   as a real theorem, not just trusting the definition's shape by eye. -/
theorem cycleToNat_glue_hom (x y : CycleId) :
  cycleToNat (cycleAdd x y) = (cycleToNat x + cycleToNat y) % 4 := by
  cases x <;> cases y <;> decide

theorem cycleToNat_unit_natural : cycleToNat cycleIncidenceFixed.unit = 0 := by decide

theorem cycleToNat_injective {x y : CycleId} (h : cycleToNat x = cycleToNat y) : x = y := by
  cases x <;> cases y <;> simp_all [cycleToNat]

/- The standard T5 pattern (cycle 5's recipe, applied to `cycleIncidenceFixed`
   since it -- unlike the unfixed `cycleIncidence`, where this would be
   vacuous -- is genuinely `≈`-faithful, cycle 27): injectivity plus the
   instance's own faithfulness theorem gives translation-reflects-`≈`.
   Combined with `cycleToNat_glue_hom`/`_unit_natural` above, `cycleToNat`
   is the *first* translation in this project that is simultaneously a
   faithful reflector of `≈` AND a genuine algebraic homomorphism --
   `cycleIncidenceFixed`'s `glue` structure is literally isomorphic to
   `Z/4Z`, with `cycleToNat` as the explicit witness (bijective, since
   `cycleOfNat` is its two-sided inverse by construction, and a
   homomorphism, per the theorems above). -/
theorem cycleToNat_reflects_approxBisim {x y : CycleId}
  (h : cycleToNat x = cycleToNat y) : approxBisim cycleIncidenceFixed x y := by
  rw [cycleIncidenceFixed_approxBisim_iff]
  exact cycleToNat_injective h

end IncidenceCore
