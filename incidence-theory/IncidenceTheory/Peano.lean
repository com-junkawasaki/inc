import IncidenceTheory.GraphModel

/- Merkle-ID: implementation.graph_model.peano
   story.jsonnet → implementation.nodes.peano
   Peano naturals realized as a concrete `Incidence` instance: `glue` is
   addition (`unit = 0` is glue's two-sided identity, as required by
   `Incidence.unit_left`/`unit_right`), and `boundary n` for `n > 0`
   points to its predecessor `n - 1` (a directed chain 0 → 1 → 2 → ...,
   independent of `glue`, in the same spirit as `triIncidence`'s edges).

   This demonstrates that Inc's primitive vocabulary (`boundary`, `glue`,
   `≈`) is expressive enough to state and prove Peano's axioms and the
   induction principle for a concrete instance, and that Inc's abstract
   bisimulation-equivalence `≈` does not collapse distinct naturals
   (faithfulness).

   Scope: this is one concrete instance, not a general construction
   internal to arbitrary incidences, and it does not attempt sets,
   category theory, or type theory internal to Inc -- those are separate,
   much larger undertakings this file does not claim to address. -/

namespace IncidenceCore

inductive PeanoRole where | pred
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.peano.boundary
   n's boundary points to its predecessor; 0 has no predecessor. -/
def peanoBoundary : Nat → Boundary Nat PeanoRole
  | 0 => []
  | n + 1 => [{ i := n, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }]

/- Merkle-ID: implementation.graph_model.peano.incidence
   Peano naturals as an Incidence: glue = addition, unit = 0. -/
def natIncidence : Incidence Nat PeanoRole GraphType where
  boundary := peanoBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => some (i + j)
  unit     := 0
  guards   := Guards.permissive Nat
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i with
    | zero => simp [peanoBoundary] at h
    | succ n => simp [peanoBoundary] at h; subst h; simp
  multiplicities := by
    intro i e h
    cases i with
    | zero => simp [peanoBoundary] at h
    | succ n => simp [peanoBoundary] at h; subst h; simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i with
    | zero => simp [peanoBoundary] at he
    | succ n =>
      simp [peanoBoundary] at he
      subst he
      simp_all
  unit_left := by intro i; simp
  unit_right := by intro i; simp
  type_preserve := fun _ _ => rfl

noncomputable def natCountablyPresentedIncidence :
    CountablyPresentedIncidence Nat PeanoRole GraphType where
  incidence := natIncidence
  atoms := {
    decode := id
    code := id
    decode_code := fun _ => rfl
  }

theorem natIncidence_internalLogic_complete
    (context : List (Formula Nat)) (formula : Formula Nat) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  natCountablyPresentedIncidence.internalLogic_complete context formula

theorem natIncidence_internalLogic_consistent_iff_model
    (context : List (Formula Nat)) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  natCountablyPresentedIncidence.internalLogic_consistent_iff_model context

theorem natIncidence_boundaryValuation_iff (n : Nat) :
    IncidenceBoundaryValuation natIncidence n ↔ n ≠ 0 := by
  cases n with
  | zero => simp [IncidenceBoundaryValuation, natIncidence, peanoBoundary]
  | succ n => simp [IncidenceBoundaryValuation, natIncidence, peanoBoundary]

theorem natIncidence_boundarySatisfies_atom_iff (n : Nat) :
    IncidenceBoundarySatisfies natIncidence (.atom n) ↔ n ≠ 0 := by
  exact natIncidence_boundaryValuation_iff n

theorem natIncidence_boundarySatisfies_zero_negation :
    IncidenceBoundarySatisfies natIncidence (Formula.neg (.atom 0)) := by
  intro holds
  exact (natIncidence_boundaryValuation_iff 0).mp holds rfl

/- glue-with-1 realizes the successor function. -/
theorem natIncidence_succ (n : Nat) : natIncidence.glue n 1 = some (n + 1) := rfl

/- Peano axiom: successor is injective. -/
theorem natIncidence_succ_injective {m n : Nat}
  (h : natIncidence.glue m 1 = natIncidence.glue n 1) : m = n := by
  simp [natIncidence] at h
  omega

/- Peano axiom: zero is not a successor. -/
theorem natIncidence_zero_ne_succ (n : Nat) :
  natIncidence.glue n 1 ≠ some natIncidence.unit := by
  simp [natIncidence]

/- Induction principle, stated purely in terms of Inc's `unit`/`glue`
   vocabulary (not raw `Nat.zero`/`Nat.succ`). -/
theorem natIncidence_induction (P : Nat → Prop)
  (hzero : P natIncidence.unit)
  (hsucc : ∀ n, P n → ∀ n', natIncidence.glue n 1 = some n' → P n') :
  ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ k ih => exact hsucc k ih (k + 1) rfl

/- The substantive hypothesis of the general `incidence_bisim_faithful`
   theorem (root file, cycle 4): elements with literally-equal,
   role-matched boundaries are equal. For natIncidence this says a
   bisimulation can't relate a zero-boundary element to a nonempty one,
   and matching predecessors (by literal equality, not just `rel`)
   forces the indices to match. -/
theorem natIncidence_hext :
  ∀ x y, natIncidence.typeFunc x = natIncidence.typeFunc y →
    boundaryMatched natIncidence (· = ·) x y → x = y := by
  intro x y _ ⟨hL, hR⟩
  cases x with
  | zero =>
    cases y with
    | zero => rfl
    | succ k =>
      exfalso
      obtain ⟨e, he, -⟩ := hR { i := k, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
        (by simp [natIncidence, peanoBoundary])
      simp [natIncidence, peanoBoundary] at he
  | succ n =>
    cases y with
    | zero =>
      exfalso
      obtain ⟨e, he, -⟩ := hL { i := n, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
        (by simp [natIncidence, peanoBoundary])
      simp [natIncidence, peanoBoundary] at he
    | succ k =>
      obtain ⟨e', he', -, heq⟩ := hL { i := n, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
        (by simp [natIncidence, peanoBoundary])
      simp [natIncidence, peanoBoundary] at he'
      subst he'
      simp at heq
      omega

theorem natIncidence_hdec :
  ∀ i e, e ∈ natIncidence.boundary i → e.i < i := by
  intro i e h
  cases i with
  | zero => simp [natIncidence, peanoBoundary] at h
  | succ k => simp [natIncidence, peanoBoundary] at h; subst h; simp

/- Faithfulness: Inc's abstract bisimulation-equivalence ≈ does not
   collapse distinct naturals -- it coincides exactly with `=`.
   Derived from the general theorem rather than a bespoke induction
   (compare cycle 1-3's hand-rolled version, no longer needed). -/
theorem natIncidence_approxBisim_iff (m n : Nat) :
  approxBisim natIncidence m n ↔ m = n := by
  constructor
  · rintro ⟨rel, hbisim, hmn⟩
    exact incidence_bisim_faithful natIncidence id natIncidence_hdec natIncidence_hext
      hbisim m n hmn
  · intro h; subst h; exact approxBisim_refl natIncidence m

theorem incidence_axioms_satisfiable :
    Nonempty (Incidence Nat PeanoRole GraphType) :=
  ⟨natIncidence⟩

theorem incidence_axioms_have_nontrivial_model :
    ∃ inc : Incidence Nat PeanoRole GraphType,
      ∃ first second : Nat,
        first ≠ second ∧ ¬ approxBisim inc first second := by
  refine ⟨natIncidence, 0, 1, Nat.zero_ne_add_one 0, ?_⟩
  intro bisimilar
  have equal := (natIncidence_approxBisim_iff 0 1).mp bisimilar
  exact Nat.zero_ne_add_one 0 equal

theorem incidence_axioms_do_not_semantically_entail_false :
    ¬ (∀ _inc : Incidence Nat PeanoRole GraphType, False) := by
  intro entailsFalse
  exact entailsFalse natIncidence

theorem incidence_axioms_do_not_force_bisimulation_collapse :
    ¬ (∀ inc : Incidence Nat PeanoRole GraphType,
      ∀ first second : Nat, approxBisim inc first second) := by
  intro forcesCollapse
  have collapsed := forcesCollapse natIncidence 0 1
  have equal := (natIncidence_approxBisim_iff 0 1).mp collapsed
  exact Nat.zero_ne_add_one 0 equal

/- Research cycle 1 (co-scientist step): does the same GluingSpec
   abstraction used for triIncidence (left-biased, non-commutative glue)
   also fit a genuinely commutative-monoid instance? Hypothesis: yes --
   natIncidence's glue-as-addition is commutative and satisfies
   GluingSpec's guarded associativity, exercising the abstraction across
   two structurally different concrete incidences. -/
theorem natIncidence_glue_comm (i j : Nat) :
  natIncidence.glue i j = natIncidence.glue j i := by
  simp [natIncidence, Nat.add_comm]

/- Merkle-ID: implementation.graph_model.peano.gluing_spec
   GluingSpec instance for natIncidence (permissive guards; addition). -/
def natGluingSpec : GluingSpec natIncidence :=
  { unit_ok := by
      intro i
      exact ⟨by simp [natIncidence], by simp [natIncidence]⟩
  , type_preserve := by intro i j k _ _; rfl
  , assoc_when_ok := by
      intro i j k ij ijk jk _ h2 _ h4 _ h6 _
      simp [natIncidence] at h2 h4 h6 ⊢
      omega
  }

/- Research cycle 5 (co-scientist step, see RESEARCH_LOG.md): T5
   ("translation preserves structure") was never given real content in
   this repo -- `TranslationPreservation.inc_to_set` (root file) maps
   every element to one of just two trivial types (`ULift Bool`/`ULift
   Unit`) based only on whether `boundary` is empty, collapsing all of
   `natIncidence`'s nonzero elements together. This is a concrete,
   *better* translation to a Set-like target (`List Unit`, built by the
   same recursion `peanoBoundary` uses: `n+1` recurses on `n`) that
   doesn't collapse anything -- it's injective, hence (combined with
   cycle 4's faithfulness theorem) reflects `≈` faithfully rather than
   erasing it. Elementary (no `Fintype`/`Equiv`, unavailable without
   mathlib) but honest: this is what T5 "soundness of translation"
   should actually mean for a concrete instance, demonstrated rather
   than asserted. -/
def natToFiniteSet : Nat → List Unit
  | 0 => []
  | n + 1 => () :: natToFiniteSet n

theorem natToFiniteSet_length (n : Nat) : (natToFiniteSet n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [natToFiniteSet, ih]

theorem natToFiniteSet_injective {m n : Nat} (h : natToFiniteSet m = natToFiniteSet n) :
  m = n := by
  have hlen := congrArg List.length h
  rwa [natToFiniteSet_length, natToFiniteSet_length] at hlen

/- T5, concretely: the translation doesn't lose information relevant to
   `≈` -- agreeing translations imply bisimilar (indeed equal)
   originals. -/
theorem natToFiniteSet_reflects_approxBisim {m n : Nat}
  (h : natToFiniteSet m = natToFiniteSet n) : approxBisim natIncidence m n := by
  rw [natIncidence_approxBisim_iff]
  exact natToFiniteSet_injective h

/- Research cycle 8 (see RESEARCH_LOG.md): T3's `boundary_operator_square_zero`
   (root file) was only ever exercised against the triangle graph, where
   it holds (`triangle_boundary_square_zero`). Hypothesis going in:
   either this trivially holds for any well-founded structure, or it's
   uninteresting for a chain. Checked empirically first (`#eval`) before
   assuming either -- neither guess was right. `natIncidence`'s chain
   *fails* ∂² = 0, genuinely and non-trivially: `boundary_composition
   natIncidence idx 2 0 = 1 ≠ 0`. Root cause, once found: the triangle's
   boundary only reaches *nodes*, which have no further boundary of
   their own (a 2-graded structure: dimension 1 → dimension 0 → nothing),
   so ∂² vanishes for the trivial reason that there's nothing beyond
   dimension 0 to compose into. `natIncidence`'s chain has *unbounded*
   depth (`boundary n` reaches `n-1`, which has its own boundary reaching
   `n-2`, ...), so composing `boundary` with itself doesn't automatically
   land outside the structure -- and the two consecutive `Sign.neg` links
   multiply to a nonzero `Sign.pos`-equivalent value instead of
   cancelling. This validates, retroactively, that the bug-fix PR's
   design decision to make `boundary_operator_square_zero` *conditional*
   on `verify_boundary_composition inc idx = true` (rather than an
   unconditional claim) was the right call -- the hypothesis is a real,
   non-vacuous constraint that this instance genuinely fails. -/
def natIdx6 : List Nat := [0, 1, 2, 3, 4, 5]

theorem natIncidence_not_boundary_square_zero :
  verify_boundary_composition natIncidence natIdx6 = false := by
  decide

theorem natIncidence_boundary_composition_witness :
  boundary_composition natIncidence natIdx6 2 0 = 1 := by
  decide

/- The requested unconditional `∂² = 0` theorem is refuted by a model of the
   implemented incidence axioms.  Thus a future universal chain-complex result
   must strengthen `Incidence` (or explicitly require a chain-complex law);
   it cannot be filled by a proof over the present interface. -/
theorem natIncidence_not_boundarySquareZeroEverywhere :
    ¬ BoundarySquareZeroEverywhere natIncidence := by
  intro hall
  have hzero := hall natIdx6 2 0 (by decide) (by decide)
  change boundary_composition natIncidence natIdx6 2 0 = 0 at hzero
  rw [natIncidence_boundary_composition_witness] at hzero
  omega

theorem incidence_axioms_do_not_imply_unconditional_boundarySquareZero :
    ¬ (∀ {I R T : Type} [DecidableEq I] (inc : Incidence I R T),
      BoundarySquareZeroEverywhere inc) := by
  intro hall
  exact natIncidence_not_boundarySquareZeroEverywhere (hall natIncidence)

/- Research cycle 9 (see RESEARCH_LOG.md): classical simplicial homology
   fixes exactly cycle 8's failure by *alternating* the boundary sign by
   degree parity. `altIncidence` tests that directly: `n+1 → n` is
   `Sign.neg` when `n` is even, `Sign.pos` when `n` is odd (unlike
   `natIncidence`, which uses `Sign.neg` uniformly). Algebraic reasoning
   first (see root file's `single_link_composition_ne_zero`): a
   single-face chain can never achieve cancellation via sign choice
   alone, since composing two links always multiplies two nonzero
   numbers together -- there's only ever one term, nothing to cancel
   against. Confirmed empirically (`#eval`, still `false`) before
   formalizing, then formalized as the general theorem in the root
   file rather than a one-off instance check. -/
def altPeanoBoundary : Nat → Boundary Nat PeanoRole
  | 0 => []
  | n + 1 =>
    [ { i := n, role := PeanoRole.pred
      , sign := if n % 2 = 0 then Sign.neg else Sign.pos
      , mult := 1 } ]

def altIncidence : Incidence Nat PeanoRole GraphType where
  boundary := altPeanoBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => some (i + j)
  unit     := 0
  guards   := Guards.permissive Nat
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := fun i e h => rfl
  sign_rules := by
    intro i e h
    cases i with
    | zero => simp [altPeanoBoundary] at h
    | succ n => simp [altPeanoBoundary] at h; subst h; split <;> simp
  multiplicities := by
    intro i e h
    cases i with
    | zero => simp [altPeanoBoundary] at h
    | succ n => simp [altPeanoBoundary] at h; subst h; simp
  well_founded := by
    rintro i ⟨e, he, hei⟩
    cases i with
    | zero => simp [altPeanoBoundary] at he
    | succ n => simp [altPeanoBoundary] at he; subst he; simp_all
  unit_left := by intro i; simp
  unit_right := by intro i; simp
  type_preserve := fun _ _ => rfl

/- Not just the alternating-sign guess refuted -- the general theorem
   proves it fails for ALL n at once, no per-instance `decide` needed
   (this is the practical payoff of having generalized cycle 8's
   one-off refutation into a real theorem). -/
theorem altIncidence_not_boundary_square_zero (n : Nat) (idx : List Nat)
  (hmem : n + 1 ∈ idx) :
  boundary_composition altIncidence idx (n + 2) n ≠ 0 :=
  single_link_composition_ne_zero altIncidence idx (n + 2) (n + 1) n
    { i := n + 1, role := PeanoRole.pred
    , sign := if (n + 1) % 2 = 0 then Sign.neg else Sign.pos, mult := 1 }
    { i := n, role := PeanoRole.pred
    , sign := if n % 2 = 0 then Sign.neg else Sign.pos, mult := 1 }
    rfl rfl (by split <;> simp)
    rfl rfl (by split <;> simp)
    hmem

end IncidenceCore
