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
  { guards := Guards.permissive Nat
  , unit_ok := by intro i; refine ⟨rfl, ?_, ?_⟩ <;> simp [natIncidence]
  , type_preserve := by intro i j k _ _; rfl
  , guard_preserve := by intro i j k _ _; trivial
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

end IncidenceCore
