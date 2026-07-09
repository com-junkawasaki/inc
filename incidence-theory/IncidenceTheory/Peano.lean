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

/- The hard direction of faithfulness: any bisimulation relating m and n
   forces m = n, by induction using the boundary-predecessor-chain
   structure (a bisimulation can't relate a zero-boundary element to a
   nonempty-boundary one, and matching predecessors recurses). -/
theorem natIncidence_rel_eq {rel : Nat → Nat → Prop}
  (hbisim : IsBisimulation natIncidence rel) :
  ∀ m n, rel m n → m = n := by
  intro m
  induction m with
  | zero =>
    intro n hmn
    obtain ⟨-, hM⟩ := hbisim 0 n hmn
    match n, hM with
    | 0, _ => rfl
    | j + 1, hM =>
      exfalso
      obtain ⟨e, he, -⟩ :=
        hM.right { i := j, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
          (by simp [natIncidence, peanoBoundary])
      simp [natIncidence, peanoBoundary] at he
  | succ k ih =>
    intro n hmn
    obtain ⟨-, hM⟩ := hbisim (k + 1) n hmn
    match n, hM with
    | 0, hM =>
      exfalso
      obtain ⟨e, he, -⟩ :=
        hM.left { i := k, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
          (by simp [natIncidence, peanoBoundary])
      simp [natIncidence, peanoBoundary] at he
    | j + 1, hM =>
      obtain ⟨e', he', -, hrel⟩ :=
        hM.left { i := k, role := PeanoRole.pred, sign := Sign.neg, mult := 1 }
          (by simp [natIncidence, peanoBoundary])
      simp [natIncidence, peanoBoundary] at he'
      subst he'
      have := ih j hrel
      omega

/- Faithfulness: Inc's abstract bisimulation-equivalence ≈ does not
   collapse distinct naturals -- it coincides exactly with `=`. -/
theorem natIncidence_approxBisim_iff (m n : Nat) :
  approxBisim natIncidence m n ↔ m = n := by
  constructor
  · rintro ⟨rel, hbisim, hmn⟩
    exact natIncidence_rel_eq hbisim m n hmn
  · intro h; subst h; exact approxBisim_refl natIncidence m

end IncidenceCore
