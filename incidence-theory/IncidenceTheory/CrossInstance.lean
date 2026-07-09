import IncidenceTheory.Peano
import IncidenceTheory.Pairs

/- Merkle-ID: implementation.graph_model.cross_instance
   story.jsonnet → implementation.nodes.cross_instance
   Research cycle 6 (see RESEARCH_LOG.md): cycles 1-5 each worked within
   a single `Incidence` instance at a time. This file asks whether
   there's a meaningful *homomorphism* connecting two different
   instances -- `natIncidence` and `pairIncidenceChained` -- since
   `PairId.atom : Nat → PairId` is a natural embedding candidate:
   `pairBoundaryChained`'s atom case was deliberately built to mirror
   `peanoBoundary`'s shape back in cycle 3.

   Finding, stated precisely rather than glossed: `PairId.atom`
   preserves `boundary` (naturally, up to a role-relabeling) and `unit`,
   but does *not* preserve `glue` -- a genuine, proven mixed result, not
   a full "Incidence homomorphism" in the strong algebraic sense. This
   reveals something real about `Incidence`'s shape: it bundles a
   coalgebraic layer (`boundary`, "what an element unfolds into") and an
   algebraic layer (`glue`, "how elements compose"), and a map that
   respects one doesn't automatically respect the other. In hindsight
   this isn't surprising -- `pairIncidenceChained.glue` was documented as
   a left-biased placeholder ("not the focus", cycles 2-3) with no
   claimed relationship to `PairId.pair`, the actual structural
   combinator -- but it's now proven rather than merely asserted. -/

namespace IncidenceCore

/- Positive: `PairId.atom` is a boundary-natural embedding -- its
   boundary is exactly `natIncidence`'s, transported through `atom`
   pointwise (with `PeanoRole.pred` relabeled to `PairRole.chain`,
   which is definitionally how `pairBoundaryChained`'s atom case was
   built in the first place). -/
theorem atom_boundary_natural (n : Nat) :
  pairIncidenceChained.boundary (PairId.atom n) =
    (natIncidence.boundary n).map (fun e =>
      ({ i := PairId.atom e.i, role := PairRole.chain, sign := e.sign, mult := e.mult }
        : Endpoint PairId PairRole)) := by
  cases n with
  | zero => simp [natIncidence, peanoBoundary, pairIncidenceChained, pairBoundaryChained]
  | succ k => simp [natIncidence, peanoBoundary, pairIncidenceChained, pairBoundaryChained]

/- Positive: `PairId.atom` preserves the unit element. -/
theorem atom_unit_natural :
  PairId.atom natIncidence.unit = pairIncidenceChained.unit := by
  simp [natIncidence, pairIncidenceChained]

/- Negative, and the interesting part: `PairId.atom` does NOT preserve
   `glue`. `natIncidence.glue` is addition; `pairIncidenceChained.glue`
   is left-biased selection -- structurally unrelated operations.
   Concrete witness: `atom 2 `glue` atom 3` would have to be `atom 5` for
   the embedding to be glue-natural, but it's `atom 2` (left-biased,
   `atom 2 ≠ atom 0`). -/
theorem atom_glue_not_natural :
  ¬ (∀ m n, pairIncidenceChained.glue (PairId.atom m) (PairId.atom n) =
       some (PairId.atom (m + n))) := by
  intro h
  have h23 := h 2 3
  simp [pairIncidenceChained] at h23

/- Consistency corollary: since `atom` is boundary/unit-natural (and
   injective, for free from the carrier's own constructor injectivity),
   `≈`-agreement on atoms inside `pairIncidenceChained` coincides exactly
   with `≈`-agreement in `natIncidence` itself -- the embedding is
   faithful at the level cycles 1-5 actually established (boundary,
   hence `≈`), even though it fails to be a `glue`-homomorphism. -/
theorem atom_approxBisim_iff (m n : Nat) :
  approxBisim pairIncidenceChained (PairId.atom m) (PairId.atom n) ↔
  approxBisim natIncidence m n := by
  rw [pairIncidenceChained_approxBisim_iff, natIncidence_approxBisim_iff]
  exact ⟨fun h => by injection h, fun h => by rw [h]⟩

end IncidenceCore
