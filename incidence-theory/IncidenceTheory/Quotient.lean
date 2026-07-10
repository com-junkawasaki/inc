import IncidenceTheory.Cycle

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

/- The positive half: `approxBisim` packages into a genuine `Setoid I`
   for ANY `Incidence` instance, unconditionally -- built entirely from
   theorems already proven in the root file (`approxBisim_refl`/
   `_symm`/`_trans`), no new proof obligations. -/
def approxBisimSetoid {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Setoid I where
  r := approxBisim inc
  iseqv := ⟨approxBisim_refl inc, approxBisim_symm, approxBisim_trans⟩

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

end IncidenceCore
