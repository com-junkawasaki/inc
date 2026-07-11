import IncidenceTheory.Peano
import IncidenceTheory.Pairs
import IncidenceTheory.PathComplex
import IncidenceTheory.Product

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

def IncIdentityFamily
    {I R T : Type u} [DecidableEq (I × I)]
    (pairIncidence : Incidence (I × I) R T) :
    IncDependentFamily pairIncidence where
  fiber := fun pair => ULift.{u} (PLift (pair.1 = pair.2))

def IncIdentityFamily.refl
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} (index : I) :
    (IncIdentityFamily pairIncidence).fiber (index, index) :=
  ⟨⟨rfl⟩⟩

def IncIdentityFamily.symm
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left right : I} :
    (IncIdentityFamily pairIncidence).fiber (left, right) →
      (IncIdentityFamily pairIncidence).fiber (right, left) :=
  fun equal => ⟨⟨equal.down.down.symm⟩⟩

def IncIdentityFamily.trans
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left middle right : I} :
    (IncIdentityFamily pairIncidence).fiber (left, middle) →
      (IncIdentityFamily pairIncidence).fiber (middle, right) →
        (IncIdentityFamily pairIncidence).fiber (left, right) :=
  fun first second => ⟨⟨first.down.down.trans second.down.down⟩⟩

def IncIdentityFamily.transport
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (family : I → Type u) {left right : I} :
    (IncIdentityFamily pairIncidence).fiber (left, right) →
      family left → family right := by
  intro equal value
  have indicesEqual : left = right := equal.down.down
  subst right
  exact value

def IncIdentityFamily.J
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (motive : ∀ left right : I, left = right → Type u)
    (reflCase : ∀ index, motive index index (Eq.refl index))
    {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    motive left right equal.down.down := by
  have proof := equal.down.down
  cases proof
  exact reflCase left

theorem IncIdentityFamily.transport_refl
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (family : I → Type u) (index : I) (value : family index) :
    IncIdentityFamily.transport (pairIncidence := pairIncidence) family
      (IncIdentityFamily.refl index) value = value := by
  simp [IncIdentityFamily.transport]

theorem IncIdentityFamily.transport_trans
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (family : I → Type u) {left middle right : I}
    (first : (IncIdentityFamily pairIncidence).fiber (left, middle))
    (second : (IncIdentityFamily pairIncidence).fiber (middle, right))
    (value : family left) :
    IncIdentityFamily.transport (pairIncidence := pairIncidence) family
        (IncIdentityFamily.trans first second) value =
      IncIdentityFamily.transport (pairIncidence := pairIncidence) family second
        (IncIdentityFamily.transport (pairIncidence := pairIncidence) family first value) := by
  have firstEq : left = middle := first.down.down
  have secondEq : middle = right := second.down.down
  subst middle
  subst right
  simp [IncIdentityFamily.transport]

theorem IncIdentityFamily.J_beta
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (motive : ∀ left right : I, left = right → Type u)
    (reflCase : ∀ index, motive index index (Eq.refl index))
    (index : I) :
    IncIdentityFamily.J (pairIncidence := pairIncidence) motive reflCase
        (IncIdentityFamily.refl (pairIncidence := pairIncidence) index) =
      reflCase index := by
  simp [IncIdentityFamily.J]

def natIncIdentityFamily :
    IncDependentFamily (incidenceProd natIncidence natIncidence) :=
  IncIdentityFamily (incidenceProd natIncidence natIncidence)

def natIncIdentity_zero_refl : natIncIdentityFamily.fiber (0, 0) :=
  IncIdentityFamily.refl (pairIncidence := incidenceProd natIncidence natIncidence) 0

theorem natIncIdentity_zero_one_empty :
    ¬ Nonempty (natIncIdentityFamily.fiber (0, 1)) := by
  rintro ⟨witness⟩
  exact Nat.zero_ne_one witness.down.down

def IncIdentityFamily.congrArg
    {I J R T R' T' : Type u}
    [DecidableEq (I × I)] [DecidableEq (J × J)]
    {sourcePairs : Incidence (I × I) R T}
    {targetPairs : Incidence (J × J) R' T'}
    (map : I → J) {left right : I} :
    (IncIdentityFamily sourcePairs).fiber (left, right) →
      (IncIdentityFamily targetPairs).fiber (map left, map right) :=
  fun equal => ⟨⟨_root_.congrArg map equal.down.down⟩⟩

theorem IncIdentityFamily.witness_unique
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left right : I}
    (first second : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    first = second := by
  rcases first with ⟨⟨firstProof⟩⟩
  rcases second with ⟨⟨secondProof⟩⟩
  have proofsEqual : firstProof = secondProof := Subsingleton.elim _ _
  exact _root_.congrArg
    (fun proof => (⟨⟨proof⟩⟩ : (IncIdentityFamily pairIncidence).fiber (left, right)))
    proofsEqual

theorem IncIdentityFamily.congrArg_id
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    IncIdentityFamily.congrArg (sourcePairs := pairIncidence)
      (targetPairs := pairIncidence) id equal = equal := by
  exact IncIdentityFamily.witness_unique _ _

theorem IncIdentityFamily.congrArg_comp
    {I J K R T R' T' R'' T'' : Type u}
    [DecidableEq (I × I)] [DecidableEq (J × J)] [DecidableEq (K × K)]
    {sourcePairs : Incidence (I × I) R T}
    {middlePairs : Incidence (J × J) R' T'}
    {targetPairs : Incidence (K × K) R'' T''}
    (second : J → K) (first : I → J) {left right : I}
    (equal : (IncIdentityFamily sourcePairs).fiber (left, right)) :
    IncIdentityFamily.congrArg (sourcePairs := sourcePairs)
        (targetPairs := targetPairs) (second ∘ first) equal =
      IncIdentityFamily.congrArg (sourcePairs := middlePairs)
        (targetPairs := targetPairs) second
        (IncIdentityFamily.congrArg (sourcePairs := sourcePairs)
          (targetPairs := middlePairs) first equal) := by
  exact IncIdentityFamily.witness_unique _ _

theorem IncIdentityFamily.transport_morphism_naturality
    {I R T Rb Tb : Type u} [DecidableEq I] [DecidableEq (I × I)]
    {baseIncidence : Incidence I Rb Tb}
    {pairIncidence : Incidence (I × I) R T}
    {source target : IncDependentFamily baseIncidence}
    (morphism : IncDependentFamilyMorphism source target)
    {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right))
    (value : source.fiber left) :
    morphism.app right
        (IncIdentityFamily.transport source.fiber equal value) =
      IncIdentityFamily.transport target.fiber equal
        (morphism.app left value) := by
  have indicesEqual : left = right := equal.down.down
  subst right
  rfl

theorem IncIdentityFamily.symm_symm
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    IncIdentityFamily.symm (pairIncidence := pairIncidence)
        (IncIdentityFamily.symm (pairIncidence := pairIncidence) equal) = equal := by
  exact IncIdentityFamily.witness_unique _ _

def IncDependentFamily.pullbackAlongBoundaryEmbedding
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (family : IncDependentFamily target)
    (embedding : IncidenceBoundaryObservationEmbedding source target) :
    IncDependentFamily source where
  fiber := fun index => family.fiber (embedding.map index)

def IncDependentFamily.pullbackSumToTarget
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (family : IncDependentFamily target)
    (embedding : IncidenceBoundaryObservationEmbedding source target) :
    IncDependentSum (family.pullbackAlongBoundaryEmbedding embedding) →
      IncDependentSum family
  | ⟨index, value⟩ => ⟨embedding.map index, value⟩

def IncDependentFamily.pullbackProduct
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (family : IncDependentFamily target)
    (embedding : IncidenceBoundaryObservationEmbedding source target)
    (term : IncDependentProduct family) :
    IncDependentProduct (family.pullbackAlongBoundaryEmbedding embedding) :=
  fun index => term (embedding.map index)

theorem IncDependentFamily.pullbackProduct_comp
    {I I' I'' R T R' T' R'' T'' : Type u}
    [DecidableEq I] [DecidableEq I'] [DecidableEq I'']
    {source : Incidence I R T} {middle : Incidence I' R' T'}
    {target : Incidence I'' R'' T''}
    (family : IncDependentFamily target)
    (second : IncidenceBoundaryObservationEmbedding middle target)
    (first : IncidenceBoundaryObservationEmbedding source middle)
    (term : IncDependentProduct family) :
    family.pullbackProduct (second.comp first) term =
      (family.pullbackAlongBoundaryEmbedding second).pullbackProduct first
        (family.pullbackProduct second term) := by
  rfl

theorem IncDependentFamily.pullbackSumToTarget_comp
    {I I' I'' R T R' T' R'' T'' : Type u}
    [DecidableEq I] [DecidableEq I'] [DecidableEq I'']
    {source : Incidence I R T} {middle : Incidence I' R' T'}
    {target : Incidence I'' R'' T''}
    (family : IncDependentFamily target)
    (second : IncidenceBoundaryObservationEmbedding middle target)
    (first : IncidenceBoundaryObservationEmbedding source middle) :
    family.pullbackSumToTarget (second.comp first) =
      family.pullbackSumToTarget second ∘
        (family.pullbackAlongBoundaryEmbedding second).pullbackSumToTarget first := by
  funext total
  rcases total with ⟨index, value⟩
  rfl

/- Positive: `PairId.atom` is a boundary-natural embedding -- its
   boundary is exactly `natIncidence`'s, transported through `atom`
   pointwise (with `PeanoRole.pred` relabeled to `PairRole.chain`,
   which is definitionally how `pairBoundaryChained`'s atom case was
   built in the first place). -/
theorem atom_boundary_natural (n : Nat) :
  pairIncidenceChained.boundary (PairId.atom n) =
    (natIncidence.boundary n).map (fun e =>
      ({ i := PairId.atom e.i, role := PairRole.chain, sign := e.sign, mult := e.mult,
         mult_pos := e.mult_pos }
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

/- Research cycle 7 (see RESEARCH_LOG.md): cycle 6 flagged a circularity
   risk for testing "pair-up"-style compatibility with `natIncidence.glue`
   -- defining a new count function specifically so it works would prove
   nothing. Sidestepped that by testing `sizeOf` instead: it already
   exists (used for `well_founded` proofs since cycle 3), wasn't defined
   for this purpose, and its exact formula (`PairId.pair.sizeOf_spec`) is
   whatever Lean's deriving mechanism happened to produce -- so whatever
   relationship it has to `glue` is discovered, not designed.

   Finding: `sizeOf` is *not* a strict `glue`-homomorphism (confirms
   cycle 6's finding via an independent route), but it IS one up to a
   precise, constant "cost" of 1 per `pair` node -- not just "doesn't
   match", but "matches exactly once you account for the pairing
   operation's own cost". A cleaner, quantified negative than cycle 6's
   qualitative one. -/
theorem sizeOf_pair_eq_succ_glue (a b : PairId) :
  sizeOf (PairId.pair a b) = 1 + (natIncidence.glue (sizeOf a) (sizeOf b)).getD 0 := by
  rw [PairId.pair.sizeOf_spec]
  simp [natIncidence]
  omega

theorem sizeOf_pair_ne_glue (a b : PairId) :
  some (sizeOf (PairId.pair a b)) ≠ natIncidence.glue (sizeOf a) (sizeOf b) := by
  simp [natIncidence, PairId.pair.sizeOf_spec]

/- Research cycle 15 (see RESEARCH_LOG.md): cycle 14 fixed
   `pathIncidenceChained`'s collapse (cycle 13) the same way cycle 3 fixed
   `pairIncidenceChained`'s (a role-tagged predecessor chain), and asked
   the queued question: does `PathId.node : Nat → PathId` -- the obvious
   embedding into a *second*, independently-built chain-shaped instance
   -- reproduce cycle 6's exact mixed result (boundary/unit natural, glue
   not), or does something different happen now that source and target
   are both single-link `Nat`-indexed chains with near-identical shape
   (unlike `PairId`, a richer nested type)?

   Finding: the SAME qualitative outcome, term for term. `node`
   preserves `boundary` (up to the same `pred → chain` role-relabeling
   pattern as `atom`) and `unit`, but not `glue` --
   `pathIncidenceChained.glue` is the same left-biased-selection
   placeholder as `pairIncidenceChained.glue`, still structurally
   unrelated to `natIncidence.glue` (addition). This is a genuine
   confirmation, not a foregone conclusion: it shows the boundary/glue
   split from cycle 6 isn't an artifact of `PairId`'s richer shape --
   it persists even between two *maximally similar* chain instances,
   because the real cause is the algebraic *kind* of `glue` (addition
   vs. selection), not any structural dissimilarity between the carrier
   types. -/
theorem node_boundary_natural (n : Nat) :
  pathIncidenceChained.boundary (PathId.node n) =
    (natIncidence.boundary n).map (fun e =>
      ({ i := PathId.node e.i, role := PathRole.chain, sign := e.sign, mult := e.mult,
         mult_pos := e.mult_pos }
        : Endpoint PathId PathRole)) := by
  cases n with
  | zero => simp [natIncidence, peanoBoundary, pathIncidenceChained, pathBoundaryChained]
  | succ k => simp [natIncidence, peanoBoundary, pathIncidenceChained, pathBoundaryChained]

def natToPathBoundaryObservationEmbedding :
    IncidenceBoundaryObservationEmbedding natIncidence pathIncidenceChained where
  map := PathId.node
  boundary_iff := by
    intro n
    cases n with
    | zero =>
      simp [IncidenceBoundaryValuation, natIncidence, peanoBoundary,
        pathIncidenceChained, pathBoundaryChained]
    | succ n =>
      simp [IncidenceBoundaryValuation, natIncidence, peanoBoundary,
        pathIncidenceChained, pathBoundaryChained]

theorem natToPath_boundaryLogic_satisfies_iff (formula : Formula Nat) :
    IncidenceBoundarySatisfies pathIncidenceChained
        (formula.map PathId.node) ↔
      IncidenceBoundarySatisfies natIncidence formula :=
  natToPathBoundaryObservationEmbedding.satisfies_iff formula

theorem natToPath_boundaryLogic_entails_iff
    (context : List (Formula Nat)) (formula : Formula Nat) :
    IncidenceBoundaryEntails pathIncidenceChained
        (Formula.mapContext PathId.node context) (formula.map PathId.node) ↔
      IncidenceBoundaryEntails natIncidence context formula :=
  natToPathBoundaryObservationEmbedding.entails_iff context formula

theorem natToPath_leafLogic_satisfies_iff (formula : Formula Nat) :
    IncidenceLeafSatisfies pathIncidenceChained (formula.map PathId.node) ↔
      IncidenceLeafSatisfies natIncidence formula :=
  natToPathBoundaryObservationEmbedding.leafSatisfies_iff formula

theorem natToPath_leafLogic_context_iff (context : List (Formula Nat)) :
    IncidenceLeafContextSatisfies pathIncidenceChained
        (Formula.mapContext PathId.node context) ↔
      IncidenceLeafContextSatisfies natIncidence context :=
  natToPathBoundaryObservationEmbedding.leafContextSatisfies_iff context

theorem natToPath_leafLogic_entails_iff
    (context : List (Formula Nat)) (formula : Formula Nat) :
    IncidenceLeafEntails pathIncidenceChained
        (Formula.mapContext PathId.node context) (formula.map PathId.node) ↔
      IncidenceLeafEntails natIncidence context formula :=
  natToPathBoundaryObservationEmbedding.leafEntails_iff context formula

theorem node_unit_natural :
  PathId.node natIncidence.unit = pathIncidenceChained.unit := by
  simp [natIncidence, pathIncidenceChained]

/- Concrete witness, same shape as `atom_glue_not_natural`: `node 2`
   `glue` `node 3` would have to be `node 5` for glue-naturality, but
   it's `node 2` (left-biased, `node 2 ≠ node 0`). -/
theorem node_glue_not_natural :
  ¬ (∀ m n, pathIncidenceChained.glue (PathId.node m) (PathId.node n) =
       some (PathId.node (m + n))) := by
  intro h
  have h23 := h 2 3
  simp [pathIncidenceChained] at h23

theorem node_approxBisim_iff (m n : Nat) :
  approxBisim pathIncidenceChained (PathId.node m) (PathId.node n) ↔
  approxBisim natIncidence m n := by
  rw [pathIncidenceChained_approxBisim_iff, natIncidence_approxBisim_iff]
  exact ⟨fun h => by injection h, fun h => by rw [h]⟩

end IncidenceCore
