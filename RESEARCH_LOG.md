# Research Log — Incidence Theory Lean formalization

Working log for a recurring, self-paced research loop advancing the
Lean 4 formalization's maturity: hypothesize → formalize → prove →
verify → record → next hypothesis. Each entry should be self-contained
enough that a fresh iteration (no memory of prior sessions) can read
this file plus the repo state and continue.

Ground rules carried over from PR #2/#3 discussion, still binding:
- No `sorry`, no vacuous `true := trivial` dressed up as a real theorem.
  If a hypothesis turns out false or unprovable as stated, say so and
  restate honestly (with an explicit hypothesis, or drop it) rather than
  faking it.
- `#print axioms` every new theorem before recording it as done; flag
  anything beyond `propext`/`Classical.choice`/`Quot.sound`.
- Prefer small, concrete, provable-today increments over restating the
  big vision (Inc ⊇ ZFC/ETCS/type theory) as a goal — that requires new
  axioms this repo doesn't have yet and isn't a 30-minute task.
- `rm -rf .lake/build && lake build` clean, then `lake exe
  incidence-theory`, before recording a cycle as verified.

## Status

- PR #2 (`fix/lean-proofs-actually-compile`): base fixes, CI green, open.
- PR #3 (`feat/peano-naturals-in-inc`, based on main): Peano naturals as
  a concrete `Incidence` instance, CI green, open.

## Cycle 1

**Hypothesis**: the `GluingSpec` abstraction (already exercised once, by
`triGluingSpec` on the triangle graph's ad hoc left-biased, non-commutative
`glue`) also fits a genuinely different kind of instance — a commutative
monoid — without needing to change `GluingSpec` itself. If so, that's a
real (if modest) generality signal: one instance could be a fluke that
happens to fit; two structurally unrelated instances is evidence the
abstraction is doing real work.

**Method**: prove `natIncidence.glue` (`= Nat.add`) is commutative, and
construct `natGluingSpec : GluingSpec natIncidence` (unit/associativity/
type-preservation obligations), reusing the *same* `GluingSpec` structure
`triGluingSpec` uses.

**Result**: confirmed. `natIncidence_glue_comm` and `natGluingSpec` both
compile with only `propext`/`Classical.choice`/`Quot.sound` — no
`sorryAx`, no widening of `GluingSpec` itself needed. Added to
`IncidenceTheory/Peano.lean` (stacked onto PR #3, unmerged).

**Next hypothesis (cycle 2, not yet attempted)**: can Inc's own boundary/
endpoint vocabulary (not a bolted-on Lean structure) encode *ordered
pairs* — i.e., an incidence `p` whose `boundary p` has exactly two
endpoints distinguished by `role` (first/second projection)? This would
be a genuine ZFC-adjacent building block (relations/functions as sets of
pairs) reachable without inventing a full axiom of infinity or
comprehension yet. Concretely: define a `PairRole` (`fst`/`snd`), a
`pairBoundary`, a `pairIncidence`, and prove the projections are
well-defined and jointly injective (`pair a b = pair a' b' → a = a' ∧ b
= b'`) the same way `natIncidence_rel_eq`/faithfulness was proved for
Peano — by induction on the bisimulation witness, not by assumption.

## Cycle 2

**Hypothesis**: (as queued above) ordered pairs encodable via `boundary`
alone, with projections recoverable structurally and pairing jointly
injective, proved the same faithfulness way as Peano's cycle.

**Method**: `PairId := atom (n : Nat) | pair (a b : PairId)`,
`pairBoundary` gives an atom `[]` and a pair its two role-tagged
endpoints, `pairIncidence : Incidence PairId PairRole GraphType`. Then
attempted the Peano-style full faithfulness theorem
(`approxBisim pairIncidence x y ↔ x = y`).

**Result**: partially confirmed, and the *refutation* is itself the
interesting finding — this is what a co-scientist loop is for, not just
banking wins:
- ✅ `pairIncidence` is a valid `Incidence` (all 14 fields).
- ✅ `pairIncidence_pair_injective`: pairing is jointly injective.
- ✅ `pairIncidence_boundary_pair`: projections literally = `boundary`,
  not a separate accessor.
- ❌ Full faithfulness (`≈` ↔ `=`) is **false** for this instance, and
  `pairIncidence_atoms_collapse` proves a concrete counterexample:
  `atom 0 ≈ atom 1` even though `atom 0 ≠ atom 1`. Cause: unlike
  `natIncidence` (where the predecessor chain gives every element a
  unique "distance from zero"), a bare atom's boundary is `[]`
  regardless of *which* atom — nothing in `boundary`/`typeFunc`
  distinguishes `atom 3` from `atom 999`, so the relation "any atom ≈
  any atom, and pairs of related things ≈ each other" is a genuine
  bisimulation. Faithfulness needs distinguishing structure; it is not
  automatic just because an instance "looks well-founded".

Added to `IncidenceTheory/Pairs.lean` (stacked onto PR #3, unmerged).
`#print axioms` on every theorem here: `propext`/`Classical.choice`/
`Quot.sound` only (`pairIncidence_pair_injective` needs no axioms at
all — it's pure `injection` on the carrier type), no `sorryAx`.

**Next hypothesis (cycle 3, not yet attempted)**: fix atom-distinguishability
by giving atoms the same predecessor-chain trick `natIncidence` used —
i.e., index atoms so `boundary (atom (n+1))` points at `atom n` (reusing
`peanoBoundary`'s shape) instead of `[]` uniformly. If that recovers full
`≈ ↔ =` faithfulness for `PairId` built over such atoms, it's evidence
that "give every leaf a canonical predecessor-style boundary" is a
*general* recipe for faithfulness in Inc, not a Peano-specific accident
— worth stating as a lemma (e.g. "any well-founded, boundary-injective
carrier is ≈-faithful") rather than re-deriving per instance.

## Cycle 3

**Hypothesis**: (as queued above) fixing atom-distinguishability with a
predecessor chain recovers full `≈ ↔ =` faithfulness for the whole
`PairId` type (atoms *and* arbitrarily nested pairs, not just atoms in
isolation) — evidence of a general recipe, not a Peano-specific fluke.

**Method**: extended `PairRole` with a third constructor `chain`, kept
disjoint from `fst`/`snd` specifically so a bisimulation can never
mistake an atom-chain-link for a pair-projection-link (`boundaryCompatible`
requires matching `role`). `pairBoundaryChained (atom (n+1))` points at
`atom n` via a `chain`-role endpoint (`atom 0` unchanged, still `[]`,
the chain's base case) — same shape as `peanoBoundary`. Built
`pairIncidenceChained : Incidence PairId PairRole GraphType`, then
attempted the full theorem by structural induction on `x : PairId`,
using the role split to rule out atom-vs-pair mismatches at each step
and the induction hypotheses on `a`/`b` for the pair-vs-pair case.

**Result**: **confirmed, hypothesis holds**. `pairIncidenceChained_rel_eq`
proves `∀ x y, rel x y → x = y` for *any* bisimulation `rel` on the
whole `PairId` type — atoms distinguished via the chain (reusing
`natIncidence_rel_eq`'s exact argument, factored out as
`pairIncidenceChained_atom_rel_eq`), pairs distinguished by recursing
into both projections via the structural induction hypotheses.
Packaged cleanly as `pairIncidenceChained_approxBisim_iff : approxBisim
pairIncidenceChained x y ↔ x = y`. `#print axioms`: `propext`/
`Classical.choice`/`Quot.sound` only, no `sorryAx`, on every theorem in
this cycle. Both the broken (`pairIncidence`) and fixed
(`pairIncidenceChained`) instances are kept in `Pairs.lean` side by
side, deliberately — the contrast (proven collapse vs. proven
faithfulness from one structural change) is the actual finding, more
useful than deleting the broken one now that it served its purpose.

This is enough evidence across three instances (`triIncidence`,
`natIncidence`, `pairIncidenceChained`) to tentatively state the general
principle in prose: **an `Incidence`'s `≈` is faithful (coincides with
`=`) when every element's `boundary` structure — role-tagged so
different "kinds" of edges can't be confused — uniquely and
well-foundedly determines that element from the boundaries of smaller
elements.** Not yet stated/proved as an actual general Lean theorem
(that would quantify over an arbitrary `Incidence` and some formal
"distinguishing" hypothesis on `boundary`, which needs care to phrase
precisely) — that formalization is the next real step, not more
instance-by-instance confirmation.

**Next hypothesis (cycle 4, not yet attempted)**: state and prove the
general theorem sketched above, roughly: given `inc : Incidence I R T`
and a well-founded measure `μ : I → Nat` such that (a) `∀ i, ∀ e ∈
boundary i, μ e.i < μ i` (boundaries strictly decrease the measure) and
(b) `boundary` is "injective enough" at each level (two elements with
the same `μ` and pairwise-`boundaryCompatible`-and-`μ`-matching
boundaries, in bijection, are equal) — then `approxBisim inc x y → x =
y`. This is real risk, not a guaranteed win: the precise "injective
enough" hypothesis is exactly the part cycles 1-3 didn't have to state
formally (they baked it in by direct case analysis per concrete
instance), and getting the induction to go through generically, without
a concrete carrier type's `cases`/`sizeOf` to lean on, may need a
genuinely different proof strategy (well-founded recursion on `μ`
instead of structural induction on `I`). If it turns out false or
needs a much stronger hypothesis to be true, that itself is the
result — record it, don't force a fake generalization.

## Cycle 4

**Hypothesis**: (as queued above) the general theorem is provable, with
the "injective enough" hypothesis phrased as *extensionality*:
`∀ x y, typeFunc x = typeFunc y → boundaryMatched inc (· = ·) x y → x =
y` — i.e. elements with literally-equal, role-matched boundaries are
equal (the Inc analogue of ZF's set extensionality). Flagged as real
risk in cycle 3; not assumed to work.

**Method**: well-founded (strong) induction on `μ x` via
`Nat.strongRecOn`, not structural induction on a concrete carrier type.
At each step, `IsBisimulation`'s `boundaryMatched rel x y` gives, for
every edge in `x`'s boundary, a `rel`-related target in `y`'s boundary
(and symmetrically); since that target's `μ` is strictly smaller (by
`hdec`), the induction hypothesis upgrades `rel` to literal `=` on it;
once every edge is upgraded this way, `boundaryMatched inc (=) x y`
holds, and `hext` closes `x = y` directly.

**Result**: **confirmed, and stronger than hoped** —
`incidence_bisim_faithful` (now in root `IncidenceTheory.lean`, next to
the bisimulation skeleton it generalizes) proves with **zero axioms**,
not even the `propext`/`Classical.choice`/`Quot.sound` that show up
almost everywhere else in this file; it's a small, fully constructive
well-founded induction. Non-vacuousness wasn't just asserted — it was
checked by instantiating `hdec`/`hext` against two independent,
structurally different carriers:
- `natIncidence` (`μ := id`): `natIncidence_hext`/`natIncidence_hdec` in
  `Peano.lean`.
- `pairIncidenceChained` (`μ := sizeOf`, the most complex instance —
  atoms *and* nested pairs, two disjoint edge roles): `pairIncidenceChained_hext`/
  `pairIncidenceChained_hdec` in `Pairs.lean`.

Both instantiations **replaced** their cycle 1/3 bespoke inductions
(`natIncidence_rel_eq`, `pairIncidenceChained_atom_rel_eq`,
`pairIncidenceChained_rel_eq` — removed, not kept redundantly; see git
history if the old proofs are wanted) rather than sitting alongside them
as a curiosity — real evidence the generalization has practical value,
not just theoretical interest. `#print axioms` on every theorem in this
cycle: `propext`/`Classical.choice`/`Quot.sound` (standard, from the
concrete carriers' own `cases`/`Decidable` machinery) or nothing at all
for `incidence_bisim_faithful` itself, no `sorryAx`.

Caveat, stated honestly rather than oversold: `hext` (the extensionality
hypothesis) still has to be proved *per instance*, by the same kind of
case analysis cycles 1-3 already did — the win isn't "no more
instance-specific proof," it's "the well-founded-induction scaffolding
(the part that actually chases the bisimulation witness through
`boundaryMatched`, which was the fiddliest part of every prior cycle) is
now written exactly once." That's a real, useful generalization; it is
not a claim that arbitrary `Incidence` instances are automatically
faithful (cycle 2's flat-atom counterexample still stands as a case
where no valid `hext` exists at all).

**Next hypothesis (cycle 5, not yet attempted)**: everything so far has
targeted *faithfulness* of `≈` (the M side of a possible foundational
correspondence). The complementary, still-untouched direction from the
original conversation's six-point list is *soundness/completeness of
translation* — e.g., does `TranslationPreservation.inc_to_set` (root
file, T5) actually preserve enough structure to be called a translation,
for a *nontrivial* instance (it's currently only checked against the
triangle graph, where every node/edge maps to a fixed `ULift Bool`/
`ULift Unit` — not yet exercised against `natIncidence` or
`pairIncidenceChained`, where the translation's *image* could plausibly
carry more information, e.g. distinguishing atoms from pairs, or
encoding the Peano order). Concretely: check whether `inc_to_set`, or a
richer translation, can be shown *injective on ≈-classes* for
`pairIncidenceChained` — i.e. genuinely reflects the faithfulness cycle
4 just established, rather than collapsing everything to two trivial
types regardless. This is exploratory (T5 was never given real content
in the original file, just a `True := trivial` for the generic case) —
expect to spend part of the cycle just deciding what "translation
preserves structure" should even mean for a concrete instance before
attempting to prove anything.

## Cycle 5

**Hypothesis**: (as queued above) a *better* translation than the
generic `inc_to_set` — one that actually reads the instance's `boundary`
recursively instead of just checking "empty or not" — can be shown
injective, hence (via cycle 4's faithfulness theorems) reflects `≈`
rather than erasing it, for both `natIncidence` and `pairIncidenceChained`.

**Method, and an early course-correction**: first checked whether
`Fintype`/`Equiv` (the natural Mathlib tools for "translated sets are
the same size ⇒ originals are equal") are available — they are not (no
mathlib dependency, confirmed via `#check`). Pivoted to an elementary,
self-contained target instead:
- `natToFiniteSet : Nat → List Unit`, built by *exactly* `peanoBoundary`'s
  own recursion (`n+1` recurses on `n`) — not an unrelated relabeling.
  `List.length` recovers `n`, giving injectivity directly.
- `PairShape` (`leaf (n : Nat) | node (l r : PairShape)`) and
  `pairToShape : PairId → PairShape`, again built by exactly
  `pairBoundaryChained`'s recursion (atom → leaf, pair → node of the two
  recursive translations) — the real test, since a naive translation
  could plausibly flatten/confuse nesting.

**Result**: confirmed for both. `natToFiniteSet_injective` and
`pairToShape_injective` both hold, composed with cycle 4's
`natIncidence_approxBisim_iff`/`pairIncidenceChained_approxBisim_iff`
into `natToFiniteSet_reflects_approxBisim`/`pairToShape_reflects_approxBisim`
— translation agreement now provably implies `≈` (indeed `=`), the
opposite of `inc_to_set`'s behavior (which collapses everything nonzero
into one type regardless of value). `#print axioms`: `propext` alone for
the two injectivity proofs (pure structural induction, no bisimulation
machinery needed), the usual three for the `approxBisim`-composed
versions. No `sorryAx`. Added to `Peano.lean`/`Pairs.lean`, wired into
`Main.lean`.

Honesty check on scope, since it's easy to oversell this: `pairToShape`
is close to a straight relabeling of `PairId` (swap `atom`/`pair` for
`leaf`/`node`), so its injectivity proof is nearly as easy as
`PairId`'s own constructor injectivity — this cycle demonstrates the
*shape* of what a faithful T5 translation looks like and that it's
achievable without mathlib, not a deep independent confirmation. The
root file's `inc_to_set`/`preserves_limits` are left untouched
(still honestly labeled unformalized for the fully general case) —
this is instance-level content, same pattern as `triangle_translation_concrete`,
not a claim about arbitrary `Incidence` translations.

**Next hypothesis (cycle 6, not yet attempted)**: everything so far
(cycles 1-5) has worked within a single `Incidence` instance at a time.
Untouched: T1/T2's *cross-instance* content — e.g., does `glue`
compose sensibly *between* `natIncidence` and `pairIncidenceChained`
(there's no operation connecting them right now; `pair (atom n) (atom m)`
and `natIncidence.glue n m` are unrelated constructions that happen to
share underlying data). Concretely: is there a meaningful `Incidence`
homomorphism notion (a map `f : I → I'` commuting with `glue`/`boundary`
in some precise sense) that would let a statement like "pairing preserves
sums" (`pairToShape (pair (atom (m+n)) x) ~ combine (pairToShape (atom m))
(pairToShape (atom n))`-ish) be *stated*, let alone proved? This is more
exploratory than prior cycles — may spend the cycle just on what the
right definition is, same as cycle 5's Fintype/Equiv pivot, and that's
an acceptable outcome to record rather than force through.

## Cycle 6

**Hypothesis**: (as queued above) `PairId.atom : Nat → PairId` is a
natural candidate embedding of `natIncidence` into `pairIncidenceChained`
— `pairBoundaryChained`'s atom case was deliberately built back in cycle
3 to mirror `peanoBoundary`'s shape. Does it commute with `boundary` and
`glue` in a precise sense, making it a genuine `Incidence` homomorphism?

**Method**: checked `boundary`-naturality (does `pairIncidenceChained.boundary
(atom n)` equal `natIncidence.boundary n` transported pointwise through
`atom`?), `unit`-preservation, and `glue`-preservation, as three
separate, independently checkable claims rather than assuming a bundled
"homomorphism" notion upfront (no `IncidenceHom` structure was invented
speculatively).

**Result**: a genuine **mixed** finding, proven precisely rather than
hand-waved:
- ✅ `atom_boundary_natural`: boundary transports exactly, up to
  relabeling `PeanoRole.pred` to `PairRole.chain` (which is
  definitionally how the chain was built in the first place).
- ✅ `atom_unit_natural`: `atom natIncidence.unit = pairIncidenceChained.unit`.
- ❌ `atom_glue_not_natural`: **refuted** with a concrete witness —
  `atom 2 "glue" atom 3` would have to be `atom 5` for glue-naturality,
  but `pairIncidenceChained.glue` is left-biased selection (returns
  `atom 2`), not addition. `natIncidence.glue` and
  `pairIncidenceChained.glue` are structurally unrelated operations.

`atom_approxBisim_iff` packages the positive part cleanly:
`≈`-agreement on atoms inside `pairIncidenceChained` coincides exactly
with `≈`-agreement in `natIncidence` — the embedding is fully faithful
at the level cycles 1-5 actually established (boundary, hence `≈`),
even though it fails to be a `glue`-homomorphism. `#print axioms`:
`propext`/`Classical.choice`/`Quot.sound` on all four theorems (the
first three don't even touch bisimulation), no `sorryAx`. Added as a
new file, `CrossInstance.lean` (imports both `Peano.lean` and
`Pairs.lean`, which don't import each other), wired into `Main.lean`.

**Why this matters, not just "one operation didn't match"**: `Incidence`
bundles two different kinds of structure that this cycle shows don't
automatically travel together under the same map — a coalgebraic layer
(`boundary`: "what does this element unfold into") and an algebraic
layer (`glue`: "how do elements compose"). `PairId.atom` is a coalgebra
homomorphism (respects the unfolding) but not an algebra homomorphism
(doesn't respect composition). In hindsight this isn't a surprising
result — `pairIncidenceChained.glue` was documented as a left-biased
placeholder with no claimed relationship to `PairId.pair` (the actual
structural combinator) as far back as cycle 2 ("`glue` isn't the focus
here") — but it's now *proven*, with a concrete refutation witness,
rather than merely asserted or silently assumed away.

**Next hypothesis (cycle 7, not yet attempted)**: cycle 6 found that
`pairIncidenceChained.glue` (left-biased selection, purely decorative)
was the wrong operation to expect compatibility from — the *actual*
structural combinator on `PairId` is the `pair` constructor itself,
which isn't wired up as any `Incidence`'s official `.glue` field. Is
there a *different*, real `Incidence` instance where `glue` genuinely
means "pair up", and does *that* one compose naturally with
`natIncidence` (e.g. via a "total atom count" map `PairId → Nat` that's
additive over `pair`, so `count (pair a b) = natIncidence.glue (count a)
(count b)` by construction)? Real risk: this may turn out to be almost
definitional (choosing `count` specifically to make it work) rather than
a substantive test, the same concern flagged and set aside in this
cycle for a "sum" map — worth checking whether there's a non-circular
way to state it before spending much time on the proof itself.

## Cycle 7

**Hypothesis**: (as queued above) a "count"-style map from `PairId` to
`Nat` composes naturally with `natIncidence.glue` via `PairId.pair`.
Flagged as at-risk for circularity — a map *defined* to be additive over
`pair` would trivially satisfy the property by construction, proving
nothing.

**Method, addressing the circularity directly**: instead of inventing a
new count function, tested `sizeOf` — it already exists (Lean's
auto-derived structural size, used for `well_founded` proofs since
cycle 3), was never defined with this test in mind, and its exact
formula (`PairId.pair.sizeOf_spec : sizeOf (pair a b) = 1 + sizeOf a +
sizeOf b`) is whatever Lean's `deriving` mechanism happened to produce.
Whatever relationship it has to `glue` is *discovered by checking*, not
designed to hold.

**Result**: `sizeOf` is **not** a strict `glue`-homomorphism
(`sizeOf_pair_ne_glue`, confirming cycle 6's qualitative finding via a
completely independent route — a different map, a different reason) —
but it *is* one up to a precise, constant correction:
`sizeOf_pair_eq_succ_glue : sizeOf (pair a b) = 1 + natIncidence.glue
(sizeOf a) (sizeOf b)`. Not just "doesn't match" (cycle 6's finding) but
"matches exactly once the pairing operation's own unit cost is
accounted for" — a sharper, quantified version of the same underlying
fact, arrived at without touching the circularity risk this cycle was
flagged for. `#print axioms`: `propext`/`Classical.choice`/`Quot.sound`
on both, no `sorryAx`. Added to `CrossInstance.lean`, wired into
`Main.lean`.

**Next hypothesis (cycle 8, not yet attempted)**: seven cycles have now
covered faithfulness (2-4), translation (5), and cross-instance maps
(6-7) for `natIncidence`/`pairIncidenceChained`/`triIncidence`. Still
completely untouched: the three explicitly-labeled-unformalized
placeholders in the root file (`glue_preserves_boundary_operator`,
`linear_invariants_preserved`, `preserves_limits`, all `True := trivial`
by design, per the original bug-fix PR's honesty policy) and T3's
`boundary_functor_soundness`/`linear_completeness` machinery, which has
never been exercised against `natIncidence`/`pairIncidenceChained` at
all (only the triangle graph, via `triangle_boundary_square_zero` and
`triangle_completeness_concrete`). Concretely: does `boundary_composition`
(root file's ∂² check) actually equal zero for a nontrivial index set
drawn from `natIncidence` or `pairIncidenceChained` -- i.e., can
`boundary_operator_square_zero`/`verify_boundary_composition` be
exercised on *these* instances the way `triangle_boundary_square_zero`
exercised them on the triangle, or does the chain/tree shape make the
check trivially pass (all products zero because chains don't "return")
in a way that's less interesting than the triangle's genuine cycle?
Worth checking what the check even *means* for a non-cyclic (tree/chain)
structure before assuming it's informative.

## Cycle 8

**Hypothesis**: (as queued above) one of two guesses about `∂² = 0` on
`natIncidence`/`pairIncidenceChained`'s chain-shaped boundary: either it
trivially holds for any well-founded structure, or it's a vacuous check
because tree/chain shapes "don't return". Checked with `#eval` *before*
committing to either guess, on principle (cheap to check, expensive to
theorize wrongly about first).

**Result**: **both guesses were wrong** — a genuine surprise, not a
confirmation. `verify_boundary_composition natIncidence natIdx6 = false`
(`#eval`, then proved with `decide`): `boundary_composition natIncidence
natIdx6 2 0 = 1 ≠ 0`. `∂² = 0` *fails*, non-trivially, for the Peano
chain. `pairIncidenceChained` fails the same way (`pairIncidenceChained_not_
boundary_square_zero`), for the identical reason, since its atom-chain is
structurally the same construction — checked composing *through* a
`pair` node too (`pairIncidenceChained_boundary_composition_witness`,
`= -1`), confirming the nonzero value propagates in via the chain
reachable from a `pair`'s `snd` endpoint rather than being isolated to
atoms.

**Why, once found**: the triangle's boundary only reaches *nodes*, which
have no boundary of their own — a 2-graded structure (dimension 1 →
dimension 0 → nothing), so `∂²` vanishes for the trivial reason that
there's nothing beyond dimension 0 to compose into. `natIncidence`'s
chain has *unbounded* depth (`boundary n` reaches `n-1`, which has its
own boundary reaching `n-2`, ...), so `∂` composed with itself doesn't
automatically land outside the structure — and the two consecutive
`Sign.neg` links multiply to a nonzero value instead of cancelling. This
retroactively validates a design decision from the original bug-fix PR:
`boundary_operator_square_zero` was made *conditional* on
`verify_boundary_composition inc idx = true` rather than an
unconditional claim, specifically because ∂²=0 isn't generically true —
this cycle shows that hypothesis is a *real*, non-vacuous constraint
that a genuine instance (not a contrived one) actually fails, not
defensive hedging against a hypothetical.

`#print axioms` on all four theorems: `propext`/`Classical.choice`/
`Quot.sound`, no `sorryAx` (`decide` stays fully kernel-checked, no
`native_decide`). Added to `Peano.lean`/`Pairs.lean`, wired into
`Main.lean`.

**Next hypothesis (cycle 9, not yet attempted)**: classical simplicial
homology hits exactly this problem and fixes it by *alternating* the
boundary sign by the element's position/degree (the standard
"alternating sum of faces" convention), specifically so that composing
the boundary map with itself telescopes to zero instead of accumulating.
`peanoBoundary` currently gives every chain link the *same* sign
(`Sign.neg`, regardless of `n`'s parity). Hypothesis: redefining the
chain with an alternating sign (e.g. `n+1 → n` is `neg` when `n` is even,
`pos` when `n` is odd, or some such convention) recovers `∂² = 0` for
the Peano chain — genuinely testable via the exact same `#eval`-first
method this cycle used, not a definition chosen post-hoc to force the
answer (the alternating-sign convention comes from established
mathematics, not from peeking at what would make this specific chain
work). If it works, that's a real, exportable design principle for any
future chain-shaped Inc instance wanting `∂²=0`; if it doesn't, that's
useful too (it would mean Inc's `boundaryMatrix`/`Int`-multiplication
setup doesn't actually reproduce the classical telescoping mechanism,
which would be worth knowing precisely, and probably worth understanding
why before cycle 10).

## Cycle 9

**Hypothesis**: (as queued above) alternating the boundary sign by
parity, the classical simplicial-homology fix, recovers `∂² = 0` for
the Peano chain.

**Method**: before writing any Lean, reasoned about it algebraically.
Real simplicial `∂² = 0` works via *cancellation among multiple faces of
the same simplex* (e.g. a 2-simplex's 3 faces cancel pairwise in the
alternating sum). `peanoBoundary` gives each nonzero element exactly
*one* boundary endpoint — a single-face chain, not a multi-face simplex.
Composing two such links multiplies exactly two nonzero numbers
(`boundaryMatrix(n+2,n+1) * boundaryMatrix(n+1,n)`), and a product of
two nonzero numbers is never zero, *regardless of which signs are
chosen* — there is only ever one term, nothing to cancel it against.
This predicted the alternating-sign fix cannot work, for a specific,
checkable reason, before touching code.

**Result**: **prediction confirmed**, on two levels:
- Empirically first (per this project's `#eval`-before-formalizing
  discipline): built `altIncidence` (`n+1 → n` alternates `Sign.neg`/
  `Sign.pos` by `n`'s parity) and checked — still `false`, as predicted.
- Then generalized past a one-off refutation into an actual theorem,
  `single_link_composition_ne_zero` (root file): for *any* `Incidence`,
  if `i`'s boundary is exactly one nonzero-sign link to `j`, and `j`'s
  boundary is exactly one nonzero-sign link to `k`, then composing
  boundary twice from `i` to `k` is nonzero — independent of which
  signs were picked. This directly proves `altIncidence` (and any other
  single-face chain, present or future) fails `∂² = 0` for *every* `n`
  at once (`altIncidence_not_boundary_square_zero`), not just the one
  index list a `decide` call would check.

This was the most proof-engineering-heavy cycle so far — getting there
required two supporting lemmas (`boundaryMatrix_single_link`: with a
single boundary endpoint, `boundaryMatrix` is exactly that endpoint's
signed value at its target and 0 elsewhere; `foldl_add_eq_count_mul`: a
`List.foldl` summing a function that vanishes off one target reduces to
count-times-value), plus real friction reasoning about `boundaryMatrix`'s
internal `by_cases`-generated term *symbolically* for an abstract
`[DecidableEq I]` — noticeably harder than the `decide`-driven concrete
proofs every earlier cycle relied on, where the kernel just computes
through everything for a concrete type. Recorded as a genuine, if minor,
finding about this codebase: reasoning abstractly about `boundaryMatrix`
is currently more awkward than reasoning about it concretely; a future
cleanup redefining it via an explicit `if h : e.i = j then ... else ...`
term (rather than a tactic-mode `by_cases` inside a `foldl` lambda) might
make this kind of general proof easier to write next time.

`#print axioms`: `boundaryMatrix_single_link` needs only `propext`;
`foldl_add_eq_count_mul` adds `Quot.sound`; the rest add
`Classical.choice` (all standard, no `sorryAx`). Added to root
`IncidenceTheory.lean` (the general theorem, next to
`boundary_operator_square_zero`) and `Peano.lean` (`altIncidence` +
its application), wired into `Main.lean`.

**What this settles**: cycles 1-3 established that `≈`-faithfulness
needs the *right kind* of distinguishing structure (not automatic).
Cycles 8-9 establish the analogous fact for `∂² = 0`: it needs the
*right kind* of multi-face structure (not automatic, and — now proven —
not fixable by sign convention alone for a single-face chain). Both are
instances of the same shape of finding: Inc's abstract machinery
(`boundaryMatrix`, `≈`) is expressive enough to state strong properties,
but satisfying them is a real, checkable constraint on the instance, not
a free consequence of "being an `Incidence`".

**Next hypothesis (cycle 10, not yet attempted)**: `single_link_composition_
ne_zero` shows *why* single-face chains can't achieve `∂² = 0`, which
implies the fix has to add a genuine second face per element, not adjust
signs. Concretely: build a *filled* structure with an actual 2-graded
shape but *infinite* extent, unlike the (finite, 3-node) triangle -- e.g.
an infinite "path complex" `PathId := node (n : Nat) | edge (n : Nat)`
where `edge n` connects `node n` and `node (n+1)` via *two* boundary
endpoints (signed +/-, mirroring `triIncidence`'s edges exactly), and
`node n` has empty boundary. Hypothesis: this satisfies `∂² = 0` for the
*same* trivial dimension-exhaustion reason the triangle does (nodes have
no further boundary) -- if so, that's not surprising, but is a useful
sanity check that the *finite-vs-infinite* distinction was never the
real issue (cycles 8-9 already located the real issue as single-face
vs. multi-face). If confirmed cheaply, more interesting to then check
whether `single_link_composition_ne_zero`'s *converse* direction has any
clean statement: is there a minimal *sufficient* condition (beyond "has
≥2 faces") under which a chain-shaped Inc instance provably satisfies
`∂² = 0`? That would be the genuinely new content for cycle 10, not
just re-confirming the 2-graded pattern again.

## Cycle 10

**Hypothesis**: (both parts queued above) (a) an infinite 2-graded path
complex satisfies `∂² = 0` for the same trivial reason the finite
triangle does, confirming finite-vs-infinite was never the real
variable; (b) there's a clean, general, provable *sufficient* condition
for `∂² = 0`, complementing cycle 9's impossibility theorem.

**Method**: went straight for (b) first, since a general theorem — if
provable — would settle (a) as a one-line corollary rather than needing
a separate proof. Sufficient condition: if every endpoint in `i`'s
boundary points to a "leaf" (an element with empty boundary of its
own), then `∂²` vanishes at `i`, for *any* index set and target. Proof
needs two supporting facts: (1) `boundaryMatrix` unfolded to a plain
`ite`-based `List.foldl` (`boundaryMatrix_eq_foldl`, reused across
several lemmas below — this is exactly the abstraction gap flagged as a
finding in cycle 9, now paid down once rather than worked around per
proof); (2) a leaf's entire row of `boundaryMatrix` is zero (trivial:
folding over `[]`), and any nonzero column must have a genuine witness
endpoint (`boundaryMatrix_ne_zero_witness`) — combine: every term in
`boundary_composition`'s sum is zero, either because `boundaryMatrix
i j = 0` outright, or because `j` is witnessed as a leaf by `hleaf`,
making `boundaryMatrix j k = 0`.

**Result**: **both confirmed**, and (b) turned out cheaper to prove
than cycle 9's impossibility theorem, not harder — no `List.count`
induction needed, since the goal is "sum of zeros is zero"
(`foldl_add_zero_of_all_zero`), simpler than cycle 9's "sum has exactly
one nonzero term" (`foldl_add_eq_count_mul`). `boundary_composition_
zero_of_leaf_boundary` (root file) proves the general sufficient
condition with `#print axioms` showing `propext` only, no `sorryAx`.
Applied it to a fresh instance, `pathIncidence` (`PathComplex.lean`) —
an *infinite* 2-graded path complex (`node n` a leaf, `edge n` connecting
`node n`/`node (n+1)` via two signed endpoints, exactly `triIncidence`'s
edge shape but unbounded) — `pathIncidence_boundary_square_zero` proves
`∂² = 0` for *every* edge, at *every* index set and target,
simultaneously. This is a **stronger** result than
`triangle_boundary_square_zero` ever was: that one `decide`-checks a
single fixed 6-element index list; this one is a universally-quantified
theorem covering infinitely many instances at once. Confirms cycles 8-9
correctly located the real variable as single-face-vs-multi-face, not
finiteness — the triangle's finiteness was never load-bearing for why
it satisfies `∂² = 0`.

`#print axioms` across the whole cycle: `boundaryMatrix_eq_foldl` and
`boundaryMatrix_eq_zero_of_leaf` need **no axioms at all**; the rest
need `propext` only (simpler dependency footprint than cycles 8-9,
which pulled in `Classical.choice`/`Quot.sound` via `decide` and
bisimulation machinery respectively). No `sorryAx`. Added to root
`IncidenceTheory.lean` (general theorem, next to cycle 9's) and a new
file `PathComplex.lean`, wired into `Main.lean`.

**Where this leaves the ∂²=0 thread (cycles 8-10)**: the full picture is
now a clean if-and-only-if-flavored pair, not just one-off checks —
`single_link_composition_ne_zero` (necessary: single-face chains always
fail, any sign) and `boundary_composition_zero_of_leaf_boundary`
(sufficient: leaf-reaching boundaries always succeed). The genuinely
open gap is the *middle* ground: instances that are neither single-face
nor leaf-reaching (e.g. an element with 2+ faces, at least one of which
points somewhere with *further* boundary) — do those succeed, fail, or
depend on details (the multiplicities/signs actually chosen)? That's
real, uncharted territory for a future cycle, not yet queued concretely
because it needs a specific candidate instance to test against first.

**Next hypothesis (cycle 11, not yet attempted)**: pick a genuinely
"middle ground" instance -- multi-face (2+ endpoints per element, so
cycle 9's impossibility doesn't apply) but *not* leaf-reaching (at least
one endpoint points to something with its own nonempty boundary, so
cycle 10's sufficiency doesn't apply either) -- and check empirically
first (per this project's now-established discipline) whether ∂²=0
holds, fails, or depends on the specific sign/multiplicity choice. A
natural, cheap candidate: extend `pathIncidence` so `edge n`'s boundary
includes *three* endpoints instead of two (e.g. add a second edge into
`node n` from `node (n-1)`, so composing through `node n` from `edge n`
now has two contributing routes instead of zero) -- or more simply,
build a small finite instance by hand (3-4 elements) with a deliberately
mixed shape and `#eval` it before committing to any formalization
effort, matching cycles 8-9's method precisely.

## Cycle 11

**Hypothesis**: (as queued above) find a genuinely "middle ground"
instance -- multi-face, faces not leaves -- and check whether `∂² = 0`
holds, fails, or depends on the specific construction.

**Method**: the most natural, well-motivated middle-ground candidate is
also the textbook one -- a genuine *filled 2-simplex*: 3 vertices
(leaves), 3 edges (`∂[i,j] = [j] - [i]`, each edge a leaf-reaching
2-endpoint element, same as `triIncidence`'s), and 1 `face` whose
boundary is the classical *alternating sum of edges*,
`∂[0,1,2] = [1,2] - [0,2] + [0,1]`. `face` has 3 endpoints (multi-face,
cycle 9 doesn't apply) pointing at *edges*, which have their own
nonempty boundary (not leaves, cycle 10 doesn't apply). This is exactly
the construction that makes `∂² = 0` a real theorem in simplicial
homology, not folklore -- worth testing whether this codebase's
`Int`-multiplication `boundaryMatrix` machinery actually reproduces
that mechanism. Checked empirically (`#eval`) before formalizing: by
hand, `∂∂(face, v0) = (+1)·(0) + (-1)·(-1) + (+1)·(-1) = 0`, matching
the classical computation. Also built `wrongSimplexIncidence` -- the
identical shape with the alternation *dropped* (all `+` on `face`'s
boundary) -- as a sensitivity check: does *any* multi-face, non-leaf
construction happen to cancel, or does it need the alternation
specifically?

**Result**: **confirmed, with real (not accidental) cancellation**.
`simplexIncidence_boundary_square_zero` proves `∂² = 0` for the whole
table (not just `face`, via `verify_boundary_composition = true`), via
`decide` -- matching the classical hand-computation exactly, e.g.
`(+1)·(0) + (-1)·(-1) + (+1)·(-1) = 0` at `v0`. And the sensitivity
check earns its keep: `wrongSimplexIncidence_not_boundary_square_zero`
proves the alternation-dropped variant *fails*
(`wrongSimplexIncidence_witness`: `boundary_composition ... face v0 =
-2`, a concrete nonzero witness) -- so this is not a degenerate case
where any sign choice would have worked; getting the alternating
convention right is load-bearing, exactly as classical simplicial
homology says it should be.

Chose `decide` over another general theorem this cycle, deliberately:
cycles 9-10 already delivered two solid general theorems (necessary and
sufficient conditions for the *single-face* and *leaf-reaching* extremes
respectively); a fully general "alternating multi-face sum cancels"
theorem would need to formalize what "alternating sum over a list of
faces" means abstractly first, a substantially larger undertaking than
either of those, for a single confirming instance. `decide` (the
triangle's own, already-proven-effective pattern) was the proportionate
choice here -- concrete, honest, fully verified, without inflating the
cycle's scope just to produce a third general theorem.

`#print axioms` on all three theorems: `propext` only, no `sorryAx`.
Added as a new file, `Simplex.lean`, wired into `Main.lean`.

**Where this leaves the ∂² = 0 thread (cycles 8-11)**: the picture is
now genuinely complete at the level this project can currently reach --
necessary condition (single-face chains always fail, cycle 9),
sufficient condition (leaf-reaching boundaries always succeed, cycle
10), and a worked confirmation that the *real* middle ground (proper
multi-level simplicial structure) succeeds via the actual classical
mechanism, not a coincidence (cycle 11, with the sensitivity check as
the falsifiable control). A general theorem covering the alternating
multi-face case remains open but is now a well-scoped, well-motivated
target rather than a vague "check something in the middle" — worth
attempting in a future cycle if there's a concrete need for it (e.g. if
a future instance wants ∂²=0 with more than 3 faces and hand-verifying
becomes impractical), rather than for its own sake.

**Next hypothesis (cycle 12, not yet attempted)**: the ∂² = 0 thread
(cycles 8-11) has reached a natural resting point. Shift back to a
different open thread from earlier cycles: cycle 6 found `PairId.atom`
preserves `boundary`/`unit` but not `glue` (algebraic vs. coalgebraic
layers don't automatically travel together); cycle 7 quantified that
gap precisely for `sizeOf`. Untested: does `simplexIncidence`
(this cycle's new instance) or `pathIncidence` (cycle 10's) offer a
*third* data point for that same question -- e.g. is there a natural
boundary-preserving embedding from `pathIncidence` into
`simplexIncidence`-like structures (both being edge/node-shaped), and
does *its* `glue` fail to compose for the same or a different reason?
Alternatively, revisit cycle 5's translation-faithfulness question for
`simplexIncidence`/`pathIncidence` specifically, now that two more
worked instances exist to test a translation against. Genuinely open
which is more promising -- decide at the start of cycle 12 based on
which has a cheaper first empirical check.

## Cycle 12

**Hypothesis**: went with the translation-faithfulness direction (the
cheaper-looking first check): validate cycle 4's general
`incidence_bisim_faithful` theorem against `simplexIncidence` as a
third, genuinely 3-graded (vertex/edge/face) data point -- expected a
confirmation, since cycles 4/8's method (assign a dimension/measure,
prove boundary strictly decreases it, prove boundary-extensionality)
looked like it should transfer directly.

**Result**: **the expectation was wrong, and the reason is a genuine,
useful discovery, not a dead end**. Attempting `hext` for
`simplexIncidence` hit an immediate wall: `v0`, `v1`, `v2` all have
*empty* boundary with *nothing* distinguishing one from another (unlike
`natIncidence`'s `0`, which is uniquely the only empty-boundary element
in its chain -- every other natural has *some* nonempty boundary
telling it apart). This means `boundaryMatched simplexIncidence (=) v0
v1` holds *vacuously* (both sides empty), so `hext` as stated is simply
false for this instance. This is cycle 2's "flat atoms collapse"
pattern (`pairIncidence_atoms_collapse`) -- independently rediscovered
here in a structurally unrelated third instance, confirming it is a
*general* phenomenon (any `Incidence` with 2+ elements sharing identical
boundary, not just an artifact of how `PairId`'s atoms happened to be
built) rather than something specific to the earlier two instances.

Proved the collapse concretely rather than asserting it:
`simplexIncidence_vertices_collapse` (`approxBisim simplexIncidence v0
v1`) via the same bisimulation-relation-construction technique as
`pairIncidence_atoms_collapse`, plus `simplexIncidence_vertices_not_eq`
as the contrasting fact (`v0 ≠ v1`). `#print axioms`: `propext`/
`Quot.sound`, no `sorryAx`.

Attempted one natural extension -- does the collapse *propagate* up a
dimension? `e01`/`e02`/`e12` only differ in *which* (now pairwise-
bisimilar) vertices they connect, so plausibly they collapse too. A
first attempt at `e01 ≈ e02` hit real proof-engineering friction (a
9-way case split from combining vertex- and edge-level relation
clauses, plus reaching for `tauto`, unavailable without mathlib) that
didn't resolve in reasonable time. **Left honestly unproved rather than
forced through** -- recorded in `Simplex.lean` as a stated, plausible,
but explicitly *not formalized* conjecture, not claimed as established.
This is the same discipline as leaving `glue_preserves_boundary_operator`
etc. as honest placeholders in the original bug-fix PR: a claim without
a proof is not a theorem here, regardless of how likely it looks.

**What this adds to the running picture**: cycles 1-4 already
established that faithfulness needs the right distinguishing structure
and isn't automatic; this cycle's contribution isn't a new *mechanism*,
it's evidence about *scope* -- three independent, structurally unrelated
instances (`pairIncidence`'s bare atoms, and now `simplexIncidence`'s
bare vertices) hit the identical failure mode, while the *fixed*
versions (`natIncidence`'s chain, `pairIncidenceChained`'s tagged
atoms) all succeed via the identical fix (give every element enough
boundary structure to be recovered uniquely). That's a stronger
confirmation of cycle 3-4's "general recipe" than any single instance
could provide on its own -- convergent failure and convergent fix
across unrelated constructions.

**Next hypothesis (cycle 13, not yet attempted)**: two candidates,
either legitimate:
(a) finish what this cycle left open -- prove
`simplexIncidence_edges_collapse` (or the full three-class
characterization: `≈` on `simplexIncidence` coincides exactly with
"same dimension") with a cleaner proof strategy than the 9-way case
split that stalled this cycle, e.g. building the relation as a single
`simplexMeasure x = simplexMeasure y` predicate (matching cycle 4's
measure-based framing) rather than an explicit disjunction of specific
element names, which may sidestep the case explosion entirely; or
(b) the translation-faithfulness direction originally queued for cycle
12, now revisited for `pathIncidence` specifically (cheaper than
`simplexIncidence` since `pathIncidence`'s nodes, like `natIncidence`'s,
are *not* uniformly empty-boundary -- only `node 0` needs checking,
not three interchangeable leaves), rather than assumed to work the same
way `natIncidence`'s did. Lean toward (a) if the `simplexMeasure`-based
relation looks like a quick win once attempted; toward (b) if it
doesn't, rather than re-fighting the same case split that already
stalled once.
