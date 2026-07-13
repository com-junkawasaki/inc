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

## Cycle 13

**Hypothesis**: tried (a) first (the `simplexMeasure`-based relation).

**Result on (a)**: **still not a quick win, correctly abandoned**. Two
focused attempts at `simplexMeasure_isBisimulation` both hit real
friction -- `simp_all`/`cases`-combinator chains behaving non-uniformly
across the differently-shaped vertex/edge/face goals (some closing
early, breaking subsequent tactic steps; residual `boundaryCompatible`
disjunctions that `decide` didn't close as cleanly as hoped through the
large `simplexIncidence` structure literal). Per the explicit guidance
from cycle 12 not to re-fight this, stopped after the second attempt
and pivoted to (b) rather than sinking further effort into a proof
strategy that had now failed twice for related but not identical
reasons -- itself the right call, not a failure to record apologetically.

**Pivoting to (b), and a self-correction along the way**: before
building the planned `pathIncidence` translation-faithfulness proof,
re-checked cycle 12's own log claim that motivated preferring
`pathIncidence` over `simplexIncidence` in the first place -- "`pathIncidence`'s
nodes, like `natIncidence`'s, are not uniformly empty-boundary, only
`node 0` needs checking." **That claim was wrong**, and had never been
verified before being written down: `pathBoundary (PathId.node _) = []`
for *every* `n`, not just `0` (`PathComplex.lean`, unchanged since
cycle 10) -- unlike `natIncidence`'s `0`, which really is the unique
empty-boundary element in its chain. Caught by re-reading the actual
definition before trusting the log's own prior claim, rather than
building the planned proof on top of an unverified premise.

Given this, `pathIncidence`'s nodes should collapse under `≈` exactly
like `simplexIncidence`'s vertices did (cycle 12) -- checked, and
**confirmed**: `pathIncidence_nodes_collapse` (`approxBisim pathIncidence
(node 0) (node 1)`) proves it via the identical bisimulation-construction
technique as `pairIncidence_atoms_collapse`/`simplexIncidence_vertices_collapse`,
plus `pathIncidence_nodes_not_eq` as the contrast. `#print axioms`:
`propext`/`Quot.sound`, no `sorryAx`. Added to `PathComplex.lean`, wired
into `Main.lean`.

This makes **four** independent, structurally unrelated instances
(`pairIncidence`'s flat atoms, `simplexIncidence`'s vertices, and now
`pathIncidence`'s nodes -- plus the three matching *fixed* instances,
`natIncidence`'s chain, `pairIncidenceChained`'s tagged atoms, that all
succeed via the identical remedy) converging on the same pattern. At
this point it's less a "surprising discovery" each time and more a
reliably-predictable failure mode this project now understands well:
*any* `Incidence` construction with 2+ elements sharing identical
(often empty) boundary will collapse under `≈`, full stop, regardless
of which unrelated domain the instance is modeling.

**What this cycle demonstrates about the method itself, not just the
math**: catching and correcting a prior cycle's own unverified claim
(rather than compounding it by building a proof on top of it) is
exactly the kind of self-checking a "co-scientist" loop is supposed to
do differently from a straight-line implementation loop -- verify
inherited premises before extending them, not just new hypotheses.

**Next hypothesis (cycle 14, not yet attempted)**: the "flat leaves
collapse" finding is now solidly established (four instances) with an
equally solid fix (three instances demonstrate it). Both `translation-
faithfulness for pathIncidence` (the *fixed* question -- pathIncidence
still needs its `hdec`/`hext` proved once nodes are excluded/fixed, or
more honestly: `pathIncidence` as currently built does *not* satisfy
full `≈`-faithfulness, so that door is now known-closed rather than
open) and `simplexMeasure`-based collapse-of-edges (option (a), twice
attempted, twice stalled) are now lower priority than they looked at
the start of cycle 12. Genuinely fresh ground: **fix `pathIncidence`'s
nodes the same way cycle 3 fixed `pairIncidenceChained`'s atoms** (give
`node n` a distinguishing chain-style boundary reaching `node (n-1)`,
reusing the exact `PeanoRole.pred`/chain-role pattern already used
twice) and re-attempt full faithfulness on the *fixed* instance -- a
well-understood recipe at this point, low risk, and would round out
`PathComplex.lean` to match `Pairs.lean`'s completed
broken-then-fixed pair (cycle 2 → cycle 3) rather than leaving it as
the one instance in this project with a known, permanent, undiagnosed-until-now
collapse and no accompanying fix.

## Cycle 14

**Hypothesis**: (as queued above) apply cycle 3's exact remedy to
`pathIncidence`'s nodes -- a distinguishing chain-style boundary, role-
tagged apart from the existing edge-endpoint structure -- and recover
full `≈`-faithfulness for the fixed instance.

**Method**: `PeanoRole` couldn't be reused directly for the fix (it has
only one constructor, `pred` -- not enough room to keep edge-endpoints
and the new node-chain-links role-disjoint, which is exactly the
disambiguation cycle 3 needed for `PairRole`). Defined a fresh
`PathRole` (`edgeEnd | chain`) instead: `node 0` stays the chain's base
case, `node (n+1)` gains one `chain`-role link to `node n`, and edges
keep their original two-endpoint shape now tagged `edgeEnd`. Built
`pathIncidenceChained` as a genuinely separate instance (`pathIncidence`
from cycle 10 untouched, its own `pathIncidence_boundary_square_zero`
still holds and doesn't need this fix) -- the same broken/fixed-sibling
relationship as `pairIncidence`/`pairIncidenceChained` (cycle 2/3).
Measure for cycle 4's general theorem: `pathMeasure (node n) = n`,
`pathMeasure (edge n) = n + 2`, chosen so both the node-chain link and
an edge's two endpoints strictly decrease it.

**Result**: **confirmed, this time without new proof-engineering
surprises** -- this was the smoothest of the three "fix + reprove
faithfulness" cycles (2→3, 12/13→14) so far, likely because the recipe
is now genuinely well-understood rather than being worked out fresh.
Two small mechanical slips did surface and get caught by the compiler
immediately: (1) `rcases X with X | X` against what turned out to be a
*singleton*-list membership (no disjunction to split, since the target
node's boundary at that point was a base case, not the general
successor case) -- fixed by dropping the `rcases`, matching the same
pattern `natIncidence_hext`/`pairIncidenceChained_hext` already used;
(2) `omega` asked to close a `PathId`-constructor-level goal (`edge m =
edge n`) from a `Nat` fact (`m = n`) -- `omega` only proves arithmetic
goals, not this; needed `rw [heq]` instead. Neither took long to
diagnose from the actual error message. `pathIncidenceChained_hdec`/
`_hext`/`_approxBisim_iff` all typecheck; `#print axioms`: the standard
`propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`. Added to
`PathComplex.lean`, wired into `Main.lean`.

While transcribing the verified scratch proof into the project file, a
small extra case-split I'd added by hand (not present in the version
that actually compiled) slipped in and needed to be caught by diffing
against the verified source before committing -- a reminder that
"verified in isolation" and "correctly copied into place" are two
different checks, both worth doing, not one implying the other.

`PathComplex.lean` now matches `Pairs.lean`'s shape exactly: one broken
instance with a proven, concrete collapse witness, one fixed instance
with proven full faithfulness, both kept side by side rather than the
broken one being deleted once superseded -- the contrast is itself part
of the record.

**Where the "flat leaves collapse" thread now stands (cycles 2-3,
12-14)**: four independent constructions hit the failure
(`pairIncidence`, `simplexIncidence`, `pathIncidence`), three of which
now have a completed, proven fix alongside them (`natIncidence` was
never broken to begin with, but demonstrates the same chain-based
remedy; `pairIncidenceChained`; `pathIncidenceChained`). The
`simplexIncidence` fix (the still-open "edges collapse too" question
from cycle 12) is the only remaining loose end in this thread, and two
attempts have already stalled on it -- worth revisiting only with a
genuinely different strategy, not a third repeat of the same case-split
approach.

## Cycle 15

**Hypothesis**: (as queued above) test `PathId.node : Nat → PathId` as a
boundary/unit/glue-naturality candidate between `natIncidence` and
`pathIncidenceChained`, via the exact three-theorem template cycle 6
used for `PairId.atom` -- expecting, but not assuming, the same
qualitative mixed result (boundary/unit natural, glue not).

**Method**: `#eval`/inspection first, per discipline. Compared
`pathBoundaryChained`'s `node (n+1)` case (`[{node n, chain, neg, 1}]`)
against `peanoBoundary`'s `succ n` case (`[{n, pred, neg, 1}]`) --
identical shape modulo the `pred → chain` role relabeling, exactly the
same relationship cycle 3 built between `pairBoundaryChained`'s atom
case and `peanoBoundary`. Compared `pathIncidenceChained.glue` (`if i =
node 0 then some j else some i`, left-biased selection) against
`natIncidence.glue` (addition) -- structurally unrelated, same as
`pairIncidenceChained.glue` vs. `natIncidence.glue` in cycle 6. Wrote
the four theorems (`node_boundary_natural`, `node_unit_natural`,
`node_glue_not_natural` with the `m=2,n=3` witness,
`node_approxBisim_iff` composing cycle 4's general faithfulness for both
instances) in a scratch file (`/tmp/test_path_hom.lean`) against
`lake env lean` before touching the project, then diffed against the
transcribed version in `CrossInstance.lean` before committing (cycle
14's transcription-slip lesson, applied).

**Result**: **confirmed -- the same qualitative outcome, term for
term**, not a foregone conclusion but a genuine (if expected) empirical
match. All four theorems typecheck with zero `sorry`; `#print axioms`
on each: `propext`, `Classical.choice`, `Quot.sound` only, no `sorryAx`.
`node` preserves `boundary` (up to the same `pred → chain` relabeling
pattern) and `unit`, and fails to preserve `glue` with the same shape of
witness (`node 2 glue node 3 = node 2 ≠ node 5`). The value of this
cycle isn't the individual theorems (each is a near-syntactic copy of
cycle 6's) but what running the *same test twice, on a deliberately more
structurally-similar pair*, rules out: it shows the boundary/glue split
from cycle 6 was never about `PairId` being a richer nested type than
`natIncidence` -- `pathIncidenceChained` is a bare `Nat`-indexed chain,
as structurally close to `natIncidence` as two independently-built
instances get, and the same split still holds. The real invariant is
`glue`'s algebraic *kind* (addition vs. left-biased selection is a
mismatch regardless of carrier shape), not any structural distance
between source and target. Added to `CrossInstance.lean` (now importing
`PathComplex.lean` alongside `Peano.lean`/`Pairs.lean`), wired into
`Main.lean`. Full `lake build`: 38/38 jobs, clean. Repo-wide `sorry`
grep: none.

**Where the "cross-instance homomorphism" thread now stands (cycles
6-7, 15)**: two independently-built `Nat`-indexed embeddings
(`PairId.atom`, `PathId.node`) into two independently-built target
instances both land on the identical mixed result, plus one independent
confirmation via a completely different function (`sizeOf`, cycle 7).
Three data points now agree; this thread doesn't need a fourth
confirmation of the same shape either, similar to how cycle 14 closed
out the "flat leaves collapse" thread.

## Cycle 16

**Hypothesis**: (item 2 queued above) does `pathIncidenceChained` (fully
faithful since cycle 14) satisfy `∂² = 0`? Its nodes are no longer
leaves (each carries a `chain` link to its predecessor), so cycle 10's
leaf-boundary sufficiency theorem shouldn't straightforwardly apply --
and the node-chain's shape looks like it should instead trigger cycle
9's impossibility theorem, the same way it did for `natIncidence` and
`pairIncidenceChained` (cycle 8).

**Method**: `#eval` first. Confirmed `boundary_composition
pathIncidenceChained pcIdx (node 2) (node 0) = 1` and
`verify_boundary_composition ... = false` on a 3-node index set --
matches the prediction. Before formalizing a bespoke proof, checked
whether the node-chain literally matches
`single_link_composition_ne_zero`'s hypothesis shape (root file, cycle
9: `boundary i = [e1]`, `e1.i = j`, `sign ≠ 0`, `boundary j = [e2]`,
`e2.i = k`, `sign ≠ 0`, `j ∈ idx`): `pathBoundaryChained (node (n+2)) =
[{node (n+1), chain, neg, 1}]` and `pathBoundaryChained (node (n+1)) =
[{node n, chain, neg, 1}]` -- an exact match, term for term, the same
shape `altIncidence_not_boundary_square_zero` (cycle 9) used for a
different instance. Applied the general theorem directly rather than
re-deriving. Also scanned wider than the queued question asked, on a
7-element index (nodes 0-3, edges 0-2) including edges, to check
honestly whether the failure was confined to the chain or not, before
writing up a claim either way.

**Result**: **confirmed, and cheaply** -- `pathIncidenceChained_not_boundary_square_zero`
is a direct one-line application of `single_link_composition_ne_zero`,
generalized over all `n` (not just a `decide`-checked instance), because
the fix's chain shape *is* the general theorem's hypothesis shape
exactly. Zero new proof engineering needed; this is the actual payoff of
having generalized `single_link_composition_ne_zero` in cycle 9 instead
of leaving it as one bespoke instance proof. `#print axioms`: standard
three, no `sorryAx`.

The wider scan surfaced something **not implied by the queued
question**: `pathIncidenceChained`'s edges *also* compose nonzero --
`edge 1` against `node 0` gives `1`, `edge 1` against `node 1` gives
`-1`, and this pattern repeats down the chain. Neither `natIncidence`
nor `pairIncidenceChained` has a multi-entry element at all, so this is
a genuinely richer failure surface than either of the two prior
instances -- and it is *not* covered by `single_link_composition_ne_zero`
(which requires a singleton boundary at the source), so generalizing it
would need new machinery, not a corollary. Reported as a concrete
`decide`-checked witness (`pathIncidenceChained_edge_witness`) rather
than forced into a general theorem the discipline doesn't support yet --
left as an explicit open item below rather than glossed over. Added to
`PathComplex.lean`, wired into `Main.lean`. Full `lake build`: 38/38
jobs. Repo-wide `sorry` grep: none.

**Synthesis -- the faithfulness-fix's price, now confirmed three times**:
`natIncidence` (never broken, but exhibits the shape), `pairIncidenceChained`
(cycle 8), and now `pathIncidenceChained` (this cycle) all received the
identical remedy for the collapse problem -- a single, nonzero-signed,
measure-decreasing chain link per element -- and all three, independently,
fail `∂² = 0` for the same reason: that remedy's shape *is*
`single_link_composition_ne_zero`'s hypothesis. This isn't a coincidence
needing three separate discoveries; it's a single provable fact
(`single_link_composition_ne_zero` itself) that keeps re-manifesting
because the ≈-faithfulness fix and the ∂²-impossibility theorem share a
hypothesis shape. Put plainly: **making elements distinguishable enough
to be `≈`-faithful, via the specific single-link-chain remedy this
codebase keeps reaching for, structurally forces `∂² ≠ 0`** on those same
elements. Whether *some other* remedy could fix faithfulness without
this cost is open -- not attempted here, and not implied by anything
proved so far.

**Where the "faithfulness-fix vs. ∂²=0" tension now stands (cycles 8-10,
16)**: three confirming instances via the same general theorem is enough
to treat this connection as established, not needing a fourth repeat.
`pathIncidenceChained`'s edge-level failure remains a genuinely open,
unformalized item (see below), distinct from this now-closed thread.

## Cycle 17

**Hypothesis**: (item 2 queued above) generalize `pathIncidenceChained`'s
edge-level `∂² ≠ 0` failure (cycle 16's `decide`-checked concrete
witness at `edge 1`) into a `∀ n` statement, by building the "two-entry-
boundary composition" machinery `single_link_composition_ne_zero`
doesn't cover.

**Method**: extended cycle 9/10's exact techniques one entry further,
rather than inventing something new. (1) `boundaryMatrix_two_link`:
the two-entry analogue of `boundaryMatrix_single_link` -- given
`inc.boundary i = [e1, e2]` with `e1.i ≠ e2.i`, `boundaryMatrix inc idx
i x` is the sum of each entry's signed contribution, gated by which of
the two targets `x` matches. (2) `foldl_add_eq_count_mul_two`: the two-
target analogue of `foldl_add_eq_count_mul`, same induction shape with
one more case split. (3) `two_link_composition_value`: composes the
first two into an exact closed-form `∂²` value at a two-entry-boundary
element, the same way `single_link_composition_ne_zero` composed its
single-entry counterparts -- except this one yields a *value*, not just
a nonzero-ness fact, since cycle 16's witnesses were exact numbers
(`-1`, `+1`), not merely "nonzero". Iterated each piece in a scratch
file against `lake env lean` before touching the project, per
discipline.

**Result**: **confirmed and fully generalized**, but with real proof-
engineering friction along the way, exactly as anticipated when this was
queued -- not a one-liner. The recurring obstacle was `if`-condition
*orientation*: `rw`/`simp only` treat `if a = b then _` and `if b = a
then _` as syntactically different targets even though propositionally
equivalent, and `boundaryMatrix_eq_foldl`'s fold produces one specific
orientation per branch that doesn't match either the hypothesis's or the
goal's orientation for free. Diagnosed each mismatch by deliberately
forcing an error (`simp` instead of `sorry`, so the elaborator prints
the exact residual goal) rather than guessing blind -- far faster than
reasoning about `dite`/fold unfolding on paper, and a better version of
the same lesson cycle 9 first hit with `dite` friction. One more surprise:
after transcribing into the *root* file, the same `simp only [...]`
calls needed no trailing `rfl` there (unlike the scratch file against
`PathComplex.lean`), and Lean reported "no goals to be solved" when the
now-redundant `rfl` was left in -- removed once caught by the build,
not assumed away. All three general lemmas verify with `propext`
(`Quot.sound` on two of them) only, no `Classical.choice`, no
`sorryAx` -- cleaner even than most instance-specific proofs in this
project. The five `PathComplex.lean`-specific corollaries built on top
(`pathIncidenceChained_node_self_boundary_zero`,
`_node_chain_boundary`, `_node_chain_boundary_zero`,
`_edge_node_witness`, `_edge_prev_node_witness`) verify with the
standard three axioms. `pathIncidenceChained_edge_node_witness` proves
`edge n` vs. `node n` is *always* `-1`, and
`pathIncidenceChained_edge_prev_node_witness` proves `edge (n+1)` vs.
`node n` is *always* `+1` -- for every `n`, not just cycle 16's `edge 1`
instance. Full `lake build`: 38/38 jobs. Repo-wide `sorry` grep: none.

Added `boundaryMatrix_two_link`/`foldl_add_eq_count_mul_two`/
`two_link_composition_value` to the root file (general, reusable
infrastructure, same placement convention as cycle 9/10's lemmas); the
five corollaries to `PathComplex.lean`; wired into `Main.lean`.

**Where the "two-entry-boundary ∂²" thread now stands (cycle 17)**:
one instance (`pathIncidenceChained`'s edges) fully generalized, and the
machinery is explicitly built instance-agnostic (parametrized over any
`Incidence`, not `PathId`-specific) so it's available for reuse --
`simplexIncidence`'s edges (`e01`/`e02`/`e12`, also two-entry boundaries)
are a natural next candidate for this exact machinery if a future cycle
wants a second confirming instance, though not queued as mandatory (one
clean general theorem may be enough, similar to how cycle 9's single-
link theorem needed only `altIncidence` as a second data point before
being trusted as general).

## Cycle 18

**Hypothesis**: (queued above) attempt cycle 12's stalled
`simplexIncidence` edges-collapse conjecture a third time, but only with
a genuinely different strategy -- specifically, build a reusable
"boundary-entries-pairwise-related ⇒ elements bisimilar" lemma first,
rather than repeating the hand-rolled existential case split that
stalled twice.

**Method**: the two prior attempts (cycle 12) worked directly with
`boundaryMatched`'s raw existential definition (`∃ e', e' ∈ ... ∧
boundaryCompatible ... ∧ rel ...`), which meant re-deriving the witness
existence proof by hand inside every one of a 9-way case split, with
`simp_all`/`tauto` (the latter unavailable without mathlib) fighting the
combinatorics. This attempt inverted the approach: build a lemma that
takes an *already-known* positional pairing between two length-2
boundaries (which entry corresponds to which, already proven compatible
and `rel`-related) and concludes `boundaryMatched` directly --
`boundaryMatched_of_two_entries`. Paired with `boundaryMatched_symm`
(free `(i,j) → (j,i)` for a symmetric `rel`, cutting the 9 edge-pair
cases to 3 "canonical" ones + their 3 symm-derived reverses + 3
self-pairs), each of the 9 post-`rcases`-`subst` goals became one
concrete term-mode `exact` call, tried via `first | ... | ...` against
all nine generated goals. Iterated in a scratch file against `lake env
lean` before touching the project, testing the two general lemmas in
isolation first, then the full 9-case proof, then the final
`approxBisim` derivation -- each stage confirmed working before moving
to the next, rather than writing the whole thing at once and debugging
blind.

**Result**: **confirmed on the first full attempt with the new
strategy** -- a sharp contrast with the two stalls, and a real
confirmation that the *shape* of the proof, not the *effort* put into
the old shape, was the blocker. `simplexEdgeVertexRel_isBisimulation`
(the 9-case proof) and `simplexIncidence_edges_collapse` (`e01 ≈ e02`,
`e01 ≠ e02`, both proven) typecheck cleanly on the first complete
transcription. `#print axioms`: `boundaryMatched_of_two_entries` and
`boundaryMatched_symm` need only `propext` -- not even
`Classical.choice`, cleaner than most instance-specific proofs in this
project; the full simplex proof adds only `Quot.sound`. No `sorryAx`
anywhere. One unrelated build snag surfaced while wiring into
`Main.lean`: `main`'s `do` block (one `IO.println` per cycle, 18 cycles
now) hit Lean's default `do`-notation recursion depth limit -- a known
consequence of long linear `do` sequences being desugared right-
recursively, not a bug in any proof. Fixed with `set_option maxRecDepth
4096` at the top of `Main.lean`, with headroom for future cycles rather
than re-hitting and re-raising it incrementally each time. Full `lake
build`: 38/38 jobs. Repo-wide `sorry` grep: none.

Added `boundaryMatched_of_two_entries`/`boundaryMatched_symm` to the
root file (general, reusable -- same placement convention as prior
cycles' infrastructure lemmas); `simplexEdgeVertexRel`/
`simplexEdgeVertexRel_symm`/`simplexCompat_refl`/
`simplexEdgeVertexRel_isBisimulation`/`simplexIncidence_edges_collapse`/
`simplexIncidence_edges_not_eq` to `Simplex.lean`, replacing the old
"plausible but not formalized" comment; wired into `Main.lean`.

**Synthesis -- a methodology lesson, not just a proof result**: this
project's own stated discipline ("worth a third attempt only with a
different strategy") is what made the difference here, concretely, not
just in principle. The first two attempts and this one all targeted the
*same true fact*; only the proof *strategy* changed, and that alone was
the entire difference between two stalls and a first-try success. Worth
carrying forward explicitly: **when a proof stalls twice on the same
tactic shape, the next attempt should change the shape (extract
reusable infrastructure that turns the hard part into a direct term)
before trying again with more tactic firepower on the same shape.**

**Where the "flat leaves collapse" thread now stands (cycles 2-3,
12-14, 18)**: all four originally-identified collapse instances
(`pairIncidence`'s atoms, `simplexIncidence`'s vertices AND now edges,
`pathIncidence`'s nodes) are fully resolved -- either fixed (three
instances) or proven to collapse with no claim of a fix needed
(`simplexIncidence`, where the collapse is simply a true fact about the
unfixed instance, not a defect requiring remedy the way the "flat atoms"
cases were). No open items remain in this thread.

## Cycle 19

**Hypothesis**: (item 1 of the audit queued above) does
`two_link_composition_value` (cycle 17) "degrade sensibly" when the
composition target `k` coincides with one of the two boundary targets
`j1`/`j2` themselves, or does it need an unstated side condition?

**Method**: re-read the theorem's own proof first, without writing new
Lean: it never assumed `k ∉ {j1, j2}` anywhere -- `k` is just the third
free index threaded through `boundaryMatrix inc idx j1 k` /
`boundaryMatrix inc idx j2 k` on the right-hand side, no case split on
its relationship to `j1`/`j2`. So in the abstract, the answer is "yes,
trivially, nothing to fix" -- but a vacuous confirmation isn't worth a
cycle on its own. Applied it concretely instead, at the one witness-
worthy value cycle 17 hadn't checked: `k = node (n+1)`, `edge n`'s *own*
forward endpoint (as opposed to `node n`, its start, and `node (n-1)`,
already covered). Checked empirically first (`#eval`): scanned `edge 2`
against `node 0`..`node 4` in one call, getting `[0, 1, -1, 0, 0]` --
before committing to formalizing just the one new point, confirmed the
*entire* row (not only `node 3` = the analogue of `node (n+1)`) is zero
outside the two already-proven witnesses, i.e. nothing else was hiding
in the row that cycle 17 missed.

**Result**: **confirmed, and the picture is now complete, not
partial**. `pathIncidenceChained_node_forward_zero` (`node n`'s
boundary never points forward to `node (n+1)`, for any `n`) plus the
already-proven `pathIncidenceChained_node_self_boundary_zero` are
exactly the two facts `two_link_composition_value` needs to conclude
`pathIncidenceChained_edge_node_next_zero`: `edge n` vs. `node (n+1)`
is *always* `0`. Combined with cycle 17's two theorems, `pathIncidenceChained`'s
edge-vs-node composition table is now fully characterized for every `n`:
`+1` at the predecessor, `-1` at the start, `0` everywhere else --
not just at three sampled points, but as a closed-form fact following
from the general machinery. One minor mechanical note: `simp` alone
couldn't close the final `¬ k = k + 1 + 1` arithmetic side-goal in
`pathIncidenceChained_node_forward_zero`'s successor case (unlike most
of this project's `PathId`-level case splits) -- needed
`PathId.node.injEq` to reduce the `PathId` equality to a bare `Nat`
one, then `omega` to close it, rather than `simp` alone. `#print
axioms`: standard three, no `sorryAx`. Full `lake build`: 38/38 jobs.
Repo-wide `sorry` grep: only a string literal inside a `Main.lean`
`IO.println` (the word "sorry" as demo *text*, describing cycle 18's
finding) -- not an actual proof gap, checked before treating the grep
hit as real.

**Synthesis**: this cycle is the first one whose starting point was
"audit an existing theorem" rather than "test a new instance" or "close
a stalled conjecture" -- and it still produced a genuinely new, useful
fact (not a restatement), because the abstract audit question
("degrades sensibly?") turned into a concrete one ("what's the value at
this specific untested point?") that the general theorem could answer
immediately once asked. Worth remembering as a cycle-selection option
going forward, alongside "new instance" and "generalize a stalled
result": periodically ask each general theorem "have all its natural
free parameters actually been exercised, or only some?" -- gaps found
this way tend to be cheap to close (this one was, having already-proven
lemmas do almost all the work) precisely because the hard infrastructure
was already built for a different purpose.

## Cycle 20

**Hypothesis**: (item 2 of cycle 18's audit queue) does
`boundaryMatched_of_two_entries` have a natural three-(or-more)-entry
generalization, motivated by `simplexIncidence.face`'s genuine 3-entry
boundary? Queued explicitly with a caution attached: check concretely
first whether `face` even has a plausible bisimulation partner, rather
than assuming the generalization is warranted.

**Method**: did the concrete check the hypothesis asked for, before
writing any Lean. Grepped every `boundary`-defining function in the
project (`peanoBoundary`, `pairBoundary`/`pairBoundaryChained`,
`pathBoundary`/`pathBoundaryChained`, `simplexBoundary`, `triBoundary`)
for any element with 3+ boundary entries besides `face` itself.

**Result**: **none found -- the generalization is premature, and
declined rather than built speculatively.** `PairId.pair`,
`pathIncidenceChained`'s edges, and `simplexIncidence`'s own edges
(`e01`/`e02`/`e12`) are all 2-entry; `face` is the *only* 3-entry
element anywhere in this codebase, and (being the unique top-dimensional
element of a single fixed 2-simplex) has no natural peer to test a
bisimulation-collapse conjecture against the way `v0`/`v1`/`v2` and
`e01`/`e02`/`e12` did. Building a 3-entry `boundaryMatched` lemma now
would validate against zero real instances, the same premature-
abstraction risk this project deliberately avoided twice already:
`single_link_composition_ne_zero` (cycle 9) waited for `altIncidence` as
a second data point before being trusted as general, and
`two_link_composition_value` (cycle 17) was itself motivated by an
*existing* concrete need (`pathIncidenceChained`'s edges), not built on
spec. Recording a declined generalization is itself a valid research
output under this project's discipline -- consistent with, not a
departure from, "don't force scope."

With that item closed (as "not now," not "abandoned" -- it can be
revisited if a second 3-entry instance ever arises), used the remaining
cycle budget on a different, well-scoped, definitely-not-premature task:
T5 (translation faithfulness) had only ever been exercised on two
instances (`natToFiniteSet` for `natIncidence`, `pairToShape` for
`pairIncidenceChained`, both cycle 5); `pathIncidenceChained` (fully
faithful since cycle 14, so the same "injective translation reflects
≈" pattern applies cleanly) never got one. Built `pathToNatBool : PathId
→ Nat × Bool` (`node n ↦ (n, false)`, `edge n ↦ (n, true)`), proved
injective by a direct `cases`/`simp` (no induction needed, unlike
`natToFiniteSet`'s length-counting or `pairToShape`'s structural
recursion), and `pathToNatBool_reflects_approxBisim` via the same
one-line composition with `pathIncidenceChained_approxBisim_iff` cycle
5's two instances used. All three theorems typecheck; `#print axioms`:
`pathToNatBool_injective` needs only `propext`, `_reflects_approxBisim`
adds the standard `Classical.choice`/`Quot.sound`. Full `lake build`:
38/38 jobs. Repo-wide `sorry`-as-tactic grep: none (a broad text grep
for the *word* "sorry" now also matches cycle 18's demo-text string in
`Main.lean`, describing "zero sorry" -- distinguished by grepping for
the tactic form specifically, not just the substring, since cycle 19
first hit this false positive).

**Synthesis**: `pathToNatBool`'s near-triviality compared to
`pairToShape`'s genuine structural recursion is itself a small but real
data point, not just an easy win -- translation-construction *effort*
tracks the *carrier type's own structure* (is it recursively nested, or
just a tagged index?), not whether the instance satisfies `Incidence` or
is `≈`-faithful. `PathId`'s simplicity (a bare `Nat`-tagged sum) made
this cycle's second half almost mechanical once the first half's audit
question was answered -- appropriate, since the point of this cycle was
closing two small open items cleanly, not chasing a new phenomenon.

## Cycle 21

**Hypothesis**: (raised, not committed to, at the end of cycle 20) could
a translation for `simplexIncidence` be built that reflects the `≈`-
quotient structure *exactly* -- constant on each class, distinct across
classes, so translation-equal would be *equivalent* to (not just imply)
`approxBisim`? Flagged as needing its own careful scoping, since it
requires characterizing `≈`'s classes completely, including whether
`face` is *provably* its own class or merely *not yet shown* to merge
with anything.

**Method**: scoped the "not yet shown" gap first, since that's exactly
where the risk was. Every non-equality result in this project to date
proved `i ≠ j` (literal inequality), never `¬ approxBisim inc i j`
(non-bisimilarity) -- a strictly stronger, previously untested kind of
claim. Worked out on paper first (no premature Lean) why non-
bisimilarity should be *provable at all* despite `approxBisim`
quantifying over *all* possible witnessing relations (seemingly
intractable to case on): `IsBisimulation`'s definition forces
`boundaryMatched` to hold for *whichever* relation is claimed to
witness bisimilarity, so if some boundary entry of `i` has *no*
`boundaryCompatible` counterpart anywhere in `j`'s boundary -- a fact
that doesn't depend on the relation at all -- *no* relation can ever
satisfy `IsBisimulation` at that pair. The universal quantifier over
relations gets discharged by `rintro`; the contradiction is then purely
about the two fixed, concrete boundaries. Verified this reasoning in a
scratch file before writing the general theorem, then built the
`simplexIncidence`-specific facts, then re-verified the general theorem
still held (it did, unchanged) once composed with the specific ones.

**Result**: **the general theorem works, proves with zero axioms, and
the three representative cross-shape facts for `simplexIncidence` all
confirmed on the first attempt (after one simp-set fix)** --
`not_approxBisim_of_boundary_mismatch` doesn't even need
`Classical.choice`, since it's a direct constructive contradiction, no
case analysis on an undecidable proposition anywhere. Its corollary
`not_approxBisim_empty_nonempty` (leaves can never be bisimilar to
non-leaves) handles the two "vertex vs. X" cases outright. The one real
snag: the first attempt at the concrete `simplexIncidence` facts hit
"`simp` made no progress" on goals like `e ∈ simplexIncidence.boundary
SimplexId.e01` when passing `simp [simplexBoundary]` -- forgot that
`simplexIncidence.boundary` needs unfolding *through* the structure
literal first (`simp [simplexIncidence, simplexBoundary]`, the two-name
pattern this project's own proofs use everywhere else), not just
through the underlying boundary function. Quick fix once traced to a
minimal isolated example rather than guessed at in place. Full `lake
build`: 38/38 jobs. Repo-wide `sorry`-as-tactic grep: none.

Combined with `simplexIncidence_vertices_collapse`/`_edges_collapse`
(cycles 12/18) and `face ≈ face` (trivial, `approxBisim_refl`), this
*does* answer the motivating question in substance: `≈`'s partition on
`simplexIncidence` is now proven **exactly three classes**
(`{v0,v1,v2}`, `{e01,e02,e12}`, `{face}`), not merely "at least these
three, possibly coarser." What was **not** attempted, and is flagged
honestly rather than glossed: the fully exhaustive `simplexToShape x =
simplexToShape y ↔ approxBisim simplexIncidence x y` theorem (49
constructor-pair cases) that would upgrade "one representative witness
per shape-pair" into a literal `Decidable`-style iff. Scoped this out
deliberately mid-cycle once it became clear the representative-witness
approach already delivers the substantive result this project's own
established convention (cycle 12/18: one pair stands for a whole class)
treats as sufficient -- attempting the 49-case exhaustive version risked
becoming exactly the kind of forced, low-payoff case-bash this project's
discipline warns against, for a stronger *statement* but no stronger
actual *finding*.

**Where the "non-bisimilarity" thread now stands (cycle 21)**: one
general theorem (zero axioms), one corollary, three confirming
instances within a single carrier type (`simplexIncidence`'s three
shape-pairs). Genuinely reusable -- any future instance with leaves
alongside non-leaves, or role/sign-incompatible boundary entries, can
reuse `not_approxBisim_of_boundary_mismatch`/`not_approxBisim_empty_nonempty`
directly, the same payoff pattern as `single_link`/`two_link`
(cycles 9/17) and `boundaryMatched_of_two_entries`/`_symm` (cycle 18).

## Cycle 22

**Hypothesis**: (option 1 of cycle 21's queue) attempt the exhaustive
`simplexToShape x = simplexToShape y ↔ approxBisim simplexIncidence x
y` theorem, using the cleaner split strategy queued: a `reflects` half
(translate-equal → `approxBisim`) and a `distinguishes` half
(`approxBisim` → translate-equal), building the extra representative
facts (`v1`/`v2` vs. edges/face, `e02`/`e12` vs. `face`) as needed.

**Method**: built a general `simplexIncidence_nonempty_not_vertex`
helper first (any nonempty-boundary element vs. any vertex, using
`List.exists_mem_of_ne_nil` to extract a witness automatically rather
than hand-picking one per element) and a `simplexIncidence_srcneg_not_face`
helper (any element with a `(src, neg)`-tagged boundary entry vs.
`face`) -- both generalizing cycle 21's one-off concrete facts to cover
all 3 vertices / all 3 edges uniformly. Tested the `reflects` half
alone first (`cases x <;> cases y <;> simp [simplexToShape] at h <;>
first | approxBisim_refl | ⟨simplexEdgeVertexRel, ...⟩`) -- **succeeded
immediately**, no issues. Then attempted `distinguishes`
(`cases x <;> cases y <;> simp [simplexToShape] <;> first | t1 | t2 |
t3 | t4`, four templates covering direct/symm × vertex/face cases) --
this is where the cycle's real content turned out to be.

**Result**: **`reflects` lands cleanly (zero issues, standard axioms);
`distinguishes` hit genuine, reproducible Lean-elaboration friction that
was diagnosed but not forced through.** Isolated minimal reproductions
confirmed each of the four closing templates works correctly *alone*
against its matching goal (e.g. the `(v0, e01)` case closes fine via
`exact absurd (approxBisim_symm h) (simplexIncidence_nonempty_not_vertex
...)` in a standalone `example`). But combined via `first | t1 | t2 |
t3 | t4` across all 49 `cases`-generated goals, the SAME goal that
closes fine standalone started failing -- and the failure mode was
identical across three different combinator strategies tried in
sequence (`first`, sequential `try ... <;> try ...`, and
`apply`/`exact`-splitting): whichever template's *inference* legitimately
fails first (e.g. trying the "no-symm" form on a goal that actually
needs "symm") appears to leave metavariable state that then breaks the
very next, otherwise-valid alternative attempted on that *same* goal --
even under `try`, which is supposed to fully roll back on failure. This
was tracked down to the specific *mechanism* (not just "it doesn't
work") via minimal bulk-vs-isolated comparisons, ruling out several
wrong hypotheses (backtracking pollution specific to `first`; `simp`
touching `h` in the goal-only `simp [simplexToShape]` call; positional
`x`/`y` no longer being referenceable post-`cases`) before landing on
underscore-inferred lemma arguments interacting badly with sibling
alternatives sharing a goal. A verbose fully-explicit 30-arm `match`
would sidestep the issue entirely (no ambiguous inference), but was
judged not worth building: cycle 21 already established the substantive
mathematical content (exact 3-way `≈`-separation, proven robustly with
concrete term-mode facts) -- the exhaustive iff would strengthen the
*statement*'s form, not add new *content*, and the friction is a tooling
quirk in this specific combinator pattern, not a gap in the underlying
math. `#print axioms simplexToShape_reflects`: standard `propext`/
`Quot.sound`. Full `lake build`: 38/38 jobs. Repo-wide `sorry`-as-tactic
grep: none. Landed `SimplexShape`/`simplexToShape`/`simplexToShape_reflects`
in `Simplex.lean`; `distinguishes` left unattempted-and-documented, not
silently dropped.

**Synthesis**: this cycle is the project's first documented case of
"tried multiple tactic strategies, all failed the same reproducible way,
diagnosed the mechanism, declined to force a workaround" -- distinct
from prior stalls (cycle 9/12's stalls were genuinely *not yet solved*
proof-engineering gaps; cycle 20's decline was about *scope*, not a
failed attempt). Worth naming as its own category: sometimes the
blocker isn't the mathematics or the proof strategy but the *tactic
combinator's* interaction with a specific proof shape, and the right
response is the same principle as always -- record honestly what was
tried, what happened, and why forcing further wasn't worth it -- applied
to a tooling-level obstacle rather than a mathematical one.

## Cycle 23

**Hypothesis**: (option 2 of cycle 21's queue, quickly scoped first)
does `not_approxBisim_of_boundary_mismatch` simplify any existing claim
in `natIncidence`/`pairIncidenceChained`/`pathIncidenceChained`? Then
(the queued fallback, since option 2 was expected to resolve fast): a
fresh, short attempt at cycle 22's deferred `distinguishes` direction
with a genuinely different combinator.

**Method for option 2**: no new Lean needed -- confirmed by re-reading
what's already proven. All three instances have a full `_approxBisim_iff`
theorem (cycle 4's `natIncidence_approxBisim_iff`, cycle 3/4's
`pairIncidenceChained_approxBisim_iff`, cycle 14's
`pathIncidenceChained_approxBisim_iff`), meaning `≈` coincides with `=`
there. Any `¬approxBisim i j` fact for `i ≠ j` on these instances is
already a direct corollary of the iff (`rw [_approxBisim_iff]; exact
h`), strictly simpler than invoking the boundary-mismatch machinery,
which needs a witness entry and a compatibility argument. **Confirmed,
quickly, as predicted**: no simplification opportunity exists on the
three faithful instances -- the new machinery's distinctive value
remains specifically for non-faithful instances, of which
`simplexIncidence` was (and, after this cycle, still is) the only one.
A clean negative finding, closed in one paragraph rather than forced
into a search for opportunities that don't exist.

**Method for the fallback**: re-attempted cycle 22's `distinguishes`
direction with a genuinely different combinator, per the queued
suggestion. Rather than `cases x <;> cases y <;> simp [...] <;> first |
t1 | t2 | t3 | t4` (tactic-mode, where a failing alternative's inference
attempt polluted a sibling's), switched to **term-mode pattern
matching**: `theorem ... : (x y : SimplexId) → approxBisim ... →
simplexToShape x = simplexToShape y | .v0, .v0, _ => rfl | ... `, with
all 49 constructor pairs as separate, explicit match arms. Each arm is
its own independent elaboration problem for Lean's equation compiler --
there is no shared tactic state between arms for one's failure to
pollute another, which is precisely the mechanism cycle 22 diagnosed as
the blocker. Tested a 6-arm prototype first (covering one instance each
of same-vertex, vertex-vs-edge both directions, edge-vs-face both
directions) before committing to writing out all 49.

**Result**: **the fallback succeeded immediately -- the 6-arm prototype
worked on the first try, and the full 49-arm version, once written out
mechanically, also typechecked on the first attempt.** Reused the exact
same underlying facts as cycle 22 (`simplexIncidence_nonempty_not_vertex`,
`simplexIncidence_srcneg_not_face`, `approxBisim_symm` for reversed-order
cases) -- only the *combinator* changed, confirming cycle 22's own
diagnosis that the blocker was tooling-specific, not mathematical.
`simplexToShape_distinguishes` and the combined
`simplexToShape_iff_approxBisim` both typecheck; `#print axioms`: the
standard `propext`/`Quot.sound`, no `Classical.choice`, no `sorryAx`.
`simplexIncidence`'s `≈` is now proven to be *exactly*
`simplexToShape`-agreement -- the exhaustive characterization queued
back in cycle 20, attempted partially in cycle 22, and completed here.
Full `lake build`: 38/38 jobs. Repo-wide `sorry`-as-tactic grep: none.

**Synthesis**: this closes the loop cycle 22 opened cleanly rather than
leaving it as permanently-deferred future work -- the "revisit with a
fresh, simpler approach" instinct from cycle 22's own queued next-steps
paid off directly, and the *specific* fresh approach (term-mode instead
of tactic-mode) was chosen *because* cycle 22's diagnosis pinpointed
exactly what needed to change (shared combinator state) rather than
guessing. Worth reinforcing as a general principle alongside cycle 18's
near-identical lesson ("when a proof stalls twice on the same shape,
change the shape") one level up: **when a proof stalls on a specific
*combinator*, not the underlying mathematics, try a structurally
different combinator (tactic-mode vs. term-mode, `first` vs. explicit
case dispatch) before concluding the result is out of reach.** The 30
extra explicit match arms (vs. 4 templates) is real verbosity, but
mechanical, predictable verbosity beats elegant-looking tactics that
don't actually work.

**Where the `simplexIncidence` characterization thread now stands
(cycles 12/18/20/21/22/23)**: fully closed. `≈`'s partition is proven
exactly three classes, and translation-equality (`simplexToShape`) is
proven *equivalent* to (not just implying) bisimilarity -- the strongest
form of characterization this project's T5/faithfulness machinery
supports, now achieved for the one instance (`simplexIncidence`) where
it was genuinely non-trivial (unlike the three fully-`≈`-faithful
instances, where `simplexToShape`-style translations would be
comparatively uninteresting, per this cycle's option-2 finding).

## Cycle 24

**Hypothesis**: (option 1 of cycle 23's queue) extend `two_link_composition_value`-
style closed-form ∂² characterization to `pairIncidenceChained`'s `pair`
nodes, which -- unlike `PathId`'s `edge` (a two-entry-boundary element
whose targets are always plain nodes, never elements with boundaries of
their own reaching back into the same territory) -- can genuinely
*nest* (`pair (pair a b) c`), testing the machinery against a
recursively nested structure for the first time.

**Method**: `#eval` first, per discipline. Built `Outer = pair (pair
(atom n) (atom (n+1))) (atom (n+2))` and scanned its `boundary_composition`
against `atom n`, `atom (n+1)`, `atom (n+2)` for `n = 0`. Result: `1, 0,
0` -- the middle value being exactly `0` was not predicted going in, and
warranted a hand-derivation to understand *why* before trusting it:
`atom (n+1)` is reached BOTH via the inner pair's `snd` projection
(value `+1`) AND via `atom (n+2)`'s own predecessor-chain link (value
`-1`), and these are the *only* two paths, so they sum to exactly zero.
Checked this wasn't a coincidence specific to `n = 0` by re-running the
scan at `n = 3` and `n = 7` before writing any proof -- both gave the
same `0`, confirming a genuine parametrized family.

**Result**: **confirmed and fully generalized over all `n`, using
existing cycle 17 machinery with only new instance-specific glue
(no new general theorems needed)**. Built four small helper facts
(`pairIncidenceChained_atom_chain_boundary`/`_zero`,
`pairIncidenceChained_pair_fst_boundary`/`_snd_boundary`, mirroring
`PathComplex`'s cycle 16/17/19 helpers but for `PairId`'s `fst`/`snd`
roles instead of `PathRole.chain`/`edgeEnd`), then composed them via
`two_link_composition_value` into two theorems: `_nested_pair_witness`
(nonzero at `atom n`, same "only one term" shape as any chain) and
`_nested_pair_cancellation` (exactly zero at `atom (n+1)`, the new
result). `#print axioms`: standard three throughout, no `sorryAx`. Full
`lake build`: 38/38 jobs. Repo-wide `sorry`-as-tactic grep: none. Added
to `Pairs.lean`, wired into `Main.lean`.

**Synthesis**: this is the project's first confirmed instance of `∂²`
cancellation arising from *converging paths through recursive nesting*,
a third, structurally distinct route to cancellation alongside the two
already on record: `simplexIncidence.face`'s cancellation (cycle 11) is
a *deliberately chosen* alternating-sum convention on a *single*
element's own boundary entries; `pathIncidenceChained`'s "elsewhere
zero" (cycle 19) is zero by *structural absence* -- no path reaches that
target at all. Here, `pair`'s recursive nesting creates a genuine
*algebraic* cancellation between two *independently-reached, unrelated*
paths (one through a child's own projection, one through a different
child's predecessor chain) that happen to converge on the same
grandchild -- not designed for cancellation the way `face`'s
alternating sum was, and not trivially zero the way `edge`'s "other"
targets were. Whether this generalizes further (e.g. does *every*
`pair (pair a b) c` where `c`'s chain-predecessor equals `b` exhibit
this, for `b`/`c` chosen more freely than the `atom n`/`atom(n+1)`/
`atom(n+2)` family tested here?) is open but not attempted -- the
family tested is itself a genuine, non-trivial, fully generalized
result and doesn't need to become maximally general to be a real
finding.

## Cycle 25

**Hypothesis**: two items queued at the end of cycle 24. (1, primary)
does `pairIncidenceChained_nested_pair_cancellation`'s family generalize
beyond the specific `atom n`/`atom (n+1)`/`atom (n+2)` construction? (2,
secondary) a quick survey of whether the term-mode-vs-tactic-mode lesson
(cycle 22→23) would clean up other historically-friction-heavy
tactic-mode proofs -- explicitly scoped as an audit, not a rewrite
mandate.

**Method for (1)**: re-read the existing proof of
`pairIncidenceChained_pair_snd_boundary` before writing any new Lean, to
ask a specific question: does the cancellation's mechanism actually
depend on the outer pair's *first* component (`a`, instantiated as
`atom n` in cycle 24) being an atom in the same chain, or only on the
*second* component's relationship to what's composed against? The
lemma's own proof only ever uses `a ≠ b` -- never anything about *what*
`a` is. Tested this concretely before trusting the reading: built `a :=
pair (atom 5) (atom 6)` (an unrelated nested pair sharing no atoms with
the rest of the construction) and checked `pair (pair a (atom 3))
(atom 4)` against `atom 3` via `#eval` -- still `0`.

**Result for (1)**: **confirmed and proven fully general.**
`pairIncidenceChained_nested_pair_cancellation_general (a : PairId) (n :
Nat) (ha : a ≠ atom n)` holds for *any* `a`, not just atoms -- the
cancellation was never about atom-chain depth at all, it's a purely
structural fact about `pair`'s `fst`/`snd` shape meeting any chain-
reaching element. Proof reuses the exact same helper lemmas from cycle
24 unchanged (they were already general in `a`; only the *theorem
statement* cycle 24 wrote was needlessly specific). `#print axioms`:
standard three, no `sorryAx`. `pairIncidenceChained_nested_pair_cancellation`
(cycle 24's specific instance) is now a special case of this (`a := atom
n`, reindexed) -- kept alongside rather than deleted, since it's a
genuine, independently-readable concrete illustration, not a broken or
superseded construction (the same "keep both, not just the general
one" choice this project made for `natIncidence`/`altIncidence` and
others).

**Method/Result for (2)**: delegated a read-only grep survey (no file
modifications) across the whole codebase for `cases <;> first | ...`
patterns. Found exactly four sites, all in `Simplex.lean`: two use only
2 alternatives with no recorded friction (the `Incidence` field proofs,
and cycle 22's `simplexToShape_reflects`); one (cycle 23's
`simplexToShape_distinguishes`) is the tactic-mode version that *already*
hit the pollution bug and was *already* replaced by the term-mode
`match` now in the file; the remaining one --
`simplexEdgeVertexRel_isBisimulation` (cycle 18, 7 alternatives across 9
`cases`-generated goals) -- is structurally the closest match to the
risky shape and the natural audit target, but cycle 18's own writeup
records it working on the *first* full attempt with no friction. **No
rewrite performed** -- this project doesn't rewrite working code for its
own sake, and the audit found no evidence (recorded or freshly
uncovered) that this specific proof is actually fragile, only that it
*structurally could be*. A clean, quick negative-ish finding: the
audit's value was ruling out a latent risk, not finding a bug.

**Synthesis**: two closed items, appropriately scoped to their actual
size -- (1) was a real generalization worth formalizing (removes an
unnecessary hypothesis, strengthens a genuine finding, cheap given the
groundwork was already general); (2) was genuinely just an audit,
correctly not escalated into unnecessary rewriting once the evidence
didn't support it. Both outcomes match this project's stated discipline
rather than manufacturing more work than the findings warranted.

## Cycle 26

**Hypothesis**: (option (a) of cycle 25's queue) introduce a genuinely
new `Incidence` carrier type -- the first since `simplexIncidence`
(cycle 11). Every existing instance is fundamentally *acyclic* (a
well-founded chain, or a finite tree/simplex with at least one empty-
boundary leaf). Does a genuine *cycle* -- every element pointing to a
"predecessor" with no base case at all -- even satisfy `Incidence`'s
own structural requirements, and if so, does the "flat leaves collapse"
pattern (cycles 2/12/13/18) generalize beyond *shared emptiness*
specifically?

**Method**: read `Incidence`'s own `well_founded` field first, before
writing any construction: `∀ i, ¬∃ e ∈ boundary i, e.i = i` -- this
forbids only a *direct* self-loop (an element in its own boundary), not
a longer cycle, so a genuine multi-step cycle is legitimate, not a
workaround. Built `CycleId := c0 | c1 | c2 | c3` with `boundary ci =
[{cyclePred ci, chain, neg, 1}]` (`c0→c3→c2→c1→c0`), and `glue` as
`Z/4Z` addition (via `Nat ↔ CycleId` helper functions and `% 4`) rather
than reusing the left-biased-selection pattern every other instance
used, specifically to get a *group*-structured `glue` (commutative,
invertible) for the first time. Built the full `Incidence` instance
(all 7 proof obligations) before testing anything else -- it typechecked
on the first attempt, confirming the structural legitimacy question
immediately. Then tested the collapse conjecture: does the same
"everything related to everything" relation from cycles 2/12/13/18
witness a bisimulation here too, where (unlike those cycles) *no*
element has empty boundary?

**Result**: **confirmed on essentially the first attempt (one minor fix:
explicit witness endpoints instead of underscore-inferred ones, a
smaller version of cycle 22's lesson) -- ALL FOUR elements collapse into
a single `≈`-class, proving with only `propext` (no `Classical.choice`,
fully constructive).** `cycleIncidence_isBisimulation_full` shows the
uniform relation satisfies `IsBisimulation`: since every element's
single boundary entry has an *identical* shape (`chain`, `neg`, `1`),
`boundaryMatched` only ever needs *some* compatible, related counterpart
to exist, and the fully-related relation trivially supplies one
regardless of which specific element it is -- structurally the same
argument as the shared-empty-boundary cases, just with a non-empty
uniform shape instead of an empty one. This confirms the hypothesis:
**"flat leaves collapse" was never really about *emptiness* -- it's
about *lacking a well-founded, distinguishing measure*, and a uniform
cycle is a second, structurally different way to lack one.** Also
confirmed, as expected rather than surprising: `single_link_composition_ne_zero`
(cycle 9) applies "for free" to `cycleIncidence` too (∂² still fails,
via the exact same general theorem, confirming its reach isn't
accidentally tied to acyclicity), and `glue`'s new algebraic properties
both hold (`cycleIncidence_glue_comm`, `cycleIncidence_glue_has_inverse`
-- the first genuinely *group*-structured `glue` in this project, unlike
`natIncidence`'s inverse-free monoid or every other instance's non-group
left-biased selection). `#print axioms` across all seven new theorems:
`propext` alone on five of them, standard three on the two that route
through `two_link`/`single_link`-family general theorems. Full `lake
build`: 40/40 jobs (new file `Cycle.lean`, wired into `Main.lean`).
Repo-wide `sorry`-as-tactic grep: none.

**Synthesis**: this is the strongest form of the "flat collapse" pattern
seen yet -- not "some pair of elements collapse" (cycles 2/12) or "some
pair collapses, but not others" (`simplexIncidence`, where vertices/
edges/face stay separated, cycles 12/18/23) but *every* element in the
entire carrier type collapsing into one class, because there's no
substructure anywhere to distinguish any element from any other. This
sharpens the general lesson first stated informally back when the fix
for `natIncidence`/`pairIncidenceChained`/`pathIncidenceChained`'s
collapse was "give elements a well-founded distinguishing chain" (cycles
2/3/13/14): the *actual* content of that fix was never about filling in
empty boundaries specifically -- it was about establishing a
well-founded *measure*, and cycle 26 is the first instance where "no
measure exists at all" is demonstrated directly (via a genuine cycle)
rather than merely "a measure exists but two elements happen to share
the same value under it" (empty boundary = measure value zero, shared
by multiple elements).

## Cycle 27

**Hypothesis**: (option 1 of cycle 26's queue) does `cycleIncidence`
admit a faithfulness-recovering "fixed" variant, the way `pairIncidence`
→ `pairIncidenceChained` (cycle 3) and `pathIncidence` →
`pathIncidenceChained` (cycle 14) did -- and if so, does the fix
necessarily pay the same `∂² ≠ 0` price (cycles 8/16)? The established
fix ("give elements a well-founded predecessor chain reaching a base
case") doesn't directly transplant: a *closed cycle* has no base case
at all, by construction.

**Method**: rather than trying to force the chain-based fix onto a
structure that has nowhere for a chain to terminate, looked for a
*different* mechanism that could still recover faithfulness. Key
observation: `boundaryMatched`'s compatibility check depends on `role`
(along with `sign`/`mult`), and every prior instance reused a small,
shared role set (1-3 constructors) across many elements. What if,
instead, each of the four cycle positions got its *own*, structurally
distinct role -- `cycleRoleOf : CycleId → CycleRoleFixed` literally
injective? Built `cycleIncidenceFixed` with the *same* `c0→c3→c2→c1→c0`
topology and the *same* `Z/4Z` `glue`, differing only in this role
labeling. Tested faithfulness via cycle 21's `not_approxBisim_of_boundary_mismatch`
directly (not cycle 4's `incidence_bisim_faithful`, which needs a
well-founded *measure* -- something a closed cycle cannot have, since
nothing ever strictly decreases around a loop): if `x ≠ y`, their
boundary entries carry different roles, so no relation can ever match
them, blocking bisimilarity structurally. One tooling snag along the
way: `by_contra` (attempted first, matching how the hard direction of
an iff is usually structured) is unavailable without mathlib -- rewritten
as `by_cases` instead, a known, previously-hit gotcha in this project,
resolved immediately rather than re-diagnosed from scratch.

**Result**: **confirmed on the first full attempt after the `by_contra`
fix -- full faithfulness (`≈ ↔ =`) recovered via a genuinely new proof
route, and the predicted price paid a fourth time.**
`cycleIncidenceFixed_approxBisim_iff` proves with *only* `propext` --
no `Classical.choice` at all, fully constructive, since role-
discrimination needs no induction or measure, just a direct structural
mismatch argument. `cycleIncidenceFixed_not_boundary_square_zero`/
`_c0_composition_ne_zero` confirm `∂² = 0` fails here too, via the exact
same `single_link_composition_ne_zero` (cycle 9) already used for
`natIncidence`/`pairIncidenceChained` (cycle 8) and
`pathIncidenceChained` (cycle 16) -- the theorem never cared about
roles, only about the single-link shape, so the fix's *mechanism*
(chain vs. role-labeling) turns out to be irrelevant to whether the
price gets paid. `#print axioms`: `propext` alone on three of four new
theorems, standard three on the one routing through
`single_link_composition_ne_zero`. Full `lake build`: 40/40 jobs.
Repo-wide `sorry`-as-tactic grep: none. Added to `Cycle.lean`, wired
into `Main.lean`.

**Synthesis**: two things worth separating clearly. First, the
"faithfulness-fix necessarily breaks `∂² = 0`" tension (cycles 8/16, now
also 27) is sharper than previously stated: it was never about *how* the
distinguishing structure is encoded (a predecessor chain reaching a
leaf, or unique role tags on a closed cycle) -- it's purely about
*keeping the single-link boundary shape*, which is exactly
`single_link_composition_ne_zero`'s hypothesis regardless of mechanism.
Second, and more novel: this project now has **two independent, general
routes to full `≈`-faithfulness** -- `incidence_bisim_faithful` (cycle
4, well-founded measure + boundary extensionality, needed for the three
acyclic chain/tree instances) and `not_approxBisim_of_boundary_mismatch`
(cycle 21, role-discrimination, usable even where no well-founded
measure could possibly exist). Neither subsumes the other: a cycle has
no measure for the first route to use, and a chain-based instance
(where every element shares the *same* role) has no role-mismatch for
the second route to use unless the roles are made unique too. Which
route applies is a genuine structural fact about the instance, not a
matter of proof-engineering preference.

## Cycle 28

**Hypothesis**: (option 2 of cycle 26's queue) does `cycleIncidence`'s
genuinely invertible `glue` (`Z/4Z`) open a new T5 translation story --
specifically, is `cycleToNat` (already defined, used internally for
`cycleAdd`) a genuine `glue`-*homomorphism* (`cycleToNat (cycleAdd x y)
= (cycleToNat x + cycleToNat y) % 4`), something no prior translation
in this project attempted, since no prior `glue` (an infinite monoid,
or non-group left-biased selection) had algebraic structure worth
checking a translation against?

**Method**: `#eval` first, per discipline, scanning all 16 pairs `(m, n)
∈ {0..3}²` via `cycleToNat (cycleAdd (cycleOfNat m) (cycleOfNat n))`
against `(m + n) % 4` directly. All 16 agreed. Formalized as
`cycleToNat_glue_hom (x y : CycleId) : cycleToNat (cycleAdd x y) =
(cycleToNat x + cycleToNat y) % 4`, proved by `cases x <;> cases y <;>
decide` (16 concrete cases, fully computational). Then built the
standard T5 injectivity/reflects-`≈` pair (cycle 5's recipe) --
targeting `cycleIncidenceFixed` specifically (the *fixed*, faithful
variant from cycle 27), not the original `cycleIncidence`, since
translate-reflects-`≈` would be vacuously true against `cycleIncidence`
(cycle 26: *everything* is `≈`-related there regardless of any
translation) and therefore uninteresting.

**Result**: **confirmed, and the proof needed no axioms at all --
`cycleToNat_glue_hom` is unconditionally true by direct computation, not
merely "true in the cases checked."** Unsurprising once stated plainly
-- `cycleAdd` was *defined* as exactly this formula wrapped in
`cycleOfNat`/`cycleToNat` -- but worth confirming as a real theorem
rather than trusting the definition's shape by eye (the same discipline
that caught real bugs elsewhere in this project). Added
`cycleToNat_unit_natural` (trivial, `decide`) and the standard
`cycleToNat_injective`/`_reflects_approxBisim` pair (`propext` only,
consistent with cycle 27's fully constructive faithfulness theorem for
`cycleIncidenceFixed`). Full `lake build`: 40/40 jobs. Repo-wide
`sorry`-as-tactic grep: none. Added to `Cycle.lean`, wired into
`Main.lean`.

**Synthesis**: `cycleToNat` is the first translation in this project
that is simultaneously a faithful `≈`-reflector (the T5 property every
prior translation had) *and* a genuine algebraic homomorphism (a
property no prior translation's target had reason to have). Combined,
these say something sharper than either alone: `cycleIncidenceFixed`'s
entire algebraic-plus-relational structure is *literally isomorphic* to
`Z/4Z` with the usual quotient equality -- `cycleToNat` is a bijection
(by injectivity plus `cycleOfNat` being its two-sided inverse by
construction) that is simultaneously a `glue`-homomorphism and reflects
`≈` exactly. This is a genuinely stronger characterization than any
prior instance's T5 result, precisely because it was the first instance
whose `glue` had a real target worth being isomorphic *to*.

## Cycle 29

**Hypothesis**: (option (a) of cycle 28's queue) a fifth new `Incidence`
instance, testing a structural shape none of the prior four tried -- a
*ternary*-branching tree, `node a b c` with a genuine *three*-entry
boundary, rather than `pairIncidenceChained`'s strictly binary nesting.
Would wider branching surface anything `pair`'s two-entry shape
couldn't? And -- since `node`'s boundary is a second real 3-entry
instance alongside `simplexIncidence.face` (cycle 11) -- does this
finally satisfy cycle 20's stated condition ("no second instance to
validate a 3-entry generalization against") for revisiting that
declined generalization?

**Method**: built `TreeId := leaf (n : Nat) | node (a b c : TreeId)`
with `treeBoundary (node a b c) = [{a,c1,pos,1},{b,c2,pos,1},{c,c3,pos,1}]`
(uniform `pos` sign, unlike `simplexIncidence.face`'s deliberate
alternating sum). One proof-engineering snag building the `Incidence`
instance itself: `well_founded`'s recursive case (`a = node a b c`,
structurally impossible) wasn't closed automatically by `simp_all` the
way it had been for every prior instance's simpler shapes -- needed an
explicit `sizeOf`-based contradiction (`congrArg sizeOf hei`, then
`simp [TreeId.node.sizeOf_spec]`, closed by `<;> omega` after `simp`
alone closed some but not all branches). Then tested, in order: (1)
whether "flat leaves collapse" (cycles 2/12/13/18/26) still holds for
bare `leaf n`s; (2) whether `boundary_composition_zero_of_leaf_boundary`
(cycle 10) still applies when a node's three children are all leaves;
(3) `#eval`-checked what happens with *non-leaf* children (a nested
`outerTree = node (node (leaf 0) (leaf 1) (leaf 2)) (leaf 3) (leaf 4)`)
before formalizing.

**Result**: **all three established patterns confirmed unchanged by
branching factor -- no qualitatively new phenomenon, and that absence is
itself the honest finding, not a lesser one.** `treeIncidence_leaves_collapse`
(fifth confirmation), `treeIncidence_leaf_children_zero` (cycle 10's
theorem reused directly, no new machinery, confirming it was never
arity-specific), and the concrete `#eval`/`decide` witnesses for
`outerTree` (nonzero at `leaf 0`/`1`/`2`, reached two levels deep
through the inner node; zero at `leaf 3`/`4`, direct leaf children;
overall `∂² ≠ 0`) all check out, matching the "single active branch, no
cancellation" shape `single_link_composition_ne_zero` (cycle 9)
captures for 1-entry boundaries -- here for a 3-entry one where only one
of three branches happens to reach any given target, so no genuine
3-way convergence (unlike `pairIncidenceChained`'s cycle 24/25 nested-
pair cancellation, which needed a *second*, independent path to the
same target to produce real cancellation; a plain ternary tree with no
other structure doesn't manufacture that on its own). Left the actual
3-entry generalization (`boundaryMatrix_three_link`/
`foldl_add_eq_count_mul_three`/`three_link_composition_value`,
mirroring cycle 17's 2-entry construction) as a `decide`-witness stage
rather than attempting the general theorem in the same cycle as the
instance -- deliberately, matching cycle 8→9's staging (introduce a
concrete failure first, generalize the mechanism in a later cycle once
motivated by more than one data point). `#print axioms`: standard three
throughout, no `sorryAx`. Full `lake build`: 42/42 jobs (new file
`Tree.lean`). Repo-wide `sorry`-as-tactic grep: none.

**Synthesis**: worth stating plainly since it cuts against the instinct
to always look for something surprising -- this cycle's value is
*ruling out* a hidden assumption ("these three patterns held only
because everything so far happened to be binary"), not discovering a
new one. Confirmatory cycles (this one; cycle 19's audit; parts of
cycle 25) are a legitimate category of finding in this project's
co-scientist discipline, distinct from but not lesser than novel-
phenomenon cycles (cycles 24, 26). The `well_founded` field's `sizeOf`
friction is also worth noting structurally: it's the first instance
where `simp_all` alone didn't suffice for an "element can't equal its
own strictly-larger constructor application" argument, likely because
ternary nesting's sizeOf arithmetic (`1 + sizeOf a + sizeOf b + sizeOf
c`) needed `omega` to close where binary/unary shapes' simpler
arithmetic let `simp` finish alone -- a small, mechanical scaling
effect of arity on proof automation, not a deep finding, but honestly
recorded rather than silently smoothed over.

## Cycle 30

**Hypothesis**: (option 1 of cycle 29's queue) build the general 3-entry
`∂²` machinery deliberately deferred there --
`boundaryMatrix_three_link`/`foldl_add_eq_count_mul_three`/
`three_link_composition_value`, mirroring cycle 17's 2-entry
construction, now validated against *two* real instances
(`simplexIncidence.face`, cycle 11; `treeIncidence.node`, cycle 29)
rather than built speculatively against one -- exactly the condition
cycle 20 said would justify revisiting its declined generalization.

**Method**: extended cycle 17's exact two-entry technique by one more
case throughout (`boundaryMatrix_two_link` → `_three_link`,
`foldl_add_eq_count_mul_two` → `_three`, `two_link_composition_value` →
`three_link_composition_value`). Hit the identical `if`-orientation
friction cycle 17 already diagnosed (`rw`/`simp` treating `a = b` and
`b = a` as different targets) and resolved it the same way (`simp`
with both a hypothesis and its `.symm` supplied per branch). One
genuinely new snag: my scratch test file's own *comment text*
("...the -1/-1 values...") accidentally contained a `/-` substring,
which Lean's *nested*-comment-aware lexer parsed as opening a second
comment inside the first, leaving the outer one "unterminated" once
only one `-/` closed it -- diagnosed by removing suspect text blocks
one at a time rather than guessing, then avoided by rewording. Applied
the finished general theorem to *both* motivating instances: generalized
cycle 29's concrete `treeIncidence` witness into a real theorem over
*any* well-formed children (not just `leaf 0`/`1`/`2`), and -- the
more valuable validation -- applied it to `simplexIncidence.face`,
which cycle 11 only ever checked via `decide` (true for one concrete
index, never explained symbolically).

**Result**: **all three general theorems and both instance validations
succeeded, cleanly, on the pattern already known to work (cycle 17's
technique scaled up without new surprises beyond the two noted
above).** `#print axioms`: `propext` alone on `boundaryMatrix_three_link`
(no `Classical.choice`, matching cycle 17's cleanest lemma), standard
sets on the rest. The `simplexIncidence.face` validation is the
cycle's most valuable output: `simplexIncidence_face_v0_general` shows
`face`'s `∂² = 0` at `v0` reduces to `count(e02) - count(e01)`, which
vanishes whenever both edges appear equally often in the index -- the
*actual reason* cycle 11's `decide` witness came out `0`, not merely a
confirmed fact about that one witness. This retroactively explains a
9-cycle-old result rather than just adding new content. Full `lake
build`: 42/42 jobs. Repo-wide `sorry`-as-tactic grep: none. Added the
three general theorems to the root file (same placement convention as
cycle 9/17's infrastructure), `treeIncidence_node_x_boundary`/
`_outer_composition_general` to `Tree.lean`,
`simplexIncidence_e12_v0_boundary`/`_e02_v0_boundary`/`_e01_v0_boundary`/
`_face_v0_general` to `Simplex.lean`.

**Synthesis**: this closes the loop cycle 20 opened four cycles ago
(cycle 20 → 29 → 30): declining a generalization for lack of evidence
isn't a permanent verdict, it's conditional on evidence that may
eventually arrive -- and treating it that way (recording the specific
condition that would justify revisiting, rather than either forcing the
generalization prematurely or dismissing it permanently) is what made
this cycle a quick, low-risk build rather than a fresh proof-engineering
gamble. The `simplexIncidence.face` validation also demonstrates a
distinct, valuable use for a newly-generalized theorem: not just
extending reach to new instances, but *retroactively explaining* an
old `decide`-only result. Worth remembering as a category of payoff
alongside "covers a new instance" and "simplifies an existing proof"
(cycle 25's audit) -- "explains why an old concrete fact was true."

## Cycle 31

**Hypothesis**: (option (b) of cycle 28's queue, carried forward twice)
revisit the original, much larger research-program questions
(constructing `ℕ`/sets/logic/category-theory concepts *internal* to
Inc, not as external `Incidence` instances) now that the instance
library and general-theorem toolkit are substantially more mature.
Scoped deliberately to a *first concrete milestone* before writing any
Lean, per the explicit caution left at the end of cycle 30: what should
that milestone actually *be*?

**Scoping, done before any Lean**: every construction in this project's
history so far -- `natIncidence`, `pairIncidenceChained`,
`pathIncidenceChained`, `simplexIncidence`, `cycleIncidence`,
`treeIncidence` -- builds a specific *instance* by hand: choosing one
carrier type, one boundary function, one `glue`, and proving the seven
`Incidence` obligations for *that* choice. The deeper, originally-
deferred question was different in kind: can Inc's primitive vocabulary
(`boundary`/`glue`/`≈`) express type-theoretic *connectives*
*generically*, as constructions that take arbitrary `Incidence`
structures as input and produce new ones as output -- the way a real
type theory's product/sum/function types are generic constructors on
types, not one-off encodings? No construction in this project has ever
done that; every one has been carrier-type-specific. Chose the single
simplest such connective -- a *product* constructor, `incidenceProd :
Incidence I1 R1 T1 → Incidence I2 R2 T2 → Incidence (I1×I2) (R1⊕R2)
(T1×T2)` -- deliberately not attempting function types, dependent
types, identity types, or induction principles in the same cycle.

**Method**: designed the construction on paper first (the standard
"box product" shape from algebraic topology: `(i1,i2)`'s boundary is
`i1`'s boundary transported with a `Sum.inl`-tagged role, plus `i2`'s
boundary transported with `Sum.inr`), then verified each of the seven
`Incidence` proof obligations reduces *directly* to the corresponding
obligation of `inc1` or `inc2` (whichever side an entry, or a
successful `glue`, came from) before writing any tactic proof. One
design correction made *during* this check, not after: an unconditionally
permissive `guards` field for the product would make `type_preserve`
unprovable in general (there'd be no way to invoke `inc1`/`inc2`'s own
`type_preserve`, which need their *own* guards to hold, not the
product's) -- fixed by defining the product's `guards` to require
*both* components' own guards to allow the move, not by assuming
permissiveness. Then built the construction and a first congruence
theorem (`≈` on components implies `≈` on the product) in a scratch
file, iterating through several rounds of friction: `rintro`'s
inability to destructure a `Prod` pattern combined with a further
`⟨...⟩` pattern in one step (worked around with explicit
`intro`/`obtain`, the same fix used for `well_founded`'s analogous
case); `boundaryCompatible`'s lifted-endpoint proof needing explicit
`congrArg Sum.inl`/`Sum.inr` reconstruction rather than reusing the
un-lifted compatibility proof directly (since the lifted entries'
`.role` fields are `Sum.inl`/`Sum.inr`-wrapped, not literally the same
term); and building small membership helper lemmas
(`prodBoundary_mem_left`/`_right`) once ad-hoc `simp` calls for
boundary membership became too fragile to reuse across both directions
of the congruence proof.

**Result**: **the full generic constructor typechecks with zero
`sorry` across all seven obligations, and the congruence theorem proves
with only `propext`/`Quot.sound` -- no `Classical.choice` at all,
fully constructive.** This is qualitatively different from every prior
cycle's output: not a new fact about an existing structure, but a new
*kind* of construction -- a function from `Incidence` structures to
`Incidence` structures, proven correct once and for all pairs, rather
than instantiated by hand each time. Sanity-checked against a real
pair of instances (`natIncidence × natIncidence`): the product's
boundary at `(2,3)` has exactly 2 entries (one from each side, matching
`natIncidence`'s own single-link shape at both `2` and `3`), the unit
is `(0,0)`, and both `approxBisim_refl` and the new congruence theorem
apply concretely, not just vacuously. `#print axioms`: `propext`/
`Quot.sound` on the membership helpers and the congruence theorem.
Full `lake build`: 44/44 jobs (new file `Product.lean`). Repo-wide
`sorry`-as-tactic grep: none.

**Synthesis**: this is the project's first step that's genuinely
*internal* to the Inc framework rather than *modeled within* it -- the
distinction the very first scope-down (natural numbers as a concrete
instance, back at the start of this thread) deliberately deferred. It's
a small step (one connective, the simplest one, with only one
congruence theorem beyond the construction itself) but a real one: it
demonstrates the *pattern* by which further connectives could be built
(sum types via `Sum I1 I2`'s boundary reusing each side's own boundary
unchanged; a terminal/unit-object instance; eventually function-type-
like or dependent constructions, though those are substantially harder
and not implied to be equally tractable by this result). The
`well_founded`-pattern reuse (the `rintro`-on-`Prod` friction) and the
`boundaryMatrix_two_link`/`_three_link` if-orientation friction from
earlier cycles both resurfaced here in slightly different guises --
worth noting as recurring categories of Lean friction in this project
(pattern-destructuring in `rintro`, and equality-direction mismatches
in `simp`/`rw`) rather than independent one-off surprises each time.

## Cycle 32

**Hypothesis**: (option 2 of cycle 31's queue, chosen over option 1's
mechanical sum-constructor repeat) does faithfulness transport through
`incidenceProd` -- if `inc1` and `inc2` are both individually
`≈`-faithful, is `incidenceProd inc1 inc2` faithful too, or does it fail
to transport the way `∂² = 0` provably fails to transport through the
collapse-fix (cycles 8/16/27)? Chosen deliberately over the sum-
constructor option because this question had a genuinely open answer,
where a second connective would have mechanically repeated cycle 31's
shape with low chance of a new finding.

**Method**: worked out the key mechanism on paper before writing Lean.
Cycle 31's congruence theorem only went one direction (`≈` on
components ⇒ `≈` on the product). The natural way to get full
faithfulness is to first establish the *converse* -- `≈` on the product
⇒ `≈` on *both* components -- then combine with each component's own
faithfulness. Realized the converse should be provable via
*projecting* a product-level witnessing relation: given `rel`
witnessing `(i1,i2) ≈ (j1,j2)` in the product, define `rel1 a1 b1 := ∃
a2 b2, rel (a1,a2) (b1,b2)` and check whether `rel1` is itself a
bisimulation for `inc1`. The key structural fact making this work:
`boundaryCompatible` requires *matching* `Sum.inl`/`Sum.inr` tags, so a
`Sum.inl`-tagged boundary entry in the product can only ever be
`boundaryMatched` against another `Sum.inl`-tagged entry -- meaning any
witness `boundaryMatched` supplies for a left-tagged entry is
automatically itself left-tagged, i.e. comes from `inc1`'s own
boundary, and `rel`'s own existential witnesses are exactly what `rel1`
needs. No new machinery beyond this observation. Built and tested the
`inc1`-side projection alone first (confirmed compiling standalone with
only a placeholder `sorry` for the symmetric `inc2` side) before writing
the `inc2` side, to isolate the technique before doubling the surface
area -- caught one copy-paste slip this way (a stray `a1` where `b1`
was needed) via the type-checker rather than by re-deriving from
scratch.

**Result**: **confirmed, and the full iff plus the faithfulness-
transport corollary all proved with only `propext`/`Quot.sound` --
fully constructive.** `incidenceProd_project` establishes the converse
generally; combined with cycle 31's `incidenceProd_approxBisim_of_approxBisim`,
`incidenceProd_approxBisim_iff` upgrades the one-directional congruence
theorem into a genuine iff: the product's `≈` is *exactly* componentwise
`≈`, no more and no less. `incidenceProd_faithful_of_faithful` then
answers the queued question directly: faithfulness transports through
the product *at no cost*, for any two individually-faithful instances,
with no analogue of the `∂² = 0` tension anywhere in sight. Confirmed
concretely (not just abstractly) by instantiating with `natIncidence`'s
own faithfulness theorem (cycle 4) applied twice: `natIncidence ×
natIncidence` is fully faithful. `#print axioms`: `propext`/`Quot.sound`
on all three new theorems, matching cycle 31's cleanliness. Full `lake
build`: 44/44 jobs. Repo-wide `sorry`-as-tactic grep: none.

One unrelated but real build failure surfaced and was fixed along the
way: adding this cycle's content pushed `Main.lean`'s single `main`
`do`-block past a *second*, different scaling limit from cycle 18's
(`maxRecDepth`, an elaborator limit) -- this time the *generated C
code*'s brace-nesting depth exceeded clang's default 256-bracket
ceiling during compilation, a downstream limit cycle 18's fix didn't
touch. Rather than reach for a compiler flag (fragile across
toolchains), split `main`'s single do-block into four helper functions
grouped by cycle range; `main` itself becomes a flat sequence of calls.
Verified the demo's full output is unchanged (all 32 cycles' text
intact, in order) before and after the split.

**Synthesis**: this cycle's headline result -- faithfulness transports
cleanly through the product, with no cost -- is worth setting explicitly
alongside the `∂² = 0` tension (cycles 8/16/27) as a *contrasting* data
point, not a lesser one: not every property this project has studied
fails to compose or transport under every construction. The
`well_founded`/`incidenceProd`-style projection technique (existentials
supplied by the very structure being projected FROM) is also a clean,
reusable pattern -- worth remembering if a `incidenceSum` or similar
construction is built later and needs an analogous converse. The
build-tooling fix is this project's second encounter with a scaling
limit purely from accumulated demo-output volume (cycle 18, cycle 32)
rather than proof complexity -- worth treating `Main.lean`'s structure
as something to keep revisiting as cycles accumulate, not a one-time
fix.

## Cycle 33

**Hypothesis**: (option 1 of cycle 32's queue, chosen over the T5-
translation option) build `incidenceSum`, the disjoint-union analogue
of `incidenceProd` (cycle 31), and test whether it also has a
faithfulness-transports-cleanly property analogous to cycle 32's, or
whether a sum behaves structurally differently from a product in ways
worth discovering.

**Method**: designed on paper before writing Lean, since a genuine
design question surfaced immediately: the product's two-sided unit is
simply `(inc1.unit, inc2.unit)`, because every element of `I1 × I2`
has both components -- but `I1 ⊕ I2` has no element belonging to
*both* sides, so a purely componentwise `glue` cannot satisfy
`unit_left`/`unit_right` at all (gluing the unit against an element
from the *other* side would need to produce that element, which
componentwise gluing structurally cannot do). Resolved by falling back
to the same "unit-absorbing" `glue` shape nearly every hand-built
instance in this project already used (`glue x y := if y = unit then
some x else if x = unit then some y else <componentwise, same side
only>`), and -- a further forced consequence -- a *constant* `typeFunc`
(`GraphType.unit`, matching every pre-cycle-31 instance), since a
genuinely varying `T1 ⊕ T2` typeFunc would make `type_preserve` fail
for the unit-absorption case (absorbing the unit against `y` produces
`y`, whose type need not match the unit's). Built the construction (all
seven obligations typechecked on the first attempt), then tested the
faithfulness question directly: does `incidenceSum natIncidence
natIncidence` stay faithful, given `natIncidence` itself is fully
faithful? Reasoned first (not guessed): `natIncidence`'s `0` is a leaf
(empty boundary) on *both* copies, and `boundaryMatched` is vacuously
satisfied when both elements have no boundary entries at all --
independent of the `Sum.inl`/`Sum.inr` tag, since there's nothing to
role-mismatch. This predicts `Sum.inl 0 ≈ Sum.inr 0` despite them being
distinct elements of `Nat ⊕ Nat`.

**Result**: **confirmed -- faithfulness does NOT transport through the
sum, in sharp contrast to cycle 32's product result.**
`incidenceSum_leaves_collapse` proves the general fact (any two leaves,
from either side, are `≈`-related in the sum -- the same "everything
related to everything" relation restricted to leaves that cycles
2/12/13/18/26 used, now shown to be forced by the *construction itself*
rather than by any one instance's design), and
`incidenceSum_leaves_cross_natIncidence` confirms it concretely:
`Sum.inl 0 ≈ Sum.inr 0` in `natIncidence ⊕ natIncidence`, even though
`natIncidence` alone is fully faithful. `#print axioms`: `propext`/
`Quot.sound` on the general theorem (no `Classical.choice`), standard
three on the concrete instantiation. One minor proof-engineering note:
a `<;>`-shared tactic bullet across `boundaryMatched`'s two clauses
(`.left`/`.right`) incorrectly cased on the same variable (`a`) for
both, when the second clause needed `b` -- caught by the type-checker
(a wrong hypothesis name appearing in the error) and fixed by splitting
into two explicit bullets, not by fighting the shared tactic further.
Full `lake build`: 46/46 jobs (new file `Sum.lean`). Repo-wide
`sorry`-as-tactic grep: none.

**Synthesis**: this is the first time two "generic constructors on
`Incidence`" have been directly compared, and the comparison itself is
the valuable output -- **which connective you choose changes which
properties survive**, exactly the kind of fact a real type theory needs
to track (products and sums behave differently with respect to
faithfulness in ordinary type theory too, for closely analogous
reasons: a sum type's injections don't carry enough structure to keep
elements from *different* summands apart when the summands' own
"empty" elements coincide under some invariant, here `≈`). The `unit`/
`typeFunc` design constraint discovered here (forced unit-absorption,
forced type-constancy) is also worth remembering as a genuine structural
fact about disjoint unions under `Incidence`'s axioms, not a proof-
engineering inconvenience -- it explains, after the fact, why every
instance built *before* `incidenceProd` (cycle 31) used exactly this
unit-absorbing shape: a disjoint-union-like construction is close to
what several early instances effectively *were* (leaf/non-leaf
disjoint cases), and the same constraint applied there too, just never
named explicitly until building a *generic* sum forced it into view.

## Cycle 34

**Hypothesis**: (option 2 of cycle 31's queue, twice carried forward)
a T5-style translation result for `incidenceProd` -- does
`natToFiniteSet` extend to a translation for `natIncidence ×
natIncidence` in the expected way, and would it also be a
`glue`-homomorphism-style result the way cycle 28's `cycleToNat` was?
Chosen over `incidenceSum`'s conditional-faithfulness option to avoid
this item being deferred a third time.

**Method**: rather than build a one-off translation specific to
`natIncidence × natIncidence`, generalized to match `incidenceProd`'s
own generic style: pairing *any* two translations that each reflect
their own instance's `≈` should produce a translation reflecting `≈`
on the product -- a direct consequence of cycle 32's
`incidenceProd_approxBisim_iff`, needing no new machinery beyond
componentwise pairing. While instantiating this against
`natToFiniteSet` specifically, a second, independent question
surfaced: `natToFiniteSet` (cycle 5) was only ever checked for
injectivity, back when no `glue` in this project had algebraic
structure worth checking a translation against -- does it *also*
happen to be a `glue`-homomorphism into list concatenation, the same
lens cycle 28 first applied to `cycleToNat`? Checked empirically first
(`#eval`, three concrete cases: `natToFiniteSet 3 ++ natToFiniteSet 4
== natToFiniteSet 7`, etc.) before formalizing.

**Result**: **both confirmed, on the second attempt for the
homomorphism proof.** `incidenceProd_translation_reflects` verifies
cleanly with `propext`/`Quot.sound`, no `Classical.choice`.
`natToFiniteSet_glue_hom` (`natToFiniteSet (m + n) = natToFiniteSet m
++ natToFiniteSet n`) needed one direction correction: the first
attempt inducted on the *second* summand (matching `Nat.add_succ`),
which produced a residual (`a :: (xs ++ ys) = xs ++ a :: ys`) that
isn't true for general lists -- a genuine mismatch between which
argument the induction should walk and which direction
`List.cons_append` associates, caught immediately by the type-checker
rather than requiring deep debugging. Inducting on the *first* summand
instead (`Nat.succ_add`) aligned cleanly with `(a :: xs) ++ ys = a ::
(xs ++ ys)`, always true, and the proof closed immediately. Combined
both into `natProdToFiniteSet_glue_hom`, showing the paired translation
is simultaneously a faithful `≈`-reflector *and* a `glue`-homomorphism
for the product -- the same "both properties at once" achievement
cycle 28 reached for `cycleToNat`, now demonstrated for a *generic*
construction rather than one hand-built instance. `#print axioms`:
`propext` alone on the pure list-append fact, standard sets on the
rest. Full `lake build`: 46/46 jobs. Repo-wide `sorry`-as-tactic grep:
none.

**Synthesis**: the genuinely notable part of this cycle isn't the
generic pairing theorem (a direct, low-risk consequence of existing
machinery) -- it's that a 29-cycle-old translation (`natToFiniteSet`,
cycle 5) still had an unchecked property, and a *new analytical lens*
introduced much later (cycle 28's "is this translation also a
homomorphism?" question) revealed it retroactively rather than only
ever applying to instances built after the lens existed. Worth keeping
in mind as a category of follow-up distinct from "new instance,"
"generalize a stalled result," or "audit unexercised parameters": periodically
re-examine *old* results through *newer* analytical questions that
didn't exist when they were first proved.

## Cycle 35

**Hypothesis**: (option from cycle 33's queue) does `incidenceSum` have
a *conditional* faithfulness result, given cycle 33 showed it fails in
general? Scoped before writing Lean: cycle 33's cross-side collapse
mechanism needs *both* sides to supply a leaf for the *same* pair, so a
natural sufficient condition is "at least one side has no leaves at
all" -- and `cycleIncidenceFixed` (cycle 27) is the perfect witness,
being both fully faithful and having *zero* leaves whatsoever (the
first instance in this project with that property).

**Method**: built the result in three pieces, mirroring cycle 32's
`incidenceProd_project` structure but adapted for a disjoint union. (1)
Cross-side non-bisimilarity whenever *either* side has any boundary
entry at all (via `not_approxBisim_of_boundary_mismatch`, cycle 21,
directly -- a `Sum.inl`-tagged entry can never be `boundaryCompatible`
with a `Sum.inr`-tagged one, the same tag-mismatch argument cycle 32
used for the product). (2) Same-side `≈` projects down to the
component instance's own `≈` -- structurally simpler than
`incidenceProd_project` since there's nothing to *combine*, only to
*isolate*. One genuine subtlety this direction had that the product's
projection didn't: `incidenceSum`'s `typeFunc` is *forced* constant
(cycle 33's design tension), so `IsBisimulation`'s type-preservation
obligation for the projected relation can't be derived for free the way
it could for the product's genuine `T1×T2` typing. Resolved by baking
`inc1.typeFunc x = inc1.typeFunc y` directly into the projected
relation's definition (rather than trying to derive it from the sum's
trivial type equality, which carries no real information), then
propagating it along boundary edges using `inc1`'s own
`type_consistent` obligation -- already guaranteed by the `Incidence`
structure, not an extra assumption. (3) Combined both into the full
iff, case-split on which side each of `p`/`q` is on (4 cases: same-side
uses the projection + each component's own faithfulness; cross-side
uses the non-bisimilarity fact, requiring only one side leafless).

**Result**: **confirmed on the first complete attempt (after the
`typeFunc` subtlety was identified and resolved during design, not
discovered as a build failure) -- and, notably, proves with only
`propext`/`Quot.sound`, no `Classical.choice`, fully constructive.**
`incidenceSum_faithful_of_faithful_no_shared_leaves` is stated
generically (restricted to `GraphType`-typed instances, matching every
concrete instance in this project, so the `typeFunc`-equality
hypothesis discharges trivially via `rfl` at call sites) and confirmed
concretely: `natIncidence ⊕ cycleIncidenceFixed` is fully faithful,
despite `natIncidence` itself having exactly one leaf (`0`) -- because
`cycleIncidenceFixed` supplies none, cross-side collapse never gets a
chance to happen. `#print axioms`: `propext`/`Quot.sound` on all five
new theorems. Full `lake build`: 46/46 jobs. Repo-wide `sorry`-as-tactic
grep: none.

**Synthesis**: this cycle closes the loop cycle 33 opened, the same way
cycle 30 closed cycle 20's loop and cycle 32 closed cycle 31's --
"declining/limiting a result for now" in this project consistently
turns out to be conditional on a specific piece of evidence, and that
evidence keeps arriving from *other* cycles' work rather than needing
to be manufactured on the spot (`cycleIncidenceFixed`, cycle 27's
byproduct of a completely different investigation, turned out to be
exactly what this cycle needed). The `typeFunc`-forced-constant
subtlety is also worth remembering as a second, independent way a
"projection" argument can need care beyond `incidenceProd_project`'s
template (that one needed only tag-matching for boundary entries; this
one additionally needed to route type-equality through
`type_consistent` by construction, not derive it from the ambient
bisimulation).

**Next hypothesis (cycle 36, not yet attempted)**: option from cycle
34's queue, not reached this cycle: does `incidenceSum` have an
analogous generic translation-pairing result (mirroring cycle 34's
`incidenceProd_translation_reflects`) -- likely via `Sum.elim t1 t2 :
I1 ⊕ I2 → S1 ⊕ S2` rather than a genuine pairing, and likely needing an
analogous "no shared collapsible structure" side-condition given this
cycle's finding that plain `incidenceSum` doesn't preserve faithfulness
unconditionally. Also open, not yet scoped: are there other existing
instances (beyond `cycleIncidenceFixed`) with the "faithful and
leafless" property this cycle's condition needs, making
`incidenceSum_faithful_of_faithful_no_shared_leaves` more broadly
reusable, or is `cycleIncidenceFixed` currently unique in this respect?

## Cycle 36

**Hypothesis**: two items queued from cycle 35. (1) An audit: is
`cycleIncidenceFixed` unique among every instance built so far in this
project in being *both* fully faithful *and* leafless -- the two
properties `incidenceSum_faithful_of_faithful_no_shared_leaves` needs
on at least one side -- or are there other witnesses that would make
that theorem more broadly reusable? (2) Does `incidenceSum` have a
generic translation-pairing result mirroring cycle 34's
`incidenceProd_translation_reflects`? The naive guess going in was
"probably conditional, needing a leafless-side hypothesis like cycle
35's faithfulness result, and probably via `Sum.elim t1 t2 : I1 ⊕ I2 →
S1 ⊕ S2` sharing a single target type `S`."

**Method**: (1) audited every named instance in the project against
the two properties. `natIncidence`: faithful (cycle 4) but has exactly
one leaf (`0`), so not leafless. `cycleIncidence` (pre-fix, cycle 26):
leafless but *not* faithful -- that gap is the entire reason cycle 26
built the fixed version. `incidenceProd`/`incidenceSum` themselves are
constructors, not base instances -- they inherit leaves from whichever
factors have them, so they can't independently break the tie.
`cycleIncidenceFixed` (cycle 27) remains the only instance combining
both properties. (2) Before writing any Lean, reconsidered the naive
guess: the queued plan used `Sum.elim t1 t2`, which maps *both* sides
into a *shared* target `S` -- the same shape that let cycle 33's
"flat leaves collapse" happen (two elements from different sides
landing in the same place). Switched to `Sum.map t1 t2 : I1 ⊕ I2 → S1 ⊕
S2` instead, which keeps the two sides' images in a genuinely disjoint
`S1 ⊕ S2`. Consequence, checked before formalizing: for `p` on the left
and `q` on the right, `Sum.map t1 t2 p = Sum.inl (t1 _)` and `Sum.map
t1 t2 q = Sum.inr (t2 _)` can *never* be equal, by `Sum`'s constructor
disjointness alone -- so cross-side translate-equality is impossible to
even hypothesize, not merely false for some instance. That leaves only
the two same-side cases to prove, each needing "same-side `≈` in a
factor lifts to `≈` in the sum" -- the converse of cycle 35's
`incidenceSum_project_left`/`_right`. Built `incidenceSum_lift_left`
and `incidenceSum_lift_right` first, in a scratch file, each
constructing the lifted bisimulation relation directly from the
factor's witnessing relation (`rel1`/`rel2`), matched only on the
same-side pattern (`Sum.inl x1, Sum.inl y1 => rel1 x1 y1`, `_, _ =>
False` otherwise) -- and found, checking the `IsBisimulation`
obligation, that *no* `typeFunc`-equality hypothesis was needed at all
in this direction: `incidenceSum`'s `typeFunc` is constant, so the
type-preservation clause is `rfl` regardless of what `inc1`/`inc2`'s
own typing says. This is the mirror image of cycle 35's subtlety (which
needed the `typeFunc`-baking trick in the *project* direction) --
confirming the asymmetry is about which direction of implication is
being proved, not an inconsistency between the two cycles' approaches.
Combined both lifts into `incidenceSum_translation_reflects` by cases
on `p`/`q`: same-side closes via `ht1`/`ht2` composed with the
corresponding lift; cross-side closes by deriving `False` from
`Sum.map`'s injectivity-per-side (`Sum.inl.injEq`/`Sum.inr.injEq` on
the same-side branches; the cross-side branches close by `simp`
alone, since `Sum.inl _ = Sum.inr _` is already absurd).

**Result**: **(1) confirmed: `cycleIncidenceFixed` is currently
unique** among every instance built in this project in combining full
faithfulness with zero leaves -- `incidenceSum_faithful_of_faithful_no_shared_leaves`
is not yet reusable with a different right-hand witness, though nothing
in its statement restricts it to `cycleIncidenceFixed` specifically,
so a future instance with the same two properties would work
immediately. **(2) confirmed on the first complete attempt for both
lifts and the combined theorem** -- and, the headline finding,
**`incidenceSum_translation_reflects` is UNCONDITIONAL**: no
faithfulness or leafless hypothesis on `inc1`/`inc2` at all, only that
`t1`/`t2` individually reflect translate-equality to `≈` in their own
factor (the same hypothesis shape as cycle 34's
`incidenceProd_translation_reflects` and the original
`natToFiniteSet_reflects_approxBisim`). Confirmed concretely: pairing
`natToFiniteSet` via `Sum.map` on both sides of `natIncidence ⊕
natIncidence` still reflects translate-equality to `≈` in the sum, even
though that very sum is *not* faithful (cycle 33's
`incidenceSum_leaves_cross_natIncidence`). `#print axioms`: only
`propext`/`Quot.sound` on `incidenceSum_lift_left`,
`incidenceSum_lift_right`, and `incidenceSum_translation_reflects`. Full
`lake build`: 46/46 jobs. Repo-wide `sorry`-as-tactic grep: none.

**Synthesis**: the two halves of this cycle sharpen each other. Item
(1) confirms `incidenceSum_faithful_of_faithful_no_shared_leaves`
(cycle 35) is currently a *single-instance* result, not yet a broadly
reusable pattern -- an honest limitation to record rather than paper
over. Item (2) is the more interesting finding: it shows that
*faithfulness-transport* and *translation-pairing* are genuinely
different properties of the same constructor (`incidenceSum`) that
need *different* side-conditions -- one conditional (cycle 35, needs a
leafless side), one unconditional (this cycle, needs nothing). The
mechanism generating the difference is not about `incidenceSum`
per se, but about which *target type* a downstream construction is
asked to land in: `≈`-transport is a property of the sum's *internal*
structure (its own elements can genuinely collapse), while
translation-pairing via `Sum.map` routes through an *external* type
(`S1 ⊕ S2`) whose disjointness is available "for free" as soon as the
translation avoids collapsing that external structure too (i.e.
`Sum.elim` instead of `Sum.map`, which was the naive first guess this
cycle explicitly avoided before writing any proof). This is also a
methodological point worth keeping for future cycles: choosing
`Sum.map` over `Sum.elim` at the *design* stage, before attempting a
proof, avoided reproducing cycle 33's already-understood collapse
mechanism inside a new theorem -- a case of applying an earlier
cycle's finding proactively rather than rediscovering it as a second
build failure.

**Next hypothesis (cycle 37, not yet attempted)**: several threads
remain open. (a) `incidenceProd` and `incidenceSum` are now each
reasonably well-understood (congruence, faithfulness-transport,
translation-pairing) -- is there a THIRD generic constructor worth
building (e.g. an internal hom / function-space `Incidence`, or a
quotient construction using `approxBisim` itself as the identifying
relation, which would be a natural place to test whether the
bisimulation machinery is well-behaved under its own quotients)? (b)
The original large research vision (internal ℕ/set/logic/dependent-type
construction inside `Inc`) remains largely untouched beyond
`natIncidence`/`Peano.lean` -- `incidenceProd`/`incidenceSum` are
plausible building blocks toward an internal logic (product ~ AND, sum
~ OR) but no cycle has yet attempted to state or prove anything in
that direction explicitly. (c) Narrower and more tractable: does
`incidenceProd_translation_reflects` (cycle 34) have the same kind of
subtlety this cycle found for the sum -- i.e., is there a "naive
target type" choice for the product analogous to `Sum.elim` that would
have caused trouble, and did cycle 34 avoid it by luck or by
structure? Worth a short confirmatory audit even if the expected answer
is "no issue, `S1×S2` was never ambiguous the way `S1⊕S2` vs `S` was."

## Cycle 37

**Hypothesis**: option (c) from cycle 36's queue, chosen for being
explicitly scoped as "narrower and more tractable" than options (a) and
(b): does `incidenceProd_translation_reflects` (cycle 34) have the same
kind of subtlety cycle 36 found for `incidenceSum` -- a "naive target
type" choice analogous to `Sum.elim` that would have caused the product
version to fail unconditionally too? Going in, the expected answer was
"no issue," but the point of the audit was to *confirm* this rather
than assume it, and to understand *why* if so -- luck, or structure.

**Method**: read the existing `incidenceProd_translation_reflects`
(`Product.lean`, cycle 34) directly rather than re-deriving it from
scratch. Its hypothesis is `(t1 p.1, t2 p.2) = (t1 q.1, t2 q.2)` -- a
pairing landing in a genuine `S1 × S2`, exactly the `Prod.map`-shaped,
non-collapsing form cycle 36 identified as the *safe* choice for sums
(as opposed to `Sum.elim`'s shared-target form). So by inspection, the
product theorem was never built the collapsing way. The more
interesting question was *why not* -- was this luck, or is there a
structural reason products never face this choice? Reasoned: `Sum.elim
t1 t2 : I1 ⊕ I2 → S` exists in the standard library specifically
*because* `Sum` has two genuinely distinct cases that must be resolved
into a single output type -- it is the canonical eliminator `Sum` is
built around, and reaching for it when building *any* translation out
of a sum is the natural, idiomatic first move. `Prod` has no analogous
eliminator into a single shared type: every element of `I1 × I2`
already carries *both* components simultaneously, so there is no
"case" to resolve -- pairing componentwise into `S1 × S2` is the only
shape that even makes sense as a *generic* translation, let alone the
first one anybody would reach for. This predicts the asymmetry is
structural, not luck -- but to avoid asserting "products are immune"
without evidence, tested the flip side directly: does a *deliberately
constructed* shared-target collapse for the product, mirroring
`Sum.elim`'s shape, also fail, the way it would have for the sum? Built
`prodCollapseTrivial : Nat × Nat → List Unit := fun _ => []` (the
product analogue of a constant `Sum.elim`) and checked, first in a
scratch file, then transcribed: does it collapse two non-`≈`-related
pairs?

**Result**: **confirmed on the first attempt, both directions.** (1)
No subtlety in the existing cycle-34 theorem -- it already uses the
`Prod.map`-shaped, non-collapsing pairing. (2) The reason is structural
(no natural eliminator into a shared type exists for `Prod`), not luck.
(3) **Products are not structurally immune to the underlying failure
mode** -- `prodCollapseTrivial (0, 0) = prodCollapseTrivial (0, 1)`
(trivially, both are `[]`) while `¬ approxBisim (incidenceProd
natIncidence natIncidence) (0, 0) (0, 1)` (via
`incidenceProd_faithful_of_faithful`, cycle 32, since `(0,0) ≠ (0,1)`)
-- a deliberately bad shared-target translation for the product fails
exactly the way `Sum.elim` would have for the sum. `#print axioms`:
`prodCollapseTrivial_collapses` needs no axioms at all (`rfl`);
`prodCollapseTrivial_not_reflects` needs `propext`/`Classical.choice`/
`Quot.sound` -- consistent with the existing baseline, since it composes
`natIncidence_approxBisim_iff` (cycle 4), which has carried
`Classical.choice` since that cycle; `incidenceProd_faithful_of_faithful`
itself remains `propext`/`Quot.sound` only, unchanged. Full `lake
build`: 46/46 jobs. Repo-wide `sorry`-as-tactic grep: none.

**Synthesis**: this cycle is a "quick audit" in the sense named back in
cycle 35/36's write-ups -- it closes a loop rather than opening new
ground, and the headline finding is a *negative* result (no subtlety
found) plus a structural explanation for *why not*, rather than a new
theorem enabling new proofs. Worth recording anyway, per this project's
standing view that confirmatory work is not inherently less valuable
than novel-phenomenon discovery: the asymmetry between cycle 34
(product, unconditional and clean on the first attempt) and cycle 33/36
(sum, conditional faithfulness but unconditional translation-pairing,
and only after identifying a specific pitfall) was never about one
constructor being *safer* than the other in any absolute sense -- both
can fail under a badly-chosen translation. It was about which
constructor has an *idiomatic, tempting* shape that happens to
coincide with the bad choice. `Sum.elim` is genuinely the "obvious"
thing to reach for when translating out of a sum; nothing analogous
exists for products. This is a useful general lesson for any *future*
generic constructor built in this project (item (a) from cycle 36's
queue, still open): when adding a translation-pairing result, check
whether the construction's *canonical eliminator/recursor* shape
happens to be collapsing, rather than assuming safety or danger from
the construction's "shape" alone.

**Next hypothesis (cycle 38, not yet attempted)**: with cycle 36's
queue now fully drained (item (b) partially addressed by this cycle's
synthesis note; item (a) and the deeper part of (b) still open), the
two live threads are: (a) a third generic constructor -- most promising
candidate is a quotient construction using `approxBisim` itself as the
identifying relation (test whether the bisimulation machinery is
well-behaved under its own quotients: does `Incidence` descend to the
`≈`-quotient of an existing instance, and if so, is the quotient
trivially/necessarily faithful by construction, in contrast to both
`incidenceProd`'s unconditional and `incidenceSum`'s conditional
results?); (b) the still-mostly-untouched original vision of an
internal ℕ/set/logic construction inside `Inc` -- concretely, does
`incidenceProd`/`incidenceSum` satisfy anything resembling logical laws
under `≈` (e.g. a distributivity-flavored statement relating
`incidenceProd inc1 (incidenceSum inc2 inc3)` to `incidenceSum
(incidenceProd inc1 inc2) (incidenceProd inc1 inc3)`)? The latter is
likely too large for one cycle as stated -- if pursued, scope it down
first (e.g. just check whether a natural map between the two carrier
types exists and is well-typed, before attempting any bisimulation
result about it).

## Cycle 38

**Hypothesis**: option (a) from cycle 37's queue -- the third generic
constructor thread, specifically the "most promising candidate" named
there: a quotient construction using `approxBisim` itself as the
identifying relation. Rather than jump straight to building a full
`Incidence` structure on the `≈`-quotient of an existing instance
(the scope-down cycle 37 itself recommended for large next steps),
this cycle checks the necessary PREREQUISITE first: does `Incidence`'s
own data (`boundary`, `glue`) even respect `≈` -- i.e. is it constant
on `≈`-equivalence classes? This is exactly the well-definedness side
condition `Quotient.lift`/`Quotient.lift₂` need to turn a function on
the carrier `I` into a function on `Quotient (approxBisimSetoid inc)`.
Going in, genuinely unsure which way this would go -- `≈` is defined
via existential "up to compatible matching" (`boundaryMatched`), not
literal equality, so there was reason to suspect it might fail, but no
prior cycle had checked.

**Method**: split into a positive half and a negative half. POSITIVE:
package `approxBisim` as a genuine `Setoid I` -- trivial given
`approxBisim_refl`/`_symm`/`_trans` already proven in the root file
(no new proof obligations at all, `approxBisimSetoid` is a one-line
anonymous-constructor definition). NEGATIVE: rather than search for a
fresh counterexample, recognized that `cycleIncidence` (cycle 26, the
*pre-fix*, non-faithful cycle instance) was already a ready-made
witness -- `cycleIncidence_all_collapse` (cycle 26) already proves
`approxBisim cycleIncidence x y` for ALL `x y : CycleId`, so `c0 ≈ c1`
was already on hand. Checked concretely (first via `decide`, which
failed because `Endpoint` has no derived `DecidableEq`, only `Repr` --
fixed with an explicit `injection`-based inequality proof extracting
the differing `i` field) whether `cycleIncidence.boundary c0` and
`cycleIncidence.boundary c1` are equal as literal lists. They are not:
`c0`'s single boundary entry points to predecessor `c3`, `c1`'s points
to `c0` -- genuinely different `Endpoint` values, not just different
positions. Once boundary's failure was confirmed, checked whether this
was isolated to `boundary` or a broader phenomenon: tested `glue`
similarly, gluing `c0` and `c1` (already known `≈`-related) against a
fixed third element `c0` -- `cycleAdd c0 c0 = c0` vs. `cycleAdd c1 c0 =
c1`, again genuinely different.

**Result**: **confirmed on the first attempt for all five theorems.**
`approxBisimSetoid` is unconditionally correct (`propext` only, in fact
needs nothing beyond what was already proven). The negative result is
real and general, not an artifact of a specific counterexample search:
**`boundary` is NOT constant on `≈`-classes** (`cycleIncidence_boundary_not_approxBisim_invariant`),
witnessed concretely and packaged existentially
(`exists_incidence_boundary_not_approxBisim_congruent`); **`glue` fails
the identical check** (`cycleIncidence_glue_not_approxBisim_invariant`).
`#print axioms`: `propext` only on all five new theorems -- fully
constructive, no `Classical.choice`. Full `lake build`: 48/48 jobs (new
file `IncidenceTheory/Quotient.lean`, wired into `Main.lean`'s
imports). Repo-wide `sorry`-as-tactic grep: none.

**Synthesis**: this cycle is a genuine "novel finding" cycle wearing
the clothes of a scoping exercise -- it doesn't build the quotient
constructor cycle 36/37 queued, but it answers a real open question
about whether the *naive* version of that constructor (the one that
would occur to anyone first: just reuse `inc.boundary`/`inc.glue`
directly via `Quotient.lift`/`lift₂`) is even well-typed, and the
answer is a clean, general **no**, for at least one instance already
built in this project. This connects to a standard distinction in
bisimulation/coalgebra theory that this project has now independently
rediscovered from first principles: bisimilarity, by design, only ever
requires *behavioral* matching (existential, up to compatible
correspondence), which is strictly weaker than requiring the
underlying *structural data* to be literally invariant -- so a
bisimulation-quotient does not automatically inherit a well-defined
copy of the original structure's operations the way a
congruence-quotient would. The methodological point matters as much as
the result: checking the prerequisite BEFORE attempting the full
construction turned what could have been a multi-cycle dead-end
(discovered only after building most of a quotient `Incidence` and
hitting an unprovable `well_founded`/`type_preserve` obligation) into a
single well-scoped cycle with a clean, useful negative result and a
reusable positive piece (`approxBisimSetoid`) salvaged from it.

**Next hypothesis (cycle 39, not yet attempted)**: given this cycle's
finding, a full "naive" quotient `Incidence` constructor is off the
table, but two refined variants remain open. (a) A quotient via
*canonical representative* (`Quotient.out`, using `Classical.choice`
under the hood, already an accepted axiom in this project): define
`boundary` on the quotient as `inc.boundary ∘ Quotient.out`. This is
trivially well-typed (no lifting needed, `Quotient.out` is already a
genuine function `Quotient s → I`), but likely uninteresting on its
own -- it doesn't actually collapse any structure, just re-indexes the
carrier type, so worth checking what (if anything) it buys before
committing to it. (b) Restrict to already-`≈`-faithful instances (where
`≈` coincides with `=`, e.g. `natIncidence`, `cycleIncidenceFixed`): is
the well-definedness question vacuous there (trivially true since
`≈`-classes are singletons), and if so, is a "quotient of a faithful
instance" simply isomorphic to the instance itself -- a clean but
low-payoff confirmatory result, or is there something less trivial to
say? Separately, option (b) from cycle 37's queue (the internal-logic
distributivity direction) remains open and untouched, still likely
needing its own scope-down step before any cycle attempts it directly.

## Cycle 39

**Hypothesis**: option (a) from cycle 38's queue -- does the
*canonical-representative* quotient variant fare any better than the
naive lift cycle 38 refuted? Concretely: define the quotient's
`boundary` via `inc.boundary` applied to a chosen class representative
(`Quotient.out`-style) rather than trying to lift `inc.boundary`
directly. Since this project has no `mathlib` dependency, `Quotient.out`
itself isn't available and would need to be built by hand from core
Lean's `Quotient.exists_rep` + `Classical.choice` first. Tested again
against `cycleIncidence` (cycle 26), since `cycleIncidence_all_collapse`
-- ALL FOUR elements already one `≈`-class -- makes it the sharpest
available case: `Quotient (approxBisimSetoid cycleIncidence)` is a
literal one-point type.

**Method**: built the representative construction concretely first
(`quotOut`, `cycleRep`, `cycleRep_respects_approxBisim`) to see exactly
what would go wrong, following the "test concretely before
generalizing" habit. While setting up the proof that `cycleRep`
respects `≈`-classes, noticed the *shape* of the argument needed
(`well_founded`'s `¬∃ e ∈ boundary i, e.i = i`, combined with the fact
that a representative of `cyclePred (rep c0)` and `c0` collapse
together since literally everything in `cycleIncidence` is `≈`-related)
generalizes far past `cycleRep` specifically: since `Quotient
(approxBisimSetoid cycleIncidence)` has only ONE point, `Subsingleton.elim`
forces *any* boundary entry's `.i` field, on *any* element of that
quotient, to equal the very element whose boundary it's attached to --
exactly what `well_founded` forbids, regardless of how `boundary` on
the quotient is actually defined. Proved this as a fully general,
`cycleIncidence`-independent theorem first
(`incidence_subsingleton_boundary_empty`: any `Incidence` structure on
a `Subsingleton` carrier has empty boundary everywhere), then confirmed
it genuinely applies here by establishing `Quotient
(approxBisimSetoid cycleIncidence)` really is a `Subsingleton`
(`Quotient.ind` twice, `Quotient.sound` via `cycleIncidence_all_collapse`).
Kept the concrete `cycleRep`-based construction too, as a hands-on
complement showing the literal self-loop a real representative
construction produces, rather than discarding the work once the more
general theorem was found.

**Result**: **confirmed on the first attempt for all seven theorems** --
`incidence_subsingleton_boundary_empty` needs only `propext`;
`cycleIncidence_quotient_subsingleton` needs `propext`/`Quot.sound`;
`quotOut`/`cycleRep`/the representative-based theorems need
`Classical.choice` in addition (expected, since core Lean's substitute
for `Quotient.out` is built from it) -- all within this project's
accepted axiom set, no `sorryAx`. The finding is **more general than
what was asked**: the question wasn't just "does the representative
variant work" (no) but "does *any* possible quotient construction work
for a fully-collapsed instance" (also no, and provably so, by
`well_founded` alone). Full `lake build`: 48/48 jobs. Repo-wide
`sorry`-as-tactic grep: none.

**Synthesis**: this cycle is the second half of a two-cycle pair with
cycle 38, and together they now settle the *entire* naive-quotient
question this project's "third generic constructor" thread opened:
cycle 38 refuted the literal lift, this cycle refutes the
representative variant AND everything else at once via a genuinely
cleaner argument than either individually. The generalization pattern
here is worth naming explicitly: starting from a specific proof
obligation (`cycleRep` respecting `≈`) and noticing that the *shape* of
what made it provable (`cyclePred (rep c0)` and `c0` collapsing via
totality) was really a fact about the *carrier type* (`Subsingleton`),
not about `cycleRep` -- so the general theorem was found by
abstracting away from an already-working concrete proof, not by
guessing at generality up front. This is a distinct discovery mode from
most of this project's prior cycles (which usually stated the general
theorem first, then instantiated it) and is itself worth remembering as
a technique: build the concrete case, then ask "what property of the
concrete setup did this proof actually use?" This closes the "third
generic constructor" thread's most promising branch as a genuine dead
end for at least one class of instances (fully-collapsed ones) --
future attempts at a quotient constructor should either restrict to
already-faithful instances (queue item (b) from cycle 38, likely
low-payoff but now the more clearly-motivated remaining option) or
target instances with a nontrivial but not-fully-collapsed `≈`-quotient
(neither tried yet, and possibly the more interesting regime -- a
quotient that's genuinely "in between" a Subsingleton and faithful).

**Next hypothesis (cycle 40, not yet attempted)**: three live threads.
(a) Item (b) from cycle 38's queue, now better motivated by this
cycle's contrast: for an already-`≈`-faithful instance (`natIncidence`,
`cycleIncidenceFixed`), is the quotient-`Incidence` question trivial
(quotient classes are singletons, so the quotient is straightforwardly
isomorphic to the original), and if so, is that isomorphism itself
worth stating as a clean theorem (a genuine, if low-drama, positive
quotient-constructor result to sit alongside this cycle's negative
one)? (b) A genuinely new regime this cycle's synthesis surfaced: does
any EXISTING instance in this project have a `≈`-quotient that is
neither a Subsingleton (fully collapsed) nor trivial (fully faithful)
-- i.e. a quotient with more than one but fewer than "all" classes? No
prior cycle has checked; `simplexIncidence` (vertices/edges/face
"stayed separated by differing boundary shapes" per cycle 33's own
recollection) is a plausible candidate worth auditing first before
attempting any construction on it. (c) Still open and untouched: option
(b) from cycle 37's queue, the internal-logic distributivity direction
relating `incidenceProd`/`incidenceSum`, likely needing its own
scope-down step before any cycle attempts it directly.

## Cycle 40

**Hypothesis**: option (a) from cycle 39's queue -- the "opposite end"
from cycles 38/39's Subsingleton finding. Those two cycles settled the
fully-collapsed case (`cycleIncidence`): every possible quotient
construction is a dead end there, forced into total triviality by
`well_founded` alone. What happens at the other extreme -- an already
`≈`-*faithful* instance (`natIncidence`, `cycleIncidenceFixed`), where
every `≈`-class is a *singleton*? Cycle 39's queue framed this as
"likely low-payoff" but worth confirming: is the quotient genuinely
just a relabeling of the original carrier, with nothing new to say?

**Method**: rather than attempt to build a full isomorphic `Incidence`
structure on the quotient (transporting `boundary`/`glue`/all 7
obligations through a bijection -- a materially bigger undertaking than
this cycle's likely payoff justifies, an explicit scoping decision made
up front rather than discovered mid-cycle), scoped down to the crux
claim: is `Quotient.mk (approxBisimSetoid inc)` a genuine bijection
`I ≃ Quotient (approxBisimSetoid inc)` for a faithful instance? Split
into injectivity and surjectivity. Injectivity needed `Quotient.exact`
(core Lean, the converse of `Quotient.sound`: `Quotient.mk s a =
Quotient.mk s b → a ≈ b`) composed directly with the instance's own
faithfulness theorem -- a one-line proof once the right core lemma was
located. Surjectivity holds unconditionally for ANY instance via
`Quotient.ind` (not specific to faithfulness at all -- included for
completeness of the bijection statement, and to make explicit which
half of the argument faithfulness actually does the work for).
Confirmed concretely against both faithful instances built so far
(`natIncidence`, cycle 4; `cycleIncidenceFixed`, cycle 27) rather than
leaving the general theorem uninstantiated.

**Result**: **confirmed on the first attempt for all three theorems.**
`quotient_mk_injective_of_faithful`, `quotient_mk_surjective`, and the
combined `quotient_mk_bijective_of_faithful` all need only `propext` --
no `Classical.choice` at all, a genuinely simpler axiom profile than
cycle 39's representative-based theorems (which needed
`Classical.choice` to build `quotOut`). Both concrete instantiations
(`natIncidence`, `cycleIncidenceFixed`) typecheck directly against the
general theorem. Full `lake build`: 48/48 jobs. Repo-wide
`sorry`-as-tactic grep: none.

**Synthesis**: this cycle completes the two-pole picture cycles 38-40
now tell together: `cycleIncidence`'s Subsingleton quotient (cycles
38/39) collapses *everything* and is forced into total triviality;
a faithful instance's quotient (this cycle) collapses *nothing* and is
just a relabeling. Both extremes turn out to be well-understood and, in
their own ways, uninteresting as genuine "new constructions" -- the
Subsingleton case because nothing survives, the faithful case because
nothing changes. This sharpens cycle 39's own synthesis note into a
concrete prediction for cycle 41: the only regime left where a
quotient-`Incidence` constructor could produce something genuinely NEW
(neither degenerate collapse nor a mere relabeling) is an instance
whose `≈`-quotient has more than one class but fewer classes than
elements -- and no cycle has yet confirmed such an instance exists
among those already built in this project. The methodological
discipline exercised this cycle (deciding NOT to build the full
isomorphic-structure transport, and saying so explicitly, rather than
either overbuilding or silently under-delivering) is worth naming: not
every queued item needs to be pursued to its maximal form to close the
loop it opens -- the crux claim can be the whole payoff.

**Next hypothesis (cycle 41, not yet attempted)**: item (b) from cycle
39's queue, now the clear next step given this cycle's completed
two-pole picture: audit whether any EXISTING instance already built in
this project has a `≈`-quotient in the genuinely interesting middle
ground -- more than one class, fewer than "all". `simplexIncidence`
(vertices/edges/face reportedly "stayed separated by differing
boundary shapes" per cycle 33's recollection, suggesting it might NOT
fully collapse but is also very likely not faithful, given `Incidence`
instances with genuine substructure have historically shown partial
collapse patterns in this project) is the leading candidate -- audit
first (which pairs of elements are/aren't `≈`-related) before
attempting any quotient construction on it. If no existing instance
qualifies, that itself would be worth noting as a gap: this project
has, apparently, only ever built instances at one of the two extremes
this cycle and cycles 38/39 characterized. Separately, option (c) from
this cycle's queue (= option (b) from cycle 37's queue) remains open:
the internal-logic distributivity direction relating
`incidenceProd`/`incidenceSum`.

## Cycle 41

**Hypothesis**: item (b) from cycle 40's queue -- does any EXISTING
instance in this project have a `≈`-quotient in the genuinely
interesting middle ground (more than one class, fewer than "all")?
Cycle 40's own note flagged `simplexIncidence` as the leading candidate
based on a loose recollection ("vertices/edges/face stayed separated by
differing boundary shapes"), but treated this as needing a fresh audit.

**Method**: before auditing from scratch, searched `Simplex.lean` for
what was already known -- and found the entire question had already
been *definitively answered*, across cycles 12 (vertices collapse), 18
(edges collapse, confirmed with a better proof strategy), 21/22 (the
three shapes are pairwise non-bisimilar, first via representative
witnesses then generalized), and 23 (the full 49-case exhaustive
characterization). `simplexToShape_iff_approxBisim` already proves `≈`
is *exactly* `simplexToShape`-agreement: three classes out of seven
elements, no coarser and no finer. This meant the "audit" step was
mostly archaeological -- recognizing that a years-old (many-cycles-old)
result already answered the current question, rather than reproving
anything about `simplexIncidence` itself. With the middle-ground
instance identified, pushed forward into genuinely new territory:
does this quotient support the same kind of construction cycles 38-40
explored for the two extremes? Checked, in order: (1) does
`simplexToShape` pass the `Quotient.lift` well-definedness check cycle
38 found `boundary`/`glue` fail for `cycleIncidence`? (Recognized this
is *exactly* what `simplexToShape_distinguishes`, cycle 23, already
proves -- no new proof needed.) (2) Is the resulting quotient map
`Quotient (approxBisimSetoid simplexIncidence) → SimplexShape`
bijective, mirroring cycle 40's faithful-instance pattern? (3) Can a
genuine fresh `Incidence` structure be built directly on `SimplexShape`
by collapsing each shape's boundary targets through `simplexToShape`,
succeeding where cycles 38/39 showed the fully-collapsed case must
fail? (4) Honestly checked, not assumed: is this new structure's `glue`
actually *derived* from `simplexIncidence`'s own `glue` (i.e. is
`simplexToShape` a `glue`-homomorphism, the property cycles 28/34
established for other translations)?

**Result**: **confirmed on the first attempt for every piece.** (1)
`simplexQuotientToShape := Quotient.lift simplexToShape
simplexToShape_distinguishes` typechecks directly -- `propext`/
`Quot.sound` only, no `Classical.choice` (a simpler axiom profile than
cycle 39's representative-based constructions, since no `Classical.choice`-
dependent representative-picking was needed at all here). (2) Genuine
bijection: `simplexQuotientToShape_injective` (via
`simplexToShape_reflects`, cycle 22, plus `Quotient.sound`) and
`simplexQuotientToShape_surjective` (three concrete witnesses, one per
shape) both hold. (3) **`shapeIncidence : Incidence SimplexShape
SimplexRole GraphType`** builds cleanly with all 7 obligations
discharged, using the SAME proof patterns `simplexIncidence`/
`cycleIncidence` already established (`cases <;> simp <;> first | ...`)
-- notably, `well_founded` is NOT violated the way cycle 39 found it
must be for `cycleIncidence`'s Subsingleton quotient: `vertex`'s
boundary is empty, `edgeShape`'s entries point only to `vertex`, and
`faceShape`'s entries point only to `edgeShape` -- the shape-grading
(0-cells ← 1-cells ← 2-cells) is itself well-founded, so collapsing
*within* each grade never creates a self-loop the way collapsing
*everything* did. (4) **`simplexToShape` is NOT a `glue`-homomorphism**
between `simplexIncidence` and `shapeIncidence`: concrete counterexample
via `decide`, `simplexIncidence.glue v1 face = some v1` (mapping to
`some vertex`) vs. `shapeIncidence.glue vertex faceShape = some
faceShape` -- a genuine mismatch, confirming (not assuming) that
`shapeIncidence` is *a* valid structure living on the quotient's
carrier, not one *derived* from `simplexIncidence`'s own `glue` via any
structure-preserving transport (consistent with, and a more textured
instance of, cycle 38's general finding that `glue` does not respect
`≈`). `#print axioms`: `propext`/`Quot.sound` on the bijection theorems,
`propext` only on the `glue`-homomorphism refutation, no `sorryAx`
anywhere. Full `lake build`: 48/48 jobs (new imports wired: `Quotient.lean`
now also imports `Simplex.lean`). Repo-wide `sorry`-as-tactic grep:
none.

**Synthesis**: this cycle closes the three-cycle arc (38, 39, 40, 41)
that this project's "third generic constructor" thread (queued since
cycle 36) opened, and it closes it with a genuine POSITIVE result at
last, after three cycles that were negative (38, naive lift fails),
negative-but-more-general (39, representative variant also fails, for a
deeper structural reason), and negative-but-trivial (40, faithful
instances add nothing new). The middle ground is not merely "in
between" in class *count* -- it is different in *kind*: what determines
whether a quotient construction can succeed is not how much collapse
happens, but whether the collapse respects some well-founded grading
already present in the instance. `simplexIncidence`'s shape-grading
(vertex/edge/face) is exactly such a structure, and it happens to
survive collapse-within-grade while `cycleIncidence`'s totally flat,
ungraded 4-cycle cannot survive any collapse at all. This is also a
methodological point worth naming: the "audit" step of this cycle
turned out to be almost pure archaeology -- the hard mathematical work
(cycles 12-23) predated the question this cycle asked by dozens of
cycles, and the actual contribution here was recognizing an old result
as the answer to a new question, then building the (comparatively
mechanical, pattern-matching) new construction on top of it. Not every
cycle's payoff is a new proof; sometimes it's a new *connection*.

**Next hypothesis (cycle 42, not yet attempted)**: two live threads,
both already queued and untouched. (a) Option (c) from cycle 41's own
queue (= option (b) from cycle 37's queue): the internal-logic
distributivity direction relating `incidenceProd`/`incidenceSum` --
still the largest, most open item, likely needing its own scope-down
step (e.g. just checking whether a natural map between the two carrier
types exists and is well-typed, before attempting any bisimulation
result). (b) A natural follow-up this cycle's `glue`-homomorphism
refutation surfaces: is there a *different*, less naive definition of
`shapeIncidence.glue` (this cycle's was a direct copy of
`simplexIncidence`'s own unit-absorbing pattern, not derived from
anything) under which `simplexToShape` WOULD be a genuine
`glue`-homomorphism -- or is that structurally impossible for the same
reason cycle 38 found `glue` doesn't respect `≈` in general, meaning no
choice of quotient-carrier `glue` could ever be induced this way?
Worth a short, focused check before concluding either way.

## Cycle 42

**Hypothesis**: pick between cycle 41's two queued threads by tractability
rather than size. Thread (a) (internal-logic distributivity between
`incidenceProd`/`incidenceSum`) was flagged as the largest, most open item,
explicitly needing its own scope-down step first. Thread (b) (a less naive
`shapeIncidence.glue` making `simplexToShape` a genuine glue-homomorphism)
was flagged as a short, focused check. Orthogonal to both, the ADR's
"完成へ向けた9項目ロードマップ" names a THIRD, independently-tracked item —
item 3, the extreme value theorem — as "進行中" with an explicit remaining
scope already isolated by the ADR's 2026-07-13 追補: generalize that a
nonempty sequentially compact real subset is bounded above/below and
achieves its `sup`/`inf`, then apply this to continuous images of closed
intervals. Since cycles prior to this one had already built closed-interval
sequential compactness, its preservation under continuous images
(`realSequentiallyCompact_continuous_image`), and Dedekind `realSup`/
`realInf` with their extremal-bound characterizations, this three-part gap
(bounded, sup/inf achieved, applied to continuous images) looked like the
most concretely pre-scoped target of the three, not a from-scratch item —
worth attempting ahead of (a)/(b) precisely because its remaining shape was
already spelled out rather than needing a scoping pass of its own.

**Method**: read `RealSequentiallyCompact`, `RealClosedInterval`, `realSup`/
`realInf` and their extremal lemmas, `RealSequence`/`RealSubsequence`, and
the existing Cauchy-boundedness lemmas (`realSequenceCauchy_bounded_above`/
`_below`) in `Reals.lean`, plus the already-proven Archimedean embedding
`real_archimedean_nat_upper`. Worked in four steps. (1) *Boundedness*: proved
a nonempty sequentially compact set can't be unbounded above, by
contradiction — an unbounded set lets a witness sequence be built (via
`Classical.choice`) exceeding the natural-number embedding at every index;
compactness extracts a convergent (hence, via `realSequenceConverges_cauchy`
+ `realSequenceCauchy_bounded_above`, Cauchy-bounded) subsequence, but the
subsequence's own indices grow past any bound by
`realSubsequence_index_large`, contradiction via `real_archimedean_nat_upper`
applied to that bound. (2) *Sup achieved*: built a genuine null sequence of
rational radii `1/(n+1)` from scratch in `Rationals.lean` (field-inverse
existence was already available, but no reciprocal-of-`n+1` sequence nor its
eventual-smallness fact existed yet), used it to construct an explicit
sequence of set members approximating the supremum to within `1/(n+1)`
(`realSupApproxSequence`, via a new general lemma `realSup_approx`
generalizing the approximation argument already inlined in cycle-prior
`realSequenceNondecreasing_converges` from a sequence-tail family to an
arbitrary bounded family), fed it to compactness, and used the ALREADY
EXISTING `realSequence_limit_unique` to identify compactness's extracted
limit with the supremum (since the approximating sequence already converges
to the supremum, any subsequence of it does too, and a sequence has at most
one limit). (3) *Below/inf*: derived boundedness-below and inf-achieved from
(1)/(2) by transport through negation, first checking negation is
`RealContinuousOn` everywhere (trivial from the ALREADY EXISTING
`realFunctionLimitAt_neg` applied to `realFunctionLimitAt_id`, no new
ε–δ argument needed) so `realSequentiallyCompact_continuous_image` transports
compactness of a set to compactness of its negation. (4) *Applied to closed
intervals*: composed all of this with the ALREADY EXISTING
`realClosedInterval_sequentiallyCompact` and
`realSequentiallyCompact_continuous_image` to get that
`RealImage function (RealClosedInterval lower upper)` is itself nonempty,
compact, bounded, and sup/inf-achieving, then unpacked that into an explicit
maximizer/minimizer in the domain.

**Result**: **confirmed, fully, sorry-free.** Six new theorems in
`Reals.lean`: `realSequentiallyCompact_bounded_above`,
`realSequentiallyCompact_bounded_below`, `realSequentiallyCompact_sup_mem`,
`realSequentiallyCompact_inf_mem`, and the two headline results,
`realContinuousOn_closedInterval_attains_max` /
`realContinuousOn_closedInterval_attains_min` — genuine extreme value
theorems: a function continuous on a closed interval `[lower, upper]`
(`lower ≤ upper`) attains a maximizer and a minimizer point IN the interval.
Supporting additions: `realSup_approx` (general supremum-approximation, not
tied to a sequence tail), `realSupApproxSequence` and its three corollaries,
`realContinuousAt_neg`/`realContinuousOn_neg` (immediate from
already-checked pieces), `realSequentiallyCompact_negFamily`. In
`Rationals.lean`: `rationalNatSucc_pos`/`_ne_zero`, `rationalNatSuccInv` (a
`Classical.choice`-selected field inverse of `n+1`) with its positivity and
its eventual-smallness fact `rationalNatSuccInv_eventually_le`, proved from
`rational_archimedean_steps` plus the ALREADY EXISTING strict-multiplication
monotonicity lemmas (`rationalLT_mul_left_of_positive`/
`_right_of_positive`) — no new rational-order infrastructure had to be
invented beyond the reciprocal itself. One implementation snag worth
recording: `omega` repeatedly failed ("No usable constraints found", or
silently treating `Int.ofNat x` and the `↑x` cast notation as different
atoms) on goals mixing bare `Int.ofNat` applications, even though an
apparently-identical existing proof elsewhere in `Rationals.lean` uses the
same-looking pattern successfully — isolating the exact working precedent in
a scratch file showed it does NOT actually reproduce standalone either,
meaning omega's success there depends on incidental surrounding context, not
the pattern itself. Replaced every such step with the explicit core lemmas
`Int.ofNat_eq_zero` / `Int.ofNat_le` / `Int.ofNat_inj`, which is more robust
and arguably clearer than relying on omega's cast-recognition heuristics
here. `lake build`: all 21 modules, including the `incidence-theory` example
binary. `#print axioms` on all six new theorems: `propext`, `Classical.choice`,
`Quot.sound` only — the same profile the rest of the project already
carries, no new axiom. Repo-wide unproved-declaration grep (`verify.sh`):
none.

**Synthesis**: this closes the ADR roadmap's item 3 (極値定理) outright,
not just its "residual" framing — the ADR's own 2026-07-13 追補 had already
narrowed the gap to exactly this: generalized boundedness/achievement for
compact sets, applied to continuous images of intervals. The route taken
underscores a pattern already visible in cycle 41's synthesis: a
disproportionate share of the actual proof weight was ALREADY sitting in
the codebase (`realClosedInterval_sequentiallyCompact`,
`realSequentiallyCompact_continuous_image`, `realSup`/`realInf` and their
extremal characterizations, `realSequence_limit_unique`,
`realFunctionLimitAt_neg`, the full rational order/field API) — the new
content this cycle contributes is comparatively small and structural: one
genuinely new mathematical ingredient (a null sequence of rationals and the
supremum-approximation lemma built from it, needed because no prior cycle
had needed to approximate an ARBITRARY bounded set's supremum by a
sequence, only a specific sequence's own tail supremum) plus the bookkeeping
to route it through compactness via limit uniqueness, plus a symmetry
argument (negation) to avoid writing the infimum case from scratch. The
omega snag is a useful methodological note for future cycles working with
`Int.ofNat`: don't assume a passing pattern generalizes without testing it
in isolation, since omega's atom-matching for `Nat`→`Int` casts is more
brittle than it looks from a single working example.

**Next hypothesis (cycle 43, not yet attempted)**: three live threads.
(a) Roadmap item 4 (Rolle's theorem / mean value theorem) is now directly
reachable: the ADR names the route as extreme value theorem → derivative
vanishes at an interior extremum → auxiliary-function construction for the
general MVT, and this cycle just supplied the extreme value theorem itself,
plus the codebase already has the full first-order differential calculus
(sum/product/quotient/chain rules, polynomial derivatives) that an
auxiliary-function argument would need. This looks like the most
directly-continuable thread of the three. (b) Cycle 41's option (c) (= cycle
37's option (b)): the internal-logic distributivity direction relating
`incidenceProd`/`incidenceSum`, still unattempted, still flagged as needing
its own scope-down step. (c) Cycle 41's option (b): whether a less naive
`shapeIncidence.glue` could make `simplexToShape` a genuine
glue-homomorphism, or whether that is structurally impossible for the same
reason cycle 38 found `glue` doesn't respect `≈` in general — still
unattempted, still flagged as a short, focused check.

## Cycle 43

**Hypothesis**: pursue thread (a) from cycle 42's queue — roadmap item 4
(Rolle's theorem / mean value theorem) — since the extreme value theorem
(cycle 42) plus the already-complete first-order differential calculus
(sum/product/quotient/chain rules, polynomial derivatives, all in
`Reals.lean`) make Fermat's interior extremum theorem (derivative vanishes at
an interior local/global extremum) directly reachable, and Rolle's theorem
follows from Fermat's theorem plus EVT by a case split on whether the
extremum sits at an interior point or an endpoint. Threads (b) and (c) from
cycle 42's queue remain untouched but were deprioritized again in favor of
this more concretely pre-scoped target, matching the tractability-over-size
selection rationale cycle 42 itself used.

**Method**: read the existing derivative API (`RealHasDerivativeAt`,
`realDifferenceQuotient`, `realHasDerivativeAt_neg`, `realDerivativeAt_spec`)
and the `RealClosedInterval`/`RealContinuousOn`/`RealDifferentiableOn`
definitions, then worked in three layers. (1) A handful of order/sign lemmas
this project had never needed before: limits, sequences and the field
structure only ever needed non-strict monotonicity of `+`, never the sign of
a *difference* or a *product* in the generality Fermat's proof needs.
Built from scratch: `realLT_of_not_le` (double-negation elimination for the
strict order, since this project has no `LinearOrder` typeclass machinery to
draw it from), `realAdd_neg_pos_of_lt`/`realAdd_lt_zero_of_lt_neg`
(difference-of-a-strict-inequality is signed), `realLT_neg_of_pos`/
`realLT_pos_of_neg` (negation flips strict sign), `realMul_pos_of_pos_pos`
(built from the already-existing `realMul_of_nonnegative` bundle plus
`nonnegativeRealMul_ne_zero`), and the two cancellation lemmas
`realLE_zero_of_mul_le_zero_of_pos`/`realLE_zero_of_zero_le_mul_of_pos` (a
positive factor's sign transfers to the other factor of a signed product) —
these compose into `realMul_differenceQuotient`'s algebraic identity
(`increment * quotient = f(point+increment) - f(point)`, already proved
in a prior cycle) to read off the *sign* of the quotient from the sign of the
increment and the sign of the numerator. (2) A reusable epsilon-delta helper,
`real_exists_rational_step_le_lt`: given a positive rational radius (from an
epsilon-delta closeness witness) and a positive real gap (the distance from a
point to a domain boundary), produces a single positive rational simultaneously
`≤` the radius and (as a real) `<` the gap — needed because Fermat's proof
must pick an increment small enough for the derivative's epsilon-delta bound
AND small enough to keep `point + increment` inside `[lower, upper]`, two
independent smallness constraints from different sources (one rational, one
real). (3) The two headline theorems:
`realHasDerivativeAt_zero_of_interior_max` (both directions worked
separately — right-hand/positive increments force the derivative `≤ 0` via
`isMax`, left-hand/negative increments force it `≥ 0` — then
`realLE_antisymm`), and `realHasDerivativeAt_zero_of_interior_min`, obtained
for free from the max case by negation (`realHasDerivativeAt_neg` plus
`realNeg_order_reverse` transports a minimizer of `function` to a maximizer of
`-function`), avoiding writing the whole two-sided argument a second time.
(4) Pushed forward into Rolle's theorem itself (`real_rolle`): EVT (cycle 42)
locates a maximizer and minimizer over `[lower, upper]`; case-split on whether
either differs from the shared endpoint value `function lower = function
upper`. If the maximizer's value differs, it cannot coincide with either
endpoint (their values are fixed at the shared endpoint value), so it is
interior and Fermat's max theorem finishes it directly; symmetrically for the
minimizer via Fermat's min theorem. If *neither* differs — both extrema equal
the shared endpoint value — then since every domain value is sandwiched
between the min and max, the function is provably constant on the whole
interval, and a genuine interior point is manufactured from scratch (the
same `real_exists_rational_step_le_lt`-style positive-rational-below-a-gap
construction, applied to the gap `upper - lower`), which is then trivially
its own local extremum (constancy) so Fermat's max theorem applies there too.

**Result**: **confirmed, fully, sorry-free.** Eleven new declarations in
`Reals.lean`, all downstream of no new axioms: the eight sign/order lemmas
above, `real_exists_rational_step_le_lt`, and the three headline theorems
`realHasDerivativeAt_zero_of_interior_max`, `realHasDerivativeAt_zero_of_interior_min`,
and `real_rolle` (statement: `lower < upper`, `function` continuous on
`[lower, upper]`, differentiable on all of `[lower, upper]` — see honest
scoping note below — and `function lower = function upper`, conclude
`∃ point, lower < point ∧ point < upper ∧ RealHasDerivativeAt function 0
point`). `#print axioms` on all three headline theorems:
`propext, Classical.choice, Quot.sound` — exactly this project's standing
axiom profile, nothing new. `lake build`: all 21 modules including the
example binary. `verify.sh` (clean `lake clean && lake build`, example run,
repo-wide unproved-declaration grep): passes end to end.

Two implementation snags worth recording alongside cycle 42's `omega` note.
First, `by_contra` is not an available tactic in this project's bare Lean 4
setup (no Mathlib/Std import) — every prior cycle's contradiction proofs use
`apply Classical.byContradiction; intro h` instead, which this cycle had
initially missed (four uses of `by_contra` all failed with "unknown tactic");
fixed by switching to the project's own established idiom. Second, a `rw`
subtlety: when a hypothesis's *both* sides match the same rewrite pattern but
with different metavariable instantiations (e.g. `realAdd (-c) (realAdd c a)
= realAdd (-c) (realAdd c b)`, rewriting `← realAdd_assoc` on both occurrences
to cancel `c`), a single pass through the rewrite list only fires on the
first-matched instantiation, silently leaving the other side untouched —
`realAdd_lt_monotone_left`'s proof needed the same three-lemma rewrite chain
listed *twice* to simplify both sides of the derived equation. Neither snag
is deep, but both cost real debugging cycles against the actual `lake build`
output rather than being visible from reading the source alone — reinforcing
cycle 42's point that this project's proof-writing loop leans on the checker,
not on offline verification, for exactly this class of mistake.

One honest scoping note: `real_rolle`'s hypothesis is `RealDifferentiableOn
function (RealClosedInterval lower upper)` — differentiable on the *closed*
interval including endpoints, not just the open interval as in the textbook
statement. This project has no `RealOpenInterval` domain predicate yet, and
introducing one was judged out of scope for this cycle; the stronger
hypothesis is harmless for every use this project is likely to make of
Rolle's theorem (all differentiability hypotheses elsewhere in `Reals.lean`
are already stated over closed-interval domains) but is worth flagging
explicitly rather than silently presenting it as the textbook-general form.
Per the task's own framing and this project's culture (cycles 38-40), the
general Mean Value Theorem (subtracting the secant line) was deliberately
left for a future cycle rather than attempted in the same sitting — Rolle's
theorem alone was already a substantial, self-contained result built on top
of Fermat's theorem, and stopping here keeps the sign-lemma infrastructure
above legible instead of burying it under a second large construction.

**Synthesis**: this closes the ADR roadmap's item 4 (Rolle's theorem) outright
via item 3's route exactly as cycle 42's queue predicted, and does so by
building a small, previously-nonexistent layer of real-number sign algebra
(lemmas 1-8 above) that no earlier cycle needed because nothing before this
one required reading a *sign* off an epsilon-delta bound rather than just a
*bound*. The pattern from cycles 41/42 continues: the majority of the proof
weight was already sitting in the codebase (EVT itself, the full derivative
calculus, `realMul_differenceQuotient`'s algebraic identity connecting
multiplication and the difference quotient, `realHasDerivativeAt_neg` for the
free min-from-max transport) — this cycle's genuine new content is the sign
algebra plus the epsilon-delta bookkeeping to route an increment through two
independent smallness constraints at once, plus recognizing that the
degenerate "both extrema at the endpoints" case reduces to manufacturing an
arbitrary interior point and reusing Fermat's theorem rather than needing any
separate "constant function has zero derivative" lemma.

**Next hypothesis (cycle 44, not yet attempted)**: three live threads.
(a) **[recommended]** The general Mean Value Theorem is now very directly
reachable from `real_rolle`: define the secant-subtracted auxiliary function
`h(x) = f(x) - f(a) - ((f(b) - f(a)) / (b - a)) * (x - a)` (an affine
function subtracted from `f`, using the already-proved
`realHasDerivativeAt_affine`/`realHasDerivativeAt_sub` to get `h`'s
derivative for free as `f'(x) - (f(b)-f(a))/(b-a)`), check `h(a) = h(b) = 0`
by construction, apply `real_rolle` to `h` to get an interior point where
`h`'s derivative is zero, and unpack that into `f'(point) = (f(b)-f(a))/(b-a)`
— this is exactly the auxiliary-function step the ADR's original roadmap
note (2607100600, addendum) named as the last piece after Fermat's theorem,
now that both Fermat's theorem and Rolle's theorem are in hand. (b) Cycle 41's
option (c) (= cycle 37's option (b)): the internal-logic distributivity
direction relating `incidenceProd`/`incidenceSum`, still unattempted across
three cycles now, still flagged as needing its own scope-down step. (c) Cycle
41's option (b): whether a less naive `shapeIncidence.glue` could make
`simplexToShape` a genuine glue-homomorphism, or whether that is structurally
impossible — still unattempted, still a short focused check.

## Cycle 44

**Hypothesis**: pursue thread (a) from cycle 43's queue — the general Mean
Value Theorem — since `real_rolle` (cycle 43) plus the existing derivative
arithmetic (`realHasDerivativeAt_affine`, `realHasDerivativeAt_sub`) make the
standard auxiliary-function proof directly reachable, exactly as cycle 43's
own note described: build `h(x) = f(x) - secant(x)` where `secant` is the
line through `(lower, f lower)` and `(upper, f upper)`, check `h` vanishes at
both endpoints, apply `real_rolle` to `h`, then unwind the resulting `h' = 0`
back into `f'(point) = slope`. Threads (b) and (c) from cycle 43's queue
remain untouched, deprioritized again for the same tractability reason cycles
42/43 already used.

**Method**: grepped `Reals.lean` for the real-number division/inverse
infrastructure the task flagged as a likely gap, and found it already fully
built (unlike cycle 42's rational reciprocal, which had to be constructed
from scratch): `realInv value nonzero` (signed multiplicative inverse),
`realInvOrZero` (its junk-value-at-zero totalization), `realDiv := fun n d =>
realMul n (realInvOrZero d)`, and the cancellation facts `realMul_inv`/
`realInv_mul` (`value * inv value = 1` both orders) plus `realMul_cancel_left`/
`realMul_cancel_right`/`real_eq_of_add_neg_eq_zero` (the last one is exactly
the "difference is zero implies equal" step the final unwinding needs). With
that confirmed, worked in four layers. (1) Nonzero-ness of the endpoint gap:
`lower < upper` (`ordered`) already gives `realAdd_neg_pos_of_lt ordered :
0 < upper - lower`, whose `.2` component (`0 ≠ gap`) flips via `fun h => ...
h.symm` into `gap ≠ 0` — no new order lemma needed, cycle 43's sign-algebra
layer already covers this. (2) Built `slope := deltaF * (inv gap gapNonzero)`
where `deltaF := f(upper) - f(lower)`, then `offset := f(lower) - slope *
lower` and `secant x := slope * x + offset` (exactly `realHasDerivativeAt_affine`'s
shape) and `h x := f(x) - secant(x)` (exactly `realHasDerivativeAt_sub`'s
shape) as a chain of local `let`s. (3) Proved `secant lower = f(lower)` and
`secant upper = f(upper)` by pure algebraic rewriting (`realAdd_assoc`/
`realAdd_comm`/`realAdd_neg`/`realMul_add`/`realMul_neg_right`), the second
one routing through a `slopeDistribute`/`slopeGapEq` pair showing `slope *
gap = deltaF` (via `realMul_assoc` + `realInv_mul` + `realMul_one_right` —
exactly the reciprocal-cancellation identity flagged as the risk in the
task), from which both endpoints of `h` vanish
(`hLowerZero`/`hUpperZero`/`hEndpoints`). (4) Built `RealDifferentiableOn h`
directly from `RealDifferentiableOn function` via `realHasDerivativeAt_sub`
+ `realHasDerivativeAt_affine` at each domain point, then noticed
`RealContinuousOn h` doesn't need any separate argument at all —
`realDifferentiableOn_continuousOn` (cycle 42, used internally by
`real_polynomial_continuousOn`) turns the differentiability just built
directly into continuity, so `real_mvt`'s hypotheses only need to state
`RealDifferentiableOn function domain`, not a redundant extra
`RealContinuousOn function domain` the way `real_rolle` itself still
requires (a small, deliberate divergence from cycle 43's own signature shape,
recorded rather than silently done). Applied `real_rolle` to `h` to get an
interior point and `RealHasDerivativeAt h 0 point`; independently rebuilt
`RealHasDerivativeAt h (d - slope) point` from `function`'s own derivative `d`
at that point (via the same `realHasDerivativeAt_sub`/`_affine` combination);
`realHasDerivativeAt_unique` on these two facts about the same function `h`
at the same point gives `d - slope = 0`, and `real_eq_of_add_neg_eq_zero`
turns that into `d = slope` — the entire MVT conclusion, with no new
uniqueness or cancellation lemma needed beyond what cycles 1-43 already
built.

**Result**: **confirmed, fully, sorry-free.** One new theorem in
`Reals.lean`, `real_mvt`: for `lower < upper` and `function` differentiable
on `[lower, upper]`, `∃ point, lower < point ∧ point < upper ∧
RealHasDerivativeAt function (realDiv (f upper - f lower) (upper - lower))
point`. No new supporting lemmas were required at all — every piece
(`realInv`/`realDiv` algebra, `realHasDerivativeAt_affine`/`_sub`,
`realHasDerivativeAt_unique`, `real_eq_of_add_neg_eq_zero`,
`realDifferentiableOn_continuousOn`, `real_rolle` itself) already existed;
this cycle's contribution is purely the auxiliary-function construction and
its bookkeeping. `#print axioms real_mvt` (checked via a scratch file fed to
`lake env lean`, then deleted): `propext, Classical.choice, Quot.sound` —
this project's standing profile, no new axiom. `lake build`: all 21 modules
including the example binary. `verify.sh` (clean `lake clean && lake build`,
example run, repo-wide unproved-declaration grep): passes end to end.

One implementation snag worth recording, a new variety distinct from cycles
42/43's `omega`/`by_contra` notes: a bridging lemma stated using a local
`let`-abbreviation (`gap := upper - lower`) as an argument, e.g. `realDiv
deltaF gap = slope`, is defeq-equal but NOT syntactically identical to the
theorem's actual stated goal (which spells out `realAdd upper (realNeg
lower)` literally, since `gap` doesn't exist at the theorem-statement scope).
`rw` matches by a syntactic/keyed search (`kabstract`), not a blanket
`isDefEq` check, so a bridging `have` needs to be stated using the SAME
literal expression the target goal uses, not the shorthand `let`-name, or the
final `rw` risks silently failing to find its target. Separately (and
non-obviously): even a plain `show` to restate the goal via defeq does NOT
bridge `realInvOrZero gap` and `realInv gap gapNonzero` — although
`realInvOrZero` is *defined* via a `dite` that looks like it should unfold,
its branch is selected through a `Classical.propDecidable`-style instance
obtained via `classical`, which is opaque to defeq/`show`; only the actual
proved lemma `realInvOrZero_of_ne` (a `dif_pos` rewrite) can perform that
step. Both of these were caught by the type-checker rejecting the naive
first draft, not by reading the source — reinforcing cycle 43's point that
this project's loop leans on `lake build`'s actual feedback for exactly this
class of near-miss.

**Synthesis**: this closes the ADR roadmap's item 4 (Rolle/MVT pairing)
completely — Rolle's theorem (cycle 43) plus the general MVT (this cycle)
together were the item's full stated scope, and unlike cycles 41-43's
pattern of needing one genuinely new supporting layer (sign algebra, a
rational reciprocal sequence, a quotient bijection), this cycle needed *zero*
new supporting infrastructure: the entire proof is a composition of already-
proved pieces, the purest instance yet of this project's recurring
observation that most of the real work predates the cycle that "closes" a
roadmap item. The one substantive design choice made rather than found —
dropping `real_rolle`'s redundant explicit `RealContinuousOn` hypothesis in
favor of deriving it from `RealDifferentiableOn` via
`realDifferentiableOn_continuousOn` — is a small but genuine improvement on
the precedent, and is recorded explicitly rather than silently presented as
if `real_rolle`'s own (also legitimate) choice were the only option. The
`let`-vs-literal `rw` snag is worth flagging forward: any future cycle
building an auxiliary object via local `let`s and then trying to relate it
back to a theorem statement's own literal terms via `rw` (as opposed to
`show`, which handles zeta/beta/delta but not classical-instance-gated
`dite`s) should state the bridging lemma in the statement's own literal
vocabulary from the start, not the cycle's internal shorthand.

**Next hypothesis (cycle 45, not yet attempted)**: with roadmap item 4 (Rolle
+ MVT) now fully closed, two live threads remain, both queued since cycle 41
without a single attempt across cycles 42-44 (three cycles running past due
to the recurring tractability-over-size argument favoring the real-analysis
thread; that thread is now exhausted for the roadmap's item 4, so one of
these should be picked next barring a newer, more concretely-scoped item
surfacing from the ADR). (a) Cycle 41's option (c) (= cycle 37's option (b)):
the internal-logic distributivity direction relating
`incidenceProd`/`incidenceSum` — the largest, most open item, still needing
its own scope-down step (e.g. checking whether a natural map between the two
carrier types even exists and is well-typed before attempting any
bisimulation result) before it can be attempted directly. (b) Cycle 41's
option (b): whether a less naive `shapeIncidence.glue` could make
`simplexToShape` a genuine glue-homomorphism, or whether that is structurally
impossible for the same reason cycle 38 found `glue` doesn't respect `≈` in
general — still flagged as a short, focused check, and given (a)'s repeated
deferral for being under-scoped, (b) may be the more immediately tractable
pick for cycle 45 specifically because it needs no scoping pass of its own.

## Cycle 45

**Hypothesis**: pursue thread (b) from cycle 44's queue (= cycle 41's option
(b)) — is there ANY well-typed `glue : SimplexShape → SimplexShape → Option
SimplexShape`, not just cycle 41's particular unit-absorbing-pattern copy,
for which `simplexToShape` is a genuine glue-homomorphism out of
`simplexIncidence` — or is that structurally impossible? Picked over thread
(a) (the `incidenceProd`/`incidenceSum` distributivity map) exactly per the
task's own tractability ranking: (b) needs no scoping pass, cycle 41 already
identified the precise open question.

**Method**: grepped `Simplex.lean` and `Quotient.lean` for
`simplexIncidence`/`shapeIncidence`/`simplexToShape`/`SimplexShape` before
assuming anything. Found `simplexToShape_not_glue_hom` (cycle 41) refutes
only the ONE `shapeIncidence.glue` this project built. But the same file
also already contains, a few lines below it,
`simplexClassification_glue_not_invariant : ¬
simplexBisimulationQuotientClassification.GlueInvariant` — a theorem this
cycle's task briefing did not know about, added not in cycle 41's own commit
(`ac06e86`) but in a batch of ~24 "feat(inc)" commits on 2026-07-11
(`c6c7610`..`1c07128`, all landed as follow-on generalization of the
bisimulation-quotient-classification framework, per the merge commit
"integrate cycle41 proof development") — chronologically after cycle 41,
chronologically before cycles 42-44 (dated 2026-07-13), but never given its
own `## Cycle N` entry in this log. The same batch produced
`docs/adr/2607100600-...md`'s "2026-07-11 追補" section, which already states
in prose: "canonical glue についても...分類 target 上の二変数演算へ descent
できることが必要十分であり...simplex 分類ではこの不変性が実際に偽であり、
`shapeIncidence.glue` が source glue の descent ではない理由を一般条件の失敗
として示した." In other words: **this cycle's exact question was already
answered by existing code and existing ADR prose**, just never connected
into an explicit closing theorem stated in the open question's own terms,
and never logged as a numbered cycle here — a genuine desync between this
file's cataloging and the actual `main` state (plausibly from a separate,
undocumented pass of the recurring automated loop touching this repo).
Rather than treat this as nothing left to do, checked whether the general
machinery actually closes the question as strongly as cycle 41's queue
asked (ALL possible glues, not just `GlueInvariant`'s abstract statement):
read `BisimulationQuotientClassification.glueRealization_iff_invariant`
(`GlueRealization ↔ GlueInvariant`, where `GlueRealization` is literally `∃
glue : Q → Q → Option Q, ∀ x y, glue (classify x) (classify y) =
mappedSourceGlue x y` — an existential over every possible glue function)
and confirmed `simplexBisimulationQuotientClassification.classify` is
definitionally `simplexToShape`, so `GlueRealization` for this
classification unfolds exactly to the open question's own existential.

**Result**: **confirmed, sorry-free, on the first attempt.** Two new
theorems in `Quotient.lean`. (1) `simplexShape_glue_not_realizable : ¬
simplexBisimulationQuotientClassification.GlueRealization`, a one-line proof
combining `glueRealization_iff_invariant` with the pre-existing
`simplexClassification_glue_not_invariant`. (2)
`simplexToShape_no_glue_homomorphism_exists : ¬ ∃ glue' : SimplexShape →
SimplexShape → Option SimplexShape, ∀ x y : SimplexId, glue' (simplexToShape
x) (simplexToShape y) = (simplexIncidence.glue x y).map simplexToShape` —
the classification-free restatement, typechecking directly against (1) by
definitional unfolding, in exactly the vocabulary cycle 41's queue posed the
question in. This is a strictly stronger closure than cycle 41's own
`simplexToShape_not_glue_hom`: that theorem ruled out one specific candidate
glue; this cycle's theorems rule out EVERY possible well-typed
`SimplexShape`-valued glue at once, confirming cycle 38's general finding
("glue does not respect `≈`") really does apply here with no escape hatch —
a **clean NEGATIVE closure**, not a positive construction, as the task
briefing said was equally legitimate. `lake build IncidenceTheory.Quotient`:
succeeds cleanly (22/22 jobs project-wide). `#print axioms` on both new
theorems (checked via a scratch file fed to `lake env lean`, then deleted):
`propext, Classical.choice, Quot.sound` — this project's standing profile,
no new axiom. Full `./verify.sh` (clean `lake clean && lake build`, example
binary run, repo-wide unproved-declaration grep): passes end to end.

**Synthesis**: this closes the multi-cycle-deferred thread (b), queued since
cycle 41 and re-queued untouched through cycles 42, 43, 44. Unlike cycle
41's own synthesis (where the hard mathematical work predated the cycle by
dozens of cycles but the *connection* was still this project's own
recognition), this cycle is even more purely archaeological: not only had
the underlying fact (`GlueInvariant` false for the simplex classification)
already been proved, it had already been correctly summarized in ADR prose,
roughly 40 hours before this cycle ran — the only genuinely missing piece
was the explicit theorem statement closing the loop in the open question's
own vocabulary, plus recognizing that this log's own "not yet attempted"
bookkeeping had drifted from the actual `main` state. Worth naming plainly
as a process finding, not just a mathematical one: a research log that
tracks work by hand-numbered cycles can silently desync from a codebase
that also receives commits outside that numbering (here, an apparent
separate documentation/generalization pass on 2026-07-11) — the fix isn't
to stop trusting the log, but to grep the actual source before trusting a
"not yet attempted" label, exactly as this cycle's method did and as cycle
41's own method already modeled. Mathematically, the result reconfirms
cycle 38's structural finding (`glue` does not respect `≈` in general) in
its sharpest form yet for this instance: it is not merely that
`simplexIncidence`'s three-shape grading fails to transport this ONE
`glue`, it is that NO `SimplexShape`-valued glue of any definition could
ever be induced by `simplexToShape` from `simplexIncidence.glue` — the
obstruction is `GlueInvariant`'s failure itself (two `≈`-related vertices,
`v0 ≈ v1`, glued against the same `face` give literally different results:
`simplexIncidence.glue v0 face = some face` vs. `simplexIncidence.glue v1
face = some v1`, which map to different shapes), not any deficiency of a
particular candidate construction.

**Next hypothesis (cycle 46, not yet attempted)**: with both of cycle 41's
queued options now resolved (option (b): closed negatively this cycle;
option (a) — cycle 37's option (b), the `incidenceProd`/`incidenceSum`
internal-logic distributivity direction — still fully open), cycle 46 should
pursue that remaining thread, scoped exactly as cycle 41/42's queues already
narrowed it: **do not** attempt a full distributivity/bisimulation theorem
in one shot. First move only: grep for existing concrete
`incidenceProd`/`incidenceSum` instances that have BOTH been constructed on
the same underlying carrier (e.g. via `natIncidence`, `NatBoolProductIncidence`
in `Quotient.lean`, or `Product.lean`/`Sum.lean` directly) and check whether
a natural, well-typed map between `incidenceProd A B`'s carrier and
`incidenceSum A B`'s carrier exists at all — before attempting any
bisimulation or homomorphism claim about that map. Separately, before
picking a thread, cycle 46 should also do a quick repo-wide sweep for other
"feat(inc)"-style commits landed outside the numbered-cycle sequence (as
this cycle found for 2026-07-11) that might have already resolved other
items this log still lists as open, to avoid re-deriving already-settled
ground a second time.

## Cycle 46

**Audit note (cycle 45's requested sweep, done first, kept brief per
scope)**: reran `git log --oneline` over the whole repo (786 commits vs.
45 logged cycles -- expected, since most cycles bundle many small commits,
not a 1:1 ratio) and specifically re-examined the exact `c6c7610..1c07128`
range cycle 45 flagged as an undocumented 2026-07-11 batch.
`git log --oneline c6c7610..1c07128 | wc -l` gives **282**, not the "~24"
cycle 45 estimated -- the gap is materially larger than previously
reported, and covers far more than the `GlueInvariant`/`GlueRealization`
material cycle 45 examined: propositional-logic quotient laws, "coherent
incidence layer" constructions, dependent-product/family semantics,
canonical boundary/glue/guard descent conditions, and more, per this
batch's own commit subjects. However, this is confirmed to be the SAME
single gap window cycle 45 already identified (bounded by the
`0a17bb4`/`91746c3` "merge: integrate cycle41 proof development" /
"merge: complete Inc proof development" commits just before it, and by
the docs/README-split and "make ternary resonance the central
interaction" commits that lead into the dated 2026-07-13 real-analysis
thread just after it), not a second, independent desync elsewhere in
history -- no other `git log` merge-style or batch-shaped commit cluster
outside this window was found lacking a `## Cycle N` entry. Also
confirmed the batch is not entirely unlogged in this repo: the ADR's
`## 2026-07-11 追補（現行 main）` section (`docs/adr/2607100600-...md`,
line 62) already prose-summarizes most of this batch's content in detail
(including, notably, "汎用 `incidenceProd` と `incidenceSum` はこの
パッケージを合成し、自然数 Incidence の積・和で検証済み" and a description
of the `natIncidence × trivialIncidence Bool` coherence example -- direct
leads for this cycle's own main thread, below). Net correction for cycle
47+: treat cycle 45's "~24 commits" figure as superseded by this cycle's
282, and treat the 2026-07-11 gap as "ADR-documented but cycle-unlogged"
rather than fully undocumented -- but do not assume every claim in that
ADR prose has a correspondingly named theorem; check the source, as both
this cycle and cycle 45 did.

**Hypothesis**: cycle 45's own next-hypothesis (= cycle 41/42's queue
item (a) = cycle 39's item (c) = cycle 37's queue item (b), the
longest-lived open thread in this log, named the "internal-logic
distributivity direction relating `incidenceProd`/`incidenceSum`" and
repeatedly flagged since cycle 37 as needing a scope-down FIRST step
before any bisimulation/homomorphism/distributivity attempt: does a
natural, well-typed map exist between `incidenceProd inc1 inc2`'s
carrier and `incidenceSum inc1 inc2`'s carrier, for the SAME `inc1`,
`inc2`? Per the task's own tractability ranking and cycle 45's explicit
recommendation, this cycle attempts ONLY that scope-down question --
no bisimulation, homomorphism, or distributivity claim about any map
found.

**Method**: read the actual definitions before guessing at shapes.
`Product.lean`'s `incidenceProd {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq
I1] [DecidableEq I2] (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2
T2) : Incidence (I1 × I2) (R1 ⊕ R2) (T1 × T2)` -- carrier `I1 × I2`.
`Sum.lean`'s `incidenceSum` with the same type parameters -- carrier
`I1 ⊕ I2`. Grepped `incidenceProd`/`incidenceSum` for every concrete
existing application (not just the constructors) across the tree: the
only concretely-applied instances are `incidenceProd natIncidence
natIncidence` (`CrossInstance.lean`'s dependent identity family),
`incidenceProd natIncidence finiteIncidence`, and `NatBoolProductIncidence
:= incidenceProd natIncidence trivialIncidence` (`Quotient.lean`, carrier
`Nat × Bool`) -- **`incidenceSum` has ZERO concretely-applied instances
anywhere outside `Sum.lean` itself** (only its own header example,
`incidenceSum finiteIncidence finiteIncidence`, and a code comment citing
`incidenceSum natIncidence natIncidence`). Also re-read cycles 37/39/41's
exact framing (as instructed) and found the thread has actually drifted
across cycles: cycle 37's ORIGINAL queue item (b) was the
*distributive-law* shape, `incidenceProd inc1 (incidenceSum inc2 inc3)`
vs. `incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)`
(three incidence structures) -- but cycle 41/42/45's restatements
simplified it to "a map between the two carrier types" without
respecifying which pairing, and the task briefing for this cycle (and
cycle 45's own next-hypothesis) explicitly resolved that ambiguity to the
same-`(A,B)` two-argument comparison. Treated that resolution as
authoritative for what to test this cycle, but recorded the drift plainly
(see Synthesis) rather than silently picking one reading.

**Result**: **answered, sorry-free, first attempt -- a clean three-part
negative for the same-`(A,B)` framing.** Added to `Sum.lean` (after
adding `import IncidenceTheory.Product`, since `Sum.lean` did not
previously import it): (1) `prodToSumCarrier`/`prodToSumCarrier'` --
`I1 × I2 → I1 ⊕ I2` exists unconditionally for any `I1`, `I2` (project-
then-inject on either side), but `prodToSumCarrier_ne_prodToSumCarrier'`
proves the two are genuinely distinct at a concrete input
(`prodToSumCarrier (5,true) = Sum.inl 5 ≠ Sum.inr true =
prodToSumCarrier' (5,true)`, via `Sum.noConfusion`) -- so a map exists in
this direction but is not canonical. (2)
`sum_to_prod_carrier_map_impossible_in_general : ¬ Nonempty ((Empty ⊕
Unit) → (Empty × Unit))` -- proves the OTHER direction fails outright for
at least one instantiation: applying any such hypothetical function to
`Sum.inr ()` would have to produce an `Empty` value, impossible
(`(f (Sum.inr ())).1.elim`), regardless of classical choice (choice picks
among existing witnesses, it cannot conjure a term of an uninhabited
type). (3) `sumToProdNatCarrier`/`sumToProdNatCarrier_basepoint_dependent`
-- restricting to this project's actual nonempty concrete carrier
(`Nat`), an ad hoc `Nat ⊕ Nat → Nat × Nat` IS constructible via a chosen
basepoint, but is genuinely basepoint-dependent, not canonical:
`sumToProdNatCarrier 0 (Sum.inl 7) ≠ sumToProdNatCarrier 1 (Sum.inl 7)`
(two equally reasonable defaults disagree on the same input).
`lake build`: 62/62 jobs. `#print axioms` on all three new theorems
(scratch file, deleted after use, exactly cycle 45's method):
`prodToSumCarrier_ne_prodToSumCarrier'` and
`sum_to_prod_carrier_map_impossible_in_general` need NO axioms at all;
`sumToProdNatCarrier_basepoint_dependent` needs only `propext` -- within
or below this project's standing profile. Full `./verify.sh` (clean
`lake clean && lake build`, example binary, repo-wide unproved-
declaration grep): passes end to end.

**Synthesis**: this closes the scope-down question exactly as posed --
NO natural/canonical map exists between `incidenceProd A B`'s carrier and
`incidenceSum A B`'s carrier, for the same `A`, `B`, in either direction,
that could serve as a non-arbitrary basis for a subsequent bisimulation/
homomorphism/distributivity claim comparing the two constructors
directly. Unlike cycles 38-40's negative results (which closed off entire
construction *families*), this is a narrower, purely carrier-level
finding -- but it is exactly the "first move" cycle 41/42/45 asked for,
and it is genuinely negative rather than an artificially forced
construction, consistent with this project's standing view (cycles
38-40) that a clean negative is fully legitimate cycle output. The more
important finding for cycle 47, though, is the drift surfaced during
Method: cycle 37's ORIGINAL motivating question was never this same-
`(A,B)` comparison -- it was the distributive-law shape over THREE
incidence structures, `incidenceProd inc1 (incidenceSum inc2 inc3)` vs.
`incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)`, whose
underlying carrier types, `I1 × (I2 ⊕ I3)` vs. `(I1 × I2) ⊕ (I1 × I3)`,
DO have a standard, canonical, natural bijection in `Type`/`Set`
(distributivity of product over coproduct -- `Type` is a distributive
category, the standard map being `fun (a, x) => x.elim (fun b => .inl
(a,b)) (fun c => .inr (a,c))` and its evident inverse). That comparison
was deliberately NOT tested this cycle (out of scope, per the task's
explicit same-`(A,B)` framing and cycle 45's own phrasing), but it is a
substantially more promising candidate for an actual POSITIVE carrier-
level map than the question this cycle answered, and this cycle's
negative result should not be read as closing the distributivity thread
overall -- only this one (mis-simplified, across cycles 41-45) framing
of its first step. Separately, the near-total asymmetry noted during
Method -- `incidenceProd` has three concrete applied instances in this
codebase, `incidenceSum` has zero outside its own definition file -- is
itself worth flagging: any future cycle attempting the THREE-argument
distributive law will need to either build a first concrete
`incidenceSum`-based instance to test against, or work at the fully
generic level from the start.

**Next hypothesis (cycle 47, not yet attempted)**: re-scope the
distributivity thread to the shape cycle 37 actually asked for, now that
this cycle has separated it from the carrier-map dead end: does the
canonical `I1 × (I2 ⊕ I3) ≃ (I1 × I2) ⊕ (I1 × I3)` bijection (construct
it explicitly first, as this cycle's `prodToSumCarrier`-style small
combinators were built, before anything else) extend to a genuine
`Incidence`-structure-level statement relating `incidenceProd inc1
(incidenceSum inc2 inc3)` and `incidenceSum (incidenceProd inc1 inc2)
(incidenceProd inc1 inc3)` -- e.g. is the bijection a `glue`-homomorphism,
a `boundary`-homomorphism, both, or neither? Scope down again if this
still proves too large: first just check whether the two `Incidence`
structures' `boundary`/`glue`/`guards` fields even have the same SHAPE
under the bijection (a definitional/computational check, no homomorphism
claim yet) before attempting any theorem. As a fallback if that also
proves too large for one cycle, cycle 39's still-open item (b) remains
queued: does any existing instance in this project have a `≈`-quotient
in the genuinely interesting middle ground beyond `simplexIncidence`
(cycle 41's only example so far)?

## Cycle 47

**Hypothesis**: cycle 46's own next-hypothesis -- re-scope the
distributivity thread to the shape cycle 37 ORIGINALLY asked for (the
three-argument distributive law, `incidenceProd inc1 (incidenceSum inc2
inc3)` vs. `incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1
inc3)`), not the same-`(A,B)` two-argument carrier-map comparison cycle
46 closed negatively (a drift cycle 46 itself identified and explicitly
deferred to this cycle). Per the task's explicit scope-down instruction:
construct the canonical `I1 × (I2 ⊕ I3) ≃ (I1 × I2) ⊕ (I1 × I3)`
bijection first (a standard, always-true `Type`-level fact, unlike
cycle 46's carrier-map question which had no general fact in either
direction), then check DEFINITIONALLY -- not via a full homomorphism or
bisimulation proof -- whether it aligns the `boundary`/`glue`/`guards`
structure of the two composite `Incidence`s, for concrete already-
existing instances.

**Method**: read `Product.lean`'s `incidenceProd`/`prodBoundary`/
`prodGlue`/`prodGuards` and `Sum.lean`'s `incidenceSum`/`sumBoundary`/
`sumGlue` definitions directly (not from memory), plus the base
`Incidence` structure in `Axioms.lean` (fields: `boundary`, `typeFunc`,
`glue`, `resonance`, `unit`, `guards`, plus the proof obligations --
confirms the task's own "boundary/glue/guards" naming is correct, all
three exist as literal field/definition names, not renamed). Per cycle
46's own asymmetry finding (`incidenceProd` has three concretely-applied
instances in this codebase -- `natIncidence × natIncidence`,
`natIncidence × finiteIncidence`, `natIncidence × trivialIncidence Bool`
-- `incidenceSum` has ZERO outside its own file's header example,
`incidenceSum finiteIncidence finiteIncidence`), picked `inc1 :=
natIncidence`, `inc2 := inc3 := finiteIncidence` -- reusing both existing
applied instances rather than inventing new ones, exactly as the task
required. Built the bijection as explicit forward/backward functions
plus round-trip lemmas (`prodSumDistribForward`/`prodSumDistribBackward`/
`prodSumDistrib_left_inverse`/`_right_inverse`) rather than a bundled
`Equiv`-style abstraction, since a grep confirms this project has no
existing `Equiv`-like convention to reuse (matching cycle 41's own
injective/surjective-pair style). For the definitional alignment check,
worked out the general algebra by hand first (which unit-absorption
conditions fire on which side, for arbitrary `inc1`/`inc2`/`inc3`) before
picking concrete numbers, then verified every prediction with `#eval` in
a scratch file (deleted after use) before transcribing anything as a
`theorem`, exactly cycle 41's discipline for concrete counterexamples.

**Result**: **a genuine three-part mixed finding -- `boundary` aligns
(generic positive), `glue` does not (concrete negative counterexample),
`guards` has an unwitnessed-but-real structural asymmetry.** Added to
`Sum.lean` (12 new declarations, no new imports needed -- already imports
`Product.lean` since cycle 46).

(1) **`boundary` aligns, generically** (not merely for the two chosen
instances): `prodBoundary_sum_{left,right}_length` and
`sumBoundary_prod_{left,right}_length` show both composite structures'
boundary at corresponding elements have equal LENGTH, for ANY `inc1`,
`inc2`, `inc3` -- a direct consequence of `prodBoundary`'s `++`/
`List.map` shape and `sumBoundary`'s `List.map` shape composing the same
way regardless of which constructor is outermost, needing nothing about
the factors' internals beyond `List.length_map`/`List.length_append`.
Combined into the headline `incidenceProd_incidenceSum_boundary_length_
aligned_{left,right}`, stated directly against the two composite
`Incidence`s' own `.boundary` field and the bijection itself. (A full
entry-level correspondence, not just length, also holds by direct
unfolding -- worked out by hand during Method -- but is not stated as a
separate theorem, per the task's explicit "definitionally first, no
homomorphism proof yet" scope; the length results are the concrete,
decidable witness asked for.)

(2) **`glue` does NOT align -- a concrete, decidable counterexample**,
`incidenceProd_incidenceSum_distrib_glue_misaligned`. Mechanism:
`incidenceSum`'s unit-absorbing `glue` (cycle 33) tests its OWN
designated unit exactly. On the LHS (`incidenceProd inc1 (incidenceSum
inc2 inc3)`), the INNER sum's absorption test inspects only the `I2 ⊕
I3` component, entirely independent of `i1` -- so it can fire (returning
the other side's element unchanged) even when `i1 ≠ inc1.unit`, provided
`inc1.glue i1 j1` still succeeds. On the RHS (`incidenceSum (incidenceProd
inc1 inc2) (incidenceProd inc1 inc3)`), the OUTER sum's absorption test
requires the FULL pair `(i1, i2)` to equal `(inc1.unit, inc2.unit)` --
strictly narrower. Verified concretely with `inc1 := natIncidence` (whose
`glue` is total addition, never `none`) and `inc2 := inc3 :=
finiteIncidence`: at `(i1, x) := (2, Sum.inl FiniteIncidence.leaf)`
(`leaf = finiteIncidence.unit`, so the inner absorption fires) and
`(j1, y) := (3, Sum.inr FiniteIncidence.root)` (opposite side, `2` and
`3` both `≠ 0 = natIncidence.unit`) -- the LHS glues to `some (Sum.inr
(5, FiniteIncidence.root))` (`5 = 2+3`) mapped through the bijection,
while the RHS glue is `none` (opposite tags after the bijection, neither
element is the RHS's exact designated unit `Sum.inl (0, leaf)`). `#eval`
confirmed both values first; `decide` closes the formal inequality.

(3) **`guards`: real structural asymmetry, but not concretely
witnessed** -- every applied concrete instance in this project
(`natIncidence`, `finiteIncidence`, `trivialIncidence`) uses
`Guards.permissive` (always `true`), so no EXISTING instance can
concretely witness a disagreement without inventing a new non-permissive
one, which the task's tractability scope disallows (and which this
cycle declined to do, to avoid fabricating a misleading "concrete"
result). The asymmetry is nonetheless real and proved generically:
`incidenceSum_prod_guards_always_permissive` shows the RHS's top-level
`guards.allow` is unconditionally `true` for every pair (cycle 33's
`incidenceSum` always sets `guards := Guards.permissive`, discarding
whatever guards its two arguments actually carry), while
`incidenceProd_sum_guards_depends_on_inc1_only` shows the LHS's top-level
`guards.allow (i1,x) (j1,y)` reduces to exactly `inc1.guards.allow i1
j1` (cycle 31's `incidenceProd` genuinely conjoins both factors' guards,
and the inner sum's own permissive guards cancel out of the `&&`). These
are not the same function in general and would diverge the moment any
future instance in this project used a non-trivial `Guards` -- flagged
as an open item for whichever future cycle builds one, not resolved here.

`lake build`: 62/62 jobs. `#print axioms` (scratch file, deleted after
use): `prodSumDistrib_left_inverse`/`_right_inverse` need NO axioms at
all (pure `rfl`/`cases`); all four boundary-length lemmas, both combined
boundary theorems, and both guards theorems need only `propext`/
`Quot.sound`; `incidenceProd_incidenceSum_distrib_glue_misaligned` needs
`propext`/`Classical.choice`/`Quot.sound` -- verified this is
`natIncidence`'s OWN standing baseline, not something this cycle's proof
introduces (`theorem t : natIncidence.glue 2 3 = some 5 := rfl` alone,
with none of this cycle's new code, already carries `Classical.choice`,
consistent with cycle 37's note that `natIncidence`-involving facts have
carried it since cycle 4). Full `./verify.sh` (clean `lake clean && lake
build`, example binary run, repo-wide unproved-declaration grep): passes
end to end.

**Synthesis**: this closes the multi-cycle-deferred original cycle-37
distributivity thread's first concrete test with a mixed, honest result
-- not a clean win, but a genuinely informative one, entirely consistent
with this project's standing view (cycles 38-40, 45, 46) that a
part-positive-part-negative finding is fully legitimate cycle output.
The headline lesson: `incidenceProd`/`incidenceSum`'s DATA-level carrier
distributes exactly as `Type`/`Set` predicts (part 1), but the
ALGEBRAIC structure built on top does not distribute along with it,
because `incidenceSum`'s unit-absorption and `guards`-discarding are
BOTH defined relative to the sum's own immediate two arguments' units,
not aware of any "outer" structure a `glue`/`guards` might be nested
inside via `incidenceProd`. This is the same family of finding as cycle
41's `simplexToShape_not_glue_hom` and cycle 45's strengthening of it
(`glue` does not commute with a carrier-level map/quotient in general) --
but this is the first time the SPECIFIC obstruction has been pinned to
`incidenceSum`'s absorption mechanism interacting with an ENCLOSING
`incidenceProd`, rather than a quotient/classification map. It also
means: any future attempt at a genuine distributivity THEOREM (glue-
homomorphism or bisimulation-respecting) for this specific pairing is
now known to be FALSE as stated for the naive bijection -- a full
positive result would need either a weaker notion of "aligns" (e.g. up
to `≈`, not on-the-nose equality) or a restricted hypothesis ruling out
the exact absorption-under-non-unit-`i1` scenario found here. Cycle 46's
"boundary/guards would need checking too" caution (implicit in its own
scope-down) turns out to have been well-founded: the three fields
genuinely behave differently under this comparison, and lumping them
together would have obscured a real, task-relevant distinction.

**Next hypothesis (cycle 48, not yet attempted)**: three live threads,
in decreasing order of promise. (a) Given this cycle's concrete `glue`
counterexample turns on ordinary (on-the-nose) equality after the
bijection, does the WEAKER statement -- `glue`-results agree up to `≈`
(`approxBisim`) rather than exact equality -- hold instead? This is the
natural next scope-down the task itself anticipated ("only pursue a
general theorem in a LATER cycle if this cycle's concrete check
succeeds" implicitly allows a WEAKENED theorem attempt when the strict
one fails, per this project's standing pattern of retrying a failed
exact-equality claim as an up-to-`≈` claim, e.g. cycles 31→32's
one-directional-then-iff arc). Concretely: is `incidenceProd
natIncidence (incidenceSum finiteIncidence finiteIncidence)`'s glue
result on the counterexample pair `≈`-related (in the SUM's own
approxBisim, after transport) to whatever the RHS's `none` would need to
"mean" -- likely requires first deciding what `≈`-relatedness even means
when one side's glue is `none` and the other is `some x` (does `none`
have a canonical `≈`-partner, or does the comparison only make sense
when BOTH sides succeed?). (b) Build a first concrete instance actually
USING `incidenceSum` with a non-permissive `guards`, to convert this
cycle's part-(3) structural-but-unwitnessed guards asymmetry into an
actual concrete counterexample (or discover it does NOT concretely
manifest even then, which would itself be a finding worth having). (c)
cycle 39's still-open item, still queued three cycles running: does any
existing instance have a `≈`-quotient in the middle ground beyond
`simplexIncidence` (cycle 41's only example)?

## Cycle 48

**Hypothesis**: cycle 47's own next-hypothesis (a), the highest-priority
of its three queued threads: cycle 47's concrete `glue` misalignment
counterexample (`incidenceProd natIncidence (incidenceSum finiteIncidence
finiteIncidence)` vs `incidenceSum (incidenceProd natIncidence
finiteIncidence) (incidenceProd natIncidence finiteIncidence)`, at
`i1=2, j1=3, x = Sum.inl FiniteIncidence.leaf, y = Sum.inr
FiniteIncidence.root`) turned on ON-THE-NOSE equality after the
bijection. Does the WEAKER claim — the two sides' `glue` results agree
up to `≈` (`approxBisim`) rather than exact equality — rescue it, or
hold more generally? Per the task's own explicit caution: since one side
of the counterexample is `none` (glue fails) and the other is `some x`
(glue succeeds), first determine whether "`≈`-related" even has a
non-strained meaning when comparing a defined outcome to an undefined
one, before attempting to force a proof through.

**Method**: first grepped for this project's actual bisimulation
machinery rather than assuming — `approxBisim` (`IncidenceTheory.lean`,
not a per-cycle file) is `∃ rel, IsBisimulation inc rel ∧ rel i j`, a
relation on the CARRIER `I` of a single `Incidence I R T`, never on
`Option I` and never comparing two DIFFERENT `Incidence` structures'
carriers directly. Also found this project already has a native notion
of "gluing respects a relation" — `GlueRespects` (`IncidenceTheory.lean`,
used since cycle-1-era `trivial_glue_respects_approxBisim` and
`BisimulationNormalizationSpec`) — and its type signature is itself
telling: `∀ {i₁ i₂ j₁ j₂ k₁ k₂}, rel i₁ i₂ → rel j₁ j₂ → inc.glue i₁ j₁ =
some k₁ → inc.glue i₂ j₂ = some k₂ → rel k₁ k₂` — quantified ONLY over
the case both sides' `glue` produce a `some`; it says nothing whatsoever
about a `none` outcome. This is direct textual evidence (not an
invented convention) that this codebase's own established vocabulary for
"glue agrees up to a relation" doesn't extend to comparing `none` against
`some x` at all.

Given that, split the investigation in two: (1) formalize the canonical
lift of `≈` to `Option` (mirroring how `=` itself lifts — `none` only
relates to `none`, `some a` only to `some b` when `a ≈ b`, and a
`none`/`some` pair is never related, by construction) and check whether
cycle 47's specific counterexample is rescued under it. (2) Since (1)
was expected to resolve negatively (a scoping finding, per the task's own
suggestion), also checked the task's suggested fallback: does a DIFFERENT
concrete case exist where BOTH sides succeed but disagree? Rather than
hunt instance-by-instance, worked out the general algebra by hand first
(as cycle 47 did): for ANY `inc1`/`inc2`/`inc3`, using only `inc1`'s
`unit_left`/`unit_right` structural obligations, whenever the RHS
(`incidenceSum (incidenceProd inc1 inc2) (incidenceProd inc1 inc3)`)'s
`glue` succeeds at all, does the LHS's `glue` (transported through
`prodSumDistribForward`) necessarily equal it? Worked through all four
tag combinations of the `I2 ⊕ I3` argument (inl/inl, inr/inr, inl/inr,
inr/inl) by hand, then transcribed each as a Lean theorem and let the
compiler catch errors in the by-hand reasoning — it did catch one: an
initial assumption that the two same-side cases (inl/inl and inr/inr)
would need symmetric case-splitting on `inc2.unit`/`inc3.unit` was wrong.
`incidenceSum`'s designated absorbing unit is ALWAYS `Sum.inl inc1.unit`
(the FIRST factor's unit only) — so a same-side pair on the SECOND
factor can never hit an absorption branch at all (wrong tag,
unconditionally), while a same-side pair on the FIRST factor genuinely
can. Two small reusable facts about `incidenceSum` fell out of pinning
this down precisely (`incidenceSum_glue_same_left`/`_same_right`/
`_cross_left`/`_cross_right`, added to `Sum.lean`) and made the
main proof mechanical once available.

**Result**: **a genuine two-part finding, one negative (closing cycle
47's exact question) and one positive (stronger than what was asked)**.
Added to `IncidenceTheory/Sum.lean` (15 new declarations: 4 general
`incidenceSum`-glue characterization lemmas, 4 per-tag-combo agreement
lemmas, the main theorem, two corollaries, an `Option`-lift definition
plus its one structural lemma, and 3 declarations transcribing cycle
47's concrete counterexample values/closing fact).

(1) **The specific counterexample is NOT rescued by weakening to `≈`** —
confirmed by `not_optionApproxBisim_some_none`, a fully general,
instance-independent fact: under `OptionApproxBisim` (the canonical
`Option`-lift of any relation on a carrier, defined precisely to mirror
how `=` lifts to `Option`), `some a` is NEVER related to `none`, for any
underlying relation and any `a` — not a deep fact, but the direct,
honest consequence of `≈` being defined only on actual carrier elements
plus this project's own `GlueRespects` already implicitly agreeing (its
hypotheses require both sides to be `some`). Instantiated concretely at
cycle 47's own values via
`incidenceProd_incidenceSum_distrib_glue_misaligned_not_bisim_rescued`
(using two newly-named facts, `..._lhs_some` = `some (Sum.inr (5,
FiniteIncidence.root))` and `..._rhs_none` = `none`, both `decide`-closed
— cycle 47 itself only proved the two sides `≠`, without naming either
value). This is the scoping resolution the task anticipated as a live
possibility, reached honestly rather than by straining a comparison that
was never well-formed to begin with: the counterexample is about a
`glue` DEFINED-vs-UNDEFINED mismatch, and `≈`/`GlueRespects` were never
built to adjudicate that.

(2) **But the investigation into WHY produced a stronger, fully general,
POSITIVE theorem that subsumes the task's suggested fallback question.**
`incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some`: for ANY
`inc1`/`inc2`/`inc3` (no instance hypothesis at all, unlike cycle 47's
necessarily-concrete counterexample) — whenever the RHS's `glue`
succeeds (`some w`), the LHS's `glue` ALSO succeeds and, transported
through the bijection, equals `w` EXACTLY, not merely up to `≈`. Proved
by cases on the four `I2 ⊕ I3`-tag combinations, using only `inc1`'s
`unit_left`/`unit_right` laws (no `natIncidence`/`finiteIncidence`
specifics). Direct corollary,
`incidenceProd_incidenceSum_distrib_glue_no_disagreement_when_both_some`:
there is consequently NO possible case, for ANY instances whatsoever,
where both sides succeed but disagree — the task's own suggested
fallback ("look for a both-succeed-but-differ case") is answered
definitively in the negative, by proof rather than by exhausting this
project's handful of concrete instances. Restated in the `≈` vocabulary
the task asked about via `..._approxBisim_of_both_some` (trivial once
the exact-equality corollary is in hand, via `approxBisim_refl` — literal
equality is always `≈`-related).

Net picture, combining (1) and (2): the misalignment cycle 47 found is
now known to be *exactly and only* a "RHS fails, LHS may still succeed"
phenomenon — never the reverse (not proved this cycle, but not needed:
cycle 47's own asymmetric absorption-mechanism description already makes
the RHS-fails/LHS-succeeds direction the only possible one, and this
cycle's part (2) rules out the remaining "both succeed, disagree" case
entirely) — and no `≈`-level rescue is available for that failing case,
for a reason unrelated to bisimulation strength: it is a category
mismatch (comparing a defined outcome to an undefined one), not a
weakness of `≈` itself.

`lake build`: 62/62 jobs (`lake clean && lake build`, matching
`verify.sh`). `#print axioms` (scratch file, deleted after use, cycles
45-47's method): the four general `incidenceSum`-glue lemmas, the main
theorem, and both corollaries need only `propext`/`Quot.sound`;
`not_optionApproxBisim_some_none` needs only `propext`; the three
declarations instantiating cycle 47's concrete
`natIncidence`/`finiteIncidence` values need
`propext`/`Classical.choice`/`Quot.sound` — the same standing baseline
cycles 37/47 already documented for any `natIncidence`-involving fact
(present since cycle 4), not something newly introduced. Full
`./verify.sh` (clean `lake clean && lake build`, example binary run,
repo-wide unproved-declaration grep): passes end to end.

**Synthesis**: this closes cycle 47's queued hypothesis (a) with an
honest, two-sided answer rather than forcing either half — the negative
half is a genuine scoping finding (the same family as cycles 38-40's
honest negatives), and the positive half is a materially STRONGER
general theorem than the bisimulation-weakening the task asked for
(exact agreement, not merely `≈`-agreement, whenever the comparison is
even meaningful). The recurring lesson from this project's "generic
constructor" thread (cycles 31-48) sharpens further: `incidenceSum`'s
unit-absorption is not merely "aware only of its own two immediate
arguments" (cycle 47's framing) but specifically "aware only of its
FIRST argument's unit" — an asymmetry between the sum's two factors that
this cycle's initial by-hand derivation got wrong on the first attempt
(assuming naive left/right symmetry) before the Lean compiler's case
analysis forced the correction, a small but genuine instance of this
project's standing discipline (cycle 37 onward) of not trusting
structural arguments by inspection alone, formal or otherwise.

**Next hypothesis (cycle 49, not yet attempted)**: two live threads
remain from cycle 47's queue (its (b) and (c)), plus one this cycle
surfaces. (a, new) This cycle proved the RHS-fails/LHS-succeeds
direction is a real asymmetry but did not prove it EXHAUSTIVELY
characterizes every misalignment case in general (only ruled out
same-value disagreement when both succeed) — is there a clean, fully
general characterization of exactly when
`incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some`'s converse
fails (LHS succeeds, RHS is `none`), stated as an iff rather than
cycle 47's single concrete witness? The by-hand cross-case analysis in
this cycle's Method section already sketches the shape (LHS's inner-sum
absorption test ignores whichever `I1` component isn't tagged into it,
RHS's outer-sum absorption test demands the full pair) — formalizing it
as a clean `↔` is the natural completion. (b) cycle 47's still-queued
item: build a first concrete instance actually USING `incidenceSum` with
a non-permissive `guards`, to convert cycle 47's part-(3)
structural-but-unwitnessed `guards` asymmetry into an actual concrete
counterexample (or discover it does NOT concretely manifest even then).
(c) cycle 39's still-open item, now queued four cycles running: does any
existing instance have a `≈`-quotient in the middle ground beyond
`simplexIncidence` (cycle 41's only example)?

## Cycle 49

**Audit note (task-mandated cycle 39/41 sanity check, done first): item (c)
of cycle 48's own queue is STALE, not open -- cycle 41 already answered it,
and cycle 45 already said so.** Before picking a target, re-read cycle 41 in
full (as instructed): cycle 41's own Method/Result sections directly answer
cycle 39's exact question ("does any EXISTING instance have a `≈`-quotient in
the genuinely interesting middle ground -- more than one class, fewer than
all") in the AFFIRMATIVE -- `simplexIncidence`'s `≈`-partition is exactly 3
classes out of 7 elements (`simplexToShape_iff_approxBisim`, established
across cycles 12/18/21/22/23 and recognized by cycle 41 as answering this
question), and cycle 41 goes on to build `shapeIncidence` on that quotient.
Cycle 41's own next-hypothesis section explicitly narrows the remaining
open thread down to option (c) alone (the internal-logic distributivity
direction) -- it does NOT re-queue the middle-ground question, because it
had just been answered. Cycle 45's own synthesis independently confirms this
in so many words: *"with both of cycle 41's queued options now resolved..."*
Despite this, cycle 47's queue re-introduced "cycle 39's still-open item" as
a fallback option (c), and cycle 48 repeated it again, verbatim, labeling it
"queued four cycles running" -- propagating a label that was already false
at the moment cycle 47 wrote it (cycle 41 had closed it six cycles earlier,
cycle 45 had said so explicitly three cycles before that). This is the SAME
failure mode cycles 45/46 each caught and corrected once (a stale "still
open" queue label surviving multiple cycles without anyone checking the
actual resolved state) -- except this time it slipped through TWO
re-statements (cycles 47 and 48) before this cycle's mandated audit caught
it a third time. **Correction for cycle 50+: item (c) is CLOSED (by cycle 41,
confirmed by cycle 45) and should not be re-queued again.** If a future
cycle wants a genuinely NEW instance of a "middle ground" `≈`-quotient
(distinct from `simplexIncidence`, the only witness so far), that would be a
different, fresh question -- not a re-run of cycle 39's original one, which
already has its answer. With (c) correctly retired, this cycle picks between
cycle 48's remaining live threads (a) and (b), per the task's own tractability
ranking: (a), the converse-iff characterization, since cycle 48's own Method
section already sketches its shape from by-hand case analysis.

**Hypothesis**: cycle 48's queued thread (a) -- cycle 48 proved
`incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some` (RHS `some` ->
LHS `some`, exactly equal, for ANY `inc1`/`inc2`/`inc3`) but left its
CONVERSE uncharacterized beyond a single concrete witness (cycle 47's
`i1:=2,j1:=3` counterexample): does LHS succeed while RHS is `none` in
general, and if so, exactly when -- stated as a clean `iff`, not merely
another one-off instance?

**Method**: grepped `Sum.lean`'s exact current statements before writing
anything (per the task's explicit instruction), confirming
`incidenceSum_glue_same_left`/`_same_right`/`_cross_left`/`_cross_right` and
`incidenceProd_incidenceSum_distrib_glue_agrees_of_rhs_some` cycle 48 added,
plus `Product.lean`'s `prodGlue`/`incidenceProd.unit := (inc1.unit,
inc2.unit)`. Two observations before writing any new theorem. (1) Cycle 48's
`incidenceSum_glue_same_left`/`_same_right` are stated only under a
"componentwise glue succeeds" hypothesis, but re-reading their own proofs
shows the SAME argument works with no hypothesis at all: if the
componentwise glue is `none`, neither argument can secretly be the
absorbing unit either (the unit laws would force a `some` result if it
were), so the sum's same-side glue is an UNCONDITIONAL equality to the
componentwise glue, not merely an implication from success. Strengthened
both to full equalities first (`incidenceSum_glue_same_left_eq`/
`_same_right_eq`) since the whole converse question turns on exactly this
kind of "what happens when it's `none`" information cycle 48's
success-only lemmas didn't carry. (2) With these equalities in hand, the
distributive law's two SAME-side tag combinations (`inl_inl`/`inr_inr`)
turn out to depend on IDENTICAL success conditions on both sides (both
reduce to "`inc1.glue i1 j1` succeeds AND the matching `I2`/`I3`-component
glue succeeds") -- so same-side pairs can NEVER misalign at all, a fact
this project's log had not stated before (cycle 48 proved only the "RHS
some -> LHS some" direction for these, not the full "never differ" fact).
Worked the two CROSS-side combinations (`inl_inr`/`inr_inl`, the only
places misalignment is even possible) out by hand using
`incidenceSum_glue_cross_left`/`_cross_right`, deriving closed
`if`-`then`-`else` forms for both the LHS and RHS glue directly, then
reading the misalignment condition off by comparing the two closed forms
-- exactly the shape cycle 48's own Method section sketched by hand
without formalizing.

**Result**: **a complete, fully general characterization, confirmed
sorry-free on the first attempt after one proof-term fix caught by the
compiler (not by hand).** Added to `Sum.lean` (18 new declarations): two
strengthened same-side equalities, two same-side "never misalign" full
equalities (`incidenceProd_incidenceSum_distrib_glue_inl_inl_eq`/
`_inr_inr_eq`), four cross-side closed-form lemmas (LHS/RHS for each of
`inl_inr`/`inr_inl`), two cross-side headline `iff`s, and one master `iff`
combining all four tag combinations.

The two cross-side `iff`s are the headline result. For `inl_inr`
(`i1`/`i2` on the left, `j1`/`j3` on the right):
```
incidenceProd_incidenceSum_distrib_glue_lhs_some_rhs_none_iff_inl_inr :
  ((∃ v, LHS.glue (i1, Sum.inl i2) (j1, Sum.inr j3) = some v) ∧
   RHS.glue (Sum.inl (i1,i2)) (Sum.inr (j1,j3)) = none)
  ↔ i2 = inc2.unit ∧ i1 ≠ inc1.unit ∧ ∃ k1, inc1.glue i1 j1 = some k1
```
i.e. LHS succeeds while RHS fails EXACTLY when the inner sum's own
absorbing unit condition (`i2 = inc2.unit`) fires (letting the inner
sum's `glue` succeed regardless of `i1`) while `i1` itself is NOT the
outer unit (so the outer sum's stricter "whole-pair-is-the-unit" test
fails) and `inc1.glue i1 j1` still happens to succeed anyway (as it always
does for `natIncidence`, confirming cycle 47's witness was the generic
case, not a special accident). `inr_inl` is the exact mirror, with the
roles of `i1`/`j1` swapped (the unit-test lands on whichever argument is
tagged `Sum.inr`'s PARTNER, i.e. `j1` here, since `incidenceSum`'s cross
test always inspects the `Sum.inl`-tagged side). The master theorem
(`incidenceProd_incidenceSum_distrib_glue_lhs_some_rhs_none_iff`) combines
all four combinations into one `iff` over arbitrary `x y : I2 ⊕ I3`,
using the same-side equalities to rule those two combinations out
entirely (their contribution to the disjunction is provably `False`,
closed via `Sum.noConfusion`-style contradictions). One hand-derivation
error the compiler caught (matching cycle 48's own experience): an initial
attempt used `rcases hk1 : inc1.glue i1 j1 with _ | k1` while the ambient
goal itself still mentioned `inc1.glue i1 j1`, which silently rewrote the
goal's own occurrence during the case split, breaking the intended
`exact ⟨k1, hk1⟩` (Lean's error: expected `some k1 = some k1`, not
`inc1.glue i1 j1 = some k1`) -- fixed by using `rfl` instead of `hk1` for
that already-substituted goal, a small but genuine instance of this
project's standing discipline of trusting the compiler's exact error over
a plausible-looking hand derivation.

`lake build`: 62/62 jobs (`lake clean && lake build`, matching `verify.sh`).
`#print axioms` (scratch file, deleted after use, cycles 45-48's method):
every one of the 18 new declarations needs only `propext`/`Quot.sound` --
strictly SIMPLER than cycle 48's own concrete-instance theorems (which
needed `Classical.choice` for the `natIncidence`-involving facts), because
this cycle's entire result is stated and proved fully generically, with no
concrete instance touched at all. Full `./verify.sh` (clean `lake clean &&
lake build`, example binary run, repo-wide unproved-declaration grep):
passes end to end.

**Synthesis**: this closes cycle 48's queued hypothesis (a) completely,
upgrading cycle 47's single concrete witness and cycle 48's one-directional
general theorem into a full converse characterization -- exactly the
"clean iff" the task asked for, not merely another instance-level check.
The net picture across cycles 47-49 is now complete: the distributive law's
`glue` misalignment is possible in EXACTLY two of the four tag
combinations (cross-side only; same-side NEVER misaligns, a new fact this
cycle establishes), and within those two, misalignment happens EXACTLY when
one factor's inner-sum absorption condition fires on a value that is not
literally the outer sum's own absorbing unit but still yields a successful
`inc1.glue` result -- the precise mechanism cycle 47 described in prose
("inner-sum absorption ignoring `i1` vs. outer-sum absorption requiring the
full pair") is now a formal `iff`, not just a mechanism description backed
by one witness. Separately, and just as important as the mathematical
result: this cycle's mandated audit step found a THIRD instance of this
project's recurring "stale queue label" failure mode (after cycles 45/46),
this time surviving through two cycles (47, 48) rather than being caught
immediately -- worth naming plainly as a process pattern, not a one-off:
this log's per-cycle "next hypothesis" sections get COPIED forward more
often than they get RE-VERIFIED against the file being copied from, and a
brief, cheap "does this really do what it says" check on the OLDEST
still-open-looking item (feasible in a few minutes, as the task's own
framing anticipated) is worth doing before every cycle, not only when
explicitly prompted to, since the cost of catching it is small and the cost
of silently repeating dead work (as nearly happened again here) is not.

**Next hypothesis (cycle 50, not yet attempted)**: with cycle 48's option
(a) now fully closed (converse iff) and option (c) retired as stale
(closed by cycle 41), the one remaining live thread from cycles 47/48's
queues is option (b): build a first concrete `Incidence` instance actually
USING `incidenceSum` with a non-permissive `guards`, to test whether the
`guards`-forcing-permissive structural asymmetry cycle 47 found
(`incidenceSum_prod_guards_always_permissive` vs.
`incidenceProd_sum_guards_depends_on_inc1_only`) concretely manifests as an
observable disagreement, or whether it turns out -- like this cycle's
same-side glue finding -- to be provably impossible for a reason not yet
identified. Scope narrowly per the task's own fallback framing: one small
non-permissive-`guards` instance built via `incidenceSum`, checked
computationally (`decide`/`rfl`), not a general theorem attempt in the same
cycle. Separately, if a future cycle wants a genuinely NEW `≈`-quotient
"middle ground" instance (distinct from `simplexIncidence`), that is a
fresh question this cycle's audit note explicitly distinguishes from the
now-closed cycle 39/41 question -- worth its own hypothesis statement, not
a queue-label carryover, if picked up later.

## Cycle 50

**Hypothesis**: cycle 49's queued option (b) -- build one concrete
`Incidence` instance where `incidenceSum inc1 inc2` is applied with an
`inc1` (or `inc2`) that has non-permissive `guards`, to test whether cycle
47's structural asymmetry (`incidenceSum_prod_guards_always_permissive`:
`incidenceSum`'s top-level guards are unconditionally `Guards.permissive`,
vs. `incidenceProd_sum_guards_depends_on_inc1_only`: `incidenceProd`'s
genuinely conjoin) actually manifests as an OBSERVABLE difference from a
natural "expected" componentwise guards definition, or is provably
impossible to observe (as cycle 49's own same-side-glue finding turned out
to be for a different question).

**Method**: grepped every `guards :=` field across `IncidenceTheory/*.lean`
before writing anything (per the task's instruction) -- confirmed cycle 47's
own claim that every concrete `Incidence` instance in this codebase
(`natIncidence`, `finiteIncidence`, `trivialIncidence`, `cycleIncidence`,
`pairIncidence`, `simplexIncidence`, `pathIncidence`, `treeIncidence`, the
various number-system instances, etc.) uses `Guards.permissive`, with no
exception; `BisimulationQuotientClassification.canonicalGuards`
(`Quotient.lean`) is a generic quotient-guards *constructor*, not a
counterexample itself, since every concrete classification it has been
applied to descends from a permissive source instance, so its own `allow`
still reduces to "always true" extensionally. So no existing instance could
serve as the required witness -- one had to be built. Modeled it directly
on `finiteIncidence` (`GraphModel.lean`): defined `Guards.never`, the exact
polar opposite of `Guards.permissive` (`allow := fun _ _ => false`), and
`finiteIncidenceNeverGuards`, `finiteIncidence` with ONLY the `guards` field
swapped. Checked first, before writing the proof, that this typechecks at
all: `finiteIncidence`'s (and `natIncidence`'s and `trivialIncidence`'s)
`type_preserve` proof already discards its `guards.allow` hypothesis
entirely (`by intro i j k hallow hglue; rfl`), because every hand-built
instance's `typeFunc` targets the single constant `GraphType.unit` -- so the
guard hypothesis was always vacuous for `type_preserve`'s purposes, and
swapping to any other `Guards` value (permissive or not) reuses the exact
same proof term unchanged. `finiteIncidence` was picked over the others
only because its two-element carrier makes the eventual `decide` cheapest.

Then built the comparison baseline: `sumGuardsExpected`, a hypothetical
componentwise guards function for a sum, following the exact same
case-structure `sumGlue`/`sumBoundary`/`sumResonance` (cycle 33) already
use -- unit-absorbing (allow unconditionally when either side is literally
the designated unit, mirroring `unit_left`/`unit_right`), same-side
delegates to the matching factor's own `guards.allow`, cross-side (the case
with no natural componentwise value -- the same tension `sumGlue` resolves
by returning `none`) disallowed. This is a standalone `def`, not a change to
`incidenceSum` itself, which stays exactly as cycle 33 left it (redesigning
`incidenceSum`'s actual `guards` field, or building a full alternate
guards-respecting sum constructor, is explicitly out of this cycle's scope,
per the task).

**Result**: **a clear, decide-confirmed positive divergence, sorry-free on
the first build.** Added to `Sum.lean` (6 new declarations: `Guards.never`,
`finiteIncidenceNeverGuards`, `sumGuardsExpected`, one general theorem, two
concrete `decide`-checked corollaries).

(1) The originally-scoped question: `incidenceSum_guards_diverges_of_inc1_disallows`
proves generically that whenever `inc1.guards` disallows some non-unit pair
`(i1, j1)`, `incidenceSum inc1 inc2`'s actual guards (`true`, unconditionally)
diverge from `sumGuardsExpected` (`false`, since it delegates to `inc1`'s
own disallowing guards) on the corresponding same-side pair
`(Sum.inl i1, Sum.inl j1)`. `incidenceSum_guards_diverges_concrete`
instantiates this at `finiteIncidenceNeverGuards`/`finiteIncidence`,
`i1 = j1 = .root` (both `≠ .leaf = unit`), `decide`-confirmed: actual `=
true`, expected `= false`. So YES -- cycle 47's structural asymmetry does
concretely manifest the moment any instance uses non-permissive guards, not
merely in the abstract.

(2) A sharper finding the task's framing did not anticipate:
`incidenceSum_guards_diverges_cross_side_permissive_factors` shows the SAME
kind of divergence already exists for CROSS-side pairs using nothing but
this project's long-standing, fully-permissive `natIncidence` -- no new
instance needed at all. At `(Sum.inl 1, Sum.inr 1)` (both `≠ 0 =
natIncidence.unit`), `incidenceSum natIncidence natIncidence`'s actual
guards give `true` (permissive, unconditionally), while
`sumGuardsExpected` gives `false` (genuine cross-side pair, the case
`sumGlue` itself resolves to `none`, and `sumGuardsExpected` mirrors that
with `false`). So the permissive/componentwise gap is not solely about a
factor's OWN guards content (cycle 47's original framing) -- it is already
present in how `incidenceSum` treats its own `Sum.inl`/`Sum.inr` case split,
visible with instances this project has had since cycle 4.

`lake build IncidenceTheory.Sum`: clean on the first attempt (no compiler
errors caught this cycle, unlike cycles 48/49's one-fix experience). Full
`./verify.sh` (`lake clean && lake build`, 62/62 jobs, example binary run,
repo-wide `axiom`/`sorry`/`sorryAx` grep): passes end to end.

**Synthesis**: this closes cycle 49's queued option (b) with a genuine
positive result, not a structural-impossibility finding like cycle 49's own
same-side-glue observation -- the two open threads cycle 49 left behind
(this one, and cycle 48/49's converse-iff) now resolve to opposite flavors
of answer, which is itself worth noting as evidence this project's guards
machinery has a real, not merely formal, asymmetry: `incidenceProd`
faithfully propagates its factors' guards; `incidenceSum` does not, and now
we have both a general theorem and two independent concrete witnesses
(one hand-built non-permissive instance, one pre-existing permissive pair)
showing the gap is observable. Taken together with cycle 47's original
finding, the full picture is: `incidenceSum`'s permissive guards is not a
narrow oversight limited to non-permissive factors -- it discards
information at BOTH the same-side (factor-guards) and cross-side
(structural, glue-shape) levels simultaneously. Per the task's explicit
instruction, this cycle does not attempt to fix or redesign
`incidenceSum`'s guards field itself, nor build a general
guards-respecting sum constructor -- that remains a distinct, larger,
not-yet-scoped undertaking.

**Next hypothesis (cycle 51, not yet attempted)**: with cycle 49's option
(b) now closed (positive divergence, both generic and concrete) and cycle
48/49's option (a) already closed (converse iff), and option (c) retired as
stale since cycle 41/45 (do NOT re-queue the cycle 39/41 middle-ground
`≈`-quotient question -- it is answered, by `simplexIncidence`), the
guards/glue-distributivity thread that has run cycles 46-50 has no further
queued item from that specific investigation. Two genuinely fresh
directions, either legitimate: (i) given this cycle showed the
guards-divergence gap has both a same-side and a cross-side component,
check whether `incidenceProd`'s own guards (`prodGuards`, cycle 31) has any
analogous BLIND SPOT of its own -- cycle 47 established it "genuinely
conjoins", but only checked the top-level `allow` value, not whether
`prodGuards` respects any WEAKER structure (e.g. does `prodGuards`'s
conjunction ever silently disagree with what `type_preserve`/`assoc_when_ok`-style
downstream consumers of guards would actually need, the way `incidenceSum`'s
permissive default turned out to under-restrict);
or (ii) a genuinely NEW middle-ground `≈`-quotient instance, distinct from
`simplexIncidence` (the only witness the project has), building on a
different concrete instance (e.g. `pathIncidence`, `treeIncidence`, or a
purpose-built one) to see whether cycle 41's "well-founded grading survives
collapse" mechanism generalizes or was special to `simplexIncidence`'s
shape-grading -- this is a fresh question cycle 49's audit note explicitly
distinguished from the now-closed cycle 39/41 original, not a re-run of it.

## Cycle 51

**Hypothesis**: cycle 50's queued option (ii), picked over option (i)
(`incidenceProd`'s own guards blind spot) by the orchestrating session's
explicit diversification choice, since five straight cycles (46-50) had
mined the `incidenceProd`/`incidenceSum` guards/glue corner and this
project's roadmap item 8 (broader algebraic reconstruction) benefits more
from fresh territory than from a sixth pass at the same corner: does cycle
41's finding -- a `≈`-quotient construction can succeed exactly when the
collapse respects a well-founded grading already present in the source
instance -- generalize to a genuinely DIFFERENT graded instance, or was it
an accident specific to `simplexIncidence`'s particular three-level
vertex/edge/face shape? `simplexIncidence` was, until this cycle, the
ONLY witness this project had ever built for the "genuine middle ground"
(more than one `≈`-class, fewer than all).

**Method**: grepped every concrete `Incidence` instance across
`IncidenceTheory/*.lean` before assuming which candidates exist (per the
task's own instruction not to invent instance names) -- confirmed the
graded/structured candidates beyond the flat/atomic ones
(`natIncidence`, `finiteIncidence`, `trivialIncidence`, `cycleIncidence`)
are `simplexIncidence` (Simplex.lean, already used), `pathIncidence`/
`pathIncidenceChained` (PathComplex.lean), and `treeIncidence`
(Tree.lean). Read `PathComplex.lean` and `Tree.lean` in full. Ruled out
`pathIncidenceChained` immediately: cycle 14's own fix made it FULLY
faithful (`pathIncidenceChained_approxBisim_iff`, `≈` coincides with `=`)
-- the "collapses nothing" extreme cycle 40 already closed, not the
middle ground. Ruled out `treeIncidence` as this cycle's primary target
on inspection, not by construction: its carrier (`TreeId`) nests
recursively without bound (`node a b c` can itself contain arbitrarily
deep further nodes), so any shape-classification collapsing "leaf-label"
information the way `simplexToShape` collapses vertex-identity would
have to be an infinite, itself-recursive `TreeShape` type indexed by
nesting depth -- a substantially larger undertaking than this cycle's
scope, and not the same kind of finite-or-uniformly-graded target
`GradedIncidenceData` (see below) was built for; left as a candidate for
a future cycle rather than forced.

That left plain `pathIncidence` (cycle 10): nodes are uniformly leaves
(`pathBoundary (node _) = []` for every `n`, cycle 13's own
`pathIncidence_nodes_collapse` already witnesses `node 0 ≈ node 1`) and
edges are non-leaves whose two boundary entries both point to nodes --
structurally a 2-level grading (nodes=0, edges=1), the same *kind* of
shape as `simplexIncidence`'s 3-level grading but one level shallower and,
crucially, over an INFINITE carrier (`node`/`edge` indexed by unbounded
`Nat`) rather than `simplexIncidence`'s finite 7 elements -- a genuinely
different data point, not a restatement. Before building anything, also
discovered that the generic machinery cycle 41's construction needed
(hand-rolled `Incidence` fields, ad hoc `well_founded` case-splitting) had
since been GENERALIZED into reusable infrastructure already sitting in
`Quotient.lean` (`GradedIncidenceData`, `IncidenceCandidateData`,
`BisimulationQuotientClassification`, `GradedBisimulationQuotientPresentation`)
-- confirmed `shapeIncidence` itself (cycle 41's own construction) is
already expressed through `GradedIncidenceData.toIncidence` in the current
`main`, not the bespoke inline record cycle 41's log describes; this
generalization landed at some point after cycle 41 (exact cycle
unattributed, same undocumented-batch phenomenon cycles 45/46 already
flagged for other parts of this file, not re-investigated further here
since it doesn't change this cycle's own method, only makes it easier).
Used this machinery directly rather than re-deriving `well_founded`'s
self-loop avoidance by hand.

**Result**: **a genuine second positive middle-ground quotient instance,
sorry-free, first build.** Added to `Quotient.lean` (after adding
`import IncidenceTheory.PathComplex`): `PathShape` (`nodeShape`/
`edgeShape`), `pathToShape`, the bisimulation relation `pathNodeEdgeRel`
generalizing cycle 13's representative-pair witness to ALL node/node and
edge/edge pairs at once (needing, notably, NO per-index case split --
unlike `simplexEdgeVertexRel_isBisimulation`'s nine enumerated arms,
`pathIncidence`'s uniform-in-`n` shape lets one generic argument per grade
suffice, the first concrete evidence the grading pattern doesn't depend on
grades being finite), and the exhaustive
`pathToShape_iff_approxBisim : pathToShape x = pathToShape y ↔ approxBisim
pathIncidence x y` -- exactly TWO classes over `pathIncidence`'s infinite
carrier, proved with 4 structural cases (not 49 like `simplexIncidence`),
again because every `node n` is uniformly a leaf (unlike `simplexIncidence`
where only 3 of 7 constructors are leaves, forcing per-constructor
enumeration in cycle 22/23).

`pathBisimulationQuotientClassification` packages this
(`classify := pathToShape`); `pathShapeBoundary`/`pathShapeGrade`
(`nodeShape ↦ 0`, `edgeShape ↦ 1`) feed `GradedIncidenceData`, whose
`boundary_decreases` obligation is discharged by a 3-line proof (vs. cycle
41's hand-written case analysis) -- `pathShapeIncidence :=
pathShapeGradedIncidenceData.toIncidence` is the fresh, genuine
`Incidence PathShape PeanoRole GraphType` structure on the quotient's
carrier, all obligations via the generic constructor. `pathQuotientToShape`
(via `Quotient.lift`) is confirmed injective and surjective, matching cycle
41's bijection pattern for `simplexIncidence`.

Task step (d), honestly checked rather than assumed:
`pathClassification_glue_not_invariant` shows `pathToShape` is NOT a
glue-homomorphism between `pathIncidence` and `pathShapeIncidence` --
`node 0 ≈ node 1` (same class), but gluing each against `edge 0` produces
DIFFERENT shapes (`edgeShape` vs. `nodeShape`), because `pathIncidence`'s
own `glue` special-cases the literal representative `node 0`, not the
whole `≈`-class it belongs to -- the identical mechanism cycle 41 found
for `simplexIncidence`. Going further than cycle 41 could in its own
cycle: because the general `GlueRealization ↔ GlueInvariant` criterion
(`glueRealization_iff_invariant`) already existed as reusable
infrastructure (built sometime after cycle 41, first exercised by
`simplexIncidence` only in cycle 45 -- one full cycle after its own
quotient was built), this cycle gets the STRONGER "no possible glue
whatsoever" closure (`pathShape_glue_not_realizable`,
`pathToShape_no_glue_homomorphism_exists`) in the SAME cycle the quotient
itself was constructed, with no separate follow-up cycle needed.

`lake build IncidenceTheory.Quotient`: 23/23 jobs, clean on the first
attempt (no compile errors, unlike several recent cycles' one-fix
experience). `#print axioms` on the six headline declarations (checked via
a scratch file fed to `lake env lean`, then deleted): all reduce to this
project's standing profile (`propext`, `Quot.sound`, and `Classical.choice`
only for the two `GlueRealization`-based closures, matching cycle 45's own
axiom profile for the analogous simplex theorems) -- no new axiom
introduced. Full `./verify.sh` (`lake clean && lake build`, example binary
run, repo-wide `axiom`/`sorry`/`sorryAx` grep): passes end to end.

**Synthesis**: cycle 41's finding generalizes -- it was not an accident of
`simplexIncidence`'s specific shape. `pathIncidence` confirms the same
mechanism (well-founded grading survives collapse-within-grade) works for
a structurally different graded instance: fewer grades (2 vs. 3), but each
grade infinite rather than a handful of named constructors, which turned
out to make several of the individual proof steps EASIER, not harder (no
per-index case split needed for the bisimulation or the shape-agreement
iff, since the uniformity-in-`n` that makes the carrier infinite also makes
each grade's leaf/non-leaf status carrier-wide rather than
constructor-by-constructor). This also validates a genuinely useful
methodological point about this project's own history: the
`GradedIncidenceData`/`BisimulationQuotientClassification` machinery that
was generalized out of cycle 41's bespoke construction (by an unattributed
later pass) is not just a refactor for its own sake -- reusing it here cut
this cycle's proof effort substantially (no hand-written `well_founded`
case split, and the `GlueRealization` closure that took `simplexIncidence`
two separate cycles, 41 then 45, to reach was available to `pathIncidence`
in one). `treeIncidence` remains a live, larger candidate for testing
whether the grading mechanism survives UNBOUNDED recursive depth (not just
unbounded per-grade multiplicity, which is what this cycle's `pathIncidence`
result actually tested) -- explicitly deferred, not attempted, since a
faithful `TreeShape` construction needs its own recursive target type and
was assessed as out of this cycle's scope rather than forced.

**Next hypothesis (cycle 52, not yet attempted)**: two live threads. (a)
`treeIncidence`'s ternary, unboundedly-recursive shape, deferred above --
does building a recursive `TreeShape` (mirroring `TreeId` but erasing leaf
labels) and its own `GradedIncidenceData` presentation (grade = structural
depth, well-founded via the same `sizeOf`-based measure `treeIncidence`
itself already uses) succeed, or does unbounded recursive depth break the
"well-founded grading survives collapse" mechanism in a way finite/
per-grade-infinite gradings (`simplexIncidence`, `pathIncidence`) do not?
This is the natural next generalization test and was explicitly scoped out
of this cycle rather than attempted underprepared. (b) Cycle 50's other
queued option (i), still untouched: does `incidenceProd`'s own guards
(`prodGuards`) have an analogous blind spot to `incidenceSum`'s (cycles
46-50), beyond top-level conjunction -- still open, still narrowly scoped,
available if (a) turns out intractable or as a change-of-pace item after
two consecutive quotient-construction cycles.

## Cycle 52

**Hypothesis**: cycle 51's own queued primary next-hypothesis, option (a):
`treeIncidence` (Tree.lean, cycle 29) is the one graded instance cycle 51
explicitly declined to attempt, because its carrier (`TreeId`) nests
recursively WITHOUT BOUND (`node a b c`'s children can themselves be nodes,
to arbitrary depth) -- unlike `simplexIncidence`'s fixed 3-level grading
(cycle 41) or `pathIncidence`'s fixed 2-level grading with unbounded
per-grade multiplicity but structurally uniform-in-`n` elements (cycle 51).
Does the "collapse survives exactly when it respects a well-founded
grading" mechanism ALSO survive when the grading itself comes from
UNBOUNDED RECURSIVE DEPTH, or does the recursive self-similarity of a tree
create a genuinely different obstruction than either prior flat case?

**Method**: read `Tree.lean` in full (cycle 29's `treeIncidence`: carrier
`TreeId := leaf Nat | node TreeId TreeId TreeId`, boundary `treeBoundary`
giving non-leaves exactly 3 role-tagged entries `c1`/`c2`/`c3`, `glue`
identical in shape to `pathIncidence`'s and `simplexIncidence`'s --
"absorb at a fixed literal unit representative" -- and `well_founded`
proved via `sizeOf`/`TreeId.node.sizeOf_spec`/`omega`, i.e. `treeIncidence`
itself already used a `sizeOf`-based well-founded measure, not a small
enumerated grade). Read `Quotient.lean` in full for the generalized
`GradedIncidenceData`/`BisimulationQuotientClassification`/
`GradedBisimulationQuotientPresentation` infrastructure cycles 41/51 built
and used. Confirmed (per cycle 51's own note) that no `TreeShape` type or
tree-quotient construction exists anywhere yet.

Designed the natural candidate before writing any Lean: a `TreeShape`
type mirroring `TreeId` but with leaf labels erased (`leaf | node
TreeShape TreeShape TreeShape`) -- itself an unboundedly recursive
inductive type, unlike `PathShape`/`SimplexShape`'s 2/3 finite named
constructors. The classifying map `treeToShape` forgets only `Nat` leaf
labels, congruence-closed up the tree. Anticipated before proving it that
the two directions of `treeToShape_iff_approxBisim` would need genuinely
different techniques than cycles 41/51: the "reflects" direction (shape-
equal → bisimilar) is a single level of case analysis, same shape as
`pathNodeEdgeRel_isBisimulation` (the relation "same shape" already
encodes whatever is needed about the children, no re-derivation needed);
but the "distinguishes" direction (bisimilar → shape-equal) cannot be a
flat argument (`pathToShape_distinguishes`, uniform-in-`n`) nor a finite
enumeration (`simplexToShape_distinguishes`, 7 elements total) since
`TreeId` nests without bound -- it needs genuine structural induction over
an arbitrary witnessing bisimulation, the first time this project's
quotient-construction thread (cycles 38-51) has needed induction rather
than direct case-splitting or finite enumeration for a classifying map's
converse direction.

**Result**: **a genuine third positive middle-ground quotient instance,
sorry-free, first build -- the recursive-depth generalization survives,
but required a strictly larger proof-technique toolkit than either prior
instance, plus two real (not merely stylistic) implementation snags worth
recording.**

Added to `IncidenceTheory.lean` (root file): `boundaryMatched_of_three_entries`,
the natural 3-entry generalization of cycle-41-era
`boundaryMatched_of_two_entries` -- needed because both `treeIncidence` and
its quotient have genuinely ternary (not binary) boundaries, unlike every
prior quotient instance. Added to `Quotient.lean` (after adding `import
IncidenceTheory.Tree`): `TreeShape`, `treeToShape`, the bisimulation
relation `treeShapeRel x y := treeToShape x = treeToShape y` (defined VIA
the recursive classifying map itself, since there is no flat non-recursive
way to state "same branching shape" for an unboundedly deep type -- unlike
`pathNodeEdgeRel`/`simplexEdgeVertexRel`, stated directly on the two
grades), and `treeShapeRel_isBisimulation` (one level of case analysis,
using the new `boundaryMatched_of_three_entries`). The converse direction,
`treeToShape_distinguishes_of_bisimulation`, is proved by genuine
structural induction on `TreeId` over an ARBITRARY witnessing bisimulation
`rel` (mirroring `incidence_bisim_faithful`'s cycle-4 structure -- induction
over a well-founded measure to chase an arbitrary bisimulation's existentials
-- but concluding shape-agreement rather than literal equality, and using
`TreeId`'s own recursor as the well-founded measure directly rather than a
separate `Nat`-valued one). The needed extraction step -- unpacking
`boundaryMatched` at a known pair of ternary nodes into the three
positional `rel` facts -- is `treeIncidence_node_node_boundaryMatched_rel`,
using that `c1`/`c2`/`c3` are pairwise distinct to rule out two "wrong
slot" matches per entry. `treeToShape_iff_approxBisim` closes the loop:
`treeIncidence`'s `≈` is exactly `treeToShape`-agreement, a genuine
middle-ground quotient (every `leaf n` collapses regardless of `n`;
distinct branching shapes remain distinct) even though the grading now
comes from unbounded recursive depth.

`treeBisimulationQuotientClassification` packages this; `treeShapeBoundary`
feeds `GradedIncidenceData`. Two real implementation snags surfaced here
that cycles 41/51 never hit (both diagnosed and fixed, not routed around):

1. The FIRST attempt at the grade used `grade := sizeOf` directly, reusing
   `TreeShape`'s auto-derived `SizeOf` instance the same way
   `treeIncidence.well_founded` itself reuses `TreeId`'s. This proved
   correctly (the `boundary_decreases` proof went through) but then failed
   to COMPILE: `lake build` rejected `treeShapeGradedIncidenceData` with
   "depends on declaration `TreeShape._sizeOf_inst`, which has no
   executable code; consider marking definition as `noncomputable`" --
   `TreeShape`'s auto-derived `SizeOf` instance is itself noncomputable
   (unlike `TreeId`'s, which compiles fine, but is only ever consumed
   inside `Prop`-valued proofs where computability never matters).
   `GradedIncidenceData` is a plain executable `def` whose `grade` field is
   real run-time data, so this is a genuine constraint, not a proof gap.
   Fixed by replacing `sizeOf` with a hand-written, structurally-recursive
   `treeShapeGrade : TreeShape → Nat` (subtree size: `leaf ↦ 0`,
   `node a b c ↦ grade a + grade b + grade c + 1`) -- fully computable,
   in exactly `pathShapeGrade`/`simplexShapeGrade`'s style (an explicit
   `Q → Nat` map) generalized from a finite lookup table to genuine
   structural recursion. `boundary_decreases`'s proof is then a 2-line
   `omega` closure, the same shape `treeIncidence`'s own `well_founded`
   proof uses.
2. The extraction lemma's role-mismatch case splits (proving e.g.
   `TernaryRole.c1 ≠ TernaryRole.c2` to rule out a wrong positional match)
   hit a reproducible Lean elaboration snag: `by decide`, even under an
   explicit type ascription, was rejected with "Expected type must not
   contain free variables" when run inside a context with unrelated free
   variables in scope (the tree's child variables `a`, `b'`, etc., bound
   by the enclosing case-split but not mentioned by the target
   proposition itself) -- `decide`'s closed-term precondition looks at the
   ambient elaboration context, not just the stated goal, and type
   ascription does not change what gets checked. Fixed by proving the six
   pairwise `TernaryRole` disequalities as standalone, fully closed
   top-level lemmas FIRST, then merely *applying* them via `absurd` at the
   point of use (a defeq check against a fully elaborated closed term, not
   a fresh in-context `decide` elaboration) -- sidesteps the snag entirely
   rather than fighting it in place.

`treeShapeIncidence := treeShapeGradedIncidenceData.toIncidence` is the
fresh, genuine `Incidence TreeShape TernaryRole GraphType` structure on
the quotient's carrier, all obligations via the generic constructor.
`treeQuotientToShape` (via `Quotient.lift`) confirmed injective and
surjective. Task step (d), honestly checked rather than assumed:
`treeClassification_glue_not_invariant`/`treeShape_glue_not_realizable`
show `treeToShape` is NOT a glue-homomorphism between `treeIncidence` and
`treeShapeIncidence` -- the identical mechanism cycles 41/51 found:
`leaf 0 ≈ leaf 1` (same class), but gluing each against a fixed non-leaf
node produces different shapes, because `treeIncidence.glue` special-cases
the literal representative `leaf 0`, not the whole `≈`-class of leaves.
The strictly stronger "no possible glue whatsoever" closure
(`treeToShape_no_glue_homomorphism_exists`) is available in the SAME cycle
the quotient itself was constructed, as for `pathIncidence` (cycle 51).

`lake build` (targeted `IncidenceTheory.Quotient`, then full project):
clean after the three fixes above (two real compile/elaboration snags plus
one straightforward missing-`simp`-lemma miss in the leaf/leaf bisimulation
case). `#print axioms` on the headline declarations (`treeToShape_iff_approxBisim`,
`treeBisimulationQuotientClassification`, `treeShapeIncidence`,
`treeGradedQuotientPresentation`, `treeShape_glue_not_realizable`,
`treeToShape_no_glue_homomorphism_exists`): all reduce to this project's
standing profile (`propext`, `Quot.sound`, `Classical.choice`) -- no new
axiom introduced. Full `./verify.sh` (`lake clean && lake build`, example
binary run, repo-wide `axiom`/`sorry`/`sorryAx` grep): passes end to end.

**Synthesis**: the well-founded-grading mechanism survives unbounded
recursive depth -- this is NOT an accident specific to flat or finite
gradings. But cycle 51's framing of this as an open question with a
genuinely uncertain outcome was well-calibrated: unlike cycle 51's own
result (which "turned out to make several proof steps EASIER, not
harder"), this cycle needed a strictly larger proof-technique toolkit
(genuine structural induction for the converse direction, a new 3-entry
root-file lemma, and two implementation-level snags requiring real
debugging rather than routine casework) even though the final mathematical
shape of the result is the same three-part pattern as cycles 41/51
(classification, `GradedIncidenceData` presentation, negative
glue-homomorphism check). The `sizeOf`-noncomputability snag is a small
but genuine addition to this project's methodological knowledge: an
auto-derived typeclass instance (`SizeOf`) that is perfectly fine to
reference inside `Prop`-valued proofs (as `treeIncidence.well_founded`
itself already did, pre-existing and unchanged) can silently be unusable
as literal run-time DATA in an executable `def` -- the failure mode is a
compile error, not a proof gap, and would not have been caught by proof
review alone. The `decide`-under-free-variables snag is a reusable
methodological note for any future cycle needing to discharge small
finite-constructor disequalities inside a context with unrelated bound
variables: prove the disequality as an isolated closed lemma first, don't
inline `decide` at the point of use.

This closes the three-instance arc cycle 51 characterized as "confirm or
refute cycle 41 was an accident of `simplexIncidence`'s specific shape":
`simplexIncidence` (finite carrier, 3 fixed grades), `pathIncidence`
(infinite carrier, 2 fixed grades, uniform-in-index elements), and now
`treeIncidence` (infinite carrier, unboundedly many grades via recursive
depth) all confirm the same mechanism. Roadmap item 8 (algebra/topology/
measure reconstruction) and item 7 (incidence/resonance ↔ internal-logic
integration) are not directly advanced by this cycle -- it is squarely a
"third generic constructor" (quotient) thread result, continuing cycles
38-51's arc rather than opening item 7/8 territory.

**Next hypothesis (cycle 53, not yet attempted)**: with all three graded
instances this project has ever built (`simplexIncidence`, `pathIncidence`,
`treeIncidence`) now confirmed to have well-behaved middle-ground
quotients under the SAME mechanism, and all three also confirmed to fail
the glue-homomorphism check by the SAME mechanism (fixed-representative
`glue` vs. whole-class collapse), two live threads: (a) is there a general
THEOREM lurking here -- e.g. "any `GradedIncidenceData`-presentable
quotient of an instance whose `glue` has the `if i = unit then some j else
some i`-style fixed-representative shape NEVER has a realizable glue
lift", proved once and for all rather than re-discovered instance-by-
instance (cycles 41/45, 51, 52 each re-derived essentially the same
negative fact by hand)? This would be a genuine generalization, not just a
fourth instance. (b) cycle 50's still-untouched option (i): does
`incidenceProd`'s own guards (`prodGuards`) have an analogous blind spot to
`incidenceSum`'s (cycles 46-50), beyond top-level conjunction -- available
as a change-of-pace item after three consecutive quotient-construction
cycles (41, 51, 52) if (a) turns out out of scope for one cycle.

## Cycle 53

**Hypothesis**: cycle 52's own queued primary next-hypothesis, option (a):
with THREE separately hand-derived instances of the same negative pattern
now on record (`simplexClassification_glue_not_invariant`/
`simplexShape_glue_not_realizable`, cycles 41/45; `pathClassification_glue_
not_invariant`/`pathShape_glue_not_realizable`, cycle 51;
`treeClassification_glue_not_invariant`/`treeShape_glue_not_realizable`,
cycle 52) -- is there ONE general theorem subsuming the repeated
instance-by-instance derivation, or do the three counterexamples resist
unification into anything more than a family resemblance? Explicitly not
assumed in advance which outcome would hold, per the task's own framing:
a rigorous "they don't unify" finding would be equally legitimate.

**Method**: read all three concrete `GlueInvariant`-refutation proofs in
`Quotient.lean` side by side (lines ~1799-1810 simplex, ~2112-2127 path,
~2500-2519 tree), rather than guessing the shared mechanism from the task
briefing's own tentative phrasing. Then read `simplexIncidence`'s/
`pathIncidence`'s/`treeIncidence`'s own `glue`/`unit` field definitions
directly in `Simplex.lean:63-64`, `PathComplex.lean:40-41`, `Tree.lean:51-52`
(delegated to a read-only sub-agent to keep this cycle's own context
focused on the proof logic, then independently confirmed the reported
lines with `grep`). Found: all three are LITERALLY the identical formula
`fun i j => if i = <unit> then some j else some i`, differing only in
which concrete element (`SimplexId.v0`/`PathId.node 0`/`TreeId.leaf 0`) is
chosen as `<unit>` -- not a coincidence of similar style, the exact same
closed term up to alpha-renaming the chosen unit constant. Then traced
each of the three `GlueInvariant`-refutation proofs' actual computation:
every one of them (a) picks some `x` in `inc.unit`'s own `≈`-class with
`x ≠ inc.unit` (`v1`/`node 1`/`leaf 1`), (b) picks some `j` OUTSIDE that
class (`face`/`edge 0`/a `node`), and (c) exploits that `inc.unit_left`
(an obligation of EVERY `Incidence`, not instance-specific) forces
`glue unit j = some j`, while the "absorbing" formula's `else` branch
forces `glue x j = some x` for the chosen `x ≠ unit` -- so `classify`
cannot tell `x` and `unit` apart (same class) but `glue` treats them
oppositely, immediately breaking `GlueInvariant` at that one pair.

**Result**: **confirmed, sorry-free, on the first `lake build` attempt --
a genuine common mechanism, not merely a family resemblance, cleanly
extractable into one theorem.** Added to `Quotient.lean`, after the tree
section: (1) `glueInvariant_fails_of_unit_class_witness`, the primitive
general lemma -- for ANY `Incidence`, ANY `BisimulationQuotientClassification`,
if some `x ≈ inc.unit` satisfies `glue x j = some x` for some `j` with
`classify j ≠ classify inc.unit`, then `¬ GlueInvariant`. Its proof needs
only `inc.unit_left` (always available, no hypothesis) plus the one
assumed fact about `x`; no reference to `SimplexId`/`PathId`/`TreeId` at
all. (2) `glueRealization_fails_of_unit_class_witness`, the immediate
`GlueRealization`-level strengthening via the pre-existing
`glueRealization_iff_invariant`. (3)
`glueInvariant_fails_of_absorbingUnitGlue`/`glueRealization_fails_of_
absorbingUnitGlue`, specializing (1)/(2) to the literal "absorbing-unit"
formula shape all three sources share -- once `inc.glue` is proved equal
to that formula, the behavioral fact `glue x j = some x` becomes automatic
from `x ≠ inc.unit` alone (`by rw [absorbing]; simp [xNeUnit]`), so no
per-instance glue computation is needed at all. (4) Three corollaries,
`simplexShape_glue_not_realizable_of_general`/`pathShape_glue_not_
realizable_of_general`/`treeShape_glue_not_realizable_of_general`, each a
one-line application of (3) at the STRONGEST (`GlueRealization`) level
directly: the `absorbing` hypothesis discharges by `rfl` (the source
`glue` fields literally ARE that formula, confirmed above, not merely
implies it), `xNeUnit`/`jOutsideUnitClass` by `decide` (finite constructor
disequalities), and `xBisimUnit` by the pre-existing `_iff_approxBisim`
characterization applied to `rfl` (both `x` and `unit` map to the same
shape definitionally). No new case-analysis on any of the three carrier
types was needed anywhere in this cycle's proofs. `lake build
IncidenceTheory.Quotient`: 24/24 jobs, clean on the very first attempt --
notably smoother than cycle 52's two implementation snags, since this
cycle's proofs are pure combinators over already-proved facts rather than
new structural recursion. `#print axioms` on all seven new declarations
(checked via a scratch file fed to `lake env lean`, then deleted): all
reduce to this project's standing profile (`propext`; `Classical.choice`
for the `GlueRealization`-level lemmas via `canonicalGlue`'s
representative-choice; `Quot.sound` additionally for the three concrete
corollaries via their classification's `Quotient`-based infrastructure) --
no new axiom introduced anywhere. Full `./verify.sh` (`lake clean && lake
build`, example binary run, repo-wide `axiom`/`sorry`/`sorryAx` grep):
passes end to end.

**Synthesis**: cycle 52's queued question resolves in the POSITIVE
direction -- the three-cycle-repeated negative pattern (41/45, 51, 52) was
never an accident of three separately-chosen constructions; it is one
theorem about `Incidence`'s own laws (`unit_left`) colliding with one
implementation choice (`glue`'s "absorb at a single literal representative"
shape) that all three source instances happened to make. The general
theorem is deliberately NOT stated in terms of `GradedIncidenceData` or
well-founded grading at all -- tracing the actual proofs showed grading is
load-bearing for a DIFFERENT question (whether the quotient's `Incidence`
structure can be built in the first place, i.e. `well_founded` surviving
collapse-within-grade, cycles 41/51/52's headline positive results) but is
completely irrelevant to THIS question (whether the classifying map is a
glue-homomorphism) -- the glue obstruction is a purely algebraic fact
about `unit_left` plus one non-singleton class, orthogonal to grading.
This is itself a useful negative-space finding: the task briefing's own
tentative guess ("a classifying map that collapses a pair of witnesses
non-injectively...") was close in spirit but the actual mechanism is
sharper and needs no talk of "argument-independence" in the abstract --
it is exactly "does some non-unit class-mate of `inc.unit` get treated
differently from `inc.unit` itself by `glue`", which `unit_left` alone
already guarantees will happen whenever `inc.unit`'s class is non-singleton
AND `glue`'s non-unit branch is not itself constant across the whole
class. The two-layer statement (primitive behavioral lemma, then a
literal-formula specialization) is deliberately kept separate: the
primitive lemma is the actually-general fact (would apply just as well to
some future instance with a differently-shaped, non-formula glue that
still happens to satisfy the one behavioral fact), while the specialization
is what makes the three EXISTING instances' re-derivation a one-line
`rfl`-driven corollary rather than requiring a fresh proof search each
time. Confirms this cycle's result is a genuine generalization (not a
restatement with hypotheses that amount to "assume it works"): the
hypotheses are checked, not assumed, against all three sources' actual
field definitions, and the corollaries reduce to `rfl`/`decide`/existing
lemmas with zero new casework.

**Next hypothesis (cycle 54, not yet attempted)**: with the "third generic
constructor" (quotient) thread's glue-homomorphism question now closed
both instance-by-instance (cycles 41/45, 51, 52) AND generally (this
cycle), the natural next moves are: (a) run the general
`glueInvariant_fails_of_unit_class_witness`/`_absorbingUnitGlue` criterion
against `BoundaryInvariant` too -- does an analogous "one law
(`type_consistent`/`sign_rules`/`multiplicities`) plus one non-singleton
class" mechanism explain why `boundary` ALSO fails to be `≈`-invariant in
the fully-general case (cycle 38's `cycleIncidence` finding), or is
`BoundaryInvariant`'s failure mode structurally different from `GlueInvariant`'s
(worth checking before assuming the same criterion transfers)? (b) cycle
50's still-untouched option (i): does `incidenceProd`'s own `guards`
(`prodGuards`) have an analogous blind spot to `incidenceSum`'s (cycles
46-50), beyond top-level conjunction -- available as a change-of-pace item
if (a) turns out to need its own scoping pass first. (c) separately, the
general criterion this cycle proved is itself a candidate lemma for
`GuardInvariant`/`GuardRealization` too (the `Guards`-level analogue built
alongside `GlueInvariant`/`GlueRealization` in the same generic
infrastructure) -- worth checking whether any EXISTING guard definition in
this project actually has an "absorbing" shape before assuming the
analogy transfers, rather than building speculative infrastructure for a
pattern that may not occur.

## Cycle 54

**Hypothesis**: option (a) from cycle 53's queue -- does the SAME
mechanism that explains simplex/path/tree's `GlueInvariant` failure
(cycle 53: the universal `unit_left` law plus a non-singleton
`≈`-class containing `unit`, witnessed against some `j` OUTSIDE that
class) ALSO explain `cycleIncidence`'s ORIGINAL `boundary`-failure
(cycle 38, `cycleIncidence_boundary_not_approxBisim_invariant`)? Or is
`cycleIncidence`'s case -- the Subsingleton, fully-collapsed extreme --
a genuinely different obstruction, as cycle 39's synthesis already
flagged when it separated "fully collapsed" from "partial middle
ground" as qualitatively different regimes? Read cycle 38's raw finding,
`cycleIncidence`'s actual definition (`Cycle.lean`), and
`BoundaryInvariant`'s definition (`Quotient.lean`, `mappedSourceBoundary`)
in full before assuming either answer, per this cycle's brief.

**Method**: read cycle 38's exact statement first --
`cycleIncidence_boundary_not_approxBisim_invariant` is a claim about the
RAW field (`∀ i j, i ≈ j → inc.boundary i = inc.boundary j`), proved
false via `c0`/`c1`'s literally different `Endpoint` lists (predecessors
`c3` vs. `c0`). This is a different (stronger, unindexed) statement than
`BoundaryInvariant` (`Quotient.lean`), which only asks for agreement
of `mappedSourceBoundary` -- `inc.boundary` with each entry's `.i` field
already remapped through a chosen `classify : I → Q` -- so cycle 38's raw
finding does not by itself say anything about whether `BoundaryInvariant`
holds for any *particular* classification of `cycleIncidence`. No such
classification had been built yet in this project (unlike
`natBoolProductClassification`/`simplexBisimulationQuotientClassification`/
etc.), so built the missing one: `cycleBisimulationQuotientClassification`,
target `Unit` (the only possible target up to equivalence, since
`cycleIncidence_all_collapse` makes `≈` relate every pair), via
`bisimulationQuotientClassificationOfKernel` + the existing
`cycleIncidence_all_collapse` proof as the kernel condition. Then checked
`BoundaryInvariant`/`GlueInvariant` directly against it, and separately
checked whether cycle 53's own hypothesis (`jOutsideUnitClass : classify
j ≠ classify unit`) can even be stated non-vacuously when the target is
`Subsingleton`.

**Result**: **the two mechanisms are opposites, not the same mechanism
in different clothes -- confirmed on the first attempt, six new
theorems, no new casework needed anywhere.** `cycleBisimulationQuotientClassification.BoundaryInvariant`
and `.GlueInvariant` both **HOLD** (`cycleBisimulationQuotientClassification_boundaryInvariant`,
`_glueInvariant`, each closed by `fun _ _ _ => rfl` / `fun _ _ _ _ _ _ =>
rfl` -- no case split on `CycleId` at all, since `classify` is constant
on a `Unit` target and `cycleBoundary`/`cycleIncidence.glue` are already
uniform in shape across every element, cycle 26's own "uniform boundary"
observation doing the work here). Both `BoundaryRealization`/
`GlueRealization` follow immediately from the already-generic
`_iff_invariant` lemmas (`cycleBisimulationQuotientClassification_boundaryRealization`,
`_glueRealization`). Separately, `no_jOutsideUnitClass_of_subsingleton`
proves cycle 53's own hypothesis is **unsatisfiable by construction**
whenever the target is `Subsingleton` (`Subsingleton.elim` alone, no
fact about `inc` needed), instantiated against `cycleBisimulationQuotientClassification`
as `cycleBisimulationQuotientClassification_unit_class_witness_vacuous`.
So cycle 53's mechanism does not merely fail to apply to `cycleIncidence`
by coincidence -- it structurally cannot apply to ANY totally-collapsed
quotient. The actual obstruction lives one level up, in `well_founded`
specifically: `canonicalBoundary_self_loop_of_subsingleton` (general,
`Subsingleton`-target + source point with nonempty boundary ⟹
`canonicalBoundary` has a self-loop at EVERY quotient point, since
`Subsingleton.elim` collapses each boundary entry's remapped index onto
the very point whose boundary it is attached to) combined with
`no_canonicalQuotientIncidenceCoherence_of_subsingleton_target` (general
corollary: no `CanonicalQuotientIncidenceCoherence` -- the actual
target-`Incidence`-assembling route cycles 41-53 use -- can ever be
completed under those conditions, `BoundaryInvariant`/`GlueInvariant`
notwithstanding) together re-derive cycle 38's original finding as
`cycleBisimulationQuotientClassification_no_coherence`, a one-line
corollary exactly mirroring cycle 53's own specialization pattern but
for the dual mechanism. `#print axioms` on all nine new declarations:
`no_jOutsideUnitClass_of_subsingleton` needs nothing; the rest need only
`propext`/`Quot.sound`(/`Classical.choice` for the `Realization`- and
`canonicalBoundary`-involving ones) -- fully within this project's
accepted axiom set. Full `lake build`: 62/62 jobs. `./verify.sh`: passes
end to end (build, example binary, repo-wide `sorry`/`axiom` grep).
Repo-wide `sorry`-as-tactic grep: none.

**Synthesis**: this cycle answers cycle 53's queued question with a
clean **no, these do not unify -- and here is precisely why, in the same
formal vocabulary cycle 53 used**, which this project's culture (cycles
38-40, 45-53) treats as fully legitimate rather than an artificial
unification to force through. The two negative results that look
superficially similar ("some quotient invariant fails, `Incidence`
instance involved") are actually dual in every load-bearing respect:
cycle 53's mechanism needs a **partial** collapse (at least two
distinguishable classes, one of them a non-singleton class containing
`unit`) and indicts a **congruence** law (`unit_left`, `glue`-level);
this cycle's mechanism needs a **total** collapse (`Subsingleton`,
zero distinguishable classes) and indicts a **shape** law
(`well_founded`, which has no congruence-style analogue among
`GlueInvariant`/`BoundaryInvariant`/`GuardInvariant` at all, since none
of those ever ask about self-loop-freeness). A classification can be
perfectly congruence-respecting (`BoundaryInvariant` AND `GlueInvariant`
both true, as proven here) and still admit no actual quotient
`Incidence`, because `well_founded` is orthogonal to congruence -- it
constrains the *shape* of whatever boundary function is chosen, not its
*agreement* across `≈`-classes. This sharpens (rather than merely
repeats) cycle 39's synthesis: cycle 39 established Subsingleton
quotients are dead via `well_founded` alone; this cycle establishes
*why the natural competing explanation (cycle 53's mechanism) cannot
be the reason instead* -- closing the possibility, left open by cycle
53's phrasing, that the two negative results were secretly one
phenomenon. The methodological point: cycle 53's own two-layer pattern
(general lemma, then instance corollaries) transfers cleanly to state
the *contrast* just as rigorously as it stated the *unification* --
generality is not intrinsically tied to a positive/unifying answer.

**Next hypothesis (cycle 55, not yet attempted)**: with `GlueInvariant`
(cycle 53) and the Subsingleton/`well_founded` obstruction (this cycle)
both now generalized, three live threads remain. (a) `GuardInvariant`/
`GuardRealization` (cycle 53's queued item (c), still untouched): does
any EXISTING guard definition in this project (`Guards.permissive`,
`prodGuards`, `sumGuards`) have an "absorbing"-style shape analogous to
`glue`'s, worth checking concretely before assuming either the cycle 53
pattern or this cycle's dual pattern transfers -- `Guards.permissive`
(used by `simplexIncidence`/`pathIncidence`/`treeIncidence`) looks
trivially total/non-absorbing by construction, so this may resolve
quickly as "the analogy doesn't apply because the hypothesis pattern
itself doesn't occur," which would itself be worth recording. (b) cycle
50's still-untouched option (i): does `incidenceProd`'s own `guards`
(`prodGuards`) have a blind spot analogous to `incidenceSum`'s (cycles
46-50)? (c) a genuinely new angle this cycle's contrast surfaced: is
there a THIRD regime -- a partial (non-Subsingleton, non-faithful)
collapse where `BoundaryInvariant` or `GlueInvariant` fails not via the
absorbing-unit mechanism but via something closer to this cycle's
shape-based obstruction (e.g. a grading that's well-founded on the
source but degenerates under collapse) -- no existing instance has been
audited for this specific combination, and it would test whether cycle
53's and cycle 54's mechanisms are truly exhaustive of the failure modes
or merely the two most obvious ones.

## Cycle 55

**Hypothesis**: cycle 54's queued option (a) / cycle 53's queued item
(c) -- does any EXISTING `Guards` definition in this project
(`Guards.permissive`, `prodGuards`, `sumGuards`) have an "absorbing"-style
shape analogous to `glue`'s absorbing-unit formula (cycle 53), so that
`GuardInvariant`/`GuardRealization` fail the same way `GlueInvariant`/
`GlueRealization` did for simplex/path/tree -- or does cycle 54's own
tentative guess ("`Guards.permissive` looks trivially total... may
resolve quickly as the analogy doesn't apply") hold up when actually
checked against the concrete `guards` fields, rather than assumed from
the name? Per the task's framing, a rigorous "the pattern doesn't occur,
here is exactly why" finding was to be treated as equally legitimate as
a positive extension.

**Method**: first grepped `Quotient.lean` for `GuardInvariant`/
`GuardRealization` case-sensitively before writing anything, per cycle
54's own explicit uncertainty ("worth checking whether any EXISTING
guard definition... before assuming the analogy transfers... may not
exist and would need to be DEFINED first"). Found both ALREADY DEFINED
(lines ~675-740), built alongside `GlueInvariant`/`GlueRealization` in
the same generic infrastructure, complete with `canonicalGuards`/
`canonicalGuards_unique` and `CanonicalGuardedQuotientIncidenceCoherence`
(~1133-1192) -- and one concrete instance already discharged,
`natBoolProductClassification_guardInvariant` (~1512-1516, over
`NatBoolProductIncidence := incidenceProd natIncidence trivialIncidence`,
guards `prodGuards natIncidence trivialIncidence`). So cycle 53/54's
phrasing ("still untouched", "might not exist") was not quite right --
the notion and one instance predate this cycle; what was actually
untouched was applying it to the three glue sources
(`simplexBisimulationQuotientClassification`/`pathBisimulationQuotientClassification`/
`treeBisimulationQuotientClassification`, cycle 53's own three) plus
`cycleBisimulationQuotientClassification` (cycle 54's Subsingleton
instance). Then read `simplexIncidence`'s/`pathIncidence`'s/
`treeIncidence`'s/`cycleIncidence`'s own `guards` fields directly
(`Simplex.lean:65`, `PathComplex.lean:42`, `Tree.lean:53`,
`Cycle.lean:61`), plus `natIncidence`'s/`trivialIncidence`'s
(`Peano.lean:40`, `GraphModel.lean:30`) for the pre-existing product
instance, rather than trusting cycle 54's "looks trivially total"
phrasing at face value. Also re-read cycles 46/47/50's `Sum.lean` guards
work (`incidenceSum_prod_guards_always_permissive`,
`incidenceProd_sum_guards_depends_on_inc1_only`,
`incidenceSum_guards_diverges_of_inc1_disallows`, `Guards.never`/
`finiteIncidenceNeverGuards`) to check for any non-permissive guards
definition actually attached to a `BisimulationQuotientClassification`
anywhere in the project.

**Result**: **confirmed, sorry-free, first `lake build` attempt --
cycle 54's speculation holds, proved rather than assumed, and
generalizes beyond `Guards.permissive` specifically.** All four of
`simplexIncidence`/`pathIncidence`/`treeIncidence`/`cycleIncidence`'s
`guards` fields are literally `Guards.permissive <I>` (the identical
closed term, confirmed by reading each file, not inferred from the
name); `natIncidence.guards` is `Guards.permissive Nat` and
`trivialIncidence.guards` is `{ allow := fun _ _ => true }` (structurally
identical, spelled inline). `Guards.never` (cycle 50) exists but is used
only in `Sum.lean`'s `sumGuardsExpected`-divergence work
(`finiteIncidenceNeverGuards`), never attached to a
`BisimulationQuotientClassification`. So EVERY `Guards` value this
project has ever attached to an actually-classified `Incidence` -- all
five existing classifications, no exceptions -- reduces to a function
that ignores BOTH its arguments; the polar opposite of `glue`'s
essential-argument-dependent absorbing-unit formula. Added to
`Quotient.lean`, after the `cycleIncidence`-no-coherence section: (1)
`guardInvariant_of_constantGuards`/`guardRealization_of_constantGuards`,
the fully general theorem -- for ANY `Incidence` and ANY
`BisimulationQuotientClassification`, if `inc.guards.allow` is constant
(`= b` for some fixed `Bool` and all argument pairs), `GuardInvariant`
holds, proved by `fun x x' y y' _ _ => (constant x y).trans (constant
x' y').symm` with NO hypothesis about `inc`'s laws at all -- no
`unit_left`-analogue, no fact about `approxBisim` beyond it being some
relation, not even `DecidableEq`-driven case splits, strictly weaker
machinery than cycle 53's mechanism needed. (2)
`guardInvariant_of_permissive`/`guardRealization_of_permissive`,
specializing to `Guards.permissive` (the constant-`true` case) via
`rfl`/`simp` once `inc.guards = Guards.permissive I` is given. (3) eight
one-line corollaries -- `GuardInvariant`+`GuardRealization` for
`simplexBisimulationQuotientClassification`/
`pathBisimulationQuotientClassification`/
`treeBisimulationQuotientClassification`/
`cycleBisimulationQuotientClassification` -- each `permissive := rfl`,
zero case analysis on `SimplexId`/`PathId`/`TreeId`/`CycleId` anywhere,
mirroring cycle 53's "zero new casework" corollary pattern but for a
positive conclusion. `lake build`: 62/62 jobs, clean on first attempt.
`#print axioms` on all twelve new declarations (scratch file fed to
`lake env lean`, then deleted): `guardInvariant_of_constantGuards`
needs nothing; the rest need only `propext`/`Quot.sound`(/
`Classical.choice` for the `Realization`-level and product-instance
ones) -- fully within this project's accepted axiom set, no new axiom
anywhere. Full `./verify.sh` (`lake clean && lake build`, example binary,
repo-wide `axiom`/`sorry`/`sorryAx` grep): passes end to end.

**Synthesis**: cycle 54's queued question resolves in the direction it
tentatively guessed, but the mechanism turns out sharper than "the
absorbing pattern doesn't happen to occur in the guards this project
built" -- it is that `Guards`' `allow : I → I → Bool` field, in EVERY
instance this project has ever classified, is constant, and constancy
of a two-argument function alone (needing no law of `Incidence`, no
property of `approxBisim`, not even that the two arguments come from
`≈`-related pairs) is already sufficient to force `GuardInvariant`. This
is the cleanest possible contrast with cycle 53's `GlueInvariant`
mechanism: `glue`'s absorbing-unit formula broke invariance BECAUSE it
was argument-dependent (`if i = unit then some j else some i` treats its
first argument differently depending on its value, and `unit_left`
forces one specific asymmetric behavior at `unit` that the `else` branch
then contradicts for `unit`'s bisimilar non-unit classmates); `guards`
never gives itself the chance to exhibit that shape in this project,
because every concrete `Guards` value built so far is a constant
(`Guards.permissive`'s `true`, or a conjunction of constants via
`prodGuards`, which stays constant). This is not a coincidence discovered
after the fact but a structural gap: `type_preserve`, the one law
`guards` is actually used for (`IncidencePreservation.type_preserve`/
`GradedIncidenceData.type_preserve`/`IncidenceCandidateData.type_preserve`),
only ever needs `guards.allow i j = true` to unlock `glue`'s
type-consistency obligation -- nothing in this project's obligations
ever needed `guards` to DENY gluing selectively based on which specific
elements are involved (cycle 50's `sumGuardsExpected`/`Guards.never`
work explored what such a selective guard would look like, but as a
counterfactual "expected" definition, never as material actually wired
into a classified instance's own `guards` field). So this cycle's
finding is a genuine, PROVEN instance of cycle 54's speculated "the
analogy doesn't apply because the hypothesis pattern itself doesn't
occur" -- extended into one theorem covering all five of the project's
classifications at once (simplex/path/tree/cycle by direct
`Guards.permissive`, the pre-existing nat/bool product instance by the
same underlying constancy fact, re-derivable from
`guardInvariant_of_constantGuards` too though not re-derived here since
`natBoolProductClassification_guardInvariant` already stood proved) --
rather than a family of separately-checked non-occurrences. Confirms
cycle 53's own methodological point (cycle 54's synthesis) once more:
generality is not intrinsically tied to a positive/unifying answer about
FAILURE -- here the general theorem unifies a POSITIVE (invariant-holds)
conclusion across every existing instance instead.

**Next hypothesis (cycle 56, not yet attempted)**: with `GlueInvariant`
(cycle 53), the Subsingleton/`well_founded` obstruction (cycle 54), and
now `GuardInvariant`'s constancy-driven triviality (this cycle) all
closed, cycle 53's next-hypothesis queue reduces to two live threads,
neither touched by this cycle's guards-focused work. (a) [still open,
cycle 53 item (b) / cycle 54 item (b)] does `incidenceProd`'s own
`guards` (`prodGuards`) have a blind spot analogous to `incidenceSum`'s
(cycles 46-50) -- this cycle established `prodGuards` of two CONSTANT
factors stays constant (hence trivially `GuardInvariant`-respecting via
the same `guardInvariant_of_constantGuards` route), but never
constructed or audited a `prodGuards` instance built from a
NON-constant factor guard, which is a genuinely different question from
anything checked here (cycle 47/50's `sumGuardsExpected`-divergence
work is about `incidenceSum`'s guards ignoring its factors' guards
entirely, a different failure mode than `GuardInvariant`-under-bisimulation).
(b) [cycle 54's item (c), the freshest angle] the still-unaudited THIRD
collapse regime: a partial (non-Subsingleton, non-faithful) quotient
where `BoundaryInvariant`/`GlueInvariant` fails not via cycle 53's
absorbing-unit mechanism but via something closer to cycle 54's
shape/`well_founded`-based obstruction (e.g. a grading well-founded on
the source that degenerates -- develops a cycle or a self-loop -- only
after collapsing into fewer-than-all classes) -- no existing instance in
the project has this specific combination, so this thread would likely
require constructing a new small instance deliberately (mirroring how
cycle 54 had to build `cycleBisimulationQuotientClassification`, which
had never been built before, to test its own hypothesis), not merely
re-deriving from what already exists. (a) is the lower-risk, narrower
next step (audit only, reusing `Sum.lean`'s existing non-permissive
witnesses like `finiteIncidenceNeverGuards`); (b) is the higher-payoff
one flagged repeatedly since cycle 54 without yet being attempted.

## Cycle 56

**Hypothesis**: option (b) from cycle 55's queue (= cycle 54's item (c)),
picked as the higher-payoff primary thread over the lower-risk `prodGuards`
audit (option (a), still open): is there a genuinely THIRD collapse regime,
distinct from both (i) cycles 41/51/52's "well-founded grading survives
collapse-within-grade" (simplex/path/tree -- the quotient's `Incidence`
succeeds, only `glue` realization fails) and (ii) cycles 38/39/54's "total
collapse forces a `Subsingleton`, `well_founded` fails EVERYWHERE"
(`cycleIncidence`)? Concretely: a PARTIAL quotient (more than one class,
fewer than all elements) where the source's grading itself degenerates --
develops a genuine `canonicalBoundary` self-loop -- but confined to ONE
class, while every OTHER class stays perfectly well-founded. Per the task's
own framing, an honest "this notion is vacuous/impossible" finding was to
be treated as equally legitimate as a positive construction.

**Method**: first checked whether any EXISTING graded instance
(`simplexIncidence`/`pathIncidence`/`treeIncidence`) could exhibit this via
a "different, coarser bisimulation collapse" of the SAME source, as the
task's framing suggested trying first. Read `BisimulationQuotientClassification`'s
exact fields (`Quotient.lean`) and `approxBisim`'s definition (`IncidenceTheory.lean:64`,
`∃ rel, IsBisimulation inc rel ∧ rel i j`) closely: `classification.reflects`
forces `classify`'s kernel to equal `≈` EXACTLY, and `≈` is *already* the
union of every bisimulation on a given source (any witnessing `rel` for
`IsBisimulation` trivially implies `approxBisim` pointwise, by definition),
hence the unique coarsest one obtainable from ANY bisimulation. So a
"different collapse of an existing instance" is not merely untried but
STRUCTURALLY UNAVAILABLE -- confirmed this is a real dead end, not an
oversight, before looking for a workaround. This meant a genuinely NEW
source instance had to be built, not a reinterpretation of one already in
the codebase.

Designed the construction from the mechanism, not from a carrier shape:
re-examined `canonicalBoundary_self_loop_of_subsingleton` (cycle 54) and
noticed its actual proof only ever uses `Subsingleton.elim` to get ONE
specific fact -- that a boundary entry's remapped target lands back in the
SAME class as the point whose boundary it's attached to. `Subsingleton`
is a sufficient but not necessary way to produce that fact; the natural
generalization is a LOCAL condition on a single element `x`, independent
of how many classes the rest of the quotient has. Built the general lemma
(`canonicalBoundary_self_loop_of_boundary_within_class`) first, purely
from this observation, before writing any concrete instance. Then designed
the minimal witness for the local condition holding at exactly one class
while genuinely failing to hold globally: cycle 26's 4-cycle (`cycleIncidence`)
already demonstrated that a closed cycle's raw `well_founded` field (only
forbids a *direct* self-loop, `e.i = i`) is satisfiable by a structure with
no base case at all -- scaled that mechanism down to its minimal case (2
elements mutually referencing each other) and combined it, for the first
time, with a structurally DISJOINT well-behaved leaf, to force a genuinely
PARTIAL classification rather than cycle 26's total collapse.

**Result**: **a genuine third regime, confirmed via both a general lemma
and a concrete witness, sorry-free, first `lake build` attempt after two
small fixes (both diagnosed immediately: `Nat.lt_trans` instead of
`.trans` for `<`, and marking the witnessing relation `abbrev` instead of
`def` so `Decidable` instances for `by decide` goals could see through
it).**

(1) `mirrorIncidence : Incidence MirrorId MirrorRole GraphType` (new,
`Quotient.lean`), carrier `MirrorId := m0 | m1 | u`: `m0`/`m1` mutually
reference each other (single boundary entry each, pointing at the other),
`u` is a genuine disjoint leaf (empty boundary). `mirrorIncidence_no_valid_grading`
confirms, as a real non-existence theorem (not merely asserted by
analogy to cycle 26): `{m0, m1}` admits NO `Nat`-valued strictly-decreasing
grading at all -- any such grading would need `grade m1 < grade m0` (from
`m0`'s boundary) AND `grade m0 < grade m1` (from `m1`'s) simultaneously,
`Nat.lt_trans`/`Nat.lt_irrefl` closing the contradiction directly. This
sharpens cycle 26's informal "no base case" observation into an actual
proof that this instance's raw `well_founded` field (satisfied, since
`m0 ≠ m1`) and genuine `GradedIncidenceData`-style well-foundedness
(Nat-gradeable) are DIFFERENT properties -- the first cycle to prove this
gap as a theorem rather than note it in prose.

(2) `mirrorToShape_iff_approxBisim` (via `mirrorRel`, a hand-built
bisimulation combining cycle 51/52's "flat relation on a grade" style with
the new `boundaryMatched_of_one_entry` root-file helper, the natural
1-entry generalization of `boundaryMatched_of_two_entries`/`_of_three_entries`
that no prior single-entry instance had needed as reusable
infrastructure): exactly TWO classes over THREE elements, `{m0, m1}`
(`pairShape`) and `{u}` (`leafShape`) -- a genuinely PARTIAL quotient,
matching cycles 41/51/52's cardinality profile (more than one, fewer than
all) but built from a source with NO valid grading at all, not a
well-founded one.

(3) `mirrorBisimulationQuotientClassification_boundaryInvariant`: `BoundaryInvariant`
HOLDS (both `m0`/`m1` produce syntactically identical remapped boundaries
once classified) -- confirming, exactly as cycle 54 found for `cycleIncidence`,
that the obstruction this cycle finds is NOT a `BoundaryInvariant` failure
(cycle 38's mechanism); it lives one level up, at `well_founded`.

(4) The headline general theorem, `canonicalBoundary_self_loop_of_boundary_within_class`:
for ANY `Incidence`/classification, if some element `x` has a boundary
entry `e` with `classify e.i = classify x` (`e.i` lands in `x`'s OWN
class -- whether `e.i = x` literally or a distinct bisimilar partner),
`canonicalBoundary` self-loops AT `classify x` SPECIFICALLY, regardless of
how many other classes exist. Cycle 54's own theorem
(`canonicalBoundary_self_loop_of_subsingleton`) is re-derived from this as
`canonicalBoundary_self_loop_of_subsingleton_via_local`, confirming the
generalization is genuine (not merely analogous): `Subsingleton` just
forces the local hypothesis to hold at EVERY point via `Subsingleton.elim`,
recovering cycle 54's global conclusion as a special case.

(5) The concrete closing theorem, `mirrorBisimulationQuotientClassification_no_coherence`:
NO `CanonicalQuotientIncidenceCoherence` can be completed for
`mirrorBisimulationQuotientClassification` -- but this time the
classification genuinely has two classes over three elements, not a
`Subsingleton`. The self-loop is confined to `pairShape` (`m0`'s boundary
entry points to `m1`, and `m1 ≈ m0`, so `classify m1 = classify m0`,
`within` closing by `rfl`); `leafShape` (`{u}`) is completely untouched,
its `canonicalBoundary` is `[]`, perfectly well-founded. Since
`CanonicalQuotientIncidenceCoherence` requires `boundary_no_self` to hold
at EVERY class, failing at just the one is already enough to rule out the
whole structure -- the genuinely PARTIAL analogue of cycle 39/54's
total-collapse self-loop this cycle's task asked about.

`lake build IncidenceTheory.Quotient`: succeeded on the second attempt (two
small, immediately-diagnosed fixes noted above), 24/24 jobs. `#print axioms`
on all eight new headline declarations (checked via a scratch file fed to
`lake env lean`, then deleted, and cross-checked against an EXISTING cycle
38 theorem in the same file to confirm the axiom profile is this project's
standing baseline, not an anomaly): `propext`/`Quot.sound` for the
non-`Classical.choice`-involving ones (`mirrorIncidence_no_valid_grading`,
`mirrorRel_isBisimulation`, `mirrorToShape_iff_approxBisim`,
`mirrorBisimulationQuotientClassification_boundaryInvariant`), plus
`Classical.choice` additionally for the `canonicalBoundary`/representative-based
ones (`canonicalBoundary_self_loop_of_boundary_within_class` and its three
downstream uses) -- fully within this project's accepted axiom set, no new
axiom introduced anywhere. Full `./verify.sh` (`lake clean && lake build`,
example binary run, repo-wide `axiom`/`sorry`/`sorryAx` grep): passes end
to end. Also added `boundaryMatched_of_one_entry` to the root file
(`IncidenceTheory.lean`, immediately after cycle 52's `boundaryMatched_of_three_entries`),
a small, natural, reusable addition to the existing 2-entry/3-entry helper
family.

**Synthesis**: the third regime this project's task briefing hypothesized
is REAL, not vacuous -- but it required building a genuinely new instance,
not reinterpreting an existing one, for a reason worth stating precisely:
`BisimulationQuotientClassification.reflects` pins `classify`'s kernel to
`≈` exactly, and `≈` (`approxBisim`) is *by construction* the union of
every bisimulation on a fixed source (the largest one obtainable), so
there is no way to "try a coarser collapse" of `simplexIncidence`/
`pathIncidence`/`treeIncidence` within this project's own quotient
framework -- their quotients are each unique up to relabeling
(`targetEquivalence`), a fact this cycle made explicit rather than assumed.
This closes off half of the task's suggested search space with a clean
structural reason, mirroring this project's culture of checking a
prerequisite before searching blind (cycles 38, 45, 53 all did this same
move). The instance that DOES witness the third regime confirms the
cycle 54/55 contrast's own deeper logic rather than complicating it:
cycle 54 showed `well_founded` is orthogonal to the congruence laws
(`BoundaryInvariant`/`GlueInvariant`) -- a classification can perfectly
respect `≈` and still admit no quotient `Incidence`, because self-loop-freeness
is a SHAPE constraint, not an agreement constraint. This cycle shows that
shape constraint is not an all-or-nothing property of the WHOLE
classification either -- it can fail LOCALLY, at exactly the classes
descending from an ungraded (cyclic) piece of the source, while other
classes descending from genuinely well-founded pieces stay fine
simultaneously, in the SAME classification. The general lemma
(`canonicalBoundary_self_loop_of_boundary_within_class`) makes this
precise: cycle 54's Subsingleton finding was always the "every point"
special case of a fact that is fundamentally local, and this cycle is the
first to state and use the local version, then confirm cycle 54's
own theorem is recoverable from it (not merely similar in spirit). The
construction method is also worth naming: rather than search the existing
codebase for a naturally-occurring third-regime instance (which the
prerequisite check above shows cannot exist among the graded instances,
and no other project instance combines an ungraded cyclic sub-structure
with a disjoint well-founded one), the general mechanism was isolated
FIRST, then the minimal instance was built FROM the mechanism's exact
hypotheses -- a "design from the lemma" approach distinct from cycles
41/51/52's "audit an existing instance, then build the machinery to match"
pattern, closer in spirit to cycle 53's "state the general theorem, then
show existing counterexamples are instances of it" but applied to a
genuinely fresh construction rather than three pre-existing ones.

This is not merely a fourth instance alongside `simplexIncidence`/
`pathIncidence`/`treeIncidence`/`cycleIncidence` -- it is a genuinely
different POINT in the space cycles 38-55 have been mapping: those four
instances are each either fully graded-and-partial (i)-type, or fully
ungraded-and-total (ii)-type; `mirrorIncidence` is the first instance
that is PARTIAL like (i) while containing an ungraded sub-structure like
(ii), and the self-loop obstruction tracks the ungraded piece specifically,
not the partial/total distinction itself. This does not change the
9-item roadmap's percentages (it is squarely a continuation of the
"third generic constructor" / quotient-construction thread cycles 38-55
have mapped, the same scope cycles 45-55 judged did not warrant an ADR
addendum) but it does close a genuine gap in that thread's own
completeness: cycle 55's queue explicitly flagged this combination as
"no existing instance... has this specific combination," and it is now
resolved rather than left as a standing open question.

**Next hypothesis (cycle 57, not yet attempted)**: two live threads. (a)
cycle 50/53/54/55's still-untouched item: does `incidenceProd`'s own
`guards` (`prodGuards`) have a blind spot analogous to `incidenceSum`'s
(cycles 46-50) when built from a genuinely NON-constant factor guard --
cycle 55 established `prodGuards` of two CONSTANT factors stays constant
(trivially `GuardInvariant`-respecting), but never constructed or audited
a `prodGuards` instance from a non-constant factor, a different question
from anything checked in cycles 46-55. This remains the lower-risk,
narrower option, now the ONLY item left on cycle 53's original three-item
queue (`GlueInvariant` generalization done cycle 53; Subsingleton contrast
done cycle 54; `GuardInvariant` done cycle 55; the third collapse regime
done this cycle). (b) a natural follow-up this cycle's general lemma
surfaces: `canonicalBoundary_self_loop_of_boundary_within_class`'s
hypothesis (`classify e.i = classify x`) is about ONE boundary entry --
does an analogous LOCAL fact hold for `GlueInvariant`/`GlueRealization`
(cycle 53's mechanism), i.e. is there a "local" refinement of cycle 53's
own general lemma the way this cycle's finding refines cycle 54's, or
does `GlueInvariant`'s two-argument, congruence-shaped obligation resist
the same kind of localization `BoundaryInvariant`'s single-argument,
shape-shaped one admits -- worth a focused check before assuming either
way, given this cycle's own finding that "local" and "global" versions of
a `well_founded`-style obstruction can differ substantially in scope.

## Cycle 57

**Hypothesis**: cycle 56's queued item (a) = cycle 55's own next-hypothesis
= the last remaining item from cycle 53's original three-item queue,
untouched for three cycles running (54 took the Subsingleton contrast, 55
took `GuardInvariant`'s constancy mechanism, 56 took the third collapse
regime) -- does `incidenceProd`'s own `guards` (`prodGuards`, `Product.lean`,
cycle 31) have a blind spot analogous to `incidenceSum`'s (cycles 46/47/50),
now tested against a GENUINELY NON-CONSTANT factor guard for the first
time, since cycle 55 confirmed every `Guards` value this project has ever
attached to a classified instance is constant?

**Method**: read `Product.lean`'s `prodGuards` directly, not assumed:
`allow := fun (i1, i2) (j1, j2) => inc1.guards.allow i1 j1 &&
inc2.guards.allow i2 j2` -- a literal, unconditional componentwise
`Bool.and`, confirming cycle 47's own reading (`prodGuards` "genuinely
conjoins") and closing off any possibility that the TOP-LEVEL `allow`
value itself could diverge from componentwise `&&` the way
`incidenceSum`'s (a hardcoded `Guards.permissive`, discarding both
factors entirely) diverges from `sumGuardsExpected` -- that specific
question was already answered by inspection, before writing anything.
The genuinely open question, per cycle 55's framing, sits one level up:
does this componentwise `&&` correctly TRANSPORT `GuardInvariant` (guards
respecting `≈`) from the factors to the product for a NON-constant
factor, or does the combination introduce a new blind spot of its own?
Built the required witness fresh (cycle 55's own audit: no existing
instance qualifies) rather than reusing `Guards.never`/
`finiteIncidenceNeverGuards` (cycle 50) as the task's initial framing
suggested -- checked first and rejected: `Guards.never`'s `allow := fun
_ _ => false` is ITSELF constant (the polar opposite of
`Guards.permissive`, not a non-constant function), so it would only
re-derive cycle 55's already-closed constant-guards case, not test
anything new. Built `Guards.diag` instead (`allow i j := decide (i =
j)`), genuinely argument-dependent, and `mirrorDiagGuards` -- cycle 56's
`mirrorIncidence` with ONLY `guards` swapped, everything else (including
`type_preserve := fun _ _ => rfl`) copied verbatim, following cycle 50's
`finiteIncidenceNeverGuards` recipe exactly (`mirrorIncidence.typeFunc` is
the constant `GraphType.unit`, so `type_preserve` never depended on its
guard hypothesis and the same proof term typechecks against any
replacement `guards`). Picked `mirrorIncidence` deliberately over a
from-scratch carrier because it is the project's only instance with a
genuinely NON-TRIVIAL `≈` collapse (`m0 ≈ m1`, cycle 56) -- a fully
faithful carrier (`natIncidence`, `cycleIncidenceFixed`, `≈ ↔ =`) would
make the guard-invariance question VACUOUS, since any function of two
arguments trivially respects plain equality, so it could never exercise
the property under test at all.

**Result**: **prodGuards has NO blind spot of its own -- proven
generically, then confirmed against the concrete non-constant witness,
sorry-free, first `lake build` attempt.** Added to `Quotient.lean`, after
cycle 56's closing theorem (8 new declarations): (1) `Guards.diag` and
`mirrorDiagGuards`. (2) `mirrorRel_isBisimulation_diag`: cycle 56's own
`mirrorRel_isBisimulation` proof term typechecks UNCHANGED at
`mirrorDiagGuards` with no new proof at all, confirming (not merely
asserting) that `IsBisimulation`/`approxBisim` (`IncidenceTheory.lean`)
are defined purely via `typeFunc`/`boundary` and never reference `guards`
-- the guards swap is completely invisible to `≈`. (3)
`mirrorDiagGuards_not_guardInvariant`: the concrete failure this cycle
needed to exist before testing the product -- `m0 ≈ m1` yet `allow m0 m0
= true ≠ false = allow m1 m0`, `decide`-checked. This is the first
hand-built `GuardInvariant` FAILURE in this project's history (cycle 55
showed every existing classified instance's guards trivially satisfies it
because every one is constant); confirms a non-constant guards value can
genuinely break the property, given a non-trivial `≈` to violate. (4) The
headline generic theorem, `incidenceProd_guardInvariant_of_factors`: for
ANY two factors (no constancy hypothesis at all), if each factor's own
guards respects its own `≈`, then ANY classification over their product
has `GuardInvariant` -- proved directly from `incidenceProd_approxBisim_iff`
(cycle 32: `≈` on the product is EXACTLY componentwise `≈`) plus
`prodGuards`'s literal `&&`. Strictly more general than cycle 55's
`guardInvariant_of_constantGuards` (a constant function trivially
satisfies this theorem's hypotheses, so that theorem is the special case,
not an alternative). (5)
`incidenceProd_mirrorDiagGuards_nat_guardInvariant_fails`: the concrete
converse confirmation, mirroring cycle 50's `_diverges_concrete` pattern
-- `incidenceProd mirrorDiagGuards natIncidence`'s ACTUAL guards diverge
on exactly the pair the theorem predicts (`natIncidence`'s permissive
right factor contributes a constant `true`, changing nothing), showing
`prodGuards` PROPAGATES a factor's pre-existing blind spot transparently
rather than hiding or amplifying it. `lake build IncidenceTheory.Quotient`:
24/24 jobs, clean on the first attempt, no fixes needed. `#print axioms`
on all seven new declarations plus `mirrorDiagGuards` itself (scratch file
fed to `lake env lean`, then deleted): all reduce to `propext`/`Quot.sound`
(plus `Classical.choice` for the one existential/`approxBisim`-witness
construction), matching this project's standing accepted axiom set
exactly, no new axiom anywhere. Full `./verify.sh` (`lake clean && lake
build`, 24/24 jobs, example binary run, repo-wide `axiom`/`sorry`/`sorryAx`
grep): passes end to end.

**Synthesis**: this closes the last item of cycle 53's original
three-item queue with a genuinely POSITIVE, asymmetric finding --
`incidenceProd` and `incidenceSum`, this project's two generic
constructors, now have PROVEN opposite behavior at the guards layer, not
merely at the top-level `allow` value (cycle 47's finding) but at the
deeper `GuardInvariant`-transport level cycle 55's queue asked about:
`incidenceSum`'s hardcoded `Guards.permissive` discards both factors'
guards unconditionally (cycles 46/47/50), so its `GuardInvariant`
behavior has nothing to do with the factors at all; `prodGuards`'s
literal componentwise `&&` transports `GuardInvariant` faithfully FROM
the factors, with no independent defect, proven for arbitrary (not merely
constant) factor guards. The task explicitly allowed for an honest
"no blind spot" finding to be as legitimate as a divergence, and that is
the honest result here -- but it required actually building the
non-constant witness cycle 55 flagged as missing (`mirrorDiagGuards`) to
confirm it rather than merely re-observing the already-closed
constant-guards case. A secondary methodological note worth recording:
the task's own suggested reuse of `Guards.never`/`finiteIncidenceNeverGuards`
(cycle 50) as "the non-constant guards factor" was checked and rejected
before use -- `Guards.never` is constant (always `false`), the mirror
image of `Guards.permissive`, not a counterexample to constancy at all;
cycle 50 built it to test `incidenceSum`'s top-level discarding behavior,
a different property than the argument-DEPENDENCE this cycle needed to
test `GuardInvariant`-transport, so a fresh witness (`Guards.diag`) had to
be built rather than reused, mirroring cycle 55's own "checked, not
assumed" methodology. Since the result is a narrow, confirmatory audit
(closing an already-scoped queue item with a positive finding, not
altering the project's overall shape) it does not warrant an ADR
addendum, matching the judgment cycles 45-56 already established for
comparable narrower/positive results.

**Next hypothesis (cycle 58, not yet attempted)**: with all three items
of cycle 53's original queue now closed (`GlueInvariant` generalization,
cycle 53; Subsingleton `well_founded` contrast, cycle 54;
`GuardInvariant` constancy, cycle 55; `prodGuards` non-constant audit,
this cycle) plus cycle 56's independently-surfaced third collapse
regime, the one live thread still queued is cycle 56's item (b): does
cycle 53's `GlueInvariant`-failure mechanism (the absorbing-unit formula)
admit an analogous LOCAL refinement the way cycle 56's
`canonicalBoundary_self_loop_of_boundary_within_class` refined cycle 54's
GLOBAL Subsingleton self-loop theorem -- i.e. is there a version of cycle
53's theorem that applies to a class-LOCAL absorbing pattern rather than
requiring the specific global `unit_left`/`unit_right` law, mirroring the
global→local generalization pattern cycle 56 established for the OTHER
(boundary/well-foundedness) mechanism? `GlueInvariant` is a TWO-argument,
congruence-shaped obligation (`x ≈ x' → y ≈ y' → glue x y` compatible with
`glue x' y'`) unlike `BoundaryInvariant`'s single-argument, shape-shaped
one, so the localization may not transfer mechanically -- worth checking
directly, per this cycle's own experience that reusing a queued framing
without re-verifying its exact shape (`Guards.never`'s constancy, above)
can be a dead end that only a direct read catches.

## Cycle 58

**Hypothesis**: cycle 56's own queued item (b), the last thread left from
the glue/boundary/guards taxonomy cycles 45-57 have been mapping: does
cycle 53's `GlueInvariant`-failure mechanism (`glueInvariant_fails_of_
unit_class_witness`, anchored on the specific distinguished `inc.unit`
element and its universal `unit_left` law) admit a class-LOCAL refinement
the way cycle 56's `canonicalBoundary_self_loop_of_boundary_within_class`
refined cycle 54's GLOBAL `Subsingleton` theorem -- or does `GlueInvariant`'s
TWO-argument, congruence-shaped obligation (unlike `BoundaryInvariant`'s
single-argument, shape-shaped one) resist the same move, per cycle 57's
own explicitly flagged caveat not to assume the pattern transfers
mechanically? Per the task's framing, a precise negative finding (with a
structural reason, not a hand-wave) was to be treated as equally
legitimate as a positive generalization.

**Method**: read `glueInvariant_fails_of_unit_class_witness`'s exact proof
again (`Quotient.lean` ~2575-2595) side by side with cycle 56's
`canonicalBoundary_self_loop_of_boundary_within_class` (~3183-3193), asking
specifically WHAT made cycle 56's generalization possible, rather than
pattern-matching on surface shape. Traced cycle 54's theorem
(`canonicalBoundary_self_loop_of_subsingleton`): its GLOBAL hypothesis was
`Subsingleton Q` -- a CARDINALITY condition on the whole quotient target,
forcing the needed per-point fact (`classify e.i = classify x`) to hold
EVERYWHERE via `Subsingleton.elim`; cycle 56 replaced that cardinality
condition with the per-point fact directly, keeping the conclusion itself
equally local (a self-loop AT one specific class). Then re-examined cycle
53's proof with the same question: is there an analogous CARDINALITY
hypothesis being relaxed? Found there is not -- `glueInvariant_fails_of_
unit_class_witness`'s conclusion (`¬ classification.GlueInvariant`) was
already existential/pointwise from the moment cycle 53 stated it (one
witnessing `x`/`j` pair suffices; nothing quantifies over "every class"),
so there was never a `Subsingleton`-style global cardinality hypothesis to
strip away in the first place -- cycle 57's "two-argument shape" worry,
while a reasonable thing to check, turned out not to be where cycle 53's
theorem was actually global. Located the REAL global dependency instead:
the proof invokes `inc.unit_left`, a law quantified `∀ j` but USABLE ONLY
at the one element `inc.unit`, yet the proof only ever instantiates that
law at the single `j` already fixed by the `xAbsorbs` hypothesis -- the
`∀ j` quantification, and the restriction to `inc.unit` specifically, are
both stronger than the proof needs. Before building anything on this
observation, checked (rather than assumed) whether some OTHER element
could always supply even the FULL `∀ j` version of the property, since if
so the "generalization" would be empty content: proved `unit_unique_full_
left_identity` (two lines, from `inc.unit_right` alone, for every
`Incidence`) -- any `e` with `∀ j, glue e j = some j` is forced to equal
`inc.unit`. So the full-law form really is unit-exclusive; a genuine
generalization has to work at the strictly weaker ONE-POINT level cycle
53's own proof actually uses.

**Result**: **a genuine local generalization exists, confirmed via both a
general lemma and a fresh concrete witness where cycle 53's own criterion
is PROVABLY inapplicable, sorry-free, first `lake build`/`./verify.sh`
attempt.** Added to `Quotient.lean`, after cycle 57's closing theorem (14
new declarations):

(1) `glueInvariant_fails_of_class_witness`/`glueRealization_fails_of_
class_witness`: cycle 53's primitive lemma with `inc.unit`/`unit_left`
replaced by an arbitrary `e : I` and a one-point hypothesis `eIdentityAt :
inc.glue e j = some j` (the exact single fact the original proof used, no
more). The proof term is structurally identical to cycle 53's, with
`inc.unit`/`unit_left j` replaced by `e`/`eIdentityAt` throughout -- no new
proof technique needed, confirming the slack was exactly where the Method
located it.

(2) `glueInvariant_fails_of_unit_class_witness_via_local`: cycle 53's
original theorem re-derived as the special case `e := inc.unit`,
`eIdentityAt := inc.unit_left j` -- confirming the generalization is
genuine, not merely analogous, exactly mirroring cycle 56's own
re-derivation of cycle 54's theorem via `canonicalBoundary_self_loop_of_
subsingleton_via_local`.

(3) `glueLocalIncidence` (new instance, `GlueLocalId := core | e | x |
out`): `core` is `inc.unit`; `e`/`x` mutually reference each other
(cycle 56's `mirrorIncidence` recipe, giving a genuine non-singleton
`≈`-class not containing `unit`); `out`'s boundary entry uses a DIFFERENT
role (`GlueLocalRole.anchor` vs. `e`/`x`'s `.link`) specifically so its
non-bisimilarity to `e`/`x` is a one-step `boundaryCompatible` role
mismatch rather than requiring a deeper argument about what `out`'s own
target bisimulates with. `glue` keeps the usual absorbing-unit shape at
`core` (satisfying `unit_left`/`unit_right`) plus ONE extra local
exception: `glue e out = some out` (the new one-point identity fact, at
`e ≠ inc.unit`) while `glue x out = some x` (the ordinary "absorb self"
behavior, producing the clash `GlueInvariant` needs). `glueLocalIncidence_
unit_class_singleton` proves `inc.unit`'s (`core`'s) `≈`-class here is a
genuine SINGLETON -- so cycle 53's own criterion is PROVABLY inapplicable
to this instance (no witness for it to use), confirming
`glueLocalIncidence_not_glueInvariant`/`_not_glueRealization` (built from
(1) at `e := GlueLocalId.e`, the genuinely new anchor point) exercise
content cycle 53's mechanism could never reach -- mirroring cycle 57's own
discipline of checking `Guards.never` and rejecting it as a dead end
before it was actually used for anything, rather than assuming any
plausible-looking existing/adjacent construction would automatically
transfer.

(4) `unit_unique_full_left_identity`: the precise limiting fact,
confirming the caveat noted in the Method is real and not merely a proof
artifact -- in EVERY `Incidence`, not just the three known glue-formula
instances, an element with the FULL `∀ j` identity property is forced to
equal `inc.unit`.

`lake build IncidenceTheory.Quotient`: 24/24 jobs, clean on the first
attempt, no fixes needed anywhere (unlike cycle 56's two small fixes).
`#print axioms` on all ten headline new declarations (scratch file fed to
`lake env lean`, then deleted, cross-checked against cycle 53's own
`glueInvariant_fails_of_unit_class_witness` in the same run to confirm
the profile matches this project's standing baseline exactly):
`unit_unique_full_left_identity` needs nothing at all; `glueInvariant_
fails_of_class_witness`/`glueInvariant_fails_of_unit_class_witness_via_
local` need only `propext` (IDENTICAL to cycle 53's own theorem's
profile, `[propext]`, confirming the generalization adds no new axiom
dependency); the `Realization`-level and concrete-instance declarations
additionally need `Classical.choice`/`Quot.sound` as usual for this
project's `canonicalGlue`/`Quotient`-based infrastructure. No new axiom
anywhere. Full `./verify.sh` (`lake clean && lake build`, example binary
run, repo-wide `axiom`/`sorry`/`sorryAx` grep): passes end to end.

**Synthesis**: cycle 57's flagged caveat -- that `GlueInvariant`'s
two-argument, congruence shape might block the same "global → local" move
cycle 56 made for `BoundaryInvariant`'s single-argument, shape-shaped
obligation -- turns out not to be the operative obstruction, but checking
it directly (rather than either assuming it blocks the move or assuming
cycle 56's pattern transfers unexamined) is precisely what surfaced the
REAL axis of generalization, which is orthogonal to argument-count
entirely. `GlueInvariant`'s negation was already pointwise/existential
from cycle 53's first statement of it, so there was never a
`Subsingleton`-style cardinality hypothesis of the kind cycle 56 relaxed;
the actual global dependency cycle 53's proof had was on WHICH ELEMENT
could supply the needed identity fact (`inc.unit`, via a law usable only
there), not on HOW MANY CLASSES the classification has. This cycle's
positive result generalizes along that different axis: `inc.unit_left`'s
`∀ j` universal guarantee is stronger than cycle 53's own proof ever used,
and weakening it to the one instantiated point the proof actually needs
is where the genuine slack was -- confirmed to be non-vacuous by
`unit_unique_full_left_identity` (no second element can ever have the
FULL law, so the generalization is only real at the strictly weaker
one-point level) and by `glueLocalIncidence` (a fresh instance where
`inc.unit`'s class is a proved singleton, so cycle 53's own criterion is
mechanically unable to explain the very failure this cycle's new
criterion proves). The methodological lesson mirrors cycle 57's own
(checking `Guards.never` and rejecting it before use) and extends it:
verifying a queued caveat carefully sometimes shows the caveat's SPECIFIC
concern was not the real obstacle, without thereby making the caveat
worthless -- it was the right question to ask, it just had to be checked
against the actual proof term (which hypothesis is doing the global work)
rather than against surface shape (how many arguments the invariant
compares) to find where the true generalization axis was. Given this
thread (`GlueInvariant`/`BoundaryInvariant`/`GuardInvariant` across
quotient constructors) has now run fourteen cycles (45-58) and this
cycle closes the LAST item left on cycle 56's own queue with a genuine
positive result (not a narrower audit or a mixed finding, unlike several
of the intervening cycles), this feels like a natural point to take stock
of the whole thread rather than immediately spawn another item from
within it -- recorded as the primary open question below rather than
decided unilaterally in this cycle's own synthesis.

**Next hypothesis (cycle 59, not yet attempted)**: two candidates, of
different character. (a) a narrower continuation in the same style as
this cycle: `GuardInvariant`'s own failure mechanism (cycle 57's
`mirrorDiagGuards_not_guardInvariant`, a hand-built non-constant-guards
witness) has not yet been checked for a `unit`/distinguished-element
dependency the way `GlueInvariant` (cycle 53, this cycle) and
`BoundaryInvariant` (cycle 54, cycle 56) both were -- worth checking
directly whether `GuardInvariant`'s failure mode has ANY analogous
"which element supplies the behavior" axis at all, or whether (since
`guards.allow` has no law analogous to `unit_left`/`unit_right` binding it
to a specific element) the question is vacuous for a precise, checkable
reason, continuing this thread's practice of checking rather than
assuming either way. (b) the higher-level candidate this cycle's own
synthesis flags: with `GlueInvariant`'s local/global taxonomy now closed
(cycle 53 global, this cycle local), `BoundaryInvariant`'s local/global
taxonomy closed (cycle 54 global, cycle 56 local), and `GuardInvariant`'s
constancy mechanism closed (cycle 55) plus its `prodGuards`-transport
question closed (cycle 57), the glue/boundary/guards/quotient thread
(cycles 45-58) may be at or near a natural stopping point for ITS OWN
scope -- worth a deliberate cycle 59 spent surveying whether a genuinely
NEW fourth axis exists within this thread (option (a) is the concrete
test of that) versus whether the next cycle should instead pick an
entirely different open thread from EARLIER in the project (e.g. the
still-unbuilt `GradedIncidenceData`-level questions cycle 41's own queue
left, or categorical/functorial directions untouched since the cycles
that opened `Coherent.lean`) -- a judgment call this cycle deliberately
leaves open rather than presuming its own thread must continue.

## Cycle 59

**Hypothesis (Part 1)**: cycle 58's queued option (a), the one cheap
confirmatory check flagged before treating the 14-cycle glue/boundary/
guards/quotient-invariant thread (cycles 45-58) as closed: does
`GuardInvariant`'s failure mechanism (cycle 57's `mirrorDiagGuards_not_
guardInvariant`) have any "which specific element" dependency analogous to
`GlueInvariant`'s original `inc.unit`-anchored mechanism (cycle 53) and its
class-local generalization (cycle 58), or is it -- as cycle 58's own
synthesis speculated -- vacuous, because `guards.allow` (the base
`Incidence` structure's `guards : Guards I` field) has no law binding it to
a distinguished element the way `glue` is bound to `unit` via `unit_left`/
`unit_right`?

**Method**: read the base `Incidence` structure field-by-field
(`incidence-theory/IncidenceTheory/Axioms.lean` L17-58) before writing
anything, together with `Guards`'s own definition
(`incidence-theory/IncidenceTheory/Axioms/A9_A13.lean` L9-10),
`GuardInvariant`'s definition (`Quotient.lean` L675-679), cycle 57's
`mirrorDiagGuards`/`mirrorDiagGuards_not_guardInvariant` (`Quotient.lean`
~L3307-3350), and cycle 58's `glueLocalIncidence`/
`glueLocalIncidence_unit_class_singleton` (`Quotient.lean` ~L3509-3660).
Confirmed by direct reading, not assumed: `Guards I` is a BARE one-field
wrapper (`allow : I → I → Bool`) with zero structural laws attached to it at
all -- contrasted directly against `glue`, which the SAME `Incidence`
structure pins down unconditionally at `unit` via `unit_left`/`unit_right :
∀ i, glue unit i = some i` / `glue i unit = some i`. The only place
`guards.allow` appears in any law of `Incidence` at all is `type_preserve :
guards.allow i j → glue i j = some k → typeFunc k = typeFunc i` -- but this
is a CONDITIONAL cross-field constraint (guards/glue/typeFunc must agree
when the guard fires), not a value-forcing law in `unit_left`'s shape; it
never singles out any distinguished element, and places zero constraint on
`guards.allow` wherever its hypothesis is false. So `guards.allow` is free
to be ANY `I → I → Bool` function subject only to this one global
implication. Went one level further than a source-reading confirmation
(matching this thread's established preference for a general theorem over
an instance-by-instance audit): checked `IsBisimulation`/`boundaryMatched`/
`boundaryCompatible` (`IncidenceTheory.lean` L36-66) and found they are
defined using ONLY `inc.typeFunc`/`inc.boundary` -- `guards` (and `glue`/
`unit`) never appear in their definitions at all, a strictly stronger fact
than "no unit_left-analog law for guards".

**Result**: **confirmed vacuous, for the precise structural reason
identified above, plus a strictly stronger general theorem, plus a fresh
concrete witness reusing cycle 58's own unit-singleton instance -- sorry-free,
`lake build`/`./verify.sh` clean after two small fixes (a metavariable
elaboration order issue and a `constructorNameAsVariable` linter rename, both
mechanical).** Added to `Quotient.lean`, after cycle 58's closing block (10
new declarations):

(1) `isBisimulation_eq_of_typeFunc_boundary_eq` / `approxBisim_eq_of_
typeFunc_boundary_eq`: for ANY two `Incidence I R T` values agreeing on
`typeFunc` and `boundary` (regardless of what their `glue`/`unit`/`guards`
are), `IsBisimulation`/`approxBisim` coincide exactly. This is the general
theorem answering cycle 58's question in its strongest form: `≈` is
provably blind to `guards` (and to `glue`/`unit`) in EVERY `Incidence`, not
merely in the instances built so far, so no future instance could ever
smuggle in a hidden guards/distinguished-element coupling through `≈`
either.

(2) `guardInvariant_fails_of_pair_witness`: the direct, structure-free
`GuardInvariant`-failure criterion -- any bisimilar pair `p ≈ p'` plus any
guards disagreement `guards.allow p y ≠ guards.allow p' y` at a shared third
point `y` immediately refutes `GuardInvariant`. Proof is a one-line
unfolding of `GuardInvariant`'s own definition, in sharp contrast to
`glueInvariant_fails_of_class_witness`'s (cycle 58) multi-step
`mappedSourceGlue` argument -- there is no analogous "which element can
supply this fact" question to even ask for guards, because `GuardInvariant`
routes through no law of `Incidence` at all.

(3) `glueLocalDiagGuards`: cycle 58's OWN `glueLocalIncidence` (the instance
whose `unit`/`core` class is a PROVEN singleton, `glueLocalIncidence_unit_
class_singleton`) with only the `guards` field swapped to `Guards.diag`
(cycle 57's non-constant witness guard, `allow i j := decide (i = j)`) --
reusing an existing instance rather than building a fresh carrier, per this
thread's established economy (cycle 57 did the same to `mirrorIncidence`).
`type_preserve := fun _ _ => rfl` carries over unchanged since `typeFunc` is
constant there, so the hypothesis is never used regardless of `guards`.

(4) `glueLocalDiagGuards_typeFunc_eq`/`_boundary_eq` (both `rfl`) plus
`glueLocalDiagGuards_approxBisim_iff`: the guards swap leaves `≈` on this
carrier completely identical to `glueLocalIncidence`'s, an instance of (1)
rather than a fresh bisimulation proof. `glueLocalDiagGuards_unit_class_
singleton`: `unit`'s class is STILL a singleton here, transferred directly
from cycle 58's own lemma through the iff, no new argument needed.

(5) `glueLocalDiagGuardsBisimulationQuotientClassification` (via
`bisimulationQuotientClassificationOfKernel`, reusing `glueLocalToShape`
unchanged) plus `approxBisim_glueLocalDiagGuards_e_x` (`e ≈ x`, both
`.pairShape`) and the closing theorem `glueLocalDiagGuards_not_
guardInvariant`: a genuine `GuardInvariant` failure (`allow e e = true ≠
false = allow x e`, `e ≈ x`) on a carrier where `unit`'s class is PROVABLY
empty of anything else -- so cycle 53/58's own unit-anchored/class-local
criteria are structurally unable to explain this failure; only "guards
carries no law at all" can.

`lake build IncidenceTheory.Quotient`: clean after two fixes needed on the
first attempt (neither a mathematical issue) -- (a) `guardInvariant_fails_
of_pair_witness`'s implicit `y` needed a named argument (`(y :=
GlueLocalId.e)`) at the call site, since `by decide` alone left a
metavariable Lean couldn't resolve from the expected-type shape; (b)
renamed `guardInvariant_fails_of_pair_witness`'s bound variables from `x
x'` to `p p'`, and `glueLocalDiagGuards_approxBisim_iff`'s from `x y` to `a
b`, to silence the `constructorNameAsVariable` linter (these generic names
happened to shadow the concrete `GlueLocalId.x` constructor already in
scope by this point in the file -- purely cosmetic, cycle 58's own
`glueLocalToShape_reflects` already used `a b` for exactly this reason).
Full `lake build` (62/62 jobs) and `./verify.sh` (clean rebuild, example
run, repo-wide `axiom`/`sorry`/`sorryAx` grep) both pass end to end.
`#print axioms` on all nine new declarations (scratch file fed to `lake env
lean`, then deleted): the two pure `≈`-structural theorems ((1) above) need
NO axioms at all; everything downstream needs only `propext`/`Quot.sound`
(the `Quotient`-based classification infrastructure's usual profile,
matching cycle 57/58's own baselines exactly). No new axiom anywhere.

**Synthesis**: cycle 58's speculation is confirmed, and for a stronger
reason than merely "no counterexample found" -- `GuardInvariant`'s failure
mechanism is STRUCTURALLY simpler than `GlueInvariant`'s along two
independent, both now-proven axes: `Guards I` carries no law at all (source
level), and `≈` itself cannot see `guards` in any `Incidence` whatsoever
(semantic level, strictly stronger, and new content beyond what cycle 58's
question asked). Reusing cycle 58's own `glueLocalIncidence` for the
concrete witness (rather than building a fourth fresh carrier) both saved
effort and gave the sharpest possible confirmation, since that instance's
`unit`-class-singleton proof was already on hand. With this check complete,
every thread cycle 53's original three-item queue and its cycles 54-58
follow-ons raised is now closed: `GlueInvariant` (global cycle 53, local
cycle 58), `BoundaryInvariant`/`well_founded` (global cycle 54, local cycle
56), `GuardInvariant` (constancy cycle 55, `prodGuards`-transport cycle 57,
element-independence this cycle). This closes the 15-cycle (45-59)
glue/boundary/guards/quotient-invariant thread. No ADR addendum: this is a
narrow, positive, confirmatory result that closes an already-scoped queue
item without changing the 9-item roadmap's status or percentages, and the
existing 2026-07-14 addendum (cycle 45-58 synthesis) already summarizes this
whole thread's shape -- adding a one-line "and cycle 59 confirmed the last
open sub-question" would not meet the bar this project has consistently
applied (cycles 45-58 individually skipped addenda for exactly this reason;
only the 14-cycle cumulative sweep warranted one).

**Hypothesis (Part 2, scouting only -- not attempted this cycle)**: with the
glue/boundary/guards/quotient-invariant thread now genuinely closed (15
cycles, 45-59), spent the remainder of this cycle surveying the ADR's
9-item roadmap (`docs/adr/2607100600-inc-theory-maturity-cycle41.md`,
"完成へ向けた9項目ロードマップ" section) plus a skim of this log's early arc
(cycles 1-44, titles/hypotheses only) to find a genuinely fresh, well-scoped
candidate for cycle 60, distinct from the family this session spent cycles
41-59 on.

**Method/findings (Part 2)**: cycles 1-44 (skimmed, not re-derived) cover:
(1-41) the T5-translation/faithfulness/∂²/generic-constructor arc across
`natIncidence`/`pairIncidence`/`pathIncidence`/`cycleIncidence`/
`treeIncidence`/`simplexIncidence` plus `incidenceSum`/`incidenceProd`/
quotient constructions -- this is roadmap item 5 (Quotient構成)'s
prehistory, continued by 45-59; (42-44) the constructive-reals analysis arc
(extreme value theorem, Rolle, mean value theorem in
`incidence-theory/IncidenceTheory/Reals.lean`) -- roadmap items 3-4, both
marked 完了 in the ADR's cycle-42/43/44 addenda. Checked the ADR's remaining
未完/部分完了 items (6, 7, 8, 9) against actual repo content before
recommending any of them, per this task's explicit instruction not to
recommend blind:

- Item 6 (dependent raw syntax → semantic Pi/Sigma/Id full interpretation/
  soundness bridge) and item 7 (incidence/resonance ↔ internal-logic ↔
  analysis integration): checked `incidence-theory/IncidenceTheory/
  CrossInstance.lean` (24,028 lines) and `incidence-theory/IncidenceTheory/
  Logic.lean` (6,221 lines) directly rather than assuming "未完/部分完了"
  means "empty". Both are FAR from empty: `CrossInstance.lean` already has
  an extensive `IncDepRaw*`-prefixed dependent raw syntax layer (renaming,
  substitution, `IncDepRawSubstitutionFiberModel.preserveFormation_pi`/
  `preserveTyping_variable`, `IncDepRawTypingSemanticResult.pi_beta`/
  `sigma_first_beta`/`sigma_second_beta`/`identity_J_beta`, closed-semantic-
  result interpretation defs) already built out to a substantial partial
  bridge; `Logic.lean` already has full `KripkeModel`/`KripkeForces`/
  pullback-naturality machinery. Picking either as a cycle-60 starting point
  would require a large, costly audit of tens of thousands of existing lines
  just to locate the actual gap before any new proof work could start -- a
  poor "well-scoped, cheap first step" candidate, unlike Part 1 above.
- Item 9 (conservativity/interpretability final theorem): explicitly
  described in the ADR itself as requiring "specify the target foundational
  system, its syntax/semantics, theorem preservation, and reflection or
  conservativity" -- a large, ill-defined meta-question, not actionable as a
  single well-scoped cycle.
- Item 8 (linear algebra / abstract algebra / topology / measure theory
  reconstruction, ADR: "これら四領域の体系的ライブラリと主要定理群は未構成" --
  NOT YET BUILT): checked directly and confirmed genuinely, concretely
  empty for THREE of the four sub-areas. `Matrix` itself
  (`incidence-theory/IncidenceTheory/Axioms/Basic.lean` L30: `def Matrix (m :
  Type u) (n : Type v) (α : Type w) := m → n → α`) has ZERO operations
  defined on it anywhere in the repo (no `Matrix.add`/`Matrix.mul`/
  `Matrix.transpose`/determinant/rank/basis/eigenvalue -- grepped for
  `structure Group`/`VectorSpace`/`Topology`/`Measure`/`Ring`/`Field`
  project-wide: zero hits). What DOES exist and should NOT be confused with
  this: (a) `boundaryMatrix`/`laplacian` (`incidence-theory/
  IncidenceTheory.lean` L645-659) are concrete, narrow, `intListSum`-based
  formulas specific to graph-Laplacian computation from an `Incidence`'s own
  `boundary` field, used throughout `GraphModel.lean` (2,884 lines, row/
  column-sum-zero and symmetry theorems) -- NOT a general matrix-algebra
  library; (b) `Axioms/A14_A17.lean` L16 has a COMMENT "A17: Laplacian (B^T @
  B)" that is never actually formalized or connected to `boundaryMatrix` via
  any real matrix multiplication -- this gap is a ready-made, concretely
  falsifiable/provable first theorem once general matrix multiplication
  exists; (c) `IncidenceTheory/Integers.lean` (`integerAssociativeResonanceSpec`/
  `integerAdditiveGroupResonanceSpec`/`integerDistributiveResonanceSpec`,
  built on Lean-core `Int`, no mathlib) shows this project already has a
  reusable GENERIC `*ResonanceSpec` framework for group/ring-shaped algebraic
  laws (defined generically over any `Incidence`, `Axioms`/`Coherent.lean`-
  adjacent), demonstrated so far only for one instance -- a real head start
  for the "abstract algebra" sub-area, but topology and measure theory have
  no analogous starting scaffolding at all, and linear algebra (vector
  spaces / matrices with actual arithmetic) has none either. Also considered
  and explicitly ruled out cycle 58's own two alternative candidates:
  `GradedIncidenceData`-level questions are NOT fresh -- that exact structure
  (`Quotient.lean` L976) was the primary machinery cycles 41/45-58 already
  mined heavily (`treeShapeGradedIncidenceData`, `pathShapeGradedIncidenceData`,
  etc.), so continuing it would just re-enter the just-closed family;
  `Coherent.lean`'s categorical/functorial direction is actually roadmap item
  7 (it packages `ChainComplexPushoutIncidence`/`CompletePropositionalInternalLogic`
  together), already substantially built per the `CrossInstance.lean`/
  `Logic.lean` audit above, so it has the same "large audit before any new
  proof" cost problem as items 6/7 rather than being a clean blank slate.

**Recommendation for cycle 60**: **roadmap item 8, linear algebra
sub-thread, starting from general matrix arithmetic on the existing
`Matrix` type.** Concrete first steps for a future agent with no other
context: (1) Read `incidence-theory/IncidenceTheory/Axioms/Basic.lean` L30
(`Matrix`'s bare definition) and `incidence-theory/IncidenceTheory.lean`
L645-716 (`boundaryMatrix`/`laplacian`/`intListSum` and its already-proven
algebra: `intListSum_add`, `intListSum_mul_left`, `intListSum_gram_row_
swap`, plus more nearby) -- this finite-sum library is the natural
summation primitive to reuse, not something to rebuild. (2) Define
`Matrix.add`/`Matrix.mul` (for `List I`-indexed, not necessarily square,
matrices over `Int`, matching this project's existing `Int`-based,
mathlib-free style, e.g. as used in `Integers.lean`) using `intListSum` for
the multiplication's inner sum, and `Matrix.transpose`. Prove the basic
laws a future "vector space/ring" layer would need: associativity/
distributivity of `Matrix.mul` over `Matrix.add` (reusing `intListSum_add`/
`intListSum_mul_left` directly rather than re-deriving finite-sum algebra
from scratch), and existence of an identity matrix. (3) The natural,
already-motivated FIRST connecting theorem back into existing project
content (giving this new thread an immediate, concrete payoff rather than
an abstract library nobody uses yet): formalize `Axioms/A14_A17.lean` L16's
currently-unformalized comment "A17: Laplacian (B^T @ B)" as an actual
theorem, `laplacian inc idx = Matrix.mul (Matrix.transpose (boundaryMatrix
inc idx)) (boundaryMatrix inc idx)` (indices/argument order to be worked out
against `laplacian`'s actual definition, `IncidenceTheory.lean` L656-659,
which already computes `∑ k, b k i * b k j` via `idx.foldl` -- this is
already LITERALLY `(Bᵀ B) i j` restricted to `idx`, so the theorem should
follow readily once `Matrix.mul` is defined compatibly, likely `rfl` or a
short `intListSum`-based rewrite). (4) Only after this lands, consider
whether to continue toward vector spaces/rank/determinant (deeper into item
8) or stop there and let a later cycle pick topology/measure-theory (which,
per the audit above, have literally no existing scaffolding at all and
would need a scoping decision of their own -- likely too large for a single
cycle 60 without first seeing how the matrix-arithmetic step goes). This
direction is distinct in kind from cycles 41-59 (no `BisimulationQuotientClassification`/
`GlueInvariant`/`GuardInvariant`/`approxBisim` machinery involved at all),
concretely well-scoped (a handful of definitions plus finite-sum-algebra
lemmas already half-available), and has a ready-made motivating theorem
(the unformalized B^T@B comment) rather than requiring the next agent to
invent its own motivating question from scratch.
