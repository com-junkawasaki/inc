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

**Next hypothesis (cycle 35, not yet attempted)**: option from cycle
33's queue, not reached this cycle: does `incidenceSum` have a
*conditional* faithfulness result analogous to cycle 32's -- e.g. if
`inc1`/`inc2` are both faithful AND have at most one leaf each (or no
"collapsible" structure shared across sides), does faithfulness hold?
Also newly worth considering: does `incidenceSum` have an analogous
generic translation-pairing result (this cycle's `incidenceProd`
theorem, adapted for a disjoint union -- likely simpler, since a sum
translation would presumably be `Sum.elim t1 t2 : I1 ⊕ I2 → S` rather
than a genuine pairing)? Neither scoped yet.
