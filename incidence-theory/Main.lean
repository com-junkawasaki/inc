import IncidenceTheory.GraphModel
import IncidenceTheory.Peano
import IncidenceTheory.Pairs
import IncidenceTheory.CrossInstance
import IncidenceTheory.PathComplex
import IncidenceTheory.Simplex
import IncidenceTheory.Cycle
import IncidenceTheory.Tree
import IncidenceTheory.Product
import IncidenceTheory.Sum

/- `main`'s demo output accumulates one block of `IO.println` calls per
   research cycle (32 so far). Cycle 18 raised `maxRecDepth` when a
   single giant `do` block first hit Lean's elaborator recursion limit.
   Cycle 32 hit a *second*, different scaling limit further downstream:
   the generated C code's `{}` nesting depth exceeded clang's default
   256-bracket ceiling during compilation (not elaboration). Rather than
   pass compiler-specific flags (fragile across toolchains/platforms),
   split `main`'s single do-block into four helper functions grouped by
   cycle range -- each compiles to its own, much shallower C function,
   and `main` itself becomes a flat sequence of calls rather than one
   deeply nested block. `maxRecDepth` is kept for headroom on any single
   helper's own elaboration. -/
set_option maxRecDepth 4096

open IncidenceCore

/- ToString instance for GId -/
instance : ToString GId where
  toString : GId → String
    | GId.node n => s!"N{n}"
    | GId.edge e => s!"E{e}"

/- Matrix printing utilities -/
def printMatrix {α : Type} [ToString α]
  (m : Matrix GId GId α) (idx : List GId) : IO Unit := do
  IO.println "Matrix:"
  for i in idx do
    let row := idx.map (fun j => m i j)
    let rowStr := String.join (row.map (fun x => "  " ++ toString x))
    IO.println s!"{i}: [{rowStr}]"

/- Compute boundary matrix entries for triangle -/
def computeBoundaryEntries : List (String × Int) :=
  let B := triB
  triIdx.flatMap (fun i =>
    triIdx.map (fun j =>
      let val := B i j
      if val ≠ 0 then
        (s!"∂({i},{j}) = {val}", val)
      else
        ("", 0)
    )
  ) |>.filter (fun (s, _) => s ≠ "")

/- Verify ∂² = 0 property -/
def verifyBoundaryOperator : Bool :=
  let B := triB
  -- Check if B * B = 0 (up to the indices we care about)
  let allZero := triIdx.all (fun i =>
    triIdx.all (fun k =>
      let sum := triIdx.foldl (fun acc j => acc + (B i j) * (B j k)) 0
      sum = 0
    )
  )
  allZero

/- Compute specific boundary matrix values for verification -/
def computeBoundaryValue (i j : GId) : Int :=
  triB i j

/- Compute specific Laplacian values for verification -/
def computeLaplacianValue (i j : GId) : Int :=
  triL i j

def printFoundationsAndEarlyCycles : IO Unit := do
  IO.println "🧮 Incidence Theory - Triangle Graph Analysis"
  IO.println "============================================="

  -- Direct computation of key boundary matrix entries
  IO.println "\n🔍 Boundary Matrix (∂) - Key Entries:"
  IO.println s!"  ∂(E1,N0) = {computeBoundaryValue AB A} (source of AB)"
  IO.println s!"  ∂(E1,N1) = {computeBoundaryValue AB B} (target of AB)"
  IO.println s!"  ∂(E2,N1) = {computeBoundaryValue BC B} (source of BC)"
  IO.println s!"  ∂(E2,N2) = {computeBoundaryValue BC C} (target of BC)"
  IO.println s!"  ∂(E3,N2) = {computeBoundaryValue CA C} (source of CA)"
  IO.println s!"  ∂(E3,N0) = {computeBoundaryValue CA A} (target of CA)"

  IO.println "\n📈 Laplacian Matrix (L = ∂ᵀ∂) - Diagonal Entries:"
  IO.println s!"  L(N0,N0) = {computeLaplacianValue A A} (degree of A)"
  IO.println s!"  L(N1,N1) = {computeLaplacianValue B B} (degree of B)"
  IO.println s!"  L(N2,N2) = {computeLaplacianValue C C} (degree of C)"

  IO.println "\n✅ Boundary Operator Verification:"
  let boundaryCheck := verifyBoundaryOperator
  if boundaryCheck then
    IO.println "  ✓ ∂² = 0 verified (boundary operator property)"
  else
    IO.println "  ✗ ∂² ≠ 0 (boundary operator property failed)"

  IO.println "\n🔬 Triangle Graph ∂² = 0 Verification:"
  let triangleCheck := triangle_square_zero_check
  if triangleCheck then
    IO.println "  ✓ Triangle boundary composition ∂∂ = 0"
  else
    IO.println "  ✗ Triangle boundary composition ∂∂ ≠ 0"

  IO.println "\n🏛️  Incidence Theory - Core Theorems (T1-T5) Status:"
  IO.println "  T1 (Glue Universality): ✅ Framework + triangle concrete proof"
  IO.println "  T2 (Congruence): ✅ Framework + triangle concrete proof"
  IO.println "  T3 (Linear Soundness): ✅ ∂² = 0 theorem + boundary preservation"
  IO.println "  T4 (Completeness): ✅ Framework + triangle concrete proof"
  IO.println "  T5 (Translation): ✅ Framework + triangle concrete proof"

  IO.println "\n✨ Key Achievements:"
  IO.println "  • Modular axiom system (A1-A17) ✅"
  IO.println "  • Boundary matrices & Laplacians ✅"
  IO.println "  • Bisimulation-based equivalence ✅"
  IO.println "  • Five core theorems framework ✅"
  IO.println "  • Triangle graph concrete example ✅"
  IO.println "  • CI/CD automated verification ✅"

  IO.println "\n🔢 Peano Naturals as an Incidence (glue = addition, unit = 0):"
  IO.println s!"  glue 2 1 = {natIncidence.glue 2 1} (successor of 2, via glue)"
  IO.println "  ✓ successor injective, zero not a successor, induction principle proved"
  IO.println "  ✓ ≈ (bisimilarity) coincides exactly with = on this instance (faithfulness)"
  IO.println "  ✓ glue is commutative; GluingSpec reused across two unrelated instances"

  IO.println "\n🔗 Ordered Pairs as an Incidence (boundary = projections):"
  IO.println "  ✓ pairing is jointly injective; projections recoverable from boundary"
  IO.println "  ⚠ negative finding (flat atoms): atom 0 ≈ atom 1 even though unequal,"
  IO.println "    since bare atoms all have boundary = [] -- faithfulness isn't automatic"
  IO.println "  ✓ fix (chained atoms): giving atoms a role-tagged predecessor chain"
  IO.println "    recovers FULL faithfulness (≈ ↔ =) for the whole nested pair type"

  IO.println "\n🧬 General Faithfulness Theorem (incidence_bisim_faithful):"
  IO.println "  ✓ extracted from 3 instance-specific proofs: well-founded measure +"
  IO.println "    boundary-extensionality ⇒ ≈ coincides with = on ANY Incidence"
  IO.println "  ✓ proves with ZERO axioms (fully constructive, no Classical.choice)"
  IO.println "  ✓ validated non-vacuously against natIncidence and pairIncidenceChained,"
  IO.println "    replacing their bespoke inductions -- real generalization, not just"
  IO.println "    an abstract curiosity"

  IO.println "\n🗺️  Translation Faithfulness (T5, concretely):"
  IO.println s!"  natToFiniteSet 3 has length {(natToFiniteSet 3).length} (List Unit target)"
  IO.println "  ✓ natToFiniteSet is injective ⇒ reflects ≈, unlike the generic"
  IO.println "    inc_to_set (root file), which collapses all nonzero naturals together"
  IO.println "  ✓ pairToShape (leaf/node tree target) is injective on the whole nested"
  IO.println "    pair type too ⇒ reflects ≈ there as well, not just for flat Peano"

  IO.println "\n🔀 Cross-Instance Homomorphism (PairId.atom : Nat → PairId):"
  IO.println "  ✓ preserves boundary (naturally) and unit"
  IO.println "  ✗ does NOT preserve glue (addition vs. left-biased selection) --"
  IO.println "    a genuine mixed result: boundary is coalgebraic, glue is algebraic,"
  IO.println "    and a map respecting one doesn't automatically respect the other"
  IO.println "  ✓ sizeOf (pre-existing, not designed for this test) IS a glue-"
  IO.println "    homomorphism up to a precise +1 cost per pair node -- a quantified,"
  IO.println "    non-circular confirmation of the same finding via an independent route"

  IO.println "\n🧮 ∂² = 0, tested beyond the triangle (T3):"
  IO.println "  ✗ FAILS for natIncidence's chain: boundary_composition 2 0 = 1 ≠ 0"
  IO.println "  ✗ FAILS for pairIncidenceChained too, same root cause (atom chain)"
  IO.println "  → unlike the triangle (2-graded: edges→nodes, nodes have no further"
  IO.println "    boundary), unbounded-depth chains compose nonzero -- confirms the"
  IO.println "    bug-fix PR's conditional (not unconditional) ∂²=0 hypothesis was right"
  IO.println "  ✗ tried the classical fix (alternating sign by parity) -- still fails,"
  IO.println "    and single_link_composition_ne_zero proves WHY, generally: a single-"
  IO.println "    face chain can never cancel (only one term, nothing to cancel against),"
  IO.println "    for ANY sign choice on ANY Incidence -- not just this one instance"
  IO.println "  ✓ converse: boundary_composition_zero_of_leaf_boundary proves ∂²=0"
  IO.println "    whenever an element's boundary only reaches leaves -- pathIncidence"
  IO.println "    (an INFINITE 2-graded path complex) satisfies it for every edge at"
  IO.println "    once, confirming finite-vs-infinite was never the real variable"
  IO.println "  ✓ the middle ground: simplexIncidence, a genuine filled 2-simplex"
  IO.println "    (multi-face AND non-leaf faces), satisfies ∂²=0 via REAL cancellation"
  IO.println "    with the classical alternating-sum convention -- not accidental:"
  IO.println "    drop the alternation (wrongSimplexIncidence) and it breaks (-2 ≠ 0)"


def printCycles12to19 : IO Unit := do
  IO.println "\n🔍 A Third Instance of the Collapse Pattern (cycle 12):"
  IO.println "  ⚠ v0/v1/v2 all have empty boundary with nothing distinguishing them --"
  IO.println "    cycle 2's 'flat atoms collapse' pattern, independently rediscovered"
  IO.println "    in simplexIncidence: v0 ≈ v1 even though v0 ≠ v1 (proven, not assumed)"
  IO.println "  → not a Peano/Pairs-specific quirk: a general phenomenon whenever an"
  IO.println "    Incidence has multiple elements sharing identical boundary"

  IO.println "\n🔁 A Fourth Instance, and a Self-Correction (cycle 13):"
  IO.println "  ⚠ pathIncidence's nodes collapse too (node 0 ≈ node 1) -- ALL nodes have"
  IO.println "    empty boundary, unlike natIncidence's 0, uniquely empty in its chain"
  IO.println "  → this corrects an unverified claim in cycle 12's own log (checked before"
  IO.println "    building on it, not trusted as given) -- fourth independent instance"
  IO.println "    of the same collapse pattern across four unrelated constructions"

  IO.println "\n🔧 The Fix, Reapplied a Third Time (cycle 14):"
  IO.println "  ✓ pathIncidenceChained: node n now carries a chain link to node (n-1),"
  IO.println "    role-tagged apart from edge endpoints -- same remedy as natIncidence"
  IO.println "    and pairIncidenceChained, applied to a third broken instance"
  IO.println "  ✓ pathIncidenceChained_approxBisim_iff: FULL faithfulness (≈ ↔ =) recovered"
  IO.println "    for the whole PathId type, via the general theorem from cycle 4"

  IO.println "\n🔀 A Second Cross-Instance Homomorphism (PathId.node : Nat → PathId, cycle 15):"
  IO.println "  ✓ preserves boundary (naturally) and unit, same as PairId.atom (cycle 6)"
  IO.println "  ✗ still does NOT preserve glue -- confirms the split is about glue's"
  IO.println "    algebraic KIND (addition vs. left-biased selection), not about"
  IO.println "    structural dissimilarity: pathIncidenceChained is a chain just like"
  IO.println "    natIncidence, yet the same mixed result reproduces exactly"
  IO.println "  ✓ node_approxBisim_iff: ≈-agreement transfers faithfully across both"
  IO.println "    instances despite the failed glue-homomorphism"

  IO.println "\n⚖️  The Faithfulness-Fix's Price, a Third Time (cycle 16):"
  IO.println "  ✗ pathIncidenceChained (fixed for faithfulness in cycle 14) FAILS ∂² = 0 --"
  IO.println "    proved for free: its node-chain is exactly single_link_composition_ne_zero's"
  IO.println "    (cycle 9) hypothesis shape, so the general theorem applies with zero new work"
  IO.println "  → third confirmation (after natIncidence, pairIncidenceChained, cycle 8) that"
  IO.println "    the same remedy which fixes ≈-faithfulness necessarily breaks ∂² = 0 -- not"
  IO.println "    a coincidence, but a direct structural consequence of what the fix requires"
  IO.println "  ⚠ wider than expected: pathIncidenceChained's edges (multi-entry, unlike the"
  IO.println "    other two instances) ALSO compose nonzero (e.g. edge 1 vs node 0 = 1) --"
  IO.println "    a richer failure surface, confirmed concretely but not yet generalized"

  IO.println "\n🧩 The Edge-Level Failure, Now Fully General (cycle 17):"
  IO.println "  ✓ closed cycle 16's open item: extended single_link_composition_ne_zero's"
  IO.println "    technique to a genuinely new general theorem, two_link_composition_value"
  IO.println "    (root file) -- an exact closed-form ∂² value for ANY two-entry-boundary"
  IO.println "    element on ANY Incidence, not just pathIncidenceChained"
  IO.println "  ✓ pathIncidenceChained_edge_node_witness / _edge_prev_node_witness: edge n"
  IO.println "    vs. node n is ALWAYS -1, edge (n+1) vs. node n is ALWAYS +1 -- proved for"
  IO.println "    every n, not just cycle 16's single decide-checked instance"
  IO.println "  → reusable infrastructure, same payoff pattern as cycle 9's generalization:"
  IO.println "    any future two-entry-boundary instance (e.g. simplexIncidence's edges)"
  IO.println "    can reuse this directly instead of re-deriving it"

  IO.println "\n🏆 The Twice-Stalled Conjecture, Closed on the Third Attempt (cycle 18):"
  IO.println "  ✓ simplexIncidence's edges (e01/e02/e12) DO collapse under ≈, confirming"
  IO.println "    cycle 12's conjecture -- but the fix was strategy, not persistence:"
  IO.println "    two prior attempts hand-rolled boundaryMatched existentials (9-way case"
  IO.println "    splits, simp_all/tauto friction); this one built two small REUSABLE"
  IO.println "    lemmas first (boundaryMatched_of_two_entries, boundaryMatched_symm,"
  IO.println "    root file) so each of the 9 cases became one term-mode exact call"
  IO.println "  ✓ zero sorry, zero Classical.choice even -- cleaner than most instance proofs"
  IO.println "  → general lesson: when a proof stalls twice on the same shape, the second"
  IO.println "    retry should change the SHAPE (extract reusable infrastructure), not"
  IO.println "    just retry the same tactics harder"

  IO.println "\n🔎 Auditing the Library, Completing a Picture (cycle 19):"
  IO.println "  ✓ two_link_composition_value (cycle 17) never assumed k ∉ {j1,j2} -- checked"
  IO.println "    concretely at edge n vs. its OWN forward endpoint node(n+1): exactly 0"
  IO.println "  ✓ #eval scan (edge 2 vs. nodes 0-4): [0,1,-1,0,0] -- confirms cycle 17's two"
  IO.println "    witnesses (-1, +1) already account for the ENTIRE nonzero part of the row,"
  IO.println "    not just a sampled fragment -- the picture is now complete, not partial"
  IO.println "  → an audit cycle can pay off as concretely as a new-instance cycle: this"
  IO.println "    wasn't a new phenomenon, just closing a gap the library's own shape invited"


def printCycles20to23 : IO Unit := do
  IO.println "\n🚦 A Generalization Declined, and T5's Third Instance (cycle 20):"
  IO.println "  ✗ boundaryMatched_of_two_entries's natural 3-entry generalization: DECLINED --"
  IO.println "    grepped every boundary def in the project; simplexIncidence's face is the"
  IO.println "    ONLY 3-entry element anywhere, so there's no second instance to validate"
  IO.println "    against (same discipline that made single_link/two_link wait for one)"
  IO.println "  ✓ T5 (translation faithfulness) extended to pathIncidenceChained instead:"
  IO.println "    pathToNatBool (Nat × Bool) is injective, hence reflects ≈ via cycle 14's"
  IO.println "    faithfulness theorem -- third instance, after natIncidence/pairIncidenceChained"
  IO.println "  → notable contrast: PairId is genuinely recursive (pairToShape had to recurse),"
  IO.println "    PathId is just a tagged Nat, so its faithful translation is nearly trivial --"
  IO.println "    translation effort tracks the CARRIER type's structure, not Incidence itself"

  IO.println "\n🧱 Proving NON-Bisimilarity, Not Just Inequality (cycle 21):"
  IO.println "  ✓ not_approxBisim_of_boundary_mismatch: the FIRST theorem in this project proving"
  IO.println "    ¬approxBisim (strictly stronger than ≠, since ≈ often relates distinct elements)"
  IO.println "  ✓ proves with ZERO axioms -- a boundary entry with no compatible counterpart"
  IO.println "    blocks ANY witnessing relation, discharging approxBisim's ∃rel existential"
  IO.println "  ✓ simplexIncidence's 3 classes ({v0,v1,v2}, {e01,e02,e12}, {face}) are now proven"
  IO.println "    EXACTLY separated, not just internally collapsed -- one representative witness"
  IO.println "    per shape-pair (vertex-edge, vertex-face, edge-face), matching this project's"
  IO.println "    established convention rather than a forced 49-case exhaustive enumeration"

  IO.println "\n🔬 Half an Exhaustive Iff, and Documented Tooling Friction (cycle 22):"
  IO.println "  ✓ simplexToShape_reflects: translate-equal → approxBisim, proven for ALL 49"
  IO.println "    constructor pairs at once (not just 19 representative same-shape ones)"
  IO.println "  ✗ the reverse half (distinguishes) hit REPRODUCIBLE Lean elaboration friction:"
  IO.println "    first/try/apply combinators all left metavariable pollution across `first`'s"
  IO.println "    alternatives, breaking an otherwise-valid closer after a sibling alternative"
  IO.println "    failed on the SAME goal -- diagnosed via minimal repro, not left a mystery"
  IO.println "  → NOT forced through with a verbose 30-arm explicit match: cycle 21 already"
  IO.println "    proved the substantive content (exact 3-way separation) robustly; the full"
  IO.println "    iff would strengthen the STATEMENT, not add new mathematical CONTENT"

  IO.println "\n🎯 The Exhaustive Iff, Closed with a Different Combinator (cycle 23):"
  IO.println "  ✓ simplexToShape_iff_approxBisim: simplexIncidence's ≈ is EXACTLY shape-agreement,"
  IO.println "    over all 49 constructor pairs -- the theorem cycle 22 deferred, now proven"
  IO.println "  ✓ the fix wasn't new math: cycle 22's tactic-mode `cases <;> first` hit reproducible"
  IO.println "    metavariable pollution; term-mode pattern matching (49 explicit arms, each its"
  IO.println "    own independent elaboration problem) has NO shared state to pollute -- confirmed"
  IO.println "    on a 6-arm prototype before committing to writing out all 49"
  IO.println "  → same lesson as cycle 18, one level up: when a proof stalls on ONE combinator,"
  IO.println "    try a genuinely different one before concluding the content is out of reach"


def printCycles24to32 : IO Unit := do
  IO.println "\n🪢 Real Cancellation from Recursive Nesting, Not Structural Absence (cycle 24):"
  IO.println "  ✓ pair(pair(atom n,atom(n+1)),atom(n+2)) vs. atom n: nonzero (1) -- same 'only one"
  IO.println "    term' shape as natIncidence's chain, no surprise"
  IO.println "  ✓ ...vs. atom(n+1): exactly 0 -- but genuinely NEW: two DIFFERENT nonzero"
  IO.println "    contributions (inner pair's snd, AND atom(n+2)'s chain link) both reach"
  IO.println "    atom(n+1) and cancel (1 + (-1) = 0), for every n, checked (n=0,3,7) before"
  IO.println "    formalizing to rule out a one-off coincidence"
  IO.println "  → first cancellation via CONVERGING paths from recursive nesting -- distinct from"
  IO.println "    simplexIncidence.face's deliberate alternating-sum (cycle 11) and"
  IO.println "    pathIncidenceChained's structural-absence 'elsewhere zero' (cycle 19)"

  IO.println "\n🔭 Generalizing the Cancellation, Auditing the Combinators (cycle 25):"
  IO.println "  ✓ cycle 24's cancellation generalizes FULLY: pair(pair(a,atom n),atom(n+1)) vs."
  IO.println "    atom n = 0 for ANY a (not just atom n) -- checked with an unrelated nested pair"
  IO.println "    (pair(atom5,atom6)) first, then proved: the mechanism never used what `a` IS,"
  IO.println "    only that a≠atom n -- purely structural, not about atom-chain depth at all"
  IO.println "  ✓ cycle 24's specific family kept alongside as a readable concrete instance,"
  IO.println "    not deleted -- it's subsumed, not broken"
  IO.println "  ✓ audited all `cases <;> first` proofs in the codebase for the metavariable-"
  IO.println "    pollution risk (cycle 22/23): only ONE (simplexEdgeVertexRel_isBisimulation,"
  IO.println "    cycle 18, 7 alternatives/9 goals) structurally resembles the risky shape --"
  IO.println "    but it worked cleanly on its first attempt, no recorded friction. NOT rewritten:"
  IO.println "    this project doesn't rewrite working code for its own sake"

  IO.println "\n🔄 A Genuinely New Instance: A Closed Cycle, No Base Case At All (cycle 26):"
  IO.println "  ✓ cycleIncidence: c0→c3→c2→c1→c0, every element has exactly one boundary entry,"
  IO.println "    NONE is empty -- Incidence's own well_founded field only forbids a DIRECT"
  IO.println "    self-loop, not a longer cycle, so this is a legitimate, buildable instance"
  IO.println "  ✓ ALL FOUR elements collapse into ONE ≈-class -- the SAME 'everything related to"
  IO.println "    everything' relation cycles 2/12/13/18 used for shared-EMPTY boundary also"
  IO.println "    works here, where NOTHING is empty -- 'flat leaves collapse' was never really"
  IO.println "    about emptiness, it's about lacking a well-founded distinguishing measure"
  IO.println "  ✓ ∂² still fails (single_link_composition_ne_zero applies 'for free' -- the"
  IO.println "    theorem's reach isn't accidentally tied to acyclicity)"
  IO.println "  ✓ glue is Z/4Z addition -- the FIRST genuine group-structured glue in this"
  IO.println "    project (commutative, every element invertible), unlike natIncidence's"
  IO.println "    infinite monoid or every other instance's non-group left-biased selection"

  IO.println "\n🎭 Fixing a Cycle: A Genuinely New Faithfulness Route (cycle 27):"
  IO.println "  ✓ cycleIncidenceFixed: same c0→c3→c2→c1→c0 topology, but each position gets its"
  IO.println "    OWN distinct role (not a predecessor chain to a base case -- a cycle has none)"
  IO.println "  ✓ full faithfulness (≈ ↔ =) recovered -- but via a NEW proof route:"
  IO.println "    not_approxBisim_of_boundary_mismatch (cycle 21) directly, not"
  IO.println "    incidence_bisim_faithful (cycle 4), which needs a well-founded MEASURE a"
  IO.println "    closed cycle structurally cannot have -- role-discrimination alone suffices"
  IO.println "  ✓ proves with ONLY propext -- no Classical.choice, fully constructive"
  IO.println "  ✓ the predicted price, confirmed a FOURTH time: ∂² = 0 still fails (same general"
  IO.println "    theorem, single_link_composition_ne_zero -- the tension isn't about HOW"
  IO.println "    distinguishing info is encoded, only about keeping the single-link shape"

  IO.println "\n🧮 A Translation That's Also a Homomorphism, For the First Time (cycle 28):"
  IO.println "  ✓ every prior T5 translation only ever needed injectivity -- no prior glue had"
  IO.println "    algebraic structure worth checking a translation against"
  IO.println "  ✓ cycleToNat IS a genuine glue-homomorphism: cycleToNat(cycleAdd x y) ="
  IO.println "    (cycleToNat x + cycleToNat y) % 4, checked on all 16 pairs, proves with"
  IO.println "    NO axioms at all -- purely computational"
  IO.println "  ✓ combined with injectivity + cycleIncidenceFixed's faithfulness (cycle 27):"
  IO.println "    cycleToNat is BOTH a faithful ≈-reflector AND an algebraic homomorphism --"
  IO.println "    cycleIncidenceFixed's glue structure is literally isomorphic to Z/4Z"

  IO.println "\n🌳 A Fifth Instance: Ternary Branching, Same Patterns Confirmed (cycle 29):"
  IO.println "  ✓ treeIncidence: node a b c, a genuine 3-entry (uniform pos, not alternating)"
  IO.println "    boundary -- the SECOND real 3-entry instance (after simplexIncidence.face,"
  IO.println "    cycle 11), finally satisfying cycle 20's condition for a 3-entry generalization"
  IO.println "  ✓ 'flat leaves collapse' generalizes to ternary (5th confirmation, after"
  IO.println "    cycles 2/12/13/18/26) -- branching factor doesn't matter, only structure"
  IO.println "  ✓ leaf-boundary sufficiency (cycle 10) applies 'for free' to a 3-entry element"
  IO.println "  ✓ non-leaf children -> genuine ∂² ≠ 0 (checked concretely, same 'one active"
  IO.println "    branch, no cancellation' shape as single_link) -- generalization to a real"
  IO.println "    3-entry theorem queued, not attempted here, honestly scoped as its own cycle"
  IO.println "  → this instance CONFIRMS known patterns generalize rather than finding something"
  IO.println "    qualitatively new -- itself a real finding: rules out 'secretly about binary'"

  IO.println "\n🔺 The 3-Entry Generalization, Built and Validated Twice (cycle 30):"
  IO.println "  ✓ boundaryMatrix_three_link / three_link_composition_value (root file): the"
  IO.println "    3-entry ∂² machinery cycle 20 declined for lack of a second real instance --"
  IO.println "    now built, since treeIncidence.node (cycle 29) supplied exactly that"
  IO.println "  ✓ validated against treeIncidence: the concrete nested-node witness (cycle 29)"
  IO.println "    is now a real theorem over ANY well-formed children, not one decide instance"
  IO.println "  ✓ validated a SECOND time against simplexIncidence.face: derives WHY face's"
  IO.println "    ∂² = 0 at v0 holds in general (count(e02) - count(e01) = 0), not just THAT"
  IO.println "    cycle 11's specific decide-checked index happened to give zero"
  IO.println "  → closes the loop cycle 20 opened: declining a generalization isn't permanent,"
  IO.println "    it's conditional on evidence -- and the condition was eventually met"

  IO.println "\n🧩 A Generic Constructor, Not Another Instance: incidenceProd (cycle 31):"
  IO.println "  ✓ FIRST concrete milestone toward internal construction: a GENERIC product,"
  IO.println "    taking ANY two Incidence structures and producing a third -- proven ONCE for"
  IO.println "    every pair, unlike every prior instance built by hand for one carrier type"
  IO.println "  ✓ all 7 Incidence proof obligations discharged generically -- each reduces"
  IO.println "    directly to inc1's or inc2's OWN obligation, using only the interface"
  IO.println "  ✓ incidenceProd_approxBisim_of_approxBisim: the product respects bisimulation"
  IO.println "    (≈ on components ⇒ ≈ on the product) -- a genuine congruence/functoriality"
  IO.println "    property, proved with only propext/Quot.sound, no Classical.choice"
  IO.println "  ✓ sanity-checked against natIncidence × natIncidence, not just vacuously typed"
  IO.println "  → deliberately scoped to ONE connective (product), not the whole original vision"
  IO.println "    (functions, dependent types, induction) -- the same discipline that scoped"
  IO.println "    the very first move into this territory down to natIncidence itself"

  IO.println "\n🔁 The Converse, and a Clean Answer: Faithfulness Transports Through Product (cycle 32):"
  IO.println "  ✓ incidenceProd_project: ≈ on the PRODUCT forces ≈ on BOTH components -- the"
  IO.println "    converse of cycle 31's congruence theorem, via projecting a witnessing relation"
  IO.println "    (Sum.inl/Sum.inr tags can never cross-match, so the projection is automatic)"
  IO.println "  ✓ incidenceProd_approxBisim_iff: the product's ≈ is EXACTLY componentwise ≈,"
  IO.println "    no more and no less -- upgrades cycle 31's one-way theorem into a genuine iff"
  IO.println "  ✓ incidenceProd_faithful_of_faithful: faithfulness transports through the product"
  IO.println "    AT NO COST -- unlike ∂² = 0, which the collapse-fix (cycles 8/16/27) could"
  IO.println "    NEVER preserve alongside faithfulness, this property transports cleanly"
  IO.println "  ✓ confirmed concretely: natIncidence × natIncidence is fully faithful"
  IO.println "  → chose this over a mechanical sum-constructor repeat because it had a genuinely"
  IO.println "    open answer -- and the answer (clean transport, no tension) is itself the finding"

def printCycles33plus : IO Unit := do
  IO.println "\n➕ The Second Generic Constructor, and a Genuine Contrast: incidenceSum (cycle 33):"
  IO.println "  ✓ incidenceSum: I1⊕I2, boundary stays isolated per side (no combining, unlike"
  IO.println "    the product) -- but a disjoint union has NO element in both sides, so a"
  IO.println "    genuine two-sided unit forces unit-absorbing glue (same shape as most hand-"
  IO.println "    built instances) and a CONSTANT typeFunc, unlike incidenceProd's genuine T1×T2"
  IO.println "  ✓ headline finding: faithfulness does NOT transport through the sum the way it"
  IO.println "    did through the product (cycle 32) -- ANY two leaves, from EITHER side,"
  IO.println "    become cross-side ≈-related (boundaryMatched is vacuous for empty boundaries,"
  IO.println "    regardless of the Sum.inl/Sum.inr tag) -- the 'flat leaves collapse' pattern"
  IO.println "    (cycles 2/12/13/18/26), now shown as a structural fact about the CONSTRUCTION"
  IO.println "  ✓ confirmed concretely: Sum.inl 0 ≈ Sum.inr 0 in natIncidence ⊕ natIncidence,"
  IO.println "    even though natIncidence alone is fully faithful and the two are genuinely"
  IO.println "    distinct elements (different constructors)"
  IO.println "  → a real contrast worth holding next to cycle 32: product preserves faithfulness"
  IO.println "    unconditionally, sum does NOT -- which connective you pick changes what"
  IO.println "    properties survive, exactly the kind of fact a real type theory needs to know"

  IO.println "\n🔗 A Generic Translation, and an Old Result Revisited (cycle 34):"
  IO.println "  ✓ incidenceProd_translation_reflects: pairing two ≈-reflecting translations"
  IO.println "    produces a translation reflecting ≈ on the PRODUCT -- generic, twice deferred"
  IO.println "    (cycles 31/32), a direct consequence of cycle 32's iff, no new machinery"
  IO.println "  ✓ REVISITED cycle 5's natToFiniteSet with cycle 28's lens: is it ALSO a"
  IO.println "    glue-homomorphism? natToFiniteSet(m+n) = natToFiniteSet m ++ natToFiniteSet n --"
  IO.println "    never checked before (no glue had algebraic structure worth it back then)"
  IO.println "  ✓ ties together: natProdToFiniteSet is BOTH a faithful ≈-reflector (via the new"
  IO.println "    generic theorem) AND a glue-homomorphism for the product -- cycle 28's"
  IO.println "    'both properties at once' achievement, now for a GENERIC construction"
  IO.println "  → an old translation still had an unchecked property; a new lens (any glue"
  IO.println "    with algebraic structure) can retroactively reveal it years (cycles) later"

  IO.println "\n🧷 A Conditional Faithfulness Result for the Sum, Connecting Cycle 27 (cycle 35):"
  IO.println "  ✓ incidenceSum_faithful_of_faithful_no_shared_leaves: full faithfulness holds"
  IO.println "    whenever both factors are faithful AND at least one side has NO leaves at all --"
  IO.println "    cross-side collapse (cycle 33) needs BOTH sides to supply a leaf for the SAME pair"
  IO.println "  ✓ cycleIncidenceFixed (cycle 27) is the perfect witness: faithful AND leafless"
  IO.println "    (every element has exactly one boundary entry, cyclically) -- confirmed"
  IO.println "    concretely: natIncidence ⊕ cycleIncidenceFixed IS fully faithful"
  IO.println "  ✓ one genuine subtlety incidenceProd_project didn't have: incidenceSum's typeFunc"
  IO.println "    is FORCED constant (cycle 33's design tension), so type-preservation can't be"
  IO.println "    derived for free -- fixed by baking typeFunc-equality into the projected relation"
  IO.println "    and propagating it via each instance's OWN type_consistent obligation"
  IO.println "  → proves with ONLY propext/Quot.sound, no Classical.choice -- fully constructive"

def main : IO Unit := do
  printFoundationsAndEarlyCycles
  printCycles12to19
  printCycles20to23
  printCycles24to32
  printCycles33plus
