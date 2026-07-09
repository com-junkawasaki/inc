import IncidenceTheory.GraphModel
import IncidenceTheory.Peano
import IncidenceTheory.Pairs
import IncidenceTheory.CrossInstance
import IncidenceTheory.PathComplex
import IncidenceTheory.Simplex

/- `main`'s `do` block accumulates one `IO.println` per research cycle
   (18 so far); Lean's `do`-notation desugaring is right-recursive and
   hits the default elaborator recursion limit around this size. Raised
   with headroom for future cycles rather than re-hit and re-raised
   incrementally each time. -/
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

def main : IO Unit := do
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
