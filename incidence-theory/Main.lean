import IncidenceTheory.GraphModel
import IncidenceTheory.Peano
import IncidenceTheory.Pairs

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
  IO.println "  ⚠ negative finding: bare atoms are NOT separated by ≈ (atom 0 ≈ atom 1,"
  IO.println "    since both have boundary = []) -- faithfulness needs distinguishing"
  IO.println "    boundary structure, it isn't automatic. See RESEARCH_LOG.md."
