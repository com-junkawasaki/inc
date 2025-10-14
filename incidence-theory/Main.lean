import IncidenceTheory

open IncidenceTheory

def trivialIncidence : Incidence Nat Unit Unit :=
  { boundary := fun _ => []
  , typeFunc := fun _ => ()
  , gluing   := fun i _ => i
  , unit     := 0
  }

-- Graph structure example: nodes and edges with boundaries
inductive GraphRole
| source
| target

instance : ToString GraphRole where
  toString r := match r with
    | GraphRole.source => "source"
    | GraphRole.target => "target"

def graphIncidence : Incidence Nat GraphRole Unit :=
  { boundary := fun i =>
      match i with
      | 0 => []  -- Node A (empty boundary)
      | 1 => []  -- Node B (empty boundary)
      | 2 => [(0, GraphRole.source, -1, 1), (1, GraphRole.target, 1, 1)]  -- Edge A→B
      | 3 => [(0, GraphRole.source, -1, 1), (0, GraphRole.target, 1, 1)]  -- Self-loop on A
      | _ => []
  , typeFunc := fun _ => ()
  , gluing   := fun i _ => i  -- Simple gluing (left-biased)
  , unit     := 0
  }

def demo : IO Unit := do
  let inc := graphIncidence
  let nodeA := 0
  let nodeB := 1
  let edgeAB := 2
  let selfLoopA := 3

  -- Verify boundaries
  let boundaryNodeA := inc.boundary nodeA
  let boundaryNodeB := inc.boundary nodeB
  let boundaryEdgeAB := inc.boundary edgeAB
  let boundarySelfLoopA := inc.boundary selfLoopA

  IO.println s!"Node A boundary: {boundaryNodeA.length} items"
  IO.println s!"Node B boundary: {boundaryNodeB.length} items"
  IO.println s!"Edge A→B boundary: {boundaryEdgeAB.length} items"
  IO.println s!"Self-loop A boundary: {boundarySelfLoopA.length} items"

  -- Verify approx: same boundaries are approx
  let _ : approx inc nodeA nodeB := And.intro rfl rfl  -- Both empty boundaries

  -- Different boundaries are not approx (type-check fails if we try)
  -- let _bad : approx inc nodeA edgeAB := sorry  -- Would fail: boundaries differ

  -- Glue example
  let glued := glue inc nodeA nodeB
  IO.println s!"glue(NodeA, NodeB) = {glued}"

  -- Approx lemmas
  let _ : approx inc nodeA nodeA := approx_refl inc nodeA
  let _ : approx inc nodeA nodeB := And.intro rfl rfl
  let _ : approx inc nodeB nodeA := approx_symm (And.intro rfl rfl)

def main : IO Unit := demo
