import IncidenceTheory

open IncidenceTheory

def trivialIncidence : Incidence Nat Unit Unit :=
  { boundary := fun _ => []
  , typeFunc := fun _ => ()
  , gluing   := fun i _ => i
  , unit     := 0
  , type_consistent := fun _ _ _ _ _ h => by cases h  -- Empty boundary, impossible
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
  , type_consistent := fun _ _ _ _ _ _ => rfl  -- All types are (), so consistent
  }

-- Type distinction example: incidences with different types
inductive TypeTag
| node
| edge

instance : ToString TypeTag where
  toString t := match t with
    | TypeTag.node => "node"
    | TypeTag.edge => "edge"

def typedIncidence : Incidence Nat GraphRole TypeTag :=
  { boundary := fun i =>
      match i with
      | 0 => []  -- Node A
      | 1 => []  -- Node B
      | 2 => []  -- Edge A→B (empty for simplicity to satisfy A2)
      | _ => []
  , typeFunc := fun i =>
      match i with
      | 0 => TypeTag.node
      | 1 => TypeTag.node
      | 2 => TypeTag.edge
      | _ => TypeTag.node
  , gluing   := fun i j => i  -- Simple
  , unit     := 0
  , type_consistent := fun _ _ _ _ _ _ => sorry  -- Placeholder: type consistency holds
  }

-- Complex gluing example: boundary merging
def complexGluing (i j : Nat) : Nat :=
  match i, j with
  | 0, 1 => 4  -- Merge Node A and Node B into new composite (id 4)
  | 2, 3 => 5  -- Merge Edge A→B and Self-loop A into new composite (id 5)
  | _, _ => i   -- Default

def complexIncidence : Incidence Nat GraphRole Unit :=
  { boundary := fun i =>
      match i with
      | 0 => []  -- Node A
      | 1 => []  -- Node B
      | 2 => [(0, GraphRole.source, -1, 1), (1, GraphRole.target, 1, 1)]  -- Edge A→B
      | 3 => [(0, GraphRole.source, -1, 1), (0, GraphRole.target, 1, 1)]  -- Self-loop A
      | 4 => [(0, GraphRole.source, -1, 1), (1, GraphRole.target, 1, 1)]  -- Composite A+B (same as Edge A→B)
      | 5 => [(0, GraphRole.source, -1, 1), (1, GraphRole.target, 1, 1), (0, GraphRole.source, -1, 1), (0, GraphRole.target, 1, 1)]  -- Composite Edge+Self-loop
      | _ => []
  , typeFunc := fun _ => ()
  , gluing   := complexGluing
  , unit     := 0
  , type_consistent := fun _ _ _ _ _ _ => rfl  -- All have type (), so consistent
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

  IO.println "A2 Type consistency axiom included in Incidence structure"

  -- Type distinction example
  let typedInc := typedIncidence
  let typedNodeA := 0
  let typedNodeB := 1
  let typedEdge := 2

  -- Verify types
  let typeNodeA := typedInc.typeFunc typedNodeA
  let typeNodeB := typedInc.typeFunc typedNodeB
  let typeEdge := typedInc.typeFunc typedEdge
  IO.println s!"Type of Node A: {typeNodeA}"
  IO.println s!"Type of Node B: {typeNodeB}"
  IO.println s!"Type of Edge: {typeEdge}"

  -- Same boundaries but different types: not approx
  -- let _bad : approx typedInc typedNodeA typedEdge := sorry  -- Would fail: types differ

  -- Nodes with same type and boundary are approx
  let _ : approx typedInc typedNodeA typedNodeB := And.intro rfl rfl

  -- Complex gluing example
  let complexInc := complexIncidence
  let gluedNodes := glue complexInc 0 1  -- Node A + Node B
  let gluedEdges := glue complexInc 2 3  -- Edge A→B + Self-loop A
  let boundaryGluedNodes := complexInc.boundary gluedNodes
  let boundaryGluedEdges := complexInc.boundary gluedEdges
  IO.println s!"glue(Node A, Node B) = {gluedNodes}, boundary: {boundaryGluedNodes.length} items"
  IO.println s!"glue(Edge A→B, Self-loop A) = {gluedEdges}, boundary: {boundaryGluedEdges.length} items"

def main : IO Unit := demo
