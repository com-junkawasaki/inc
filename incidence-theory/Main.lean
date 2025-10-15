import IncidenceTheory.GraphModel

open IncidenceCore

def main : IO Unit := do
  let _ := triIncidence
  let _ := triIdx
  let _ := triB
  let _ := triL
  IO.println "incidence-theory: build ok"
