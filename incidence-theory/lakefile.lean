import Lake
open Lake DSL

package "incidence-theory" where
  version := v!"0.1.0"

lean_lib "IncidenceTheory" where
  -- builds modules under IncidenceTheory/

@[default_target]
lean_exe "incidence-theory" where
  root := `Main
  supportInterpreter := true
