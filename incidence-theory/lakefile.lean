import Lake
open Lake DSL

package "incidence-theory" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

lean_lib "IncidenceTheory" where
  -- builds modules under IncidenceTheory/

@[default_target]
lean_exe "incidence-theory" where
  root := `Main
  supportInterpreter := true
