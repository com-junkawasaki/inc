import Lake
open Lake DSL

package "incidence-theory" where
  version := v!"0.1.0"

lean_lib IncidenceTheory where
  -- add library configuration options here

lean_exe "incidence-theory" where
  root := `Main
