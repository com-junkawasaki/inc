import IncidenceTheory

open IncidenceTheory

def trivialIncidence : Incidence Nat Unit Unit :=
  { boundary := fun _ => []
  , typeFunc := fun _ => ()
  , gluing   := fun i _ => i
  , unit     := 0
  }

def demo : IO Unit := do
  let inc := trivialIncidence
  let a := 1
  let b := 2
  let c := glue inc a b
  -- Type-check basic lemmas
  let _ : approx inc a a := approx_refl inc a
  let _ : approx inc a b := And.intro rfl rfl
  let _ : approx inc b a := approx_symm (And.intro rfl rfl)
  let _ : approx inc a a := approx_trans (And.intro rfl rfl) (And.intro rfl rfl)
  IO.println s!"glue(1,2) = {c}"

def main : IO Unit := demo
