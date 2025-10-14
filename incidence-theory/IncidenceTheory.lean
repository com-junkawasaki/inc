namespace IncidenceTheory

universe u

structure Incidence (I R T : Type u) where
  boundary : I → List (I × R × Int × Nat)
  typeFunc : I → T
  gluing   : I → I → I
  unit     : I

def glue {I R T : Type u} (inc : Incidence I R T) (i j : I) : I :=
  inc.gluing i j

def approx {I R T : Type u} (inc : Incidence I R T) (i j : I) : Prop :=
  inc.typeFunc i = inc.typeFunc j ∧ inc.boundary i = inc.boundary j

theorem approx_refl {I R T : Type u} (inc : Incidence I R T) (i : I) :
    approx inc i i :=
  And.intro rfl rfl

theorem approx_symm {I R T : Type u} {inc : Incidence I R T} {i j : I} :
    approx inc i j → approx inc j i :=
  fun h => And.intro (Eq.symm h.left) (Eq.symm h.right)

theorem approx_trans {I R T : Type u} {inc : Incidence I R T} {i j k : I} :
    approx inc i j → approx inc j k → approx inc i k :=
  fun hij hjk =>
    let hT := Eq.trans hij.left hjk.left
    let hB := Eq.trans hij.right hjk.right
    And.intro hT hB

end IncidenceTheory
