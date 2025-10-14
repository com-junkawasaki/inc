universe u

structure Incidence (I R T : Type u) where
  boundary : I → List (I × R × Int × Nat)
  typeFunc : I → T
  gluing   : I → I → I
  unit     : I
  -- Axiom A2: Type Consistency
  type_consistent : ∀ i j r s m, (j, r, s, m) ∈ boundary i → typeFunc j = typeFunc i
  -- Axiom A3: Sign Rules
  sign_rules : ∀ i j r s m, (j, r, s, m) ∈ boundary i → s = -1 ∨ s = 0 ∨ s = 1

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

-- Axiom A2: Type Consistency Theorem
theorem type_consistency {I R T : Type u} (inc : Incidence I R T) (i j : I) (r : R) (s : Int) (m : Nat) :
  (j, r, s, m) ∈ inc.boundary i → inc.typeFunc j = inc.typeFunc i :=
inc.type_consistent i j r s m

-- Axiom A3: Sign Rules Theorem
theorem sign_rules_theorem {I R T : Type u} (inc : Incidence I R T) (i j : I) (r : R) (s : Int) (m : Nat) :
  (j, r, s, m) ∈ inc.boundary i → s = -1 ∨ s = 0 ∨ s = 1 :=
inc.sign_rules i j r s m
