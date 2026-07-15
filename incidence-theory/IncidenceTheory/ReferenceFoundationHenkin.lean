import IncidenceTheory.ReferenceFoundationLindenbaum

/-! Fresh-constant abstraction used by the Henkin extension argument. -/

namespace IncidenceCore.ReferenceFoundation

structure SyntaxMap where
  onVar : Nat → Term
  onConst : Nat → Term

@[ext] theorem SyntaxMap.ext {first second : SyntaxMap}
    (varEq : first.onVar = second.onVar)
    (constEq : first.onConst = second.onConst) : first = second := by
  cases first
  cases second
  simp_all

def SyntaxMap.lift (mapping : SyntaxMap) : SyntaxMap where
  onVar := liftSubstitution mapping.onVar
  onConst := fun index => (mapping.onConst index).rename Nat.succ

def Term.mapSyntax (mapping : SyntaxMap) : Term → Term
  | .var index => mapping.onVar index
  | .const index => mapping.onConst index
  | .empty => .empty
  | .pair left right => .pair (left.mapSyntax mapping) (right.mapSyntax mapping)
  | .union term => .union (term.mapSyntax mapping)
  | .powerset term => .powerset (term.mapSyntax mapping)

def Formula.mapSyntax (mapping : SyntaxMap) : Formula → Formula
  | .mem left right => .mem (left.mapSyntax mapping) (right.mapSyntax mapping)
  | .eq left right => .eq (left.mapSyntax mapping) (right.mapSyntax mapping)
  | .bot => .bot
  | .and left right => .and (left.mapSyntax mapping) (right.mapSyntax mapping)
  | .or left right => .or (left.mapSyntax mapping) (right.mapSyntax mapping)
  | .imp left right => .imp (left.mapSyntax mapping) (right.mapSyntax mapping)
  | .all body => .all (body.mapSyntax mapping.lift)
  | .ex body => .ex (body.mapSyntax mapping.lift)

def SyntaxMap.afterSubstitution (mapping : SyntaxMap)
    (substitution : Nat → Term) : SyntaxMap where
  onVar := fun index => (substitution index).mapSyntax mapping
  onConst := mapping.onConst

theorem Term.mapSyntax_substitute (term : Term) (mapping : SyntaxMap)
    (substitution : Nat → Term) :
    (term.substitute substitution).mapSyntax mapping =
      term.mapSyntax (mapping.afterSubstitution substitution) := by
  induction term <;> simp [Term.substitute, Term.mapSyntax,
    SyntaxMap.afterSubstitution, *]

theorem Term.mapSyntax_rename_succ (term : Term) (mapping : SyntaxMap) :
    (term.rename Nat.succ).mapSyntax mapping.lift =
      (term.mapSyntax mapping).rename Nat.succ := by
  induction term with
  | var index => cases index <;> rfl
  | «const» index => rfl
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp only [Term.rename, Term.mapSyntax]
      rw [ihLeft, ihRight]
  | union term ih =>
      simp only [Term.rename, Term.mapSyntax]
      rw [ih]
  | powerset term ih =>
      simp only [Term.rename, Term.mapSyntax]
      rw [ih]

theorem SyntaxMap.lift_afterSubstitution (mapping : SyntaxMap)
    (substitution : Nat → Term) :
    (mapping.afterSubstitution substitution).lift =
      mapping.lift.afterSubstitution (liftSubstitution substitution) := by
  cases mapping with
  | mk onVar onConst =>
      apply SyntaxMap.ext <;> funext index
      · cases index with
        | zero => rfl
        | succ index =>
            simp only [SyntaxMap.afterSubstitution, SyntaxMap.lift,
              liftSubstitution]
            exact (Term.mapSyntax_rename_succ (substitution index)
              { onVar := onVar, onConst := onConst }).symm
      · rfl

theorem Formula.mapSyntax_substitute (formula : Formula)
    (mapping : SyntaxMap) (substitution : Nat → Term) :
    (formula.substitute substitution).mapSyntax mapping =
      formula.mapSyntax (mapping.afterSubstitution substitution) := by
  induction formula generalizing mapping substitution with
  | mem left right =>
      simp [Formula.substitute, Formula.mapSyntax, Term.mapSyntax_substitute]
  | eq left right =>
      simp [Formula.substitute, Formula.mapSyntax, Term.mapSyntax_substitute]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.substitute, Formula.mapSyntax, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.substitute, Formula.mapSyntax, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.substitute, Formula.mapSyntax, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.substitute, Formula.mapSyntax]
      rw [ih, SyntaxMap.lift_afterSubstitution]
  | ex body ih =>
      simp only [Formula.substitute, Formula.mapSyntax]
      rw [ih, SyntaxMap.lift_afterSubstitution]

def SyntaxMap.thenSubstitution (mapping : SyntaxMap)
    (substitution : Nat → Term) : SyntaxMap where
  onVar := fun index => (mapping.onVar index).substitute substitution
  onConst := fun index => (mapping.onConst index).substitute substitution

theorem Term.substitute_mapSyntax (term : Term) (mapping : SyntaxMap)
    (substitution : Nat → Term) :
    (term.mapSyntax mapping).substitute substitution =
      term.mapSyntax (mapping.thenSubstitution substitution) := by
  induction term <;> simp [Term.substitute, Term.mapSyntax,
    SyntaxMap.thenSubstitution, *]

theorem Term.rename_succ_substitute_lift (term : Term)
    (substitution : Nat → Term) :
    (term.rename Nat.succ).substitute (liftSubstitution substitution) =
      (term.substitute substitution).rename Nat.succ := by
  rw [Term.rename_then_substitute, Term.substitute_then_rename]
  apply congrArg (fun mapped => term.substitute mapped)
  funext index
  rfl

theorem SyntaxMap.lift_thenSubstitution (mapping : SyntaxMap)
    (substitution : Nat → Term) :
    (mapping.thenSubstitution substitution).lift =
      mapping.lift.thenSubstitution (liftSubstitution substitution) := by
  cases mapping with
  | mk onVar onConst =>
      apply SyntaxMap.ext <;> funext index
      · cases index with
        | zero => rfl
        | succ index =>
            simp only [SyntaxMap.thenSubstitution, SyntaxMap.lift,
              liftSubstitution]
            exact (Term.rename_succ_substitute_lift
              (onVar index) substitution).symm
      · simp only [SyntaxMap.thenSubstitution, SyntaxMap.lift]
        exact (Term.rename_succ_substitute_lift
          (onConst index) substitution).symm

theorem Term.rename_succ_instantiate (term witness : Term) :
    (term.rename Nat.succ).substitute (instantiateSubstitution witness) = term := by
  induction term <;> simp [Term.rename, Term.substitute,
    instantiateSubstitution, *]

theorem Formula.substitute_mapSyntax (formula : Formula)
    (mapping : SyntaxMap) (substitution : Nat → Term) :
    (formula.mapSyntax mapping).substitute substitution =
      formula.mapSyntax (mapping.thenSubstitution substitution) := by
  induction formula generalizing mapping substitution with
  | mem left right =>
      simp [Formula.substitute, Formula.mapSyntax, Term.substitute_mapSyntax]
  | eq left right =>
      simp [Formula.substitute, Formula.mapSyntax, Term.substitute_mapSyntax]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.substitute, Formula.mapSyntax, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.substitute, Formula.mapSyntax, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.substitute, Formula.mapSyntax, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.substitute, Formula.mapSyntax]
      rw [ih, SyntaxMap.lift_thenSubstitution]
  | ex body ih =>
      simp only [Formula.substitute, Formula.mapSyntax]
      rw [ih, SyntaxMap.lift_thenSubstitution]

theorem SyntaxMap.instantiate_commutes (mapping : SyntaxMap) (term : Term) :
    mapping.afterSubstitution (instantiateSubstitution term) =
      mapping.lift.thenSubstitution
        (instantiateSubstitution (term.mapSyntax mapping)) := by
  cases mapping with
  | mk onVar onConst =>
      apply SyntaxMap.ext <;> funext index
      · cases index with
        | zero => rfl
        | succ index =>
            simp [SyntaxMap.afterSubstitution, SyntaxMap.thenSubstitution,
              SyntaxMap.lift, instantiateSubstitution, Term.mapSyntax,
              liftSubstitution, Term.rename_succ_instantiate]
      · simp [SyntaxMap.afterSubstitution, SyntaxMap.thenSubstitution,
          SyntaxMap.lift, instantiateSubstitution, Term.mapSyntax,
          Term.rename_succ_instantiate]

theorem Formula.mapSyntax_instantiate (body : Formula) (mapping : SyntaxMap)
    (term : Term) :
    (body.instantiate term).mapSyntax mapping =
      (body.mapSyntax mapping.lift).instantiate (term.mapSyntax mapping) := by
  rw [Formula.instantiate_eq, Formula.instantiate_eq,
    Formula.mapSyntax_substitute]
  rw [Formula.substitute_mapSyntax, SyntaxMap.instantiate_commutes]

def insertRenaming (depth : Nat) (index : Nat) : Nat :=
  if index < depth then index else index + 1

def Term.abstractConst (constant depth : Nat) : Term → Term
  | .var index => .var (insertRenaming depth index)
  | .const index => if index = constant then .var depth else .const index
  | .empty => .empty
  | .pair left right =>
      .pair (left.abstractConst constant depth) (right.abstractConst constant depth)
  | .union term => .union (term.abstractConst constant depth)
  | .powerset term => .powerset (term.abstractConst constant depth)

def Formula.abstractConst (constant depth : Nat) : Formula → Formula
  | .mem left right =>
      .mem (left.abstractConst constant depth) (right.abstractConst constant depth)
  | .eq left right =>
      .eq (left.abstractConst constant depth) (right.abstractConst constant depth)
  | .bot => .bot
  | .and left right =>
      .and (left.abstractConst constant depth) (right.abstractConst constant depth)
  | .or left right =>
      .or (left.abstractConst constant depth) (right.abstractConst constant depth)
  | .imp left right =>
      .imp (left.abstractConst constant depth) (right.abstractConst constant depth)
  | .all body => .all (body.abstractConst constant (depth + 1))
  | .ex body => .ex (body.abstractConst constant (depth + 1))

def abstractSyntaxMap (constant depth : Nat) : SyntaxMap where
  onVar := fun index => .var (insertRenaming depth index)
  onConst := fun index => if index = constant then .var depth else .const index

theorem abstractSyntaxMap_lift (constant depth : Nat) :
    (abstractSyntaxMap constant depth).lift =
      abstractSyntaxMap constant (depth + 1) := by
  apply SyntaxMap.ext <;> funext index
  · cases index with
    | zero => simp [abstractSyntaxMap, SyntaxMap.lift, liftSubstitution,
        insertRenaming]
    | succ index =>
        by_cases below : index < depth
        · simp [abstractSyntaxMap, SyntaxMap.lift, liftSubstitution,
            insertRenaming, Term.rename, below]
        · simp [abstractSyntaxMap, SyntaxMap.lift, liftSubstitution,
            insertRenaming, Term.rename, below]
  · simp [abstractSyntaxMap, SyntaxMap.lift]
    split <;> simp [Term.rename]

theorem Term.mapSyntax_abstractSyntaxMap (term : Term)
    (constant depth : Nat) :
    term.mapSyntax (abstractSyntaxMap constant depth) =
      term.abstractConst constant depth := by
  induction term with
  | var index => rfl
  | «const» index => rfl
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp only [Term.mapSyntax, Term.abstractConst]
      rw [ihLeft, ihRight]
  | union term ih =>
      simp only [Term.mapSyntax, Term.abstractConst]
      rw [ih]
  | powerset term ih =>
      simp only [Term.mapSyntax, Term.abstractConst]
      rw [ih]

theorem Formula.mapSyntax_abstractSyntaxMap (formula : Formula)
    (constant depth : Nat) :
    formula.mapSyntax (abstractSyntaxMap constant depth) =
      formula.abstractConst constant depth := by
  induction formula generalizing depth with
  | mem left right =>
      simp [Formula.mapSyntax, Formula.abstractConst,
        Term.mapSyntax_abstractSyntaxMap]
  | eq left right =>
      simp [Formula.mapSyntax, Formula.abstractConst,
        Term.mapSyntax_abstractSyntaxMap]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.mapSyntax, Formula.abstractConst, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.mapSyntax, Formula.abstractConst, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.mapSyntax, Formula.abstractConst, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.mapSyntax, Formula.abstractConst]
      rw [abstractSyntaxMap_lift, ih]
  | ex body ih =>
      simp only [Formula.mapSyntax, Formula.abstractConst]
      rw [abstractSyntaxMap_lift, ih]

theorem Formula.abstractConst_instantiate (body : Formula) (term : Term)
    (constant depth : Nat) :
    (body.instantiate term).abstractConst constant depth =
      (body.abstractConst constant (depth + 1)).instantiate
        (term.abstractConst constant depth) := by
  rw [← Formula.mapSyntax_abstractSyntaxMap,
    Formula.mapSyntax_instantiate,
    abstractSyntaxMap_lift,
    Formula.mapSyntax_abstractSyntaxMap,
    Term.mapSyntax_abstractSyntaxMap]

theorem Term.rename_eq_substitute_vars (term : Term) (rho : Nat → Nat) :
    term.rename rho = term.substitute (fun index => .var (rho index)) := by
  induction term <;> simp [Term.rename, Term.substitute, *]

theorem Formula.rename_eq_substitute_vars (formula : Formula)
    (rho : Nat → Nat) :
    formula.rename rho =
      formula.substitute (fun index => .var (rho index)) := by
  induction formula generalizing rho with
  | mem left right =>
      simp [Formula.rename, Formula.substitute, Term.rename_eq_substitute_vars]
  | eq left right =>
      simp [Formula.rename, Formula.substitute, Term.rename_eq_substitute_vars]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.rename, Formula.substitute, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.rename, Formula.substitute, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.rename, Formula.substitute, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.rename, Formula.substitute]
      rw [ih]
      congr 2
      funext index
      cases index <;> rfl
  | ex body ih =>
      simp only [Formula.rename, Formula.substitute]
      rw [ih]
      congr 2
      funext index
      cases index <;> rfl

theorem Term.ConstFree.rename {term : Term} (free : term.ConstFree)
    (rho : Nat → Nat) : (term.rename rho).ConstFree := by
  induction term with
  | var index => trivial
  | «const» index => exact False.elim free
  | empty => trivial
  | pair left right ihLeft ihRight => exact ⟨ihLeft free.1, ihRight free.2⟩
  | union term ih => exact ih free
  | powerset term ih => exact ih free

theorem Formula.ConstFree.rename {formula : Formula} (free : formula.ConstFree)
    (rho : Nat → Nat) : (formula.rename rho).ConstFree := by
  induction formula generalizing rho with
  | mem left right => exact ⟨free.1.rename rho, free.2.rename rho⟩
  | eq left right => exact ⟨free.1.rename rho, free.2.rename rho⟩
  | bot => trivial
  | and left right ihLeft ihRight => exact ⟨ihLeft free.1 rho, ihRight free.2 rho⟩
  | or left right ihLeft ihRight => exact ⟨ihLeft free.1 rho, ihRight free.2 rho⟩
  | imp left right ihLeft ihRight => exact ⟨ihLeft free.1 rho, ihRight free.2 rho⟩
  | all body ih => exact ih free (liftRenaming rho)
  | ex body ih => exact ih free (liftRenaming rho)
theorem Axiom.constFree {infinity : InfinitySchema} {formula : Formula}
    (valid : Axiom infinity formula) : formula.ConstFree := by
  cases valid with
  | extensionality => trivial
  | emptySet => trivial
  | pairing => trivial
  | unionSet => trivial
  | powerSet => trivial
  | boundedSeparation bounded scopeProof bodyFree substitutionClosed =>
      simpa [separationInstance, Formula.iff, Formula.ConstFree,
        Term.ConstFree] using bodyFree.rename (fun | 0 => 0 | n + 1 => n + 2)
  | «infinity» => exact infinity.const_free

theorem liftRenaming_insertRenaming (depth : Nat) :
    liftRenaming (insertRenaming depth) = insertRenaming (depth + 1) := by
  funext index
  cases index with
  | zero => simp [liftRenaming, insertRenaming]
  | succ index =>
      simp only [liftRenaming, insertRenaming]
      split <;> split <;> omega

theorem Term.abstractConst_eq_rename_of_constFree
    {term : Term} (constant depth : Nat) (free : term.ConstFree) :
    term.abstractConst constant depth = term.rename (insertRenaming depth) := by
  induction term with
  | var index => rfl
  | «const» index => exact False.elim free
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp only [Term.ConstFree] at free
      simp [Term.abstractConst, Term.rename, ihLeft free.1, ihRight free.2]
  | union term ih =>
      simp [Term.abstractConst, Term.rename, ih free]
  | powerset term ih =>
      simp [Term.abstractConst, Term.rename, ih free]

theorem Formula.abstractConst_eq_rename_of_constFree
    {formula : Formula} (constant depth : Nat) (free : formula.ConstFree) :
    formula.abstractConst constant depth =
      formula.rename (insertRenaming depth) := by
  induction formula generalizing depth with
  | mem left right =>
      exact congrArg₂ Formula.mem
        (left.abstractConst_eq_rename_of_constFree constant depth free.1)
        (right.abstractConst_eq_rename_of_constFree constant depth free.2)
  | eq left right =>
      exact congrArg₂ Formula.eq
        (left.abstractConst_eq_rename_of_constFree constant depth free.1)
        (right.abstractConst_eq_rename_of_constFree constant depth free.2)
  | bot => rfl
  | and left right ihLeft ihRight =>
      exact congrArg₂ Formula.and (ihLeft depth free.1) (ihRight depth free.2)
  | or left right ihLeft ihRight =>
      exact congrArg₂ Formula.or (ihLeft depth free.1) (ihRight depth free.2)
  | imp left right ihLeft ihRight =>
      exact congrArg₂ Formula.imp (ihLeft depth free.1) (ihRight depth free.2)
  | all body ih =>
      simp only [Formula.abstractConst, Formula.rename]
      rw [ih (depth + 1) free, liftRenaming_insertRenaming]
  | ex body ih =>
      simp only [Formula.abstractConst, Formula.rename]
      rw [ih (depth + 1) free, liftRenaming_insertRenaming]

theorem insertRenaming_zero : insertRenaming 0 = Nat.succ := by
  funext index
  simp [insertRenaming]

theorem Axiom.abstractConst_eq {infinity : InfinitySchema}
    {formula : Formula} (valid : Axiom infinity formula)
    (constant depth : Nat) :
    formula.abstractConst constant depth = formula := by
  rw [formula.abstractConst_eq_rename_of_constFree constant depth valid.constFree,
    Formula.rename_eq_substitute_vars]
  exact valid.substitution_closed _

theorem Formula.abstractConst_zero_eq_rename_succ_of_constFree
    {formula : Formula} (constant : Nat) (free : formula.ConstFree) :
    formula.abstractConst constant 0 = formula.rename Nat.succ := by
  rw [formula.abstractConst_eq_rename_of_constFree constant 0 free,
    insertRenaming_zero]

theorem Term.abstractConst_eq_rename_of_not_contains
    {term : Term} (constant depth : Nat)
    (fresh : ¬ term.ContainsConst constant) :
    term.abstractConst constant depth = term.rename (insertRenaming depth) := by
  induction term with
  | var index => rfl
  | «const» index =>
      simp only [Term.ContainsConst] at fresh
      simp [Term.abstractConst, Term.rename, fresh]
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp only [Term.ContainsConst, not_or] at fresh
      simp [Term.abstractConst, Term.rename, ihLeft fresh.1, ihRight fresh.2]
  | union term ih => simp [Term.abstractConst, Term.rename, ih fresh]
  | powerset term ih => simp [Term.abstractConst, Term.rename, ih fresh]

theorem Formula.abstractConst_eq_rename_of_not_contains
    {formula : Formula} (constant depth : Nat)
    (fresh : ¬ formula.ContainsConst constant) :
    formula.abstractConst constant depth =
      formula.rename (insertRenaming depth) := by
  induction formula generalizing depth with
  | mem left right =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.mem
        (left.abstractConst_eq_rename_of_not_contains constant depth fresh.1)
        (right.abstractConst_eq_rename_of_not_contains constant depth fresh.2)
  | eq left right =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.eq
        (left.abstractConst_eq_rename_of_not_contains constant depth fresh.1)
        (right.abstractConst_eq_rename_of_not_contains constant depth fresh.2)
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.and (ihLeft depth fresh.1) (ihRight depth fresh.2)
  | or left right ihLeft ihRight =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.or (ihLeft depth fresh.1) (ihRight depth fresh.2)
  | imp left right ihLeft ihRight =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.imp (ihLeft depth fresh.1) (ihRight depth fresh.2)
  | all body ih =>
      simp only [Formula.abstractConst, Formula.rename, Formula.ContainsConst]
      rw [ih (depth + 1) fresh, liftRenaming_insertRenaming]
  | ex body ih =>
      simp only [Formula.abstractConst, Formula.rename, Formula.ContainsConst]
      rw [ih (depth + 1) fresh, liftRenaming_insertRenaming]

theorem Formula.abstractConst_zero_eq_rename_succ_of_not_contains
    {formula : Formula} (constant : Nat)
    (fresh : ¬ formula.ContainsConst constant) :
    formula.abstractConst constant 0 = formula.rename Nat.succ := by
  rw [formula.abstractConst_eq_rename_of_not_contains constant 0 fresh,
    insertRenaming_zero]

def eliminateSubstitution (constant depth : Nat) (index : Nat) : Term :=
  if index < depth then .var index
  else if index = depth then .const constant
  else .var (index - 1)

theorem liftSubstitution_eliminateSubstitution (constant depth : Nat) :
    liftSubstitution (eliminateSubstitution constant depth) =
      eliminateSubstitution constant (depth + 1) := by
  funext index
  cases index with
  | zero => simp [liftSubstitution, eliminateSubstitution]
  | succ index =>
      by_cases below : index < depth
      · simp [liftSubstitution, eliminateSubstitution, below, Term.rename]
      · by_cases equal : index = depth
        · subst index
          simp [liftSubstitution, eliminateSubstitution, Term.rename]
        · have above : depth < index := Nat.lt_of_le_of_ne (Nat.le_of_not_gt below)
              (Ne.symm equal)
          simp [liftSubstitution, eliminateSubstitution, below, equal,
            Term.rename, Nat.succ_lt_succ_iff]
          exact Nat.sub_add_cancel
            (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt above))

theorem Term.abstractConst_substitute_eliminate
    {term : Term} (constant depth : Nat)
    (fresh : ¬ term.ContainsConst constant) :
    (term.substitute (eliminateSubstitution constant depth)).abstractConst
        constant depth = term := by
  induction term with
  | var index =>
      by_cases below : index < depth
      · simp [Term.substitute, eliminateSubstitution, below,
          Term.abstractConst, insertRenaming]
      · by_cases equal : index = depth
        · subst index
          simp [Term.substitute, eliminateSubstitution,
            Term.abstractConst, insertRenaming]
        · have above : depth < index := Nat.lt_of_le_of_ne (Nat.le_of_not_gt below)
              (Ne.symm equal)
          have notBelow : ¬ index - 1 < depth := by omega
          simp [Term.substitute, eliminateSubstitution, below, equal,
            Term.abstractConst, insertRenaming, notBelow]
          exact Nat.sub_add_cancel
            (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt above))
  | «const» index =>
      simp only [Term.ContainsConst] at fresh
      simp [Term.substitute, Term.abstractConst, fresh]
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp only [Term.ContainsConst, not_or] at fresh
      exact congrArg₂ Term.pair (ihLeft fresh.1) (ihRight fresh.2)
  | union term ih => exact congrArg Term.union (ih fresh)
  | powerset term ih => exact congrArg Term.powerset (ih fresh)

theorem Formula.abstractConst_substitute_eliminate
    {formula : Formula} (constant depth : Nat)
    (fresh : ¬ formula.ContainsConst constant) :
    (formula.substitute (eliminateSubstitution constant depth)).abstractConst
        constant depth = formula := by
  induction formula generalizing depth with
  | mem left right =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.mem
        (left.abstractConst_substitute_eliminate constant depth fresh.1)
        (right.abstractConst_substitute_eliminate constant depth fresh.2)
  | eq left right =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.eq
        (left.abstractConst_substitute_eliminate constant depth fresh.1)
        (right.abstractConst_substitute_eliminate constant depth fresh.2)
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.and (ihLeft depth fresh.1) (ihRight depth fresh.2)
  | or left right ihLeft ihRight =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.or (ihLeft depth fresh.1) (ihRight depth fresh.2)
  | imp left right ihLeft ihRight =>
      simp only [Formula.ContainsConst, not_or] at fresh
      exact congrArg₂ Formula.imp (ihLeft depth fresh.1) (ihRight depth fresh.2)
  | all body ih =>
      simp only [Formula.substitute, Formula.abstractConst]
      rw [liftSubstitution_eliminateSubstitution, ih (depth + 1) fresh]
  | ex body ih =>
      simp only [Formula.substitute, Formula.abstractConst]
      rw [liftSubstitution_eliminateSubstitution, ih (depth + 1) fresh]

theorem Formula.abstractConst_instantiate_const
    {body : Formula} (constant : Nat)
    (fresh : ¬ body.ContainsConst constant) :
    (body.instantiate (.const constant)).abstractConst constant 0 = body := by
  rw [Formula.instantiate_eq]
  have substitutions : instantiateSubstitution (.const constant) =
      eliminateSubstitution constant 0 := by
    funext index
    cases index <;> simp [instantiateSubstitution, eliminateSubstitution]
  rw [substitutions]
  exact Formula.abstractConst_substitute_eliminate constant 0 fresh

theorem Term.abstractConst_insertRenaming (term : Term)
    (constant depth binderDepth : Nat) :
    (term.rename (insertRenaming binderDepth)).abstractConst constant
        (depth + binderDepth + 1) =
      (term.abstractConst constant (depth + binderDepth)).rename
        (insertRenaming binderDepth) := by
  induction term with
  | var index =>
      by_cases belowBinder : index < binderDepth
      · have belowSlot : index < depth + binderDepth := by omega
        have renamedBelowSlot : index < depth + binderDepth + 1 := by omega
        simp [Term.rename, Term.abstractConst, insertRenaming, belowBinder,
          belowSlot, renamedBelowSlot]
      · by_cases belowSlot : index < depth + binderDepth
        · have renamedNotBelowBinder : ¬ index + 1 < binderDepth := by omega
          have renamedBelowSlot : index + 1 < depth + binderDepth + 1 := by omega
          simp [Term.rename, Term.abstractConst, insertRenaming, belowBinder,
            belowSlot, renamedNotBelowBinder, renamedBelowSlot]
        · have renamedNotBelowBinder : ¬ index + 1 < binderDepth := by omega
          have renamedNotBelowSlot : ¬ index + 1 < depth + binderDepth + 1 := by
            omega
          simp [Term.rename, Term.abstractConst, insertRenaming, belowBinder,
            belowSlot, renamedNotBelowBinder, renamedNotBelowSlot]
  | «const» index =>
      simp [Term.rename, Term.abstractConst]
      split
      · simp [Term.rename, insertRenaming]
      · simp [Term.rename, Term.abstractConst]
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp [Term.rename, Term.abstractConst, ihLeft, ihRight]
  | union term ih => simp [Term.rename, Term.abstractConst, ih]
  | powerset term ih => simp [Term.rename, Term.abstractConst, ih]

theorem Formula.abstractConst_insertRenaming (formula : Formula)
    (constant depth binderDepth : Nat) :
    (formula.rename (insertRenaming binderDepth)).abstractConst constant
        (depth + binderDepth + 1) =
      (formula.abstractConst constant (depth + binderDepth)).rename
        (insertRenaming binderDepth) := by
  induction formula generalizing binderDepth with
  | mem left right =>
      simp [Formula.rename, Formula.abstractConst,
        Term.abstractConst_insertRenaming]
  | eq left right =>
      simp [Formula.rename, Formula.abstractConst,
        Term.abstractConst_insertRenaming]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.rename, Formula.abstractConst, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.rename, Formula.abstractConst, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.rename, Formula.abstractConst, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.rename, Formula.abstractConst]
      rw [liftRenaming_insertRenaming]
      have nested := ih (binderDepth + 1)
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at nested ⊢
      exact congrArg Formula.all nested
  | ex body ih =>
      simp only [Formula.rename, Formula.abstractConst]
      rw [liftRenaming_insertRenaming]
      have nested := ih (binderDepth + 1)
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at nested ⊢
      exact congrArg Formula.ex nested

theorem Formula.abstractConst_rename_succ (formula : Formula)
    (constant depth : Nat) :
    (formula.rename Nat.succ).abstractConst constant (depth + 1) =
      (formula.abstractConst constant depth).rename Nat.succ := by
  simpa [insertRenaming_zero] using
    formula.abstractConst_insertRenaming constant depth 0

theorem Derives.abstractConst {infinity : InfinitySchema}
    {context : Context} {formula : Formula}
    (proof : Derives infinity context formula) (constant depth : Nat) :
    Derives infinity (context.map (Formula.abstractConst constant depth))
      (formula.abstractConst constant depth) := by
  induction proof generalizing depth with
  | assumption member => exact Derives.assumption (List.mem_map_of_mem member)
  | «axiom» valid =>
      rw [valid.abstractConst_eq constant depth]
      exact Derives.axiom valid
  | topIntro => exact Derives.topIntro
  | botElim premise ih => exact Derives.botElim (ih depth)
  | andIntro left right ihLeft ihRight =>
      exact Derives.andIntro (ihLeft depth) (ihRight depth)
  | andElimLeft premise ih => exact Derives.andElimLeft (ih depth)
  | andElimRight premise ih => exact Derives.andElimRight (ih depth)
  | orIntroLeft premise ih => exact Derives.orIntroLeft (ih depth)
  | orIntroRight premise ih => exact Derives.orIntroRight (ih depth)
  | orElim disjunction left right ihDisjunction ihLeft ihRight =>
      exact Derives.orElim (ihDisjunction depth) (ihLeft depth) (ihRight depth)
  | impIntro premise ih => exact Derives.impIntro (ih depth)
  | impElim implication premise ihImplication ihPremise =>
      exact Derives.impElim (ihImplication depth) (ihPremise depth)
  | allIntro premise ih =>
      apply Derives.allIntro
      simpa [List.map_map, Function.comp_def,
        Formula.abstractConst_rename_succ] using ih (depth + 1)
  | allElim premise term ih =>
      have instantiated := Derives.allElim (ih depth)
        (term.abstractConst constant depth)
      simpa [Formula.abstractConst,
        Formula.abstractConst_instantiate] using instantiated
  | exIntro term premise ih =>
      apply Derives.exIntro (term.abstractConst constant depth)
      simpa [Formula.abstractConst_instantiate] using ih depth
  | exElim existential branch ihExistential ihBranch =>
      apply Derives.exElim (ihExistential depth)
      simpa [List.map_map, Function.comp_def,
        Formula.abstractConst_rename_succ] using ihBranch (depth + 1)

theorem Context.map_abstractConst_zero_eq_rename_succ
    {context : Context} (constant : Nat)
    (fresh : ∀ formula ∈ context, ¬ formula.ContainsConst constant) :
    context.map (Formula.abstractConst constant 0) =
      context.map (Formula.rename Nat.succ) := by
  apply List.map_congr_left
  intro formula member
  exact formula.abstractConst_zero_eq_rename_succ_of_not_contains constant
    (fresh formula member)

theorem Derives.eliminate_fresh_witness
    {infinity : InfinitySchema} {context : Context}
    {body target : Formula} {constant : Nat}
    (bodyFresh : ¬ body.ContainsConst constant)
    (contextFresh : ∀ formula ∈ context,
      ¬ formula.ContainsConst constant)
    (targetFresh : ¬ target.ContainsConst constant)
    (existential : Derives infinity context (.ex body))
    (withWitness : Derives infinity
      (body.instantiate (.const constant) :: context) target) :
    Derives infinity context target := by
  have abstracted := withWitness.abstractConst constant 0
  have branch : Derives infinity
      (body :: context.map (Formula.rename Nat.succ))
      (target.rename Nat.succ) := by
    simpa [Formula.abstractConst_instantiate_const constant bodyFresh,
      Context.map_abstractConst_zero_eq_rename_succ constant contextFresh,
      Formula.abstractConst_zero_eq_rename_succ_of_not_contains constant
        targetFresh] using abstracted
  exact Derives.exElim existential branch

theorem SetDerives.eliminate_fresh_witness
    {infinity : InfinitySchema} {theory : Set Formula}
    {body target : Formula} {constant : Nat}
    (bodyFresh : ¬ body.ContainsConst constant)
    (theoryFresh : ∀ formula ∈ theory,
      ¬ formula.ContainsConst constant)
    (targetFresh : ¬ target.ContainsConst constant)
    (existential : SetDerives infinity theory (.ex body))
    (withWitness : SetDerives infinity
      (Set.insert (body.instantiate (.const constant)) theory) target) :
    SetDerives infinity theory target := by
  classical
  rcases existential with ⟨existentialContext, existentialIn,
    derivesExistential⟩
  rcases withWitness with ⟨witnessContext, witnessIn, derivesTarget⟩
  rcases SetDerives.strip_insert witnessIn derivesTarget with
    ⟨derivesStripped, remainderIn⟩
  let witness := body.instantiate (.const constant)
  let remainder := witnessContext.filter (fun item => item != witness)
  let combined := existentialContext ++ remainder
  have existentialCombined : Derives infinity combined (.ex body) :=
    derivesExistential.weaken (fun member =>
      List.mem_append_left remainder member)
  have targetCombined : Derives infinity (witness :: combined) target :=
    derivesStripped.weaken (by
      intro item member
      simp only [List.mem_cons] at member ⊢
      exact member.elim Or.inl (fun tail => Or.inr
        (List.mem_append_right existentialContext tail)))
  refine ⟨combined, ?_, Derives.eliminate_fresh_witness bodyFresh ?_
    targetFresh existentialCombined targetCombined⟩
  · intro formula member
    rcases List.mem_append.mp member with inExistential | inRemainder
    · exact existentialIn formula inExistential
    · exact remainderIn formula inRemainder
  · intro formula member
    rcases List.mem_append.mp member with inExistential | inRemainder
    · exact theoryFresh formula (existentialIn formula inExistential)
    · exact theoryFresh formula (remainderIn formula inRemainder)

end IncidenceCore.ReferenceFoundation
