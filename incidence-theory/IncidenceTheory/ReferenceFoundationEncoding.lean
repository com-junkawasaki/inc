import Mathlib.Tactic.DeriveEncodable
import Mathlib.Data.Nat.Pairing
import IncidenceTheory.ReferenceFoundationCanonical

/-! Effective enumeration and freshness bounds for the Henkin construction. -/

namespace IncidenceCore.ReferenceFoundation

deriving instance Encodable for Term
deriving instance Encodable for Formula

def Term.maxVar : Term → Nat
  | .var index => index
  | .const _ => 0
  | .empty => 0
  | .pair left right => max left.maxVar right.maxVar
  | .union term => term.maxVar
  | .powerset term => term.maxVar

def Formula.maxVar : Formula → Nat
  | .mem left right => max left.maxVar right.maxVar
  | .eq left right => max left.maxVar right.maxVar
  | .bot => 0
  | .and left right => max left.maxVar right.maxVar
  | .or left right => max left.maxVar right.maxVar
  | .imp left right => max left.maxVar right.maxVar
  | .all body => body.maxVar
  | .ex body => body.maxVar

def Term.constBound : Term → Nat
  | .var _ => 0
  | .const index => index + 1
  | .empty => 0
  | .pair left right => max left.constBound right.constBound
  | .union term => term.constBound
  | .powerset term => term.constBound

def Formula.constBound : Formula → Nat
  | .mem left right => max left.constBound right.constBound
  | .eq left right => max left.constBound right.constBound
  | .bot => 0
  | .and left right => max left.constBound right.constBound
  | .or left right => max left.constBound right.constBound
  | .imp left right => max left.constBound right.constBound
  | .all body => body.constBound
  | .ex body => body.constBound

def Term.constLevelBound : Term → Nat
  | .var _ => 0
  | .const code => code.unpair.1 + 1
  | .empty => 0
  | .pair left right => max left.constLevelBound right.constLevelBound
  | .union term => term.constLevelBound
  | .powerset term => term.constLevelBound

def Formula.constLevelBound : Formula → Nat
  | .mem left right => max left.constLevelBound right.constLevelBound
  | .eq left right => max left.constLevelBound right.constLevelBound
  | .bot => 0
  | .and left right => max left.constLevelBound right.constLevelBound
  | .or left right => max left.constLevelBound right.constLevelBound
  | .imp left right => max left.constLevelBound right.constLevelBound
  | .all body => body.constLevelBound
  | .ex body => body.constLevelBound

def Term.localConstBound (level : Nat) : Term → Nat
  | .var _ => 0
  | .const code => if code.unpair.1 = level then code.unpair.2 + 1 else 0
  | .empty => 0
  | .pair left right => max (left.localConstBound level)
      (right.localConstBound level)
  | .union term => term.localConstBound level
  | .powerset term => term.localConstBound level

def Formula.localConstBound (level : Nat) : Formula → Nat
  | .mem left right => max (left.localConstBound level)
      (right.localConstBound level)
  | .eq left right => max (left.localConstBound level)
      (right.localConstBound level)
  | .bot => 0
  | .and left right => max (left.localConstBound level)
      (right.localConstBound level)
  | .or left right => max (left.localConstBound level)
      (right.localConstBound level)
  | .imp left right => max (left.localConstBound level)
      (right.localConstBound level)
  | .all body => body.localConstBound level
  | .ex body => body.localConstBound level

@[simp] theorem Term.constBound_rename (term : Term) (rho : Nat → Nat) :
    (term.rename rho).constBound = term.constBound := by
  induction term <;> simp [Term.rename, Term.constBound, *]

@[simp] theorem Formula.constBound_rename (formula : Formula)
    (rho : Nat → Nat) :
    (formula.rename rho).constBound = formula.constBound := by
  induction formula generalizing rho <;>
    simp [Formula.rename, Formula.constBound, *]

@[simp] theorem Term.constLevelBound_rename (term : Term) (rho : Nat → Nat) :
    (term.rename rho).constLevelBound = term.constLevelBound := by
  induction term <;> simp [Term.rename, Term.constLevelBound, *]

@[simp] theorem Formula.constLevelBound_rename (formula : Formula)
    (rho : Nat → Nat) :
    (formula.rename rho).constLevelBound = formula.constLevelBound := by
  induction formula generalizing rho <;>
    simp [Formula.rename, Formula.constLevelBound, *]

@[simp] theorem Term.localConstBound_rename (term : Term)
    (level : Nat) (rho : Nat → Nat) :
    (term.rename rho).localConstBound level = term.localConstBound level := by
  induction term <;> simp [Term.rename, Term.localConstBound, *]

@[simp] theorem Formula.localConstBound_rename (formula : Formula)
    (level : Nat) (rho : Nat → Nat) :
    (formula.rename rho).localConstBound level =
      formula.localConstBound level := by
  induction formula generalizing rho <;>
    simp [Formula.rename, Formula.localConstBound, *]

theorem Term.constBound_substitute_le (term : Term) (substitution : Nat → Term)
    (bound : Nat) (boundVars : ∀ index,
      (substitution index).constBound ≤ bound) :
    (term.substitute substitution).constBound ≤ max term.constBound bound := by
  induction term with
  | var index => exact le_trans (boundVars index) (Nat.le_max_right _ _)
  | «const» index => simp [Term.substitute, Term.constBound]
  | empty => simp [Term.substitute, Term.constBound]
  | pair left right ihLeft ihRight =>
      simp only [Term.substitute, Term.constBound]
      exact max_le
        (le_trans ihLeft (by omega))
        (le_trans ihRight (by omega))
  | union term ih => exact ih
  | powerset term ih => exact ih

theorem Formula.constBound_substitute_le (formula : Formula)
    (substitution : Nat → Term) (bound : Nat)
    (boundVars : ∀ index, (substitution index).constBound ≤ bound) :
    (formula.substitute substitution).constBound ≤
      max formula.constBound bound := by
  induction formula generalizing substitution with
  | mem left right =>
      simp only [Formula.substitute, Formula.constBound]
      exact max_le
        (le_trans (left.constBound_substitute_le substitution bound boundVars)
          (by omega))
        (le_trans (right.constBound_substitute_le substitution bound boundVars)
          (by omega))
  | eq left right =>
      simp only [Formula.substitute, Formula.constBound]
      exact max_le
        (le_trans (left.constBound_substitute_le substitution bound boundVars)
          (by omega))
        (le_trans (right.constBound_substitute_le substitution bound boundVars)
          (by omega))
  | bot => simp [Formula.substitute, Formula.constBound]
  | and left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.constBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | or left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.constBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | imp left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.constBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | all body ih =>
      simp only [Formula.substitute, Formula.constBound]
      apply ih
      intro index
      cases index with
      | zero => simp [liftSubstitution, Term.constBound]
      | succ index => simpa [liftSubstitution] using boundVars index
  | ex body ih =>
      simp only [Formula.substitute, Formula.constBound]
      apply ih
      intro index
      cases index with
      | zero => simp [liftSubstitution, Term.constBound]
      | succ index => simpa [liftSubstitution] using boundVars index

theorem Formula.constBound_instantiate_const_le (body : Formula)
    (constant : Nat) :
    (body.instantiate (.const constant)).constBound ≤
      max body.constBound (constant + 1) := by
  rw [Formula.instantiate_eq]
  apply body.constBound_substitute_le _ (constant + 1)
  intro index
  cases index <;> simp [instantiateSubstitution, Term.constBound]

theorem Term.constLevelBound_substitute_le (term : Term)
    (substitution : Nat → Term) (bound : Nat)
    (boundVars : ∀ index, (substitution index).constLevelBound ≤ bound) :
    (term.substitute substitution).constLevelBound ≤
      max term.constLevelBound bound := by
  induction term with
  | var index => exact le_trans (boundVars index) (Nat.le_max_right _ _)
  | «const» index => simp [Term.substitute, Term.constLevelBound]
  | empty => simp [Term.substitute, Term.constLevelBound]
  | pair left right ihLeft ihRight =>
      simp only [Term.substitute, Term.constLevelBound]
      exact max_le (le_trans ihLeft (by omega)) (le_trans ihRight (by omega))
  | union term ih => exact ih
  | powerset term ih => exact ih

theorem Formula.constLevelBound_substitute_le (formula : Formula)
    (substitution : Nat → Term) (bound : Nat)
    (boundVars : ∀ index, (substitution index).constLevelBound ≤ bound) :
    (formula.substitute substitution).constLevelBound ≤
      max formula.constLevelBound bound := by
  induction formula generalizing substitution with
  | mem left right =>
      simp only [Formula.substitute, Formula.constLevelBound]
      exact max_le
        (le_trans (left.constLevelBound_substitute_le substitution bound boundVars)
          (by omega))
        (le_trans (right.constLevelBound_substitute_le substitution bound boundVars)
          (by omega))
  | eq left right =>
      simp only [Formula.substitute, Formula.constLevelBound]
      exact max_le
        (le_trans (left.constLevelBound_substitute_le substitution bound boundVars)
          (by omega))
        (le_trans (right.constLevelBound_substitute_le substitution bound boundVars)
          (by omega))
  | bot => simp [Formula.substitute, Formula.constLevelBound]
  | and left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.constLevelBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | or left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.constLevelBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | imp left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.constLevelBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | all body ih =>
      simp only [Formula.substitute, Formula.constLevelBound]
      apply ih
      intro index
      cases index with
      | zero => simp [liftSubstitution, Term.constLevelBound]
      | succ index => simpa [liftSubstitution] using boundVars index
  | ex body ih =>
      simp only [Formula.substitute, Formula.constLevelBound]
      apply ih
      intro index
      cases index with
      | zero => simp [liftSubstitution, Term.constLevelBound]
      | succ index => simpa [liftSubstitution] using boundVars index

theorem Formula.constLevelBound_instantiate_const_le (body : Formula)
    (constant : Nat) :
    (body.instantiate (.const constant)).constLevelBound ≤
      max body.constLevelBound (constant.unpair.1 + 1) := by
  rw [Formula.instantiate_eq]
  apply body.constLevelBound_substitute_le _ (constant.unpair.1 + 1)
  intro index
  cases index <;> simp [instantiateSubstitution, Term.constLevelBound]

theorem Term.localConstBound_substitute_le (term : Term)
    (substitution : Nat → Term) (level bound : Nat)
    (boundVars : ∀ index,
      (substitution index).localConstBound level ≤ bound) :
    (term.substitute substitution).localConstBound level ≤
      max (term.localConstBound level) bound := by
  induction term with
  | var index => exact le_trans (boundVars index) (Nat.le_max_right _ _)
  | «const» index => simp [Term.substitute, Term.localConstBound]
  | empty => simp [Term.substitute, Term.localConstBound]
  | pair left right ihLeft ihRight =>
      simp only [Term.substitute, Term.localConstBound]
      exact max_le (le_trans ihLeft (by omega)) (le_trans ihRight (by omega))
  | union term ih => exact ih
  | powerset term ih => exact ih

theorem Formula.localConstBound_substitute_le (formula : Formula)
    (substitution : Nat → Term) (level bound : Nat)
    (boundVars : ∀ index,
      (substitution index).localConstBound level ≤ bound) :
    (formula.substitute substitution).localConstBound level ≤
      max (formula.localConstBound level) bound := by
  induction formula generalizing substitution with
  | mem left right =>
      simp only [Formula.substitute, Formula.localConstBound]
      exact max_le
        (le_trans (left.localConstBound_substitute_le substitution level bound
          boundVars) (by omega))
        (le_trans (right.localConstBound_substitute_le substitution level bound
          boundVars) (by omega))
  | eq left right =>
      simp only [Formula.substitute, Formula.localConstBound]
      exact max_le
        (le_trans (left.localConstBound_substitute_le substitution level bound
          boundVars) (by omega))
        (le_trans (right.localConstBound_substitute_le substitution level bound
          boundVars) (by omega))
  | bot => simp [Formula.substitute, Formula.localConstBound]
  | and left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.localConstBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | or left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.localConstBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | imp left right ihLeft ihRight =>
      simp only [Formula.substitute, Formula.localConstBound]
      exact max_le (le_trans (ihLeft substitution boundVars) (by omega))
        (le_trans (ihRight substitution boundVars) (by omega))
  | all body ih =>
      simp only [Formula.substitute, Formula.localConstBound]
      apply ih
      intro index
      cases index with
      | zero => simp [liftSubstitution, Term.localConstBound]
      | succ index => simpa [liftSubstitution] using boundVars index
  | ex body ih =>
      simp only [Formula.substitute, Formula.localConstBound]
      apply ih
      intro index
      cases index with
      | zero => simp [liftSubstitution, Term.localConstBound]
      | succ index => simpa [liftSubstitution] using boundVars index

theorem Formula.localConstBound_instantiate_const_le (body : Formula)
    (level constant : Nat) :
    (body.instantiate (.const constant)).localConstBound level ≤
      max (body.localConstBound level)
        (if constant.unpair.1 = level then constant.unpair.2 + 1 else 0) := by
  rw [Formula.instantiate_eq]
  apply body.localConstBound_substitute_le _ level
    (if constant.unpair.1 = level then constant.unpair.2 + 1 else 0)
  intro index
  cases index <;>
    simp [instantiateSubstitution, Term.localConstBound]

theorem pair_constLevel (level index : Nat) :
    (Nat.pair level index).unpair.1 = level := by
  simp [Nat.unpair_pair]

theorem pair_constLocal (level index : Nat) :
    (Nat.pair level index).unpair.2 = index := by
  simp [Nat.unpair_pair]

def Term.ContainsConst (index : Nat) : Term → Prop
  | .var _ => False
  | .const found => found = index
  | .empty => False
  | .pair left right => left.ContainsConst index ∨ right.ContainsConst index
  | .union term => term.ContainsConst index
  | .powerset term => term.ContainsConst index

def Formula.ContainsConst (index : Nat) : Formula → Prop
  | .mem left right => left.ContainsConst index ∨ right.ContainsConst index
  | .eq left right => left.ContainsConst index ∨ right.ContainsConst index
  | .bot => False
  | .and left right => left.ContainsConst index ∨ right.ContainsConst index
  | .or left right => left.ContainsConst index ∨ right.ContainsConst index
  | .imp left right => left.ContainsConst index ∨ right.ContainsConst index
  | .all body => body.ContainsConst index
  | .ex body => body.ContainsConst index

theorem Term.lt_constLevelBound_of_contains {term : Term} {code : Nat}
    (contains : term.ContainsConst code) :
    code.unpair.1 < term.constLevelBound := by
  induction term with
  | var index => exact False.elim contains
  | «const» found =>
      simp only [Term.ContainsConst] at contains
      subst found
      simp [Term.constLevelBound]
  | empty => exact False.elim contains
  | pair left right ihLeft ihRight =>
      rcases contains with inLeft | inRight
      · exact lt_of_lt_of_le (ihLeft inLeft) (Nat.le_max_left _ _)
      · exact lt_of_lt_of_le (ihRight inRight) (Nat.le_max_right _ _)
  | union term ih => exact ih contains
  | powerset term ih => exact ih contains

theorem Formula.lt_constLevelBound_of_contains
    {formula : Formula} {code : Nat}
    (contains : formula.ContainsConst code) :
    code.unpair.1 < formula.constLevelBound := by
  induction formula with
  | mem left right =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le
          (Term.lt_constLevelBound_of_contains proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le
          (Term.lt_constLevelBound_of_contains proof) (Nat.le_max_right _ _))
  | eq left right =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le
          (Term.lt_constLevelBound_of_contains proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le
          (Term.lt_constLevelBound_of_contains proof) (Nat.le_max_right _ _))
  | bot => exact False.elim contains
  | and left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | or left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | imp left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | all body ih => exact ih contains
  | ex body ih => exact ih contains

theorem Term.lt_localConstBound_of_contains {term : Term} {code level : Nat}
    (contains : term.ContainsConst code) (atLevel : code.unpair.1 = level) :
    code.unpair.2 < term.localConstBound level := by
  induction term with
  | var index => exact False.elim contains
  | «const» found =>
      simp only [Term.ContainsConst] at contains
      subst found
      simp [Term.localConstBound, atLevel]
  | empty => exact False.elim contains
  | pair left right ihLeft ihRight =>
      rcases contains with inLeft | inRight
      · exact lt_of_lt_of_le (ihLeft inLeft) (Nat.le_max_left _ _)
      · exact lt_of_lt_of_le (ihRight inRight) (Nat.le_max_right _ _)
  | union term ih => exact ih contains
  | powerset term ih => exact ih contains

theorem Formula.lt_localConstBound_of_contains
    {formula : Formula} {code level : Nat}
    (contains : formula.ContainsConst code) (atLevel : code.unpair.1 = level) :
    code.unpair.2 < formula.localConstBound level := by
  induction formula with
  | mem left right =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le
          (Term.lt_localConstBound_of_contains proof atLevel)
          (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le
          (Term.lt_localConstBound_of_contains proof atLevel)
          (Nat.le_max_right _ _))
  | eq left right =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le
          (Term.lt_localConstBound_of_contains proof atLevel)
          (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le
          (Term.lt_localConstBound_of_contains proof atLevel)
          (Nat.le_max_right _ _))
  | bot => exact False.elim contains
  | and left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | or left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | imp left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | all body ih => exact ih contains
  | ex body ih => exact ih contains

theorem Term.localConstBound_eq_zero_of_levelBound_le
    (term : Term) (level : Nat) (bounded : term.constLevelBound ≤ level) :
    term.localConstBound level = 0 := by
  induction term with
  | var index => rfl
  | «const» code =>
      simp only [Term.constLevelBound] at bounded
      simp only [Term.localConstBound]
      split
      next equal => omega
      next notEqual => rfl
  | empty => rfl
  | pair left right ihLeft ihRight =>
      simp only [Term.constLevelBound] at bounded
      simp [Term.localConstBound, ihLeft (le_trans (Nat.le_max_left _ _) bounded),
        ihRight (le_trans (Nat.le_max_right _ _) bounded)]
  | union term ih => exact ih bounded
  | powerset term ih => exact ih bounded

theorem Formula.localConstBound_eq_zero_of_levelBound_le
    (formula : Formula) (level : Nat)
    (bounded : formula.constLevelBound ≤ level) :
    formula.localConstBound level = 0 := by
  induction formula with
  | mem left right =>
      simp only [Formula.constLevelBound] at bounded
      simp [Formula.localConstBound,
        left.localConstBound_eq_zero_of_levelBound_le level
          (le_trans (Nat.le_max_left _ _) bounded),
        right.localConstBound_eq_zero_of_levelBound_le level
          (le_trans (Nat.le_max_right _ _) bounded)]
  | eq left right =>
      simp only [Formula.constLevelBound] at bounded
      simp [Formula.localConstBound,
        left.localConstBound_eq_zero_of_levelBound_le level
          (le_trans (Nat.le_max_left _ _) bounded),
        right.localConstBound_eq_zero_of_levelBound_le level
          (le_trans (Nat.le_max_right _ _) bounded)]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp only [Formula.constLevelBound] at bounded
      simp [Formula.localConstBound,
        ihLeft (le_trans (Nat.le_max_left _ _) bounded),
        ihRight (le_trans (Nat.le_max_right _ _) bounded)]
  | or left right ihLeft ihRight =>
      simp only [Formula.constLevelBound] at bounded
      simp [Formula.localConstBound,
        ihLeft (le_trans (Nat.le_max_left _ _) bounded),
        ihRight (le_trans (Nat.le_max_right _ _) bounded)]
  | imp left right ihLeft ihRight =>
      simp only [Formula.constLevelBound] at bounded
      simp [Formula.localConstBound,
        ihLeft (le_trans (Nat.le_max_left _ _) bounded),
        ihRight (le_trans (Nat.le_max_right _ _) bounded)]
  | all body ih => exact ih bounded
  | ex body ih => exact ih bounded

theorem Term.lt_constBound_of_contains {term : Term} {index : Nat}
    (contains : term.ContainsConst index) : index < term.constBound := by
  induction term with
  | var index => exact False.elim contains
  | «const» found =>
      simp only [Term.ContainsConst] at contains
      subst found
      simp [Term.constBound]
  | empty => exact False.elim contains
  | pair left right ihLeft ihRight =>
      rcases contains with inLeft | inRight
      · exact lt_of_lt_of_le (ihLeft inLeft) (Nat.le_max_left _ _)
      · exact lt_of_lt_of_le (ihRight inRight) (Nat.le_max_right _ _)
  | union term ih => exact ih contains
  | powerset term ih => exact ih contains

theorem Formula.lt_constBound_of_contains {formula : Formula} {index : Nat}
    (contains : formula.ContainsConst index) : index < formula.constBound := by
  induction formula with
  | mem left right =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (Term.lt_constBound_of_contains proof)
          (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (Term.lt_constBound_of_contains proof)
          (Nat.le_max_right _ _))
  | eq left right =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (Term.lt_constBound_of_contains proof)
          (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (Term.lt_constBound_of_contains proof)
          (Nat.le_max_right _ _))
  | bot => exact False.elim contains
  | and left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | or left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | imp left right ihLeft ihRight =>
      exact contains.elim
        (fun proof => lt_of_lt_of_le (ihLeft proof) (Nat.le_max_left _ _))
        (fun proof => lt_of_lt_of_le (ihRight proof) (Nat.le_max_right _ _))
  | all body ih => exact ih contains
  | ex body ih => exact ih contains

theorem Term.Scoped.mono {term : Term} {smaller larger : Nat}
    (bound : smaller ≤ larger) (scopedTerm : term.Scoped smaller) :
    term.Scoped larger := by
  induction term with
  | var index => exact Nat.lt_of_lt_of_le scopedTerm bound
  | «const» index => trivial
  | empty => trivial
  | pair left right ihLeft ihRight =>
      exact ⟨ihLeft scopedTerm.1, ihRight scopedTerm.2⟩
  | union term ih => exact ih scopedTerm
  | powerset term ih => exact ih scopedTerm

theorem Formula.Scoped.mono {formula : Formula} {smaller larger : Nat}
    (bound : smaller ≤ larger) (scopedFormula : formula.Scoped smaller) :
    formula.Scoped larger := by
  induction formula generalizing smaller larger with
  | mem left right =>
      exact ⟨scopedFormula.1.mono bound, scopedFormula.2.mono bound⟩
  | eq left right =>
      exact ⟨scopedFormula.1.mono bound, scopedFormula.2.mono bound⟩
  | bot => trivial
  | and left right ihLeft ihRight =>
      exact ⟨ihLeft bound scopedFormula.1, ihRight bound scopedFormula.2⟩
  | or left right ihLeft ihRight =>
      exact ⟨ihLeft bound scopedFormula.1, ihRight bound scopedFormula.2⟩
  | imp left right ihLeft ihRight =>
      exact ⟨ihLeft bound scopedFormula.1, ihRight bound scopedFormula.2⟩
  | all body ih => exact ih (Nat.add_le_add_right bound 1) scopedFormula
  | ex body ih => exact ih (Nat.add_le_add_right bound 1) scopedFormula

theorem Term.scoped_maxVar_succ (term : Term) :
    term.Scoped (term.maxVar + 1) := by
  induction term with
  | var index => simp [Term.Scoped, Term.maxVar]
  | «const» index => trivial
  | empty => trivial
  | pair left right ihLeft ihRight =>
      constructor
      · exact Term.Scoped.mono (by simp [Term.maxVar]) ihLeft
      · exact Term.Scoped.mono (by simp [Term.maxVar]) ihRight
  | union term ih => exact ih
  | powerset term ih => exact ih

theorem Formula.scoped_maxVar_succ (formula : Formula) :
    formula.Scoped (formula.maxVar + 1) := by
  induction formula with
  | mem left right =>
      constructor
      · exact Term.Scoped.mono (by simp [Formula.maxVar]) left.scoped_maxVar_succ
      · exact Term.Scoped.mono (by simp [Formula.maxVar]) right.scoped_maxVar_succ
  | eq left right =>
      constructor
      · exact Term.Scoped.mono (by simp [Formula.maxVar]) left.scoped_maxVar_succ
      · exact Term.Scoped.mono (by simp [Formula.maxVar]) right.scoped_maxVar_succ
  | bot => trivial
  | and left right ihLeft ihRight =>
      exact ⟨ihLeft.mono (by simp [Formula.maxVar]),
        ihRight.mono (by simp [Formula.maxVar])⟩
  | or left right ihLeft ihRight =>
      exact ⟨ihLeft.mono (by simp [Formula.maxVar]),
        ihRight.mono (by simp [Formula.maxVar])⟩
  | imp left right ihLeft ihRight =>
      exact ⟨ihLeft.mono (by simp [Formula.maxVar]),
        ihRight.mono (by simp [Formula.maxVar])⟩
  | all body ih =>
      simpa [Formula.maxVar] using ih.mono (Nat.le_succ (body.maxVar + 1))
  | ex body ih =>
      simpa [Formula.maxVar] using ih.mono (Nat.le_succ (body.maxVar + 1))

def formulaAt (index : Nat) : Formula :=
  (Encodable.decode index).getD .bot

theorem formulaAt_encode (formula : Formula) :
    formulaAt (Encodable.encode formula) = formula := by
  simp [formulaAt, Encodable.encodek]

theorem formulaAt_surjective : Function.Surjective formulaAt := by
  intro formula
  exact ⟨Encodable.encode formula, formulaAt_encode formula⟩

def repeatedFormulaAt (stage : Nat) : Formula :=
  formulaAt stage.unpair.1

theorem repeatedFormulaAt_pair (formula : Formula) (round : Nat) :
    repeatedFormulaAt (Nat.pair (Encodable.encode formula) round) = formula := by
  simp [repeatedFormulaAt, Nat.unpair_pair, formulaAt_encode]

def layerFormulaAt (level stage : Nat) : Formula :=
  let formula := repeatedFormulaAt stage
  if formula.constLevelBound ≤ level + 1 then formula else .bot

theorem layerFormulaAt_levelBound (level stage : Nat) :
    (layerFormulaAt level stage).constLevelBound ≤ level + 1 := by
  simp only [layerFormulaAt]
  split
  · assumption
  · simp [Formula.constLevelBound]

theorem layerFormulaAt_pair {formula : Formula} {level : Nat}
    (available : formula.constLevelBound ≤ level + 1) (round : Nat) :
    layerFormulaAt level (Nat.pair (Encodable.encode formula) round) = formula := by
  simp [layerFormulaAt, repeatedFormulaAt_pair, available]

def layerSaturationBound (level : Nat) : Nat → Nat
  | 0 => 0
  | stage + 1 => max (layerSaturationBound level stage)
      ((layerFormulaAt level stage).localConstBound level) + 1

def layerSaturationIndex (level stage : Nat) : Nat :=
  max (layerSaturationBound level stage)
    ((layerFormulaAt level stage).localConstBound level)

def layerSaturationConstant (level stage : Nat) : Nat :=
  Nat.pair level (layerSaturationIndex level stage)

theorem layerSaturationBound_step (level stage : Nat) :
    layerSaturationBound level (stage + 1) =
      layerSaturationIndex level stage + 1 := by
  rfl

theorem layerSaturationBound_le_next (level stage : Nat) :
    layerSaturationBound level stage ≤
      layerSaturationBound level (stage + 1) := by
  rw [layerSaturationBound_step]
  exact Nat.le_succ_of_le (Nat.le_max_left _ _)

theorem layerSaturationBound_mono (level : Nat) {first second : Nat}
    (order : first ≤ second) :
    layerSaturationBound level first ≤ layerSaturationBound level second := by
  induction order with
  | refl => exact Nat.le_refl _
  | @step second order ih =>
      exact le_trans ih (layerSaturationBound_le_next level second)

theorem layerFormula_localBound_le_index (level stage : Nat) :
    (layerFormulaAt level stage).localConstBound level ≤
      layerSaturationIndex level stage :=
  Nat.le_max_right _ _

@[simp] theorem layerSaturationConstant_level (level stage : Nat) :
    (layerSaturationConstant level stage).unpair.1 = level := by
  simp [layerSaturationConstant, Nat.unpair_pair]

@[simp] theorem layerSaturationConstant_local (level stage : Nat) :
    (layerSaturationConstant level stage).unpair.2 =
      layerSaturationIndex level stage := by
  simp [layerSaturationConstant, Nat.unpair_pair]

def saturationBound (seed : Nat) : Nat → Nat
  | 0 => seed
  | stage + 1 => max (saturationBound seed stage)
      (repeatedFormulaAt stage).constBound + 1

def saturationConstant (seed stage : Nat) : Nat :=
  max (saturationBound seed stage) (repeatedFormulaAt stage).constBound

theorem saturationBound_step (seed stage : Nat) :
    saturationBound seed (stage + 1) = saturationConstant seed stage + 1 := by
  rfl

theorem saturationBound_le_next (seed stage : Nat) :
    saturationBound seed stage ≤ saturationBound seed (stage + 1) := by
  rw [saturationBound_step]
  exact Nat.le_succ_of_le (Nat.le_max_left _ _)

theorem saturationBound_mono (seed : Nat) {first second : Nat}
    (order : first ≤ second) :
    saturationBound seed first ≤ saturationBound seed second := by
  induction order with
  | refl => exact Nat.le_refl _
  | @step second order ih =>
      exact le_trans ih (saturationBound_le_next seed second)

theorem saturationConstant_lt_next_bound (seed stage : Nat) :
    saturationConstant seed stage < saturationBound seed (stage + 1) := by
  rw [saturationBound_step]
  exact Nat.lt_succ_self _

theorem repeatedFormula_constBound_le_saturationConstant (seed stage : Nat) :
    (repeatedFormulaAt stage).constBound ≤ saturationConstant seed stage :=
  Nat.le_max_right _ _

def henkinBound (seed : Nat) : Nat → Nat
  | 0 => seed
  | stage + 1 => max (henkinBound seed stage)
      (formulaAt stage).constBound + 1

def henkinConstant (seed stage : Nat) : Nat :=
  max (henkinBound seed stage) (formulaAt stage).constBound

theorem henkinBound_step (seed stage : Nat) :
    henkinBound seed (stage + 1) = henkinConstant seed stage + 1 := by
  rfl

theorem henkinBound_le_next (seed stage : Nat) :
    henkinBound seed stage ≤ henkinBound seed (stage + 1) := by
  rw [henkinBound_step]
  exact Nat.le_succ_of_le (Nat.le_max_left _ _)

theorem henkinBound_mono (seed : Nat) {first second : Nat}
    (order : first ≤ second) :
    henkinBound seed first ≤ henkinBound seed second := by
  induction order with
  | refl => exact Nat.le_refl _
  | @step second order ih =>
      exact le_trans ih (henkinBound_le_next seed second)

theorem henkinConstant_lt_next_bound (seed stage : Nat) :
    henkinConstant seed stage < henkinBound seed (stage + 1) := by
  rw [henkinBound_step]
  exact Nat.lt_succ_self _

theorem henkinConstant_lt_later_bound (seed : Nat) {first later : Nat}
    (order : first < later) :
    henkinConstant seed first < henkinBound seed later := by
  have nextOrder : first + 1 ≤ later := order
  exact lt_of_lt_of_le (henkinConstant_lt_next_bound seed first)
    (henkinBound_mono seed nextOrder)

theorem seed_le_henkinBound (seed stage : Nat) :
    seed ≤ henkinBound seed stage := by
  exact henkinBound_mono seed (Nat.zero_le stage)

theorem henkinConstant_ge_seed (seed stage : Nat) :
    seed ≤ henkinConstant seed stage := by
  exact le_trans (seed_le_henkinBound seed stage) (Nat.le_max_left _ _)

theorem henkinConstant_fresh_for_stage (seed stage : Nat) :
    ¬ (formulaAt stage).ContainsConst (henkinConstant seed stage) := by
  intro contains
  have below := Formula.lt_constBound_of_contains contains
  unfold henkinConstant at below
  omega

def henkinWitnessAxiom (seed stage : Nat) : Formula :=
  let body := formulaAt stage
  .imp (.ex body) (body.instantiate (.const (henkinConstant seed stage)))

def freshVariable : List Formula → Nat
  | [] => 0
  | formula :: formulas => max (formula.maxVar + 1) (freshVariable formulas)

theorem maxVar_lt_freshVariable_of_mem {formula : Formula} {formulas : List Formula}
    (member : formula ∈ formulas) :
    formula.maxVar < freshVariable formulas := by
  induction formulas generalizing formula with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [freshVariable]
      · exact lt_of_lt_of_le (ih member) (Nat.le_max_right _ _)

end IncidenceCore.ReferenceFoundation
