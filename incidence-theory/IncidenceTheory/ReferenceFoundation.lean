/-!
  The reference foundation used by the completion programme.

  This module closes ADR-2607141850/G0: the comparison target is no longer
  “all existing mathematics”, but a concrete intuitionistic first-order set
  theory.  Syntax is intrinsically scoped only by convention for now; the
  de Bruijn operations below are total and are the operations whose laws the
  G1 metatheory must establish.
-/

namespace IncidenceCore.ReferenceFoundation

universe u

/-! ## First-order language of sets -/

inductive Term where
  | var : Nat → Term
  | const : Nat → Term
  | empty : Term
  | pair : Term → Term → Term
  | union : Term → Term
  | powerset : Term → Term
  deriving DecidableEq, Repr

inductive Formula where
  | mem : Term → Term → Formula
  | eq : Term → Term → Formula
  | bot : Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | all : Formula → Formula
  | ex : Formula → Formula
  deriving DecidableEq, Repr

def Term.Scoped (arity : Nat) : Term → Prop
  | .var index => index < arity
  | .const _ => True
  | .empty => True
  | .pair left right => left.Scoped arity ∧ right.Scoped arity
  | .union term => term.Scoped arity
  | .powerset term => term.Scoped arity

def Formula.Scoped (arity : Nat) : Formula → Prop
  | .mem left right => left.Scoped arity ∧ right.Scoped arity
  | .eq left right => left.Scoped arity ∧ right.Scoped arity
  | .bot => True
  | .and left right => left.Scoped arity ∧ right.Scoped arity
  | .or left right => left.Scoped arity ∧ right.Scoped arity
  | .imp left right => left.Scoped arity ∧ right.Scoped arity
  | .all body => body.Scoped (arity + 1)
  | .ex body => body.Scoped (arity + 1)

def Term.ConstFree : Term → Prop
  | .var _ => True
  | .const _ => False
  | .empty => True
  | .pair left right => left.ConstFree ∧ right.ConstFree
  | .union term => term.ConstFree
  | .powerset term => term.ConstFree

def Formula.ConstFree : Formula → Prop
  | .mem left right => left.ConstFree ∧ right.ConstFree
  | .eq left right => left.ConstFree ∧ right.ConstFree
  | .bot => True
  | .and left right => left.ConstFree ∧ right.ConstFree
  | .or left right => left.ConstFree ∧ right.ConstFree
  | .imp left right => left.ConstFree ∧ right.ConstFree
  | .all body => body.ConstFree
  | .ex body => body.ConstFree

abbrev Context := List Formula
abbrev Sentence := Formula

def Formula.top : Formula := .imp .bot .bot
def Formula.neg (p : Formula) : Formula := .imp p .bot
def Formula.iff (p q : Formula) : Formula := .and (.imp p q) (.imp q p)

def liftRenaming (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def Term.rename (ρ : Nat → Nat) : Term → Term
  | .var n => .var (ρ n)
  | .const n => .const n
  | .empty => .empty
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | .union a => .union (a.rename ρ)
  | .powerset a => .powerset (a.rename ρ)

def Formula.rename (ρ : Nat → Nat) : Formula → Formula
  | .mem a b => .mem (a.rename ρ) (b.rename ρ)
  | .eq a b => .eq (a.rename ρ) (b.rename ρ)
  | .bot => .bot
  | .and p q => .and (p.rename ρ) (q.rename ρ)
  | .or p q => .or (p.rename ρ) (q.rename ρ)
  | .imp p q => .imp (p.rename ρ) (q.rename ρ)
  | .all p => .all (p.rename (liftRenaming ρ))
  | .ex p => .ex (p.rename (liftRenaming ρ))

def liftSubstitution (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

def Term.substitute (σ : Nat → Term) : Term → Term
  | .var n => σ n
  | .const n => .const n
  | .empty => .empty
  | .pair a b => .pair (a.substitute σ) (b.substitute σ)
  | .union a => .union (a.substitute σ)
  | .powerset a => .powerset (a.substitute σ)

def Formula.substitute (σ : Nat → Term) : Formula → Formula
  | .mem a b => .mem (a.substitute σ) (b.substitute σ)
  | .eq a b => .eq (a.substitute σ) (b.substitute σ)
  | .bot => .bot
  | .and p q => .and (p.substitute σ) (q.substitute σ)
  | .or p q => .or (p.substitute σ) (q.substitute σ)
  | .imp p q => .imp (p.substitute σ) (q.substitute σ)
  | .all p => .all (p.substitute (liftSubstitution σ))
  | .ex p => .ex (p.substitute (liftSubstitution σ))

def Formula.instantiate (body : Formula) (term : Term) : Formula :=
  body.substitute (fun
    | 0 => term
    | n + 1 => .var n)

def Formula.closed (p : Formula) : Prop :=
  ∀ ρ : Nat → Nat, p.rename ρ = p

/-! ## Named finite axiom fragment

`boundedSeparation body` is a schema indexed by a formula with two free
variables: `var 0` is the candidate member and `var 1` is the source set.
The formation predicate is intentionally explicit, so strengthening the schema
cannot happen silently.
-/

def extensionality : Sentence :=
  .all (.all (.imp
    (.all (.iff
      (.mem (.var 0) (.var 2))
      (.mem (.var 0) (.var 1))))
    (.eq (.var 1) (.var 0))))

def emptySet : Sentence :=
  .all (.neg (.mem (.var 0) .empty))

def pairing : Sentence :=
  .all (.all (.all (.iff
    (.mem (.var 0) (.pair (.var 2) (.var 1)))
    (.or (.eq (.var 0) (.var 2)) (.eq (.var 0) (.var 1))))))

def unionSet : Sentence :=
  .all (.all (.iff
    (.mem (.var 0) (.union (.var 1)))
    (.ex (.and
      (.mem (.var 1) (.var 0))
      (.mem (.var 0) (.var 2))))))

def powerSet : Sentence :=
  .all (.all (.iff
    (.mem (.var 0) (.powerset (.var 1)))
    (.all (.imp
      (.mem (.var 0) (.var 1))
      (.mem (.var 0) (.var 2))))))

/- A bounded formula uses no primitive unbounded quantifier.  Quantification
   may still be represented by the usual bounded encoding in the object logic. -/
inductive Bounded : Formula → Prop where
  | mem (a b) : Bounded (.mem a b)
  | eq (a b) : Bounded (.eq a b)
  | bot : Bounded .bot
  | and {p q} : Bounded p → Bounded q → Bounded (.and p q)
  | or {p q} : Bounded p → Bounded q → Bounded (.or p q)
  | imp {p q} : Bounded p → Bounded q → Bounded (.imp p q)

def separationInstance (body : Formula) : Sentence :=
  .all (.ex (.all (.iff
    (.mem (.var 0) (.var 1))
    (.and
      (.mem (.var 0) (.var 2))
      (body.rename (fun
        | 0 => 0
        | n + 1 => n + 2))))))

/- Infinity is deliberately a schema hook rather than a hidden appeal to Lean's
   `Nat`: a client supplies an object-language sentence describing the chosen
   finite-stage infinity principle and proves it is closed. -/
structure InfinitySchema where
  statement : Sentence
  closed : statement.closed
  const_free : statement.ConstFree
  substitution_closed : ∀ substitution,
    statement.substitute substitution = statement

inductive Axiom (infinity : InfinitySchema) : Sentence → Prop where
  | extensionality : Axiom infinity ReferenceFoundation.extensionality
  | emptySet : Axiom infinity ReferenceFoundation.emptySet
  | pairing : Axiom infinity ReferenceFoundation.pairing
  | unionSet : Axiom infinity ReferenceFoundation.unionSet
  | powerSet : Axiom infinity ReferenceFoundation.powerSet
  | boundedSeparation {body} : Bounded body → body.Scoped 2 → body.ConstFree →
      (∀ substitution, (separationInstance body).substitute substitution =
        separationInstance body) →
      Axiom infinity (separationInstance body)
  | infinity : Axiom infinity infinity.statement

/-! ## Intuitionistic natural deduction -/

inductive Derives (infinity : InfinitySchema) : Context → Formula → Prop where
  | assumption {Γ p} : p ∈ Γ → Derives infinity Γ p
  | axiom {Γ p} : Axiom infinity p → Derives infinity Γ p
  | topIntro {Γ} : Derives infinity Γ .top
  | botElim {Γ p} : Derives infinity Γ .bot → Derives infinity Γ p
  | andIntro {Γ p q} : Derives infinity Γ p → Derives infinity Γ q →
      Derives infinity Γ (.and p q)
  | andElimLeft {Γ p q} : Derives infinity Γ (.and p q) → Derives infinity Γ p
  | andElimRight {Γ p q} : Derives infinity Γ (.and p q) → Derives infinity Γ q
  | orIntroLeft {Γ p q} : Derives infinity Γ p → Derives infinity Γ (.or p q)
  | orIntroRight {Γ p q} : Derives infinity Γ q → Derives infinity Γ (.or p q)
  | orElim {Γ p q r} : Derives infinity Γ (.or p q) →
      Derives infinity (p :: Γ) r → Derives infinity (q :: Γ) r →
      Derives infinity Γ r
  | impIntro {Γ p q} : Derives infinity (p :: Γ) q →
      Derives infinity Γ (.imp p q)
  | impElim {Γ p q} : Derives infinity Γ (.imp p q) →
      Derives infinity Γ p → Derives infinity Γ q
  | allIntro {Γ p} : Derives infinity (Γ.map (Formula.rename Nat.succ)) p →
      Derives infinity Γ (.all p)
  | allElim {Γ p} : Derives infinity Γ (.all p) → (term : Term) →
      Derives infinity Γ (p.instantiate term)
  | exIntro {Γ p} (term : Term) : Derives infinity Γ (p.instantiate term) →
      Derives infinity Γ (.ex p)
  | exElim {Γ p q} : Derives infinity Γ (.ex p) →
      Derives infinity (p :: Γ.map (Formula.rename Nat.succ)) (q.rename Nat.succ) →
      Derives infinity Γ q

structure Theory where
  infinity : InfinitySchema

def Theory.Proves (theory : Theory) (p : Sentence) : Prop :=
  Derives theory.infinity [] p

def Theory.Consistent (theory : Theory) : Prop :=
  ¬ theory.Proves .bot

/- The exact public surface consumed by the later interpretation theorem. -/
structure CompletionTarget where
  theory : Theory
  encodedObject : Type u
  encodeTerm : Term → encodedObject
  encodeFormula : Formula → Prop

end IncidenceCore.ReferenceFoundation
