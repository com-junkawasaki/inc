/-!
  A propositional internal-logic fragment whose atoms may be incidences.
  The soundness theorem is independent of a particular incidence model; clients
  instantiate `Atom` with their incidence type.
-/

namespace IncidenceCore

universe u v

inductive Formula (Atom : Type u) where
  | atom : Atom → Formula Atom
  | top : Formula Atom
  | bot : Formula Atom
  | and : Formula Atom → Formula Atom → Formula Atom
  | or : Formula Atom → Formula Atom → Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom

def Formula.map {Atom Atom' : Type u} (f : Atom → Atom') : Formula Atom → Formula Atom'
  | .atom a => .atom (f a)
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.map f) (q.map f)
  | .or p q => .or (p.map f) (q.map f)
  | .imp p q => .imp (p.map f) (q.map f)

def Formula.neg {Atom : Type u} (formula : Formula Atom) : Formula Atom :=
  .imp formula .bot

def formulaSubformulas {Atom : Type u} : Formula Atom → List (Formula Atom)
  | .atom atom => [.atom atom]
  | .top => [.top]
  | .bot => [.bot]
  | .and p q => .and p q :: formulaSubformulas p ++ formulaSubformulas q
  | .or p q => .or p q :: formulaSubformulas p ++ formulaSubformulas q
  | .imp p q => .imp p q :: formulaSubformulas p ++ formulaSubformulas q

theorem formula_mem_subformulas (formula : Formula Atom) :
    formula ∈ formulaSubformulas formula := by
  cases formula <;> simp [formulaSubformulas]

theorem left_mem_subformulas_and (p q : Formula Atom) :
    p ∈ formulaSubformulas (.and p q) := by
  simp [formulaSubformulas, formula_mem_subformulas]

theorem right_mem_subformulas_and (p q : Formula Atom) :
    q ∈ formulaSubformulas (.and p q) := by
  simp [formulaSubformulas, formula_mem_subformulas]

theorem left_mem_subformulas_or (p q : Formula Atom) :
    p ∈ formulaSubformulas (.or p q) := by
  simp [formulaSubformulas, formula_mem_subformulas]

theorem right_mem_subformulas_or (p q : Formula Atom) :
    q ∈ formulaSubformulas (.or p q) := by
  simp [formulaSubformulas, formula_mem_subformulas]

theorem left_mem_subformulas_imp (p q : Formula Atom) :
    p ∈ formulaSubformulas (.imp p q) := by
  simp [formulaSubformulas, formula_mem_subformulas]

theorem right_mem_subformulas_imp (p q : Formula Atom) :
    q ∈ formulaSubformulas (.imp p q) := by
  simp [formulaSubformulas, formula_mem_subformulas]

theorem formulaSubformulas_trans {Atom : Type u} {formula subformula nested : Formula Atom}
    (hsub : subformula ∈ formulaSubformulas formula)
    (hnested : nested ∈ formulaSubformulas subformula) :
    nested ∈ formulaSubformulas formula := by
  induction formula generalizing subformula nested with
  | atom atom =>
    have h : subformula = .atom atom := by simpa [formulaSubformulas] using hsub
    subst subformula
    exact hnested
  | top =>
    have h : subformula = .top := by simpa [formulaSubformulas] using hsub
    subst subformula
    exact hnested
  | bot =>
    have h : subformula = .bot := by simpa [formulaSubformulas] using hsub
    subst subformula
    exact hnested
  | and p q ihp ihq =>
    rcases List.mem_cons.mp hsub with rfl | hsub
    · exact hnested
    rcases List.mem_append.mp hsub with hp | hq
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihp hp hnested)))
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihq hq hnested)))
  | or p q ihp ihq =>
    rcases List.mem_cons.mp hsub with rfl | hsub
    · exact hnested
    rcases List.mem_append.mp hsub with hp | hq
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihp hp hnested)))
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihq hq hnested)))
  | imp p q ihp ihq =>
    rcases List.mem_cons.mp hsub with rfl | hsub
    · exact hnested
    rcases List.mem_append.mp hsub with hp | hq
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihp hp hnested)))
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihq hq hnested)))

def Formula.mapContext {Atom Atom' : Type u} (f : Atom → Atom')
    (context : List (Formula Atom)) : List (Formula Atom') :=
  context.map (Formula.map f)

def Satisfies {Atom : Type u} (valuation : Atom → Prop) : Formula Atom → Prop
  | .atom a => valuation a
  | .top => True
  | .bot => False
  | .and p q => Satisfies valuation p ∧ Satisfies valuation q
  | .or p q => Satisfies valuation p ∨ Satisfies valuation q
  | .imp p q => Satisfies valuation p → Satisfies valuation q

def ContextSatisfies {Atom : Type u} (valuation : Atom → Prop)
    (context : List (Formula Atom)) : Prop :=
  ∀ formula, formula ∈ context → Satisfies valuation formula

def ContextSubset {Atom : Type u} (source target : List (Formula Atom)) : Prop :=
  ∀ formula, formula ∈ source → formula ∈ target

def SemanticallyEntails {Atom : Type u} (context : List (Formula Atom))
    (formula : Formula Atom) : Prop :=
  ∀ valuation : Atom → Prop, ContextSatisfies valuation context →
    Satisfies valuation formula

theorem satisfies_map {Atom Atom' : Type u} (f : Atom → Atom')
    (valuation : Atom' → Prop) : ∀ formula : Formula Atom,
      Satisfies valuation (formula.map f) ↔ Satisfies (fun atom => valuation (f atom)) formula := by
  intro formula
  induction formula with
  | atom => exact Iff.rfl
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | and p q ihp ihq => exact and_congr ihp ihq
  | or p q ihp ihq => exact or_congr ihp ihq
  | imp p q ihp ihq =>
    constructor
    · intro h hp
      exact ihq.mp (h (ihp.mpr hp))
    · intro h hp
      exact ihq.mpr (h (ihp.mp hp))

inductive Derives {Atom : Type u} : List (Formula Atom) → Formula Atom → Prop where
  | ax {p} : p ∈ context → Derives context p
  | topI : Derives context .top
  | botE {p} : Derives context .bot → Derives context p
  | andI {p q} : Derives context p → Derives context q → Derives context (.and p q)
  | andEL {p q} : Derives context (.and p q) → Derives context p
  | andER {p q} : Derives context (.and p q) → Derives context q
  | orIL {p q} : Derives context p → Derives context (.or p q)
  | orIR {p q} : Derives context q → Derives context (.or p q)
  | orE {p q r} : Derives context (.or p q) →
      Derives (p :: context) r → Derives (q :: context) r → Derives context r
  | impI {p q} : Derives (p :: context) q → Derives context (.imp p q)
  | impE {p q} : Derives context (.imp p q) → Derives context p → Derives context q

def DerivationallyConsistent {Atom : Type u} (context : List (Formula Atom)) : Prop :=
  ¬ Derives context .bot

def DerivationallyAvoids {Atom : Type u} (context : List (Formula Atom))
    (forbidden : Formula Atom) : Prop :=
  ¬ Derives context forbidden

theorem derives_sound {Atom : Type u} {context : List (Formula Atom)}
    {formula : Formula Atom} (derivation : Derives context formula) :
    ∀ {valuation : Atom → Prop}, ContextSatisfies valuation context →
      Satisfies valuation formula := by
  induction derivation with
  | ax h =>
    intro valuation holds
    exact holds _ h
  | topI =>
    intro valuation holds
    trivial
  | botE d ih =>
    intro valuation holds
    exact False.elim (ih holds)
  | andI dp dq ihp ihq =>
    intro valuation holds
    exact ⟨ihp holds, ihq holds⟩
  | andEL d ih =>
    intro valuation holds
    exact (ih holds).left
  | andER d ih =>
    intro valuation holds
    exact (ih holds).right
  | orIL d ih =>
    intro valuation holds
    exact Or.inl (ih holds)
  | orIR d ih =>
    intro valuation holds
    exact Or.inr (ih holds)
  | orE dpq dpr dqr ihpq ihpr ihqr =>
    intro valuation holds
    rcases ihpq holds with hp | hq
    · apply ihpr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · exact holds x hx
    · apply ihqr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hq
      · exact holds x hx
  | impI d ih =>
    intro valuation holds hp
    apply ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · exact holds x hx
  | impE dpq dp ihpq ihp =>
    intro valuation holds
    exact ihpq holds (ihp holds)

theorem derives_semantically_entails {Atom : Type u} {context : List (Formula Atom)}
    {formula : Formula Atom} (derivation : Derives context formula) :
    SemanticallyEntails context formula :=
  fun _ holds => derives_sound derivation holds

/- Formula translation acts functorially on proofs: translating atoms cannot
   turn a derivation into a non-derivation. -/
theorem derives_map {Atom Atom' : Type u} (f : Atom → Atom')
    {context : List (Formula Atom)} {formula : Formula Atom} :
    Derives context formula →
      Derives (Formula.mapContext f context) (formula.map f) := by
  intro derivation
  induction derivation with
  | ax h => exact Derives.ax (List.mem_map.mpr ⟨_, h, rfl⟩)
  | topI => exact Derives.topI
  | botE d ih => exact Derives.botE ih
  | andI dp dq ihp ihq => exact Derives.andI ihp ihq
  | andEL d ih => exact Derives.andEL ih
  | andER d ih => exact Derives.andER ih
  | orIL d ih => exact Derives.orIL ih
  | orIR d ih => exact Derives.orIR ih
  | orE dpq dpr dqr ihpq ihpr ihqr =>
    apply Derives.orE ihpq
    · simpa [Formula.mapContext] using ihpr
    · simpa [Formula.mapContext] using ihqr
  | impI d ih =>
    apply Derives.impI
    simpa [Formula.mapContext] using ih
  | impE dpq dp ihpq ihp => exact Derives.impE ihpq ihp

/- Structural weakening is needed whenever an incidence translation introduces
   auxiliary assumptions. -/
theorem derives_weaken {Atom : Type u} {source target : List (Formula Atom)}
    {formula : Formula Atom} (hsub : ContextSubset source target) :
    Derives source formula → Derives target formula := by
  intro derivation
  induction derivation generalizing target with
  | ax h => exact Derives.ax (hsub _ h)
  | topI => exact Derives.topI
  | botE d ih => exact Derives.botE (ih hsub)
  | andI dp dq ihp ihq => exact Derives.andI (ihp hsub) (ihq hsub)
  | andEL d ih => exact Derives.andEL (ih hsub)
  | andER d ih => exact Derives.andER (ih hsub)
  | orIL d ih => exact Derives.orIL (ih hsub)
  | orIR d ih => exact Derives.orIR (ih hsub)
  | orE dpq dpr dqr ihpq ihpr ihqr =>
    apply Derives.orE (ihpq hsub)
    · apply ihpr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem _ (hsub _ hx)
    · apply ihqr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem _ (hsub _ hx)
  | impI d ih =>
    apply Derives.impI
    apply ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact List.mem_cons_of_mem _ (hsub _ hx)
  | impE dpq dp ihpq ihp => exact Derives.impE (ihpq hsub) (ihp hsub)

/- Simultaneous replacement of assumptions by their derivations.  This is the
   syntactic substitution principle used by the canonical-model construction. -/
theorem derives_substitute {Atom : Type u} {source target : List (Formula Atom)}
    {formula : Formula Atom}
    (assumptions : ∀ assumption, assumption ∈ source → Derives target assumption) :
    Derives source formula → Derives target formula := by
  intro derivation
  induction derivation generalizing target with
  | ax h => exact assumptions _ h
  | topI => exact Derives.topI
  | botE d ih => exact Derives.botE (ih assumptions)
  | andI dp dq ihp ihq => exact Derives.andI (ihp assumptions) (ihq assumptions)
  | andEL d ih => exact Derives.andEL (ih assumptions)
  | andER d ih => exact Derives.andER (ih assumptions)
  | orIL d ih => exact Derives.orIL (ih assumptions)
  | orIR d ih => exact Derives.orIR (ih assumptions)
  | orE dpq dpr dqr ihpq ihpr ihqr =>
    apply Derives.orE (ihpq assumptions)
    · apply ihpr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Derives.ax (by simp)
      · exact derives_weaken (fun y hy => List.mem_cons_of_mem _ hy) (assumptions x hx)
    · apply ihqr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Derives.ax (by simp)
      · exact derives_weaken (fun y hy => List.mem_cons_of_mem _ hy) (assumptions x hx)
  | impI d ih =>
    apply Derives.impI
    apply ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Derives.ax (by simp)
    · exact derives_weaken (fun y hy => List.mem_cons_of_mem _ hy) (assumptions x hx)
  | impE dpq dp ihpq ihp => exact Derives.impE (ihpq assumptions) (ihp assumptions)

/- The derivable formulas of any finite context form a deductively closed
   theory.  This turns finite Lindenbaum contexts into genuine theory objects. -/
structure DeductivelyClosedTheory (Atom : Type u) where
  contains : Formula Atom → Prop
  closed : ∀ {context formula},
    (∀ assumption, assumption ∈ context → contains assumption) →
      Derives context formula → contains formula

def derivationClosure {Atom : Type u} (context : List (Formula Atom))
    (formula : Formula Atom) : Prop :=
  Derives context formula

theorem derivationClosure_closed {Atom : Type u} (base : List (Formula Atom)) :
    ∀ {context formula},
      (∀ assumption, assumption ∈ context → derivationClosure base assumption) →
        Derives context formula → derivationClosure base formula := by
  intro context formula hassumptions derivation
  exact derives_substitute hassumptions derivation

def derivationClosedTheory {Atom : Type u} (context : List (Formula Atom)) :
    DeductivelyClosedTheory Atom where
  contains := derivationClosure context
  closed := derivationClosure_closed context

def PrimeOn {Atom : Type u} (candidates : List (Formula Atom))
    (contains : Formula Atom → Prop) : Prop :=
  ∀ p q, p ∈ candidates → q ∈ candidates →
    contains (.or p q) → contains p ∨ contains q

/- A finite, closed prime theory.  Unlike `PrimeTheory`, primeness and
   decidability are deliberately restricted to its recorded finite language;
   this is the concrete object supplied by the finite Lindenbaum construction. -/
structure FinitePrimeTheory (Atom : Type u) where
  candidates : List (Formula Atom)
  contains : Formula Atom → Prop
  closed : ∀ {context formula},
    (∀ assumption, assumption ∈ context → contains assumption) →
      Derives context formula → contains formula
  consistent : ¬ contains .bot
  decides : ∀ formula, formula ∈ candidates →
    contains formula ∨ contains formula.neg
  prime : PrimeOn candidates contains

theorem finitePrimeTheory_contains_derivable {Atom : Type u}
    (theory : FinitePrimeTheory Atom) {context : List (Formula Atom)}
    {formula : Formula Atom}
    (hcontext : ∀ assumption, assumption ∈ context → theory.contains assumption)
    (hderives : Derives context formula) : theory.contains formula :=
  theory.closed hcontext hderives

theorem derives_cut {Atom : Type u} {context : List (Formula Atom)}
    {assumption formula : Formula Atom} :
    Derives context assumption → Derives (assumption :: context) formula →
      Derives context formula := by
  intro hassumption hformula
  apply derives_substitute (source := assumption :: context)
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hassumption
    · exact Derives.ax hx
  · exact hformula

theorem derives_imp_iff {Atom : Type u} {context : List (Formula Atom)}
    {assumption conclusion : Formula Atom} :
    Derives context (.imp assumption conclusion) ↔
      Derives (assumption :: context) conclusion := by
  constructor
  · intro himp
    exact Derives.impE
      (derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) himp)
      (Derives.ax (by simp))
  · exact Derives.impI

theorem inconsistent_extension_iff_derives_neg {Atom : Type u}
    {context : List (Formula Atom)} {formula : Formula Atom} :
    Derives (formula :: context) .bot ↔ Derives context formula.neg :=
  derives_imp_iff.symm

/- The one-step Lindenbaum lemma.  It gives a consistency-preserving choice at
   every formula; a full extension theorem still needs an enumeration and the
   limit-stage closure argument. -/
theorem consistent_extend_formula_or_neg {Atom : Type u}
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hconsistent : DerivationallyConsistent context) :
    DerivationallyConsistent (formula :: context) ∨
      DerivationallyConsistent (formula.neg :: context) := by
  by_cases hformula : DerivationallyConsistent (formula :: context)
  · exact Or.inl hformula
  · right
    intro hneg
    apply hconsistent
    have hformulaBot : Derives (formula :: context) .bot :=
      Classical.byContradiction hformula
    have hformulaNeg : Derives context formula.neg :=
      inconsistent_extension_iff_derives_neg.mp hformulaBot
    have hnegNeg : Derives context formula.neg.neg :=
      inconsistent_extension_iff_derives_neg.mp hneg
    exact Derives.impE hnegNeg hformulaNeg

/- A supplied enumeration is the only infinitary input needed to pass from
   finite Lindenbaum steps to a countable chain.  Keeping it explicit avoids
   imposing a countability assumption on arbitrary incidence-atom types. -/
structure FormulaEnumeration (Atom : Type u) where
  enumerate : Nat → Formula Atom
  exhaustive : ∀ formula, ∃ index, enumerate index = formula

noncomputable def lindenbaumChain {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) : Nat → List (Formula Atom)
  | 0 => []
  | n + 1 => by
    classical
    exact if DerivationallyConsistent
      (enumeration.enumerate n :: lindenbaumChain enumeration n)
      then enumeration.enumerate n :: lindenbaumChain enumeration n
      else (enumeration.enumerate n).neg :: lindenbaumChain enumeration n

theorem lindenbaumChain_subset_succ {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (n : Nat) :
    ContextSubset (lindenbaumChain enumeration n) (lindenbaumChain enumeration (n + 1)) := by
  simp only [lindenbaumChain]
  split <;> intro formula hmem <;> exact List.mem_cons_of_mem _ hmem

theorem lindenbaumChain_consistent {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) :
    ∀ n, DerivationallyConsistent (lindenbaumChain enumeration n) := by
  intro n
  induction n with
  | zero =>
    intro hbot
    change Derives [] .bot at hbot
    have hfalse := derives_sound hbot
      (valuation := fun _ : Atom => False) (by
        intro formula hmem
        simp at hmem)
    exact hfalse
  | succ n ih =>
    simp only [lindenbaumChain]
    split
    · assumption
    · rename_i hnot
      rcases consistent_extend_formula_or_neg
        (context := lindenbaumChain enumeration n)
        (formula := enumeration.enumerate n) ih with hpos | hneg
      · exact False.elim (hnot hpos)
      · exact hneg

theorem lindenbaumChain_decides {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (formula : Formula Atom) :
    ∃ stage, formula ∈ lindenbaumChain enumeration stage ∨
      formula.neg ∈ lindenbaumChain enumeration stage := by
  rcases enumeration.exhaustive formula with ⟨index, hindex⟩
  refine ⟨index + 1, ?_⟩
  rw [← hindex]
  simp only [lindenbaumChain]
  split
  · exact Or.inl List.mem_cons_self
  · exact Or.inr List.mem_cons_self

theorem lindenbaumChain_subset_of_le {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) {source target : Nat} :
    source ≤ target →
      ContextSubset (lindenbaumChain enumeration source)
        (lindenbaumChain enumeration target) := by
  intro hle
  induction target generalizing source with
  | zero =>
    have hzero : source = 0 := Nat.eq_zero_of_le_zero hle
    subst source
    exact fun _ h => h
  | succ target ih =>
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · intro formula hmem
      exact lindenbaumChain_subset_succ enumeration target formula
        (ih (Nat.le_of_lt_succ hlt) formula hmem)
    · exact fun _ h => h

theorem lindenbaumChain_derives_mono {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) {source target : Nat}
    (hle : source ≤ target) {formula : Formula Atom} :
    Derives (lindenbaumChain enumeration source) formula →
      Derives (lindenbaumChain enumeration target) formula :=
  derives_weaken (lindenbaumChain_subset_of_le enumeration hle)

def lindenbaumLimitDerives {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (formula : Formula Atom) : Prop :=
  ∃ stage, Derives (lindenbaumChain enumeration stage) formula

theorem finite_context_lindenbaum_bound {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) :
    ∀ context : List (Formula Atom),
      (∀ assumption, assumption ∈ context → lindenbaumLimitDerives enumeration assumption) →
        ∃ stage, ∀ assumption, assumption ∈ context →
          Derives (lindenbaumChain enumeration stage) assumption := by
  intro context
  induction context with
  | nil =>
    intro _
    exact ⟨0, by intro assumption hmem; simp at hmem⟩
  | cons head tail ih =>
    intro hcontains
    rcases hcontains head (by simp) with ⟨headStage, hhead⟩
    rcases ih (by
      intro assumption hassumption
      exact hcontains assumption (List.mem_cons_of_mem _ hassumption)) with
      ⟨tailStage, htail⟩
    refine ⟨Nat.max headStage tailStage, ?_⟩
    intro assumption hassumption
    rcases List.mem_cons.mp hassumption with rfl | hassumption
    · exact lindenbaumChain_derives_mono enumeration (Nat.le_max_left _ _) hhead
    · exact lindenbaumChain_derives_mono enumeration (Nat.le_max_right _ _)
        (htail assumption hassumption)

theorem lindenbaumLimitDerives_closed {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) :
    ∀ {context formula},
      (∀ assumption, assumption ∈ context → lindenbaumLimitDerives enumeration assumption) →
        Derives context formula → lindenbaumLimitDerives enumeration formula := by
  intro context formula hcontains hderives
  rcases finite_context_lindenbaum_bound enumeration context hcontains with ⟨stage, hstage⟩
  exact ⟨stage, derives_substitute hstage hderives⟩

theorem lindenbaumLimitDerives_consistent {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) :
    ¬ lindenbaumLimitDerives enumeration .bot := by
  rintro ⟨stage, hbot⟩
  exact lindenbaumChain_consistent enumeration stage hbot

theorem lindenbaumLimitDerives_decides {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (formula : Formula Atom) :
    lindenbaumLimitDerives enumeration formula ∨
      lindenbaumLimitDerives enumeration formula.neg := by
  rcases lindenbaumChain_decides enumeration formula with ⟨stage, hpos | hneg⟩
  · exact Or.inl ⟨stage, Derives.ax hpos⟩
  · exact Or.inr ⟨stage, Derives.ax hneg⟩

/- The same countable construction can start from an arbitrary consistent
   finite context.  This is the extension half of the Lindenbaum argument. -/
noncomputable def lindenbaumChainFrom {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom)) :
    Nat → List (Formula Atom)
  | 0 => base
  | n + 1 => by
    classical
    exact if DerivationallyConsistent
      (enumeration.enumerate n :: lindenbaumChainFrom enumeration base n)
      then enumeration.enumerate n :: lindenbaumChainFrom enumeration base n
      else (enumeration.enumerate n).neg :: lindenbaumChainFrom enumeration base n

theorem lindenbaumChainFrom_subset_succ {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom)) (n : Nat) :
    ContextSubset (lindenbaumChainFrom enumeration base n)
      (lindenbaumChainFrom enumeration base (n + 1)) := by
  simp only [lindenbaumChainFrom]
  split <;> intro formula hmem <;> exact List.mem_cons_of_mem _ hmem

theorem lindenbaumChainFrom_consistent {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (hbase : DerivationallyConsistent base) :
    ∀ n, DerivationallyConsistent (lindenbaumChainFrom enumeration base n) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    simp only [lindenbaumChainFrom]
    split
    · assumption
    · rename_i hnot
      rcases consistent_extend_formula_or_neg
        (context := lindenbaumChainFrom enumeration base n)
        (formula := enumeration.enumerate n) ih with hpos | hneg
      · exact False.elim (hnot hpos)
      · exact hneg

theorem base_subset_lindenbaumChainFrom {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom)) :
    ∀ stage, ContextSubset base (lindenbaumChainFrom enumeration base stage) := by
  intro stage
  induction stage with
  | zero => exact fun _ h => h
  | succ stage ih =>
    intro formula hmem
    exact lindenbaumChainFrom_subset_succ enumeration base stage formula (ih formula hmem)

theorem lindenbaumChainFrom_decides {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (formula : Formula Atom) :
    ∃ stage, formula ∈ lindenbaumChainFrom enumeration base stage ∨
      formula.neg ∈ lindenbaumChainFrom enumeration base stage := by
  rcases enumeration.exhaustive formula with ⟨index, hindex⟩
  refine ⟨index + 1, ?_⟩
  rw [← hindex]
  simp only [lindenbaumChainFrom]
  split
  · exact Or.inl List.mem_cons_self
  · exact Or.inr List.mem_cons_self

theorem lindenbaumChainFrom_subset_of_le {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    {source target : Nat} : source ≤ target →
      ContextSubset (lindenbaumChainFrom enumeration base source)
        (lindenbaumChainFrom enumeration base target) := by
  intro hle
  induction target generalizing source with
  | zero =>
    have hzero : source = 0 := Nat.eq_zero_of_le_zero hle
    subst source
    exact fun _ h => h
  | succ target ih =>
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · intro formula hmem
      exact lindenbaumChainFrom_subset_succ enumeration base target formula
        (ih (Nat.le_of_lt_succ hlt) formula hmem)
    · exact fun _ h => h

theorem lindenbaumChainFrom_derives_mono {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    {source target : Nat} (hle : source ≤ target) {formula : Formula Atom} :
    Derives (lindenbaumChainFrom enumeration base source) formula →
      Derives (lindenbaumChainFrom enumeration base target) formula :=
  derives_weaken (lindenbaumChainFrom_subset_of_le enumeration base hle)

def lindenbaumLimitDerivesFrom {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (formula : Formula Atom) : Prop :=
  ∃ stage, Derives (lindenbaumChainFrom enumeration base stage) formula

theorem finite_context_lindenbaumFrom_bound {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom)) :
    ∀ context : List (Formula Atom),
      (∀ assumption, assumption ∈ context →
        lindenbaumLimitDerivesFrom enumeration base assumption) →
        ∃ stage, ∀ assumption, assumption ∈ context →
          Derives (lindenbaumChainFrom enumeration base stage) assumption := by
  intro context
  induction context with
  | nil =>
    intro _
    exact ⟨0, by intro assumption hmem; simp at hmem⟩
  | cons head tail ih =>
    intro hcontains
    rcases hcontains head (by simp) with ⟨headStage, hhead⟩
    rcases ih (by
      intro assumption hassumption
      exact hcontains assumption (List.mem_cons_of_mem _ hassumption)) with
      ⟨tailStage, htail⟩
    refine ⟨Nat.max headStage tailStage, ?_⟩
    intro assumption hassumption
    rcases List.mem_cons.mp hassumption with rfl | hassumption
    · exact lindenbaumChainFrom_derives_mono enumeration base
        (Nat.le_max_left _ _) hhead
    · exact lindenbaumChainFrom_derives_mono enumeration base
        (Nat.le_max_right _ _) (htail assumption hassumption)

theorem lindenbaumLimitDerivesFrom_closed {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom)) :
    ∀ {context formula},
      (∀ assumption, assumption ∈ context →
        lindenbaumLimitDerivesFrom enumeration base assumption) →
        Derives context formula →
          lindenbaumLimitDerivesFrom enumeration base formula := by
  intro context formula hcontains hderives
  rcases finite_context_lindenbaumFrom_bound enumeration base context hcontains with
    ⟨stage, hstage⟩
  exact ⟨stage, derives_substitute hstage hderives⟩

theorem lindenbaumLimitDerivesFrom_consistent {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (hbase : DerivationallyConsistent base) :
    ¬ lindenbaumLimitDerivesFrom enumeration base .bot := by
  rintro ⟨stage, hbot⟩
  exact lindenbaumChainFrom_consistent enumeration base hbase stage hbot

theorem lindenbaumLimitDerivesFrom_decides {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (formula : Formula Atom) :
    lindenbaumLimitDerivesFrom enumeration base formula ∨
      lindenbaumLimitDerivesFrom enumeration base formula.neg := by
  rcases lindenbaumChainFrom_decides enumeration base formula with ⟨stage, hpos | hneg⟩
  · exact Or.inl ⟨stage, Derives.ax hpos⟩
  · exact Or.inr ⟨stage, Derives.ax hneg⟩

/- A finite Lindenbaum chain.  Every finite family of formulas can be decided
   (formula or negation) while retaining all initial assumptions and
   derivational consistency. -/
theorem finite_lindenbaum_extension {Atom : Type u}
    (context candidates : List (Formula Atom))
    (hconsistent : DerivationallyConsistent context) :
    ∃ extension : List (Formula Atom),
      ContextSubset context extension ∧ DerivationallyConsistent extension ∧
        ∀ formula, formula ∈ candidates →
          formula ∈ extension ∨ formula.neg ∈ extension := by
  induction candidates generalizing context with
  | nil =>
    refine ⟨context, (fun formula hmem => hmem), hconsistent, ?_⟩
    intro formula hmem
    simp at hmem
  | cons candidate candidates ih =>
    rcases consistent_extend_formula_or_neg (context := context) (formula := candidate)
      hconsistent with hpos | hneg
    · rcases ih (candidate :: context) hpos with ⟨extension, hsub, hext, hdec⟩
      refine ⟨extension, ?_, hext, ?_⟩
      · intro formula hmem
        exact hsub formula (List.mem_cons_of_mem candidate hmem)
      · intro formula hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Or.inl (hsub formula (by simp))
        · exact hdec formula hmem
    · rcases ih (candidate.neg :: context) hneg with ⟨extension, hsub, hext, hdec⟩
      refine ⟨extension, ?_, hext, ?_⟩
      · intro formula hmem
        exact hsub formula (List.mem_cons_of_mem candidate.neg hmem)
      · intro formula hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Or.inr (hsub formula.neg (by simp))
        · exact hdec formula hmem

/- If both disjuncts have been decided in a consistent context, a derivable
   disjunction has a derivable side.  This is the finite prime-theory step. -/
theorem derives_or_choice_of_decisions {Atom : Type u}
    {context : List (Formula Atom)} {p q : Formula Atom}
    (hconsistent : DerivationallyConsistent context)
    (hor : Derives context (.or p q))
    (hp : p ∈ context ∨ p.neg ∈ context)
    (hq : q ∈ context ∨ q.neg ∈ context) :
    Derives context p ∨ Derives context q := by
  rcases hp with hp | hnp
  · exact Or.inl (Derives.ax hp)
  rcases hq with hq | hnq
  · exact Or.inr (Derives.ax hq)
  · exact False.elim (hconsistent (Derives.orE hor
      (Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem p hmem)
          (Derives.ax hnp))
        (Derives.ax (by simp)))
      (Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem q hmem)
          (Derives.ax hnq))
        (Derives.ax (by simp)))))

theorem finite_lindenbaum_prime_extension {Atom : Type u}
    (context candidates : List (Formula Atom))
    (hconsistent : DerivationallyConsistent context) :
    ∃ extension : List (Formula Atom),
      ContextSubset context extension ∧ DerivationallyConsistent extension ∧
        (∀ formula, formula ∈ candidates →
          formula ∈ extension ∨ formula.neg ∈ extension) ∧
        (∀ p q, p ∈ candidates → q ∈ candidates →
          Derives extension (.or p q) → Derives extension p ∨ Derives extension q) := by
  rcases finite_lindenbaum_extension context candidates hconsistent with
    ⟨extension, hsub, hext, hdec⟩
  refine ⟨extension, hsub, hext, hdec, ?_⟩
  intro p q hp hq hor
  exact derives_or_choice_of_decisions hext hor (hdec p hp) (hdec q hq)

theorem finite_lindenbaum_subformula_extension {Atom : Type u}
    (context : List (Formula Atom)) (formula : Formula Atom)
    (hconsistent : DerivationallyConsistent context) :
    ∃ extension : List (Formula Atom),
      ContextSubset context extension ∧ DerivationallyConsistent extension ∧
        ∀ subformula, subformula ∈ formulaSubformulas formula →
          subformula ∈ extension ∨ subformula.neg ∈ extension :=
  finite_lindenbaum_extension context (formulaSubformulas formula) hconsistent

theorem finite_subformula_prime_extension {Atom : Type u}
    (context : List (Formula Atom)) (formula : Formula Atom)
    (hconsistent : DerivationallyConsistent context) :
    ∃ extension : List (Formula Atom),
      ContextSubset context extension ∧ DerivationallyConsistent extension ∧
        (∀ subformula, subformula ∈ formulaSubformulas formula →
          subformula ∈ extension ∨ subformula.neg ∈ extension) ∧
        (∀ p q, (.or p q) ∈ formulaSubformulas formula →
          Derives extension (.or p q) → Derives extension p ∨ Derives extension q) := by
  rcases finite_lindenbaum_prime_extension context (formulaSubformulas formula) hconsistent with
    ⟨extension, hsub, hext, hdec, hprime⟩
  refine ⟨extension, hsub, hext, hdec, ?_⟩
  intro p q hor hderives
  apply hprime p q
  · exact formulaSubformulas_trans hor (left_mem_subformulas_or p q)
  · exact formulaSubformulas_trans hor (right_mem_subformulas_or p q)
  · exact hderives

theorem finite_subformula_prime_closed_theory {Atom : Type u}
    (context : List (Formula Atom)) (formula : Formula Atom)
    (hconsistent : DerivationallyConsistent context) :
    ∃ extension : List (Formula Atom),
      ContextSubset context extension ∧ DerivationallyConsistent extension ∧
        (∀ subformula, subformula ∈ formulaSubformulas formula →
          derivationClosure extension subformula ∨
            derivationClosure extension subformula.neg) ∧
        PrimeOn (formulaSubformulas formula) (derivationClosure extension) := by
  rcases finite_lindenbaum_prime_extension context (formulaSubformulas formula) hconsistent with
    ⟨extension, hsub, hext, hdec, hprime⟩
  refine ⟨extension, hsub, hext, ?_, ?_⟩
  · intro subformula hmem
    rcases hdec subformula hmem with hsubformula | hneg
    · exact Or.inl (Derives.ax hsubformula)
    · exact Or.inr (Derives.ax hneg)
  · intro p q hp hq hor
    exact hprime p q hp hq hor

/- The finite Lindenbaum construction now yields an actual bounded canonical
   world: it is closed under every derivation, consistent, and prime/decisive
   on exactly the finite subformula language under consideration. -/
theorem finite_subformula_finitePrimeTheory {Atom : Type u}
    (context : List (Formula Atom)) (formula : Formula Atom)
    (hconsistent : DerivationallyConsistent context) :
    ∃ theory : FinitePrimeTheory Atom,
      theory.candidates = formulaSubformulas formula ∧
      ∀ assumption, assumption ∈ context → theory.contains assumption := by
  rcases finite_subformula_prime_closed_theory context formula hconsistent with
    ⟨extension, hsub, hext, hdec, hprime⟩
  refine ⟨{
    candidates := formulaSubformulas formula
    contains := derivationClosure extension
    closed := derivationClosure_closed extension
    consistent := hext
    decides := hdec
    prime := hprime
  }, rfl, ?_⟩
  intro assumption hassumption
  exact Derives.ax (hsub assumption hassumption)

/- Relative Lindenbaum steps for a fixed forbidden conclusion.  These are the
   local countermodel lemmas required by the implication and disjunction cases
   of a canonical completeness proof. -/
theorem avoids_imp_extension {Atom : Type u}
    {context : List (Formula Atom)} {premise forbidden : Formula Atom}
    (havoid : DerivationallyAvoids context (.imp premise forbidden)) :
    DerivationallyAvoids (premise :: context) forbidden := by
  intro hforbidden
  exact havoid (Derives.impI hforbidden)

theorem avoids_consistent {Atom : Type u} {context : List (Formula Atom)}
    {forbidden : Formula Atom} :
    DerivationallyAvoids context forbidden → DerivationallyConsistent context := by
  intro havoid hbot
  exact havoid (Derives.botE hbot)

theorem avoids_or_extension_left_or_right {Atom : Type u}
    {context : List (Formula Atom)} {left right forbidden : Formula Atom}
    (havoid : DerivationallyAvoids context forbidden)
    (hor : Derives context (.or left right)) :
    DerivationallyAvoids (left :: context) forbidden ∨
      DerivationallyAvoids (right :: context) forbidden := by
  by_cases hleft : DerivationallyAvoids (left :: context) forbidden
  · exact Or.inl hleft
  · right
    intro hright
    apply havoid
    apply Derives.orE hor
    · exact Classical.byContradiction hleft
    · exact hright

/- A recurrent schedule revisits every formula after every finite stage.  It
   is the enumeration datum needed to saturate a theory by disjunction choices
   while preserving a fixed forbidden conclusion. -/
structure RecurrentFormulaSchedule (Atom : Type u) where
  formulaAt : Nat → Formula Atom
  revisits : ∀ formula stage, ∃ later, stage ≤ later ∧ formulaAt later = formula

noncomputable def avoidanceStep {Atom : Type u}
  (forbidden : Formula Atom) (current : List (Formula Atom)) :
    Formula Atom → List (Formula Atom)
  | .or left right => by
    classical
    exact if hor : Derives current (.or left right)
      then if hleft : DerivationallyAvoids (left :: current) forbidden
        then left :: current
        else right :: current
      else current
  | _ => current

noncomputable def avoidanceChain {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) : Nat → List (Formula Atom)
  | 0 => base
  | n + 1 => by
    classical
    exact avoidanceStep forbidden (avoidanceChain schedule forbidden base n)
      (schedule.formulaAt n)

theorem avoidanceStep_subset {Atom : Type u} (forbidden : Formula Atom)
    (current : List (Formula Atom)) (candidate : Formula Atom) :
    ContextSubset current (avoidanceStep forbidden current candidate) := by
  cases candidate with
  | atom => exact fun _ h => h
  | top => exact fun _ h => h
  | bot => exact fun _ h => h
  | and left right => exact fun _ h => h
  | imp left right => exact fun _ h => h
  | or left right =>
    simp only [avoidanceStep]
    split
    · split <;> exact fun _ h => List.mem_cons_of_mem _ h
    · exact fun _ h => h

theorem avoidanceStep_avoids {Atom : Type u} (forbidden : Formula Atom)
    (current : List (Formula Atom)) (candidate : Formula Atom)
    (hcurrent : DerivationallyAvoids current forbidden) :
    DerivationallyAvoids (avoidanceStep forbidden current candidate) forbidden := by
  cases candidate with
  | atom => exact hcurrent
  | top => exact hcurrent
  | bot => exact hcurrent
  | and left right => exact hcurrent
  | imp left right => exact hcurrent
  | or left right =>
    simp only [avoidanceStep]
    split
    · rename_i hor
      split
      · assumption
      · rename_i hnotleft
        rcases avoids_or_extension_left_or_right hcurrent hor with hleft | hright
        · exact False.elim (hnotleft hleft)
        · exact hright
    · exact hcurrent

theorem avoidanceChain_subset_succ {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (n : Nat) :
    ContextSubset (avoidanceChain schedule forbidden base n)
      (avoidanceChain schedule forbidden base (n + 1)) := by
  change ContextSubset _
    (avoidanceStep forbidden (avoidanceChain schedule forbidden base n)
      (schedule.formulaAt n))
  exact avoidanceStep_subset forbidden _ _

theorem avoidanceChain_avoids {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom))
    (hbase : DerivationallyAvoids base forbidden) :
    ∀ n, DerivationallyAvoids (avoidanceChain schedule forbidden base n) forbidden := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    change DerivationallyAvoids
      (avoidanceStep forbidden (avoidanceChain schedule forbidden base n)
        (schedule.formulaAt n)) forbidden
    exact avoidanceStep_avoids forbidden _ _ ih

theorem avoidanceChain_subset_of_le {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {source target : Nat} : source ≤ target →
      ContextSubset (avoidanceChain schedule forbidden base source)
        (avoidanceChain schedule forbidden base target) := by
  intro hle
  induction target generalizing source with
  | zero =>
    have hzero : source = 0 := Nat.eq_zero_of_le_zero hle
    subst source
    exact fun _ h => h
  | succ target ih =>
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · intro formula hmem
      exact avoidanceChain_subset_succ schedule forbidden base target formula
        (ih (Nat.le_of_lt_succ hlt) formula hmem)
    · exact fun _ h => h

theorem avoidanceChain_derives_mono {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {source target : Nat} (hle : source ≤ target)
    {formula : Formula Atom} :
    Derives (avoidanceChain schedule forbidden base source) formula →
      Derives (avoidanceChain schedule forbidden base target) formula :=
  derives_weaken (avoidanceChain_subset_of_le schedule forbidden base hle)

def avoidanceLimitDerives {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (formula : Formula Atom) : Prop :=
  ∃ stage, Derives (avoidanceChain schedule forbidden base stage) formula

theorem finite_context_avoidance_bound {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) :
    ∀ context : List (Formula Atom),
      (∀ assumption, assumption ∈ context →
        avoidanceLimitDerives schedule forbidden base assumption) →
        ∃ stage, ∀ assumption, assumption ∈ context →
          Derives (avoidanceChain schedule forbidden base stage) assumption := by
  intro context
  induction context with
  | nil =>
    intro _
    exact ⟨0, by intro assumption hmem; simp at hmem⟩
  | cons head tail ih =>
    intro hcontains
    rcases hcontains head (by simp) with ⟨headStage, hhead⟩
    rcases ih (by
      intro assumption hassumption
      exact hcontains assumption (List.mem_cons_of_mem _ hassumption)) with
      ⟨tailStage, htail⟩
    refine ⟨Nat.max headStage tailStage, ?_⟩
    intro assumption hassumption
    rcases List.mem_cons.mp hassumption with rfl | hassumption
    · exact avoidanceChain_derives_mono schedule forbidden base
        (Nat.le_max_left _ _) hhead
    · exact avoidanceChain_derives_mono schedule forbidden base
        (Nat.le_max_right _ _) (htail assumption hassumption)

theorem avoidanceLimitDerives_closed {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) :
    ∀ {context formula},
      (∀ assumption, assumption ∈ context →
        avoidanceLimitDerives schedule forbidden base assumption) →
        Derives context formula → avoidanceLimitDerives schedule forbidden base formula := by
  intro context formula hcontains hderives
  rcases finite_context_avoidance_bound schedule forbidden base context hcontains with
    ⟨stage, hstage⟩
  exact ⟨stage, derives_substitute hstage hderives⟩

theorem avoidanceLimitDerives_avoids {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom))
    (hbase : DerivationallyAvoids base forbidden) :
    ¬ avoidanceLimitDerives schedule forbidden base forbidden := by
  rintro ⟨stage, hforbidden⟩
  exact avoidanceChain_avoids schedule forbidden base hbase stage hforbidden

theorem avoidanceLimitDerives_contains_base {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {formula : Formula Atom} :
    formula ∈ base → avoidanceLimitDerives schedule forbidden base formula := by
  intro hformula
  refine ⟨0, ?_⟩
  change Derives base formula
  exact Derives.ax hformula

theorem avoidanceChain_or_choice {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (stage : Nat) (p q : Formula Atom)
    (hscheduled : schedule.formulaAt stage = .or p q)
    (hor : Derives (avoidanceChain schedule forbidden base stage) (.or p q)) :
    p ∈ avoidanceChain schedule forbidden base (stage + 1) ∨
      q ∈ avoidanceChain schedule forbidden base (stage + 1) := by
  change p ∈ avoidanceStep forbidden (avoidanceChain schedule forbidden base stage)
      (schedule.formulaAt stage) ∨
        q ∈ avoidanceStep forbidden (avoidanceChain schedule forbidden base stage)
          (schedule.formulaAt stage)
  rw [hscheduled]
  simp only [avoidanceStep]
  split
  · split
    · exact Or.inl List.mem_cons_self
    · exact Or.inr List.mem_cons_self
  · rename_i hnot
    exact False.elim (hnot hor)

theorem avoidanceLimitDerives_prime {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {p q : Formula Atom} :
    avoidanceLimitDerives schedule forbidden base (.or p q) →
      avoidanceLimitDerives schedule forbidden base p ∨
        avoidanceLimitDerives schedule forbidden base q := by
  rintro ⟨stage, hor⟩
  rcases schedule.revisits (.or p q) stage with ⟨later, hle, hscheduled⟩
  have horLater : Derives (avoidanceChain schedule forbidden base later) (.or p q) :=
    avoidanceChain_derives_mono schedule forbidden base hle hor
  rcases avoidanceChain_or_choice schedule forbidden base later p q hscheduled horLater with hp | hq
  · exact Or.inl ⟨later + 1, Derives.ax hp⟩
  · exact Or.inr ⟨later + 1, Derives.ax hq⟩

theorem avoidanceLimitDerives_consistent {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom))
    (hbase : DerivationallyAvoids base forbidden) :
    ¬ avoidanceLimitDerives schedule forbidden base .bot := by
  rintro ⟨stage, hbot⟩
  apply avoidanceLimitDerives_avoids schedule forbidden base hbase
  exact ⟨stage, Derives.botE hbot⟩

/- A translation that preserves atom truth preserves every formula and every
   semantic consequence in this propositional fragment. -/
theorem satisfies_congr {Atom : Type u} {v w : Atom → Prop}
    (h : ∀ atom, v atom ↔ w atom) : ∀ formula : Formula Atom,
      Satisfies v formula ↔ Satisfies w formula := by
  intro formula
  induction formula with
  | atom atom => exact h atom
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | and p q ihp ihq => exact and_congr ihp ihq
  | or p q ihp ihq => exact or_congr ihp ihq
  | imp p q ihp ihq =>
    constructor
    · intro hp hwp
      exact ihq.mp (hp (ihp.mpr hwp))
    · intro hq hvp
      exact ihq.mpr (hq (ihp.mp hvp))

theorem contextSatisfies_congr {Atom : Type u} {v w : Atom → Prop}
    (h : ∀ atom, v atom ↔ w atom) (context : List (Formula Atom)) :
    ContextSatisfies v context ↔ ContextSatisfies w context := by
  constructor <;> intro holds formula hmem
  · exact (satisfies_congr h formula).mp (holds formula hmem)
  · exact (satisfies_congr h formula).mpr (holds formula hmem)

theorem semantic_entailment_congr {Atom : Type u} {v w : Atom → Prop}
    {context : List (Formula Atom)} {formula : Formula Atom}
    (h : ∀ atom, v atom ↔ w atom) :
    (ContextSatisfies v context → Satisfies v formula) ↔
      (ContextSatisfies w context → Satisfies w formula) := by
  constructor
  · intro hv hw
    exact (satisfies_congr h formula).mp (hv ((contextSatisfies_congr h context).mpr hw))
  · intro hw hv
    exact (satisfies_congr h formula).mpr (hw ((contextSatisfies_congr h context).mp hv))

/- The natural-deduction rules are intuitionistic.  Kripke semantics, rather
   than one-world classical `Prop` valuations, is therefore the appropriate
   semantic basis for a completeness theorem. -/
structure KripkeModel (Atom : Type u) where
  World : Type v
  le : World → World → Prop
  le_refl : ∀ world, le world world
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  valuation : World → Atom → Prop
  valuation_mono : ∀ {world world' atom}, le world world' →
    valuation world atom → valuation world' atom

def KripkeForces {Atom : Type u} (model : KripkeModel Atom)
    (world : model.World) : Formula Atom → Prop
  | .atom atom => model.valuation world atom
  | .top => True
  | .bot => False
  | .and p q => KripkeForces model world p ∧ KripkeForces model world q
  | .or p q => KripkeForces model world p ∨ KripkeForces model world q
  | .imp p q => ∀ world', model.le world world' →
      KripkeForces model world' p → KripkeForces model world' q

def KripkeContextForces {Atom : Type u} (model : KripkeModel Atom)
    (world : model.World) (context : List (Formula Atom)) : Prop :=
  ∀ formula, formula ∈ context → KripkeForces model world formula

/- Reindex a Kripke model along an atom/incidence translation.  This is the
   semantic counterpart of `Formula.map` and `derives_map`. -/
def KripkeModel.pullback {Atom Atom' : Type u} (f : Atom → Atom')
    (model : KripkeModel Atom') : KripkeModel Atom where
  World := model.World
  le := model.le
  le_refl := model.le_refl
  le_trans := model.le_trans
  valuation := fun world atom => model.valuation world (f atom)
  valuation_mono := by
    intro world world' atom hle holds
    exact model.valuation_mono hle holds

theorem kripke_forces_map_iff {Atom Atom' : Type u} (f : Atom → Atom')
    (model : KripkeModel Atom') (world : model.World) :
    ∀ formula : Formula Atom,
      KripkeForces model world (formula.map f) ↔
        KripkeForces (KripkeModel.pullback f model) world formula := by
  intro formula
  induction formula generalizing world with
  | atom => exact Iff.rfl
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | and p q ihp ihq => exact and_congr (ihp world) (ihq world)
  | or p q ihp ihq => exact or_congr (ihp world) (ihq world)
  | imp p q ihp ihq =>
    constructor
    · intro h world' hle hp
      exact (ihq world').mp (h world' hle ((ihp world').mpr hp))
    · intro h world' hle hp
      exact (ihq world').mpr (h world' hle ((ihp world').mp hp))

theorem kripke_context_forces_map_iff {Atom Atom' : Type u} (f : Atom → Atom')
    (model : KripkeModel Atom') (world : model.World)
    (context : List (Formula Atom)) :
    KripkeContextForces model world (Formula.mapContext f context) ↔
      KripkeContextForces (KripkeModel.pullback f model) world context := by
  constructor
  · intro holds formula hmem
    have hmapped : formula.map f ∈ Formula.mapContext f context :=
      List.mem_map.mpr ⟨formula, hmem, rfl⟩
    exact (kripke_forces_map_iff f model world formula).mp (holds _ hmapped)
  · intro holds mapped hmem
    rcases List.mem_map.mp hmem with ⟨formula, hformula, rfl⟩
    exact (kripke_forces_map_iff f model world formula).mpr (holds formula hformula)

theorem kripke_forces_mono {Atom : Type u} {model : KripkeModel Atom}
    {world world' : model.World} (hww' : model.le world world') :
    ∀ formula : Formula Atom, KripkeForces model world formula →
      KripkeForces model world' formula := by
  intro formula
  induction formula generalizing world world' with
  | atom atom => exact model.valuation_mono hww'
  | top => intro _; trivial
  | bot => intro h; exact False.elim h
  | and p q ihp ihq =>
    rintro ⟨hp, hq⟩
    exact ⟨ihp hww' hp, ihq hww' hq⟩
  | or p q ihp ihq =>
    rintro (hp | hq)
    · exact Or.inl (ihp hww' hp)
    · exact Or.inr (ihq hww' hq)
  | imp p q ihp ihq =>
    intro h world'' hw'w'' hp
    exact h world'' (model.le_trans hww' hw'w'') hp

theorem kripke_context_forces_mono {Atom : Type u} {model : KripkeModel Atom}
    {world world' : model.World} (hww' : model.le world world')
    {context : List (Formula Atom)} :
    KripkeContextForces model world context →
      KripkeContextForces model world' context := by
  intro holds formula hmem
  exact kripke_forces_mono hww' formula (holds formula hmem)

theorem derives_kripke_sound {Atom : Type u} {context : List (Formula Atom)}
    {formula : Formula Atom} (derivation : Derives context formula) :
    ∀ (model : KripkeModel Atom) (world : model.World),
      KripkeContextForces model world context → KripkeForces model world formula := by
  induction derivation with
  | ax h => intro model world holds; exact holds _ h
  | topI => intro model world holds; trivial
  | botE d ih => intro model world holds; exact False.elim (ih model world holds)
  | andI dp dq ihp ihq =>
    intro model world holds
    exact ⟨ihp model world holds, ihq model world holds⟩
  | andEL d ih => intro model world holds; exact (ih model world holds).left
  | andER d ih => intro model world holds; exact (ih model world holds).right
  | orIL d ih => intro model world holds; exact Or.inl (ih model world holds)
  | orIR d ih => intro model world holds; exact Or.inr (ih model world holds)
  | orE dpq dpr dqr ihpq ihpr ihqr =>
    intro model world holds
    rcases ihpq model world holds with hp | hq
    · apply ihpr model world
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · exact holds x hx
    · apply ihqr model world
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hq
      · exact holds x hx
  | impI d ih =>
    intro model world holds world' hww' hp
    apply ih model world'
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · exact kripke_forces_mono hww' x (holds x hx)
  | impE dpq dp ihpq ihp =>
    intro model world holds
    exact ihpq model world holds world (model.le_refl world) (ihp model world holds)

def KripkeEntails {Atom : Type u} (context : List (Formula Atom))
    (formula : Formula Atom) : Prop :=
  ∀ (model : KripkeModel.{u, v} Atom) (world : model.World),
    KripkeContextForces model world context → KripkeForces model world formula

theorem derives_kripke_entails {Atom : Type u} {context : List (Formula Atom)}
    {formula : Formula Atom} (derivation : Derives context formula) :
    KripkeEntails.{u, v} context formula :=
  fun model world holds => derives_kripke_sound derivation model world holds

def emptyKripkeModel (Atom : Type u) : KripkeModel Atom where
  World := Unit
  le := fun _ _ => True
  le_refl := fun _ => trivial
  le_trans := fun _ _ => trivial
  valuation := fun _ _ => False
  valuation_mono := by
    intro world world' atom hle holds
    exact False.elim holds

theorem kripke_satisfiable_consistent {Atom : Type u} {context : List (Formula Atom)}
    {model : KripkeModel Atom} {world : model.World}
    (holds : KripkeContextForces model world context) :
    DerivationallyConsistent context := by
  intro hbot
  exact derives_kripke_sound hbot model world holds

/- A concrete relative consistency theorem for the implemented internal logic. -/
theorem empty_context_consistent (Atom : Type u) :
    DerivationallyConsistent ([] : List (Formula Atom)) := by
  apply kripke_satisfiable_consistent (model := emptyKripkeModel Atom) (world := ())
  intro formula hmem
  simp at hmem

/- A two-world Kripke frame supplies a concrete nonclassical countermodel.
   The selected atom becomes true only at the later world. -/
def delayedAtomKripkeModel (Atom : Type u) (selected : Atom) : KripkeModel Atom where
  World := Bool
  le := fun source target => source = false ∨ target = true
  le_refl := by
    intro world
    cases world <;> simp
  le_trans := by
    intro source middle target hsm hmt
    rcases hsm with hsource | hmiddle
    · exact Or.inl hsource
    · rcases hmt with hmiddle' | htarget
      · cases hmiddle
        cases hmiddle'
      · exact Or.inr htarget
  valuation := fun world atom => world = true ∧ atom = selected
  valuation_mono := by
    intro source target atom hle holds
    rcases hle with hsource | htarget
    · cases hsource
      cases holds.left
    · exact ⟨htarget, holds.right⟩

/- This proves that the implemented natural deduction is genuinely
   intuitionistic: excluded middle is not derivable from the empty context. -/
theorem excluded_middle_not_derivable {Atom : Type u} (atom : Atom) :
    ¬ Derives ([] : List (Formula Atom))
      (Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom))) := by
  intro derivation
  have forces := derives_kripke_sound derivation
    (delayedAtomKripkeModel Atom atom) false (by
      intro formula hmem
      simp at hmem)
  rcases forces with hatom | hneg
  · exact Bool.noConfusion hatom.left
  · exact hneg true (Or.inl rfl) ⟨rfl, rfl⟩

/- The intuitionistically valid double-negated form is nevertheless derivable.
   Together with `excluded_middle_not_derivable`, this records the precise
   constructive boundary of the implemented internal logic. -/
theorem double_neg_excluded_middle_derivable {Atom : Type u} (atom : Atom) :
    Derives ([] : List (Formula Atom))
      (Formula.neg (Formula.neg
        (Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom))))) := by
  apply Derives.impI
  apply Derives.impE
    (p := Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom)))
    (q := Formula.bot)
  · simpa [Formula.neg] using
      (Derives.ax (by simp) : Derives
        [Formula.neg (Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom)))]
        (Formula.neg (Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom)))))
  · apply Derives.orIR (p := Formula.atom atom)
    apply Derives.impI (p := Formula.atom atom) (q := Formula.bot)
    apply Derives.impE
      (p := Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom)))
      (q := Formula.bot)
    · simpa [Formula.neg] using
        (Derives.ax (List.mem_cons_of_mem _ (by simp)) : Derives
          [Formula.atom atom,
            Formula.neg (Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom)))]
          (Formula.neg (Formula.or (Formula.atom atom) (Formula.neg (Formula.atom atom)))))
    · apply Derives.orIL
      exact Derives.ax (by simp)

/- Canonical worlds for the eventual completeness construction.  Closure is
   stated directly in terms of finite natural-deduction derivations. -/
structure PrimeTheory (Atom : Type u) where
  contains : Formula Atom → Prop
  closed : ∀ {context formula},
    (∀ assumption, assumption ∈ context → contains assumption) →
      Derives context formula → contains formula
  consistent : ¬ contains .bot
  prime : ∀ {p q}, contains (.or p q) → contains p ∨ contains q

def avoidanceLimitPrimeTheory {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom))
    (hbase : DerivationallyAvoids base forbidden) : PrimeTheory Atom where
  contains := avoidanceLimitDerives schedule forbidden base
  closed := avoidanceLimitDerives_closed schedule forbidden base
  consistent := avoidanceLimitDerives_consistent schedule forbidden base hbase
  prime := fun hor => avoidanceLimitDerives_prime schedule forbidden base hor

theorem relative_prime_extension {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom))
    (hbase : DerivationallyAvoids base forbidden) :
    ∃ theory : PrimeTheory Atom,
      (∀ formula, formula ∈ base → theory.contains formula) ∧
        ¬ theory.contains forbidden := by
  refine ⟨avoidanceLimitPrimeTheory schedule forbidden base hbase, ?_, ?_⟩
  · intro formula hformula
    exact avoidanceLimitDerives_contains_base schedule forbidden base hformula
  · exact avoidanceLimitDerives_avoids schedule forbidden base hbase

/- Finite-base implication failure has an explicit prime-theory witness. -/
theorem finite_implication_failure_prime_extension {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom)
    (context : List (Formula Atom)) (premise conclusion : Formula Atom)
    (havoid : DerivationallyAvoids context (.imp premise conclusion)) :
    ∃ theory : PrimeTheory Atom,
      (∀ formula, formula ∈ context → theory.contains formula) ∧
        theory.contains premise ∧ ¬ theory.contains conclusion := by
  have hbase : DerivationallyAvoids (premise :: context) conclusion :=
    avoids_imp_extension havoid
  rcases relative_prime_extension schedule conclusion (premise :: context) hbase with
    ⟨theory, hcontains, hnot⟩
  refine ⟨theory, ?_, ?_, hnot⟩
  · intro formula hformula
    exact hcontains formula (List.mem_cons_of_mem premise hformula)
  · exact hcontains premise (by simp)

theorem lindenbaumLimitDerives_prime {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) {p q : Formula Atom} :
    lindenbaumLimitDerives enumeration (.or p q) →
      lindenbaumLimitDerives enumeration p ∨ lindenbaumLimitDerives enumeration q := by
  rintro ⟨orStage, hor⟩
  rcases lindenbaumChain_decides enumeration p with ⟨pStage, hpDecision⟩
  rcases lindenbaumChain_decides enumeration q with ⟨qStage, hqDecision⟩
  let stage := Nat.max (Nat.max orStage pStage) qStage
  have hor' : Derives (lindenbaumChain enumeration stage) (.or p q) :=
    lindenbaumChain_derives_mono enumeration
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hor
  have hp' : p ∈ lindenbaumChain enumeration stage ∨
      p.neg ∈ lindenbaumChain enumeration stage := by
    · rcases hpDecision with hp | hnp
      · exact Or.inl (lindenbaumChain_subset_of_le enumeration
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) p hp)
      · exact Or.inr (lindenbaumChain_subset_of_le enumeration
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) p.neg hnp)
  have hq' : q ∈ lindenbaumChain enumeration stage ∨
      q.neg ∈ lindenbaumChain enumeration stage := by
    · rcases hqDecision with hq | hnq
      · exact Or.inl (lindenbaumChain_subset_of_le enumeration
          (Nat.le_max_right _ _) q hq)
      · exact Or.inr (lindenbaumChain_subset_of_le enumeration
          (Nat.le_max_right _ _) q.neg hnq)
  rcases derives_or_choice_of_decisions
    (lindenbaumChain_consistent enumeration stage) hor' hp' hq' with hdp | hdq
  · exact Or.inl ⟨stage, hdp⟩
  · exact Or.inr ⟨stage, hdq⟩

def lindenbaumLimitPrimeTheory {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) : PrimeTheory Atom where
  contains := lindenbaumLimitDerives enumeration
  closed := lindenbaumLimitDerives_closed enumeration
  consistent := lindenbaumLimitDerives_consistent enumeration
  prime := fun hor => lindenbaumLimitDerives_prime enumeration hor

theorem lindenbaumLimitDerivesFrom_prime {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (hbase : DerivationallyConsistent base)
    {p q : Formula Atom} :
    lindenbaumLimitDerivesFrom enumeration base (.or p q) →
      lindenbaumLimitDerivesFrom enumeration base p ∨
        lindenbaumLimitDerivesFrom enumeration base q := by
  rintro ⟨orStage, hor⟩
  rcases lindenbaumChainFrom_decides enumeration base p with ⟨pStage, hpDecision⟩
  rcases lindenbaumChainFrom_decides enumeration base q with ⟨qStage, hqDecision⟩
  let stage := Nat.max (Nat.max orStage pStage) qStage
  have hor' : Derives (lindenbaumChainFrom enumeration base stage) (.or p q) :=
    lindenbaumChainFrom_derives_mono enumeration base
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hor
  have hp' : p ∈ lindenbaumChainFrom enumeration base stage ∨
      p.neg ∈ lindenbaumChainFrom enumeration base stage := by
    rcases hpDecision with hp | hnp
    · exact Or.inl (lindenbaumChainFrom_subset_of_le enumeration base
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) p hp)
    · exact Or.inr (lindenbaumChainFrom_subset_of_le enumeration base
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) p.neg hnp)
  have hq' : q ∈ lindenbaumChainFrom enumeration base stage ∨
      q.neg ∈ lindenbaumChainFrom enumeration base stage := by
    rcases hqDecision with hq | hnq
    · exact Or.inl (lindenbaumChainFrom_subset_of_le enumeration base
        (Nat.le_max_right _ _) q hq)
    · exact Or.inr (lindenbaumChainFrom_subset_of_le enumeration base
        (Nat.le_max_right _ _) q.neg hnq)
  rcases derives_or_choice_of_decisions
    (lindenbaumChainFrom_consistent enumeration base hbase stage) hor' hp' hq' with hdp | hdq
  · exact Or.inl ⟨stage, hdp⟩
  · exact Or.inr ⟨stage, hdq⟩

def lindenbaumLimitPrimeTheoryFrom {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (hbase : DerivationallyConsistent base) : PrimeTheory Atom where
  contains := lindenbaumLimitDerivesFrom enumeration base
  closed := lindenbaumLimitDerivesFrom_closed enumeration base
  consistent := lindenbaumLimitDerivesFrom_consistent enumeration base hbase
  prime := fun hor => lindenbaumLimitDerivesFrom_prime enumeration base hbase hor

theorem lindenbaumLimitPrimeTheoryFrom_contains_base {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (base : List (Formula Atom))
    (hbase : DerivationallyConsistent base) {formula : Formula Atom} :
    formula ∈ base →
      (lindenbaumLimitPrimeTheoryFrom enumeration base hbase).contains formula := by
  intro hformula
  refine ⟨0, ?_⟩
  change Derives base formula
  exact Derives.ax hformula

def primeTheoryLe {Atom : Type u} (source target : PrimeTheory Atom) : Prop :=
  ∀ formula, source.contains formula → target.contains formula

/- The closure field of a prime theory yields the expected internal rules.
   Keeping these as named lemmas makes the remaining prime-extension argument
   independent of the representation of a theory. -/
theorem primeTheory_contains_top {Atom : Type u} (theory : PrimeTheory Atom) :
    theory.contains .top := by
  apply theory.closed (context := [])
  · intro assumption hmem
    simp at hmem
  · exact Derives.topI

theorem primeTheory_contains_and_iff {Atom : Type u} (theory : PrimeTheory Atom)
    (p q : Formula Atom) :
    theory.contains (.and p q) ↔ theory.contains p ∧ theory.contains q := by
  constructor
  · intro hand
    constructor
    · apply theory.closed (context := [.and p q])
      · intro assumption hmem
        have h : assumption = .and p q := by simpa using hmem
        subst assumption
        exact hand
      · exact Derives.andEL (p := p) (q := q) (Derives.ax (by simp))
    · apply theory.closed (context := [.and p q])
      · intro assumption hmem
        have h : assumption = .and p q := by simpa using hmem
        subst assumption
        exact hand
      · exact Derives.andER (p := p) (q := q) (Derives.ax (by simp))
  · rintro ⟨hp, hq⟩
    apply theory.closed (context := [p, q])
    · intro assumption hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hp
      · have h : assumption = q := by simpa using hmem
        subst assumption
        exact hq
    · exact Derives.andI (Derives.ax (by simp)) (Derives.ax (by simp))

theorem primeTheory_contains_or_iff {Atom : Type u} (theory : PrimeTheory Atom)
    (p q : Formula Atom) :
    theory.contains (.or p q) ↔ theory.contains p ∨ theory.contains q := by
  constructor
  · exact theory.prime
  · rintro (hp | hq)
    · apply theory.closed (context := [p])
      · intro assumption hmem
        have h : assumption = p := by simpa using hmem
        subst assumption
        exact hp
      · exact Derives.orIL (Derives.ax (by simp))
    · apply theory.closed (context := [q])
      · intro assumption hmem
        have h : assumption = q := by simpa using hmem
        subst assumption
        exact hq
      · exact Derives.orIR (Derives.ax (by simp))

theorem primeTheory_imp_apply {Atom : Type u} (theory : PrimeTheory Atom)
    {p q : Formula Atom} :
    theory.contains (.imp p q) → theory.contains p → theory.contains q := by
  intro himp hp
  apply theory.closed (context := [.imp p q, p])
  · intro assumption hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact himp
    · have h : assumption = p := by simpa using hmem
      subst assumption
      exact hp
  · exact Derives.impE (p := p) (q := q)
      (Derives.ax (by simp)) (Derives.ax (by simp))

theorem primeTheoryLe_refl {Atom : Type u} (theory : PrimeTheory Atom) :
    primeTheoryLe theory theory := fun _ h => h

theorem primeTheoryLe_trans {Atom : Type u} {r s t : PrimeTheory Atom} :
    primeTheoryLe r s → primeTheoryLe s t → primeTheoryLe r t := by
  intro hrs hst formula hr
  exact hst formula (hrs formula hr)

def canonicalKripkeModel (Atom : Type u) : KripkeModel (Atom := Atom) where
  World := PrimeTheory Atom
  le := primeTheoryLe
  le_refl := fun _ _ h => h
  le_trans := fun hst htu formula h => htu formula (hst formula h)
  valuation := fun theory atom => theory.contains (.atom atom)
  valuation_mono := fun hle h => hle _ h

/- This is the exact Lindenbaum obligation still needed for completeness: an
   implication absent from a prime theory has a prime extension witnessing its
   failure.  The truth lemma below is a proved consequence of this condition. -/
structure PrimeExtensionWitness (Atom : Type u) where
  extend_imp_failure : ∀ (theory : PrimeTheory Atom) (p q : Formula Atom),
    ¬ theory.contains (.imp p q) →
      ∃ extension : PrimeTheory Atom, primeTheoryLe theory extension ∧
        extension.contains p ∧ ¬ extension.contains q

theorem canonical_truth_lemma {Atom : Type u} (witness : PrimeExtensionWitness Atom)
    (theory : PrimeTheory Atom) : ∀ formula : Formula Atom,
      KripkeForces (canonicalKripkeModel Atom) theory formula ↔ theory.contains formula := by
  intro formula
  induction formula generalizing theory with
  | atom atom => exact Iff.rfl
  | top =>
    constructor
    · intro _
      apply theory.closed (context := [])
      · intro assumption hmem
        simp at hmem
      · exact Derives.topI
    · intro _
      trivial
  | bot =>
    constructor
    · intro h
      exact False.elim h
    · intro h
      exact False.elim (theory.consistent h)
  | and p q ihp ihq =>
    constructor
    · rintro ⟨hp, hq⟩
      apply theory.closed (context := [p, q])
      · intro assumption hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact (ihp theory).mp hp
        · have ha : assumption = q := by simpa using hmem
          subst assumption
          exact (ihq theory).mp hq
      · exact Derives.andI (Derives.ax (by simp)) (Derives.ax (by simp))
    · intro h
      constructor
      · apply (ihp theory).mpr
        apply theory.closed (context := [.and p q])
        · intro assumption hmem
          have ha : assumption = .and p q := by simpa using hmem
          subst assumption
          exact h
        · exact Derives.andEL (p := p) (q := q) (Derives.ax (by simp))
      · apply (ihq theory).mpr
        apply theory.closed (context := [.and p q])
        · intro assumption hmem
          have ha : assumption = .and p q := by simpa using hmem
          subst assumption
          exact h
        · exact Derives.andER (p := p) (q := q) (Derives.ax (by simp))
  | or p q ihp ihq =>
    constructor
    · rintro (hp | hq)
      · apply theory.closed (context := [p])
        · intro assumption hmem
          have ha : assumption = p := by simpa using hmem
          subst assumption
          exact (ihp theory).mp hp
        · exact Derives.orIL (Derives.ax (by simp))
      · apply theory.closed (context := [q])
        · intro assumption hmem
          have ha : assumption = q := by simpa using hmem
          subst assumption
          exact (ihq theory).mp hq
        · exact Derives.orIR (Derives.ax (by simp))
    · intro h
      rcases theory.prime h with hp | hq
      · exact Or.inl ((ihp theory).mpr hp)
      · exact Or.inr ((ihq theory).mpr hq)
  | imp p q ihp ihq =>
    constructor
    · intro h
      apply Classical.byContradiction
      intro hnot
      rcases witness.extend_imp_failure theory p q hnot with ⟨extension, hle, hp, hnq⟩
      have hq : KripkeForces (canonicalKripkeModel Atom) extension q :=
        h extension hle ((ihp extension).mpr hp)
      exact hnq ((ihq extension).mp hq)
    · intro h extension hle hp
      apply (ihq extension).mpr
      apply extension.closed (context := [.imp p q, p])
      · intro assumption hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hle _ h
        · have ha : assumption = p := by simpa using hmem
          subst assumption
          exact (ihp extension).mp hp
      · exact Derives.impE (p := p) (q := q)
          (Derives.ax (by simp)) (Derives.ax (by simp))

/- Incidence-specialized notation for clients of the core structure. -/
abbrev IncidenceFormula (I : Type u) := Formula I

end IncidenceCore
