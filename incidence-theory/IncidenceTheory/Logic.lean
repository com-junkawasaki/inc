import IncidenceTheory.Axioms

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

/- Atom translations act strictly functorially on formulas.  These small
   equalities are what permit a faithful incidence translation to reflect,
   rather than merely preserve, derivations below. -/
theorem Formula.map_id {Atom : Type u} (formula : Formula Atom) :
    formula.map id = formula := by
  induction formula <;> simp [Formula.map, *]

theorem Formula.map_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (formula : Formula Atom) :
    (formula.map f).map g = formula.map (g ∘ f) := by
  induction formula <;> simp [Formula.map, *, Function.comp_def]

def Formula.neg {Atom : Type u} (formula : Formula Atom) : Formula Atom :=
  .imp formula .bot

/- Internal logical equivalence is represented by its two implication
   directions.  It is syntax, rather than Lean equality, so it can be proved,
   translated, and later placed under binders. -/
def Formula.iff {Atom : Type u} (left right : Formula Atom) : Formula Atom :=
  .and (.imp left right) (.imp right left)

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

theorem Formula.mapContext_id {Atom : Type u} (context : List (Formula Atom)) :
    Formula.mapContext id context = context := by
  induction context with
  | nil => rfl
  | cons formula context ih =>
    change Formula.map id formula :: Formula.mapContext id context = formula :: context
    rw [Formula.map_id, ih]

theorem Formula.mapContext_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (context : List (Formula Atom)) :
    Formula.mapContext g (Formula.mapContext f context) =
      Formula.mapContext (g ∘ f) context := by
  simp [Formula.mapContext, Formula.map_comp]

theorem Formula.map_leftInverse {Atom Atom' : Type u} (f : Atom → Atom')
    (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom) (formula : Formula Atom) :
    (formula.map f).map g = formula := by
  induction formula <;> simp [Formula.map, *]

theorem Formula.map_surjective {Atom Atom' : Type u} (f : Atom → Atom')
    (surjective : ∀ target, ∃ source, f source = target) :
    ∀ formula : Formula Atom', ∃ source : Formula Atom, source.map f = formula := by
  intro formula
  induction formula with
  | atom atom =>
      obtain ⟨source, rfl⟩ := surjective atom
      exact ⟨.atom source, rfl⟩
  | top => exact ⟨.top, rfl⟩
  | bot => exact ⟨.bot, rfl⟩
  | and left right ihLeft ihRight =>
      obtain ⟨leftSource, hleft⟩ := ihLeft
      obtain ⟨rightSource, hright⟩ := ihRight
      exact ⟨.and leftSource rightSource, by simp [Formula.map, hleft, hright]⟩
  | or left right ihLeft ihRight =>
      obtain ⟨leftSource, hleft⟩ := ihLeft
      obtain ⟨rightSource, hright⟩ := ihRight
      exact ⟨.or leftSource rightSource, by simp [Formula.map, hleft, hright]⟩
  | imp left right ihLeft ihRight =>
      obtain ⟨leftSource, hleft⟩ := ihLeft
      obtain ⟨rightSource, hright⟩ := ihRight
      exact ⟨.imp leftSource rightSource, by simp [Formula.map, hleft, hright]⟩

theorem Formula.mapContext_leftInverse {Atom Atom' : Type u} (f : Atom → Atom')
    (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    (context : List (Formula Atom)) :
    Formula.mapContext g (Formula.mapContext f context) = context := by
  induction context with
  | nil => rfl
  | cons formula context ih =>
    change Formula.map g (Formula.map f formula) ::
      Formula.mapContext g (Formula.mapContext f context) = formula :: context
    rw [Formula.map_leftInverse f g hgf, ih]

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

theorem satisfies_iff {Atom : Type u} (valuation : Atom → Prop)
    (left right : Formula Atom) :
    Satisfies valuation (Formula.iff left right) ↔
      (Satisfies valuation left ↔ Satisfies valuation right) := by
  constructor
  · rintro ⟨hforward, hbackward⟩
    exact ⟨hforward, hbackward⟩
  · rintro ⟨hforward, hbackward⟩
    exact ⟨hforward, hbackward⟩

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

/-! The propositional interpretation of atom maps is functorial: mapping by
   the identity changes no truth value, and two maps pull a valuation back by
   their composite. -/
theorem satisfies_map_id {Atom : Type u} (valuation : Atom → Prop)
    (formula : Formula Atom) :
    Satisfies valuation (formula.map id) ↔ Satisfies valuation formula := by
  rw [Formula.map_id]

theorem satisfies_map_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (valuation : Atom'' → Prop) (formula : Formula Atom) :
    Satisfies valuation ((formula.map f).map g) ↔
      Satisfies (fun atom => valuation (g (f atom))) formula := by
  rw [Formula.map_comp]
  exact satisfies_map (g ∘ f) valuation formula

/- Reindexing commutes not only with a single formula but with a whole
   finite theory.  This is the propositional semantic form of simultaneous
   atom substitution. -/
theorem context_satisfies_map_iff {Atom Atom' : Type u} (f : Atom → Atom')
    (valuation : Atom' → Prop) (context : List (Formula Atom)) :
    ContextSatisfies valuation (Formula.mapContext f context) ↔
      ContextSatisfies (fun atom => valuation (f atom)) context := by
  constructor
  · intro holds formula hmem
    have hmapped : formula.map f ∈ Formula.mapContext f context :=
      List.mem_map.mpr ⟨formula, hmem, rfl⟩
    exact (satisfies_map f valuation formula).mp (holds _ hmapped)
  · intro holds mapped hmem
    rcases List.mem_map.mp hmem with ⟨formula, hformula, rfl⟩
    exact (satisfies_map f valuation formula).mpr (holds formula hformula)

theorem context_satisfies_map_id {Atom : Type u} (valuation : Atom → Prop)
    (context : List (Formula Atom)) :
    ContextSatisfies valuation (Formula.mapContext id context) ↔
      ContextSatisfies valuation context := by
  rw [Formula.mapContext_id]

theorem context_satisfies_map_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (valuation : Atom'' → Prop) (context : List (Formula Atom)) :
    ContextSatisfies valuation (Formula.mapContext g (Formula.mapContext f context)) ↔
      ContextSatisfies (fun atom => valuation (g (f atom))) context := by
  rw [Formula.mapContext_comp]
  exact context_satisfies_map_iff (g ∘ f) valuation context

theorem satisfies_map_leftInverse {Atom Atom' : Type u} (f : Atom → Atom')
    (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    (valuation : Atom → Prop) : ∀ formula : Formula Atom,
      Satisfies (fun atom' => valuation (g atom')) (formula.map f) ↔
        Satisfies valuation formula := by
  intro formula
  induction formula with
  | atom atom =>
    change valuation (g (f atom)) ↔ valuation atom
    rw [hgf atom]
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

theorem context_satisfies_map_leftInverse {Atom Atom' : Type u} (f : Atom → Atom')
    (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    (valuation : Atom → Prop) (context : List (Formula Atom)) :
    ContextSatisfies (fun atom' => valuation (g atom')) (Formula.mapContext f context) ↔
      ContextSatisfies valuation context := by
  constructor
  · intro holds formula hmem
    have hmapped : formula.map f ∈ Formula.mapContext f context :=
      List.mem_map.mpr ⟨formula, hmem, rfl⟩
    exact (satisfies_map_leftInverse f g hgf valuation formula).mp (holds _ hmapped)
  · intro holds mapped hmem
    rcases List.mem_map.mp hmem with ⟨formula, hformula, rfl⟩
    exact (satisfies_map_leftInverse f g hgf valuation formula).mpr (holds formula hformula)

/- Semantic entailment is invariant under a split-injective atom translation.
   Together with `derives_map_iff_of_leftInverse`, this makes faithful
   incidence renamings exact on both syntax and one-world semantics. -/
theorem semantically_entails_map {Atom Atom' : Type u} (f : Atom → Atom')
    {context : List (Formula Atom)} {formula : Formula Atom} :
    SemanticallyEntails context formula →
      SemanticallyEntails (Formula.mapContext f context) (formula.map f) := by
  intro hentails valuation holds
  have hsource : ContextSatisfies (fun atom => valuation (f atom)) context :=
    (context_satisfies_map_iff f valuation context).mp holds
  exact (satisfies_map f valuation formula).mpr (hentails _ hsource)

theorem semantically_entails_map_reflect_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    SemanticallyEntails (Formula.mapContext f context) (formula.map f) →
      SemanticallyEntails context formula := by
  intro hentails valuation holds
  have hmapped : ContextSatisfies (fun atom' => valuation (g atom'))
      (Formula.mapContext f context) :=
    (context_satisfies_map_leftInverse f g hgf valuation context).mpr holds
  exact (satisfies_map_leftInverse f g hgf valuation formula).mp
    (hentails _ hmapped)

theorem semantically_entails_map_iff_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    SemanticallyEntails (Formula.mapContext f context) (formula.map f) ↔
      SemanticallyEntails context formula := by
  constructor
  · exact semantically_entails_map_reflect_of_leftInverse f g hgf
  · exact semantically_entails_map f

theorem semantically_entails_map_id {Atom : Type u}
    (context : List (Formula Atom)) (formula : Formula Atom) :
    SemanticallyEntails (Formula.mapContext id context) (formula.map id) ↔
      SemanticallyEntails context formula := by
  rw [Formula.mapContext_id, Formula.map_id]

/-! Naturality of semantic consequence itself.  This is an equality-level
   coherence statement, complementary to `semantically_entails_map`, while
   `semantically_entails_map_iff_of_leftInverse` supplies reflection for
   faithful translations. -/
theorem semantically_entails_map_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (context : List (Formula Atom)) (formula : Formula Atom) :
    SemanticallyEntails (Formula.mapContext g (Formula.mapContext f context))
        ((formula.map f).map g) ↔
      SemanticallyEntails (Formula.mapContext (g ∘ f) context)
        (formula.map (g ∘ f)) := by
  rw [Formula.mapContext_comp, Formula.map_comp]

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

/- A split-injective translation is conservative for finite derivations:
   translate a proof back along its retraction and normalize the two maps.
   In particular, changing incidence names through a bijection is an exact
   equivalence of derivability, not just a sound forward translation. -/
theorem derives_map_reflect_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    Derives (Formula.mapContext f context) (formula.map f) →
      Derives context formula := by
  intro hderives
  have hback := derives_map g hderives
  simpa only [Formula.mapContext_leftInverse f g hgf,
    Formula.map_leftInverse f g hgf formula] using hback

theorem derives_map_iff_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    Derives (Formula.mapContext f context) (formula.map f) ↔
      Derives context formula := by
  constructor
  · exact derives_map_reflect_of_leftInverse f g hgf
  · exact derives_map f

/- Consistency is contravariant under arbitrary atom translations: if the
   translated theory is consistent, then the source theory was consistent.
   A split injection upgrades this to an exact preservation-and-reflection
   theorem, matching the corresponding results for derivability and semantic
   entailment. -/
theorem derivationallyConsistent_of_map {Atom Atom' : Type u}
    (f : Atom → Atom') {context : List (Formula Atom)} :
    DerivationallyConsistent (Formula.mapContext f context) →
      DerivationallyConsistent context := by
  intro mappedConsistent sourceInconsistent
  exact mappedConsistent (derives_map f sourceInconsistent)

theorem derivationallyConsistent_map_iff_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} :
    DerivationallyConsistent (Formula.mapContext f context) ↔
      DerivationallyConsistent context := by
  unfold DerivationallyConsistent
  constructor
  · exact derivationallyConsistent_of_map f
  · intro sourceConsistent mappedInconsistent
    apply sourceConsistent
    exact derives_map_reflect_of_leftInverse f g hgf
      (formula := .bot) mappedInconsistent

theorem derivationallyAvoids_of_map {Atom Atom' : Type u}
    (f : Atom → Atom') {context : List (Formula Atom)}
    {forbidden : Formula Atom} :
    DerivationallyAvoids (Formula.mapContext f context) (forbidden.map f) →
      DerivationallyAvoids context forbidden := by
  intro mappedAvoids sourceDerives
  exact mappedAvoids (derives_map f sourceDerives)

theorem derivationallyAvoids_map_iff_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} {forbidden : Formula Atom} :
    DerivationallyAvoids (Formula.mapContext f context) (forbidden.map f) ↔
      DerivationallyAvoids context forbidden := by
  unfold DerivationallyAvoids
  rw [derives_map_iff_of_leftInverse f g hgf]

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

theorem derives_iffI {Atom : Type u} {context : List (Formula Atom)}
    {left right : Formula Atom} :
    Derives context (.imp left right) → Derives context (.imp right left) →
      Derives context (Formula.iff left right) :=
  Derives.andI

theorem derives_iffEL {Atom : Type u} {context : List (Formula Atom)}
    {left right : Formula Atom} :
    Derives context (Formula.iff left right) → Derives context (.imp left right) :=
  Derives.andEL

theorem derives_iffER {Atom : Type u} {context : List (Formula Atom)}
    {left right : Formula Atom} :
    Derives context (Formula.iff left right) → Derives context (.imp right left) :=
  Derives.andER

def Formula.DerivablyEquivalent {Atom : Type u}
    (left right : Formula Atom) : Prop :=
  Derives [] (Formula.iff left right)

theorem derivablyEquivalent_refl {Atom : Type u} (formula : Formula Atom) :
    Formula.DerivablyEquivalent formula formula := by
  apply derives_iffI <;> apply Derives.impI
  all_goals exact Derives.ax (by simp)

theorem derivablyEquivalent_symm {Atom : Type u} {left right : Formula Atom} :
    Formula.DerivablyEquivalent left right →
      Formula.DerivablyEquivalent right left := by
  intro equivalent
  exact derives_iffI (derives_iffER equivalent) (derives_iffEL equivalent)

theorem derivablyEquivalent_trans {Atom : Type u} {left middle right : Formula Atom} :
    Formula.DerivablyEquivalent left middle →
      Formula.DerivablyEquivalent middle right →
        Formula.DerivablyEquivalent left right := by
  intro leftMiddle middleRight
  apply derives_iffI
  · apply Derives.impI
    apply Derives.impE
    · exact derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem)
        (derives_iffEL middleRight)
    · apply Derives.impE
      · exact derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem)
          (derives_iffEL leftMiddle)
      · exact Derives.ax (by simp)
  · apply Derives.impI
    apply Derives.impE
    · exact derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem)
        (derives_iffER leftMiddle)
    · apply Derives.impE
      · exact derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem)
          (derives_iffER middleRight)
      · exact Derives.ax (by simp)

theorem derivablyEquivalent_equivalence {Atom : Type u} :
    Equivalence (@Formula.DerivablyEquivalent Atom) where
  refl := derivablyEquivalent_refl
  symm := derivablyEquivalent_symm
  trans := derivablyEquivalent_trans

theorem derivablyEquivalent_and_congr {Atom : Type u}
    {left left' right right' : Formula Atom} :
    Formula.DerivablyEquivalent left left' →
      Formula.DerivablyEquivalent right right' →
        Formula.DerivablyEquivalent (.and left right) (.and left' right') := by
  intro leftEquivalent rightEquivalent
  apply derives_iffI
  · apply Derives.impI
    apply Derives.andI
    · apply Derives.impE
      · exact derives_weaken (source := []) (target := (.and left right) :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffEL (context := []) (left := left) (right := left') leftEquivalent)
      · exact Derives.andEL (p := left) (q := right) (Derives.ax (by simp))
    · apply Derives.impE
      · exact derives_weaken (source := []) (target := (.and left right) :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffEL (context := []) (left := right) (right := right') rightEquivalent)
      · exact Derives.andER (p := left) (q := right) (Derives.ax (by simp))
  · apply Derives.impI
    apply Derives.andI
    · apply Derives.impE
      · exact derives_weaken (source := []) (target := (.and left' right') :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffER (context := []) (left := left) (right := left') leftEquivalent)
      · exact Derives.andEL (p := left') (q := right') (Derives.ax (by simp))
    · apply Derives.impE
      · exact derives_weaken (source := []) (target := (.and left' right') :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffER (context := []) (left := right) (right := right') rightEquivalent)
      · exact Derives.andER (p := left') (q := right') (Derives.ax (by simp))

theorem derivablyEquivalent_or_congr {Atom : Type u}
    {left left' right right' : Formula Atom} :
    Formula.DerivablyEquivalent left left' →
      Formula.DerivablyEquivalent right right' →
        Formula.DerivablyEquivalent (.or left right) (.or left' right') := by
  intro leftEquivalent rightEquivalent
  apply derives_iffI
  · apply Derives.impI
    refine Derives.orE (p := left) (q := right) (r := .or left' right')
      (Derives.ax (by simp)) ?_ ?_
    · apply Derives.orIL
      apply Derives.impE
      · exact derives_weaken (source := []) (target := left :: (.or left right) :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffEL (context := []) (left := left) (right := left') leftEquivalent)
      · exact Derives.ax (by simp)
    · apply Derives.orIR
      apply Derives.impE
      · exact derives_weaken (source := []) (target := right :: (.or left right) :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffEL (context := []) (left := right) (right := right') rightEquivalent)
      · exact Derives.ax (by simp)
  · apply Derives.impI
    refine Derives.orE (p := left') (q := right') (r := .or left right)
      (Derives.ax (by simp)) ?_ ?_
    · apply Derives.orIL
      apply Derives.impE
      · exact derives_weaken (source := []) (target := left' :: (.or left' right') :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffER (context := []) (left := left) (right := left') leftEquivalent)
      · exact Derives.ax (by simp)
    · apply Derives.orIR
      apply Derives.impE
      · exact derives_weaken (source := []) (target := right' :: (.or left' right') :: [])
          (by intro formula hmem; simp at hmem)
          (derives_iffER (context := []) (left := right) (right := right') rightEquivalent)
      · exact Derives.ax (by simp)

theorem derivablyEquivalent_imp_congr {Atom : Type u}
    {left left' right right' : Formula Atom} :
    Formula.DerivablyEquivalent left left' →
      Formula.DerivablyEquivalent right right' →
        Formula.DerivablyEquivalent (.imp left right) (.imp left' right') := by
  intro leftEquivalent rightEquivalent
  apply derives_iffI
  · apply Derives.impI
    apply Derives.impI
    apply Derives.impE
    · exact derives_weaken (source := [])
        (target := left' :: (.imp left right) :: [])
        (by intro formula hmem; simp at hmem)
        (derives_iffEL (context := []) (left := right) (right := right') rightEquivalent)
    · apply Derives.impE
      · exact Derives.ax (p := .imp left right) (by simp)
      · apply Derives.impE
        · exact derives_weaken (source := [])
            (target := left' :: (.imp left right) :: [])
            (by intro formula hmem; simp at hmem)
            (derives_iffER (context := []) (left := left) (right := left') leftEquivalent)
        · exact Derives.ax (by simp)

  · apply Derives.impI
    apply Derives.impI
    apply Derives.impE
    · exact derives_weaken (source := [])
        (target := left :: (.imp left' right') :: [])
        (by intro formula hmem; simp at hmem)
        (derives_iffER (context := []) (left := right) (right := right') rightEquivalent)
    · apply Derives.impE
      · exact Derives.ax (p := .imp left' right') (by simp)
      · apply Derives.impE
        · exact derives_weaken (source := [])
            (target := left :: (.imp left' right') :: [])
            (by intro formula hmem; simp at hmem)
            (derives_iffEL (context := []) (left := left) (right := left') leftEquivalent)
        · exact Derives.ax (by simp)

theorem derivablyEquivalent_map {Atom Atom' : Type u} (f : Atom → Atom')
    {left right : Formula Atom} :
    Formula.DerivablyEquivalent left right →
      Formula.DerivablyEquivalent (left.map f) (right.map f) := by
  intro equivalent
  simpa [Formula.DerivablyEquivalent, Formula.iff, Formula.map,
    Formula.mapContext] using derives_map f equivalent

def Formula.derivablyEquivalentSetoid (Atom : Type u) : Setoid (Formula Atom) where
  r := Formula.DerivablyEquivalent
  iseqv := derivablyEquivalent_equivalence

abbrev Formula.LogicalEquivalenceClass (Atom : Type u) : Type u :=
  Quotient (Formula.derivablyEquivalentSetoid Atom)

def Formula.logicalMap {Atom Atom' : Type u} (f : Atom → Atom')
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.LogicalEquivalenceClass Atom' :=
  Quotient.liftOn formula
    (fun formula => Quotient.mk (Formula.derivablyEquivalentSetoid Atom') (formula.map f))
    (by
      intro left right equivalent
      exact Quotient.sound (derivablyEquivalent_map f equivalent))

theorem Formula.logicalClass_eq_of_derivablyEquivalent {Atom : Type u}
    {left right : Formula Atom}
    (equivalent : Formula.DerivablyEquivalent left right) :
    (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left :
      Formula.LogicalEquivalenceClass Atom) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right :=
  Quotient.sound equivalent

theorem Formula.logicalClass_eq_iff_derives_iff {Atom : Type u}
    (left right : Formula Atom) :
    (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left :
        Formula.LogicalEquivalenceClass Atom) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right ↔
      Derives [] (Formula.iff left right) := by
  constructor
  · exact Quotient.exact
  · intro derives
    apply Quotient.sound
    exact derives

def Formula.logicalAnd {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.LogicalEquivalenceClass Atom :=
  Quotient.liftOn₂ left right
    (fun left right => Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.and left right))
    (by
      intro left right left' right' hleft hright
      exact Quotient.sound (derivablyEquivalent_and_congr hleft hright))

def Formula.logicalOr {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.LogicalEquivalenceClass Atom :=
  Quotient.liftOn₂ left right
    (fun left right => Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.or left right))
    (by
      intro left right left' right' hleft hright
      exact Quotient.sound (derivablyEquivalent_or_congr hleft hright))

def Formula.logicalImp {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.LogicalEquivalenceClass Atom :=
  Quotient.liftOn₂ left right
    (fun left right => Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.imp left right))
    (by
      intro left right left' right' hleft hright
      exact Quotient.sound (derivablyEquivalent_imp_congr hleft hright))

def Formula.logicalTop {Atom : Type u} : Formula.LogicalEquivalenceClass Atom :=
  Quotient.mk (Formula.derivablyEquivalentSetoid Atom) .top

def Formula.logicalBottom {Atom : Type u} : Formula.LogicalEquivalenceClass Atom :=
  Quotient.mk (Formula.derivablyEquivalentSetoid Atom) .bot

def Formula.logicalNeg {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.LogicalEquivalenceClass Atom :=
  Formula.logicalImp formula Formula.logicalBottom

theorem Formula.logicalAnd_mk {Atom : Type u} (left right : Formula Atom) :
    Formula.logicalAnd
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left)
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.and left right) := rfl

theorem Formula.logicalOr_mk {Atom : Type u} (left right : Formula Atom) :
    Formula.logicalOr
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left)
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.or left right) := rfl

theorem Formula.logicalImp_mk {Atom : Type u} (left right : Formula Atom) :
    Formula.logicalImp
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left)
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.imp left right) := rfl

theorem Formula.logicalNeg_mk {Atom : Type u} (formula : Formula Atom) :
    Formula.logicalNeg
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula.neg := rfl

theorem Formula.logicalMap_mk {Atom Atom' : Type u} (f : Atom → Atom')
    (formula : Formula Atom) :
    Formula.logicalMap f
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom') (formula.map f) := rfl

theorem Formula.logicalMap_top {Atom Atom' : Type u} (f : Atom → Atom') :
    Formula.logicalMap f (Formula.logicalTop : Formula.LogicalEquivalenceClass Atom) =
      (Formula.logicalTop : Formula.LogicalEquivalenceClass Atom') := rfl

theorem Formula.logicalMap_bottom {Atom Atom' : Type u} (f : Atom → Atom') :
    Formula.logicalMap f (Formula.logicalBottom : Formula.LogicalEquivalenceClass Atom) =
      (Formula.logicalBottom : Formula.LogicalEquivalenceClass Atom') := rfl

theorem Formula.logicalMap_and {Atom Atom' : Type u} (f : Atom → Atom')
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap f (Formula.logicalAnd left right) =
      Formula.logicalAnd (Formula.logicalMap f left) (Formula.logicalMap f right) := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  rfl

theorem Formula.logicalMap_or {Atom Atom' : Type u} (f : Atom → Atom')
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap f (Formula.logicalOr left right) =
      Formula.logicalOr (Formula.logicalMap f left) (Formula.logicalMap f right) := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  rfl

theorem Formula.logicalMap_imp {Atom Atom' : Type u} (f : Atom → Atom')
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap f (Formula.logicalImp left right) =
      Formula.logicalImp (Formula.logicalMap f left) (Formula.logicalMap f right) := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  rfl

theorem Formula.logicalMap_neg {Atom Atom' : Type u} (f : Atom → Atom')
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap f (Formula.logicalNeg formula) =
      Formula.logicalNeg (Formula.logicalMap f formula) := by
  unfold Formula.logicalNeg
  rw [Formula.logicalMap_imp, Formula.logicalMap_bottom]

theorem Formula.logicalMap_id {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap id formula = formula := by
  refine Quotient.inductionOn formula ?_
  intro formula
  change Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (formula.map id) =
    Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula
  rw [Formula.map_id]

theorem Formula.logicalMap_comp {Atom Atom' Atom'' : Type u}
    (g : Atom' → Atom'') (f : Atom → Atom')
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap g (Formula.logicalMap f formula) =
      Formula.logicalMap (g ∘ f) formula := by
  refine Quotient.inductionOn formula ?_
  intro formula
  change Quotient.mk (Formula.derivablyEquivalentSetoid Atom'')
      ((formula.map f).map g) =
    Quotient.mk (Formula.derivablyEquivalentSetoid Atom'') (formula.map (g ∘ f))
  rw [Formula.map_comp]

theorem Formula.logicalMap_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom)
    (hgf : ∀ atom, g (f atom) = atom)
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap g (Formula.logicalMap f formula) = formula := by
  rw [Formula.logicalMap_comp]
  refine Quotient.inductionOn formula ?_
  intro formula
  change Quotient.mk (Formula.derivablyEquivalentSetoid Atom)
      (formula.map (g ∘ f)) =
    Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula
  have hmap : formula.map (g ∘ f) = formula := by
    rw [← Formula.map_comp g f]
    exact Formula.map_leftInverse f g hgf formula
  rw [hmap]

theorem Formula.logicalMap_rightInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom)
    (hfg : ∀ atom', f (g atom') = atom')
    (formula : Formula.LogicalEquivalenceClass Atom') :
    Formula.logicalMap f (Formula.logicalMap g formula) = formula :=
  Formula.logicalMap_leftInverse g f hfg formula

structure Formula.LogicalHeytingIsomorphism (Atom Atom' : Type u) where
  forward : Formula.LogicalEquivalenceClass Atom →
    Formula.LogicalEquivalenceClass Atom'
  inverse : Formula.LogicalEquivalenceClass Atom' →
    Formula.LogicalEquivalenceClass Atom
  left_inverse : ∀ formula, inverse (forward formula) = formula
  right_inverse : ∀ formula, forward (inverse formula) = formula
  map_top : forward Formula.logicalTop = Formula.logicalTop
  map_bottom : forward Formula.logicalBottom = Formula.logicalBottom
  map_and : ∀ left right,
    forward (Formula.logicalAnd left right) =
      Formula.logicalAnd (forward left) (forward right)
  map_or : ∀ left right,
    forward (Formula.logicalOr left right) =
      Formula.logicalOr (forward left) (forward right)
  map_imp : ∀ left right,
    forward (Formula.logicalImp left right) =
      Formula.logicalImp (forward left) (forward right)
  map_neg : ∀ formula,
    forward (Formula.logicalNeg formula) = Formula.logicalNeg (forward formula)

def Formula.logicalMap_isomorphism {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom)
    (hgf : ∀ atom, g (f atom) = atom)
    (hfg : ∀ atom', f (g atom') = atom') :
    Formula.LogicalHeytingIsomorphism Atom Atom' where
  forward := Formula.logicalMap f
  inverse := Formula.logicalMap g
  left_inverse := Formula.logicalMap_leftInverse f g hgf
  right_inverse := Formula.logicalMap_rightInverse f g hfg
  map_top := Formula.logicalMap_top f
  map_bottom := Formula.logicalMap_bottom f
  map_and := Formula.logicalMap_and f
  map_or := Formula.logicalMap_or f
  map_imp := Formula.logicalMap_imp f
  map_neg := Formula.logicalMap_neg f

theorem Formula.LogicalHeytingIsomorphism.injective {Atom Atom' : Type u}
    (iso : Formula.LogicalHeytingIsomorphism Atom Atom') :
    ∀ ⦃left right⦄, iso.forward left = iso.forward right → left = right := by
  intro left right equal
  have mappedEqual := congrArg iso.inverse equal
  simpa only [iso.left_inverse] using mappedEqual

theorem Formula.LogicalHeytingIsomorphism.surjective {Atom Atom' : Type u}
    (iso : Formula.LogicalHeytingIsomorphism Atom Atom') :
    ∀ target, ∃ source, iso.forward source = target := by
  intro target
  exact ⟨iso.inverse target, iso.right_inverse target⟩

theorem Formula.LogicalHeytingIsomorphism.eq_iff {Atom Atom' : Type u}
    (iso : Formula.LogicalHeytingIsomorphism Atom Atom')
    (left right : Formula.LogicalEquivalenceClass Atom) :
    iso.forward left = iso.forward right ↔ left = right := by
  constructor
  · exact iso.injective (left := left) (right := right)
  · intro equal
    rw [equal]

theorem Formula.logicalMap_injective_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom)
    (hgf : ∀ atom, g (f atom) = atom) :
    ∀ ⦃left right : Formula.LogicalEquivalenceClass Atom⦄,
      Formula.logicalMap f left = Formula.logicalMap f right → left = right := by
  intro left right equal
  have mappedEqual := congrArg (Formula.logicalMap g) equal
  simpa only [Formula.logicalMap_leftInverse f g hgf] using mappedEqual

theorem Formula.logicalMap_surjective {Atom Atom' : Type u} (f : Atom → Atom')
    (surjective : ∀ target, ∃ source, f source = target) :
    ∀ target : Formula.LogicalEquivalenceClass Atom',
      ∃ source : Formula.LogicalEquivalenceClass Atom,
        Formula.logicalMap f source = target := by
  intro target
  refine Quotient.inductionOn target ?_
  intro formula
  obtain ⟨source, hsource⟩ := Formula.map_surjective f surjective formula
  exact ⟨Quotient.mk (Formula.derivablyEquivalentSetoid Atom) source, by
    change Quotient.mk (Formula.derivablyEquivalentSetoid Atom') (source.map f) =
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom') formula
    rw [hsource]⟩

def Formula.LogicalEntails {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) : Prop :=
  Formula.logicalImp left right = Formula.logicalTop

theorem logicalClass_eq_top_iff_derives {Atom : Type u} (formula : Formula Atom) :
    (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula :
        Formula.LogicalEquivalenceClass Atom) = Formula.logicalTop ↔
      Derives [] formula := by
  constructor
  · intro equal
    have equivalent : Formula.DerivablyEquivalent formula .top := Quotient.exact equal
    exact Derives.impE (derives_iffER equivalent) Derives.topI
  · intro derives
    apply Quotient.sound
    apply derives_iffI
    · apply Derives.impI
      exact Derives.topI
    · apply Derives.impI
      exact derives_weaken (source := []) (target := [.top])
        (by intro assumption hmem; simp at hmem) derives

theorem derives_imp_and_curry_iff {Atom : Type u} (p q r : Formula Atom) :
    Derives [] (Formula.iff (.imp (.and p q) r) (.imp p (.imp q r))) := by
  apply derives_iffI
  · apply Derives.impI
    apply Derives.impI
    apply Derives.impI
    apply Derives.impE
    · exact Derives.ax (p := .imp (.and p q) r) (by simp)
    · exact Derives.andI (Derives.ax (p := p) (by simp))
        (Derives.ax (p := q) (by simp))
  · apply Derives.impI
    apply Derives.impI
    apply Derives.impE
    · apply Derives.impE
      · exact Derives.ax (p := .imp p (.imp q r)) (by simp)
      · exact Derives.andEL (p := p) (q := q) (Derives.ax (by simp))
    · exact Derives.andER (p := p) (q := q) (Derives.ax (by simp))

theorem Formula.logicalImp_and_curry {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalImp (Formula.logicalAnd p q) r =
      Formula.logicalImp p (Formula.logicalImp q r) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  exact Quotient.sound (derives_imp_and_curry_iff p q r)

theorem Formula.logicalEntails_and_iff {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.LogicalEntails (Formula.logicalAnd p q) r ↔
      Formula.LogicalEntails p (Formula.logicalImp q r) := by
  unfold Formula.LogicalEntails
  rw [Formula.logicalImp_and_curry]

theorem logicalImp_class_eq_top_iff_derives {Atom : Type u}
    (left right : Formula Atom) :
    (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.imp left right) :
        Formula.LogicalEquivalenceClass Atom) = Formula.logicalTop ↔
      Derives [] (.imp left right) := by
  constructor
  · intro equal
    have equivalent : Formula.DerivablyEquivalent (.imp left right) .top :=
      Quotient.exact equal
    exact Derives.impE (derives_iffER equivalent) Derives.topI
  · intro derives
    apply Quotient.sound
    apply derives_iffI
    · apply Derives.impI
      exact Derives.topI
    · apply Derives.impI
      exact derives_weaken (source := []) (target := [.top])
        (by intro formula hmem; simp at hmem) derives

theorem Formula.logicalEntails_refl {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.LogicalEntails formula formula := by
  refine Quotient.inductionOn formula ?_
  intro formula
  apply (logicalImp_class_eq_top_iff_derives formula formula).2
  apply Derives.impI
  exact Derives.ax (by simp)

theorem Formula.logicalEntails_trans {Atom : Type u}
    {left middle right : Formula.LogicalEquivalenceClass Atom} :
    Formula.LogicalEntails left middle →
      Formula.LogicalEntails middle right →
        Formula.LogicalEntails left right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn middle ?_
  intro middle
  refine Quotient.inductionOn right ?_
  intro right leftMiddle middleRight
  have hlm : Derives [] (.imp left middle) :=
    (logicalImp_class_eq_top_iff_derives left middle).1 leftMiddle
  have hmr : Derives [] (.imp middle right) :=
    (logicalImp_class_eq_top_iff_derives middle right).1 middleRight
  apply (logicalImp_class_eq_top_iff_derives left right).2
  apply Derives.impI
  apply Derives.impE
  · exact derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) hmr
  · apply Derives.impE
    · exact derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) hlm
    · exact Derives.ax (by simp)

theorem Formula.logicalEntails_antisymm {Atom : Type u}
    {left right : Formula.LogicalEquivalenceClass Atom} :
    Formula.LogicalEntails left right →
      Formula.LogicalEntails right left → left = right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right leftRight rightLeft
  apply Quotient.sound
  apply derives_iffI
  · exact (logicalImp_class_eq_top_iff_derives left right).1 leftRight
  · exact (logicalImp_class_eq_top_iff_derives right left).1 rightLeft

instance Formula.logicalEntailsLE (Atom : Type u) :
    LE (Formula.LogicalEquivalenceClass Atom) where
  le := Formula.LogicalEntails

structure Formula.LogicalPartialOrderLaws (Atom : Type u) : Prop where
  refl : ∀ formula : Formula.LogicalEquivalenceClass Atom, formula ≤ formula
  trans : ∀ {left middle right : Formula.LogicalEquivalenceClass Atom},
    left ≤ middle → middle ≤ right → left ≤ right
  antisymm : ∀ {left right : Formula.LogicalEquivalenceClass Atom},
    left ≤ right → right ≤ left → left = right

theorem Formula.logicalEntailsOrderLaws (Atom : Type u) :
    Formula.LogicalPartialOrderLaws Atom where
  refl := Formula.logicalEntails_refl
  trans := Formula.logicalEntails_trans
  antisymm := Formula.logicalEntails_antisymm

theorem Formula.logicalAnd_le_iff_le_logicalImp {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd p q ≤ r ↔ p ≤ Formula.logicalImp q r :=
  Formula.logicalEntails_and_iff p q r

theorem logicalEntails_mk_iff_derives {Atom : Type u} (left right : Formula Atom) :
    Formula.LogicalEntails
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left)
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right) ↔
      Derives [] (.imp left right) :=
  logicalImp_class_eq_top_iff_derives left right

theorem Formula.logicalMap_monotone {Atom Atom' : Type u} (f : Atom → Atom')
    {left right : Formula.LogicalEquivalenceClass Atom} :
    left ≤ right → Formula.logicalMap f left ≤ Formula.logicalMap f right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right leftRight
  have derives : Derives [] (.imp left right) :=
    (logicalEntails_mk_iff_derives left right).1 leftRight
  apply (logicalEntails_mk_iff_derives (left.map f) (right.map f)).2
  simpa [Formula.map, Formula.mapContext] using derives_map f derives

theorem Formula.logicalMap_reflects_order_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom)
    (hgf : ∀ atom, g (f atom) = atom)
    {left right : Formula.LogicalEquivalenceClass Atom} :
    Formula.logicalMap f left ≤ Formula.logicalMap f right → left ≤ right := by
  intro mappedOrder
  have reflected := Formula.logicalMap_monotone g mappedOrder
  simpa only [Formula.logicalMap_leftInverse f g hgf] using reflected

theorem Formula.logicalMap_orderEmbedding_iff {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom)
    (hgf : ∀ atom, g (f atom) = atom)
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalMap f left ≤ Formula.logicalMap f right ↔ left ≤ right := by
  constructor
  · exact Formula.logicalMap_reflects_order_of_leftInverse f g hgf
  · exact Formula.logicalMap_monotone f

theorem Formula.LogicalHeytingIsomorphism.monotone {Atom Atom' : Type u}
    (iso : Formula.LogicalHeytingIsomorphism Atom Atom')
    {left right : Formula.LogicalEquivalenceClass Atom} :
    left ≤ right → iso.forward left ≤ iso.forward right := by
  intro leftRight
  change Formula.LogicalEntails left right at leftRight
  change Formula.LogicalEntails (iso.forward left) (iso.forward right)
  unfold Formula.LogicalEntails at leftRight ⊢
  calc
    Formula.logicalImp (iso.forward left) (iso.forward right) =
        iso.forward (Formula.logicalImp left right) := (iso.map_imp left right).symm
    _ = iso.forward Formula.logicalTop := congrArg iso.forward leftRight
    _ = Formula.logicalTop := iso.map_top

theorem Formula.LogicalHeytingIsomorphism.reflects_order {Atom Atom' : Type u}
    (iso : Formula.LogicalHeytingIsomorphism Atom Atom')
    {left right : Formula.LogicalEquivalenceClass Atom} :
    iso.forward left ≤ iso.forward right → left ≤ right := by
  intro mappedOrder
  change Formula.LogicalEntails (iso.forward left) (iso.forward right) at mappedOrder
  change Formula.LogicalEntails left right
  unfold Formula.LogicalEntails at mappedOrder ⊢
  apply iso.injective
  rw [iso.map_imp, iso.map_top]
  exact mappedOrder

theorem Formula.LogicalHeytingIsomorphism.order_iff {Atom Atom' : Type u}
    (iso : Formula.LogicalHeytingIsomorphism Atom Atom')
    (left right : Formula.LogicalEquivalenceClass Atom) :
    iso.forward left ≤ iso.forward right ↔ left ≤ right := by
  constructor
  · exact iso.reflects_order
  · exact iso.monotone

theorem Formula.logicalAnd_le_left {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd left right ≤ left := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply (logicalEntails_mk_iff_derives (.and left right) left).2
  apply Derives.impI
  exact Derives.andEL (p := left) (q := right) (Derives.ax (by simp))

theorem Formula.logicalAnd_le_right {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd left right ≤ right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply (logicalEntails_mk_iff_derives (.and left right) right).2
  apply Derives.impI
  exact Derives.andER (p := left) (q := right) (Derives.ax (by simp))

theorem Formula.le_logicalAnd_iff {Atom : Type u}
    (lower left right : Formula.LogicalEquivalenceClass Atom) :
    lower ≤ Formula.logicalAnd left right ↔ lower ≤ left ∧ lower ≤ right := by
  refine Quotient.inductionOn lower ?_
  intro lower
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  constructor
  · intro lowerAnd
    have derives : Derives [] (.imp lower (.and left right)) :=
      (logicalEntails_mk_iff_derives lower (.and left right)).1 lowerAnd
    constructor
    · apply (logicalEntails_mk_iff_derives lower left).2
      apply Derives.impI
      exact Derives.andEL (Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) derives)
        (Derives.ax (by simp)))
    · apply (logicalEntails_mk_iff_derives lower right).2
      apply Derives.impI
      exact Derives.andER (Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) derives)
        (Derives.ax (by simp)))
  · rintro ⟨lowerLeft, lowerRight⟩
    have hleft := (logicalEntails_mk_iff_derives lower left).1 lowerLeft
    have hright := (logicalEntails_mk_iff_derives lower right).1 lowerRight
    apply (logicalEntails_mk_iff_derives lower (.and left right)).2
    apply Derives.impI
    apply Derives.andI
    · exact Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) hleft)
        (Derives.ax (by simp))
    · exact Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) hright)
        (Derives.ax (by simp))

theorem Formula.logicalOr_le_iff {Atom : Type u}
    (left right upper : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr left right ≤ upper ↔ left ≤ upper ∧ right ≤ upper := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  refine Quotient.inductionOn upper ?_
  intro upper
  constructor
  · intro orUpper
    have derives := (logicalEntails_mk_iff_derives (.or left right) upper).1 orUpper
    constructor
    · apply (logicalEntails_mk_iff_derives left upper).2
      apply Derives.impI
      exact Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) derives)
        (Derives.orIL (Derives.ax (by simp)))
    · apply (logicalEntails_mk_iff_derives right upper).2
      apply Derives.impI
      exact Derives.impE
        (derives_weaken (fun formula hmem => List.mem_cons_of_mem _ hmem) derives)
        (Derives.orIR (Derives.ax (by simp)))
  · rintro ⟨leftUpper, rightUpper⟩
    have hleft := (logicalEntails_mk_iff_derives left upper).1 leftUpper
    have hright := (logicalEntails_mk_iff_derives right upper).1 rightUpper
    apply (logicalEntails_mk_iff_derives (.or left right) upper).2
    apply Derives.impI
    refine Derives.orE (p := left) (q := right) (r := upper)
      (Derives.ax (by simp)) ?_ ?_
    · exact Derives.impE
        (derives_weaken (source := []) (target := left :: [.or left right])
          (by intro formula hmem; simp at hmem) hleft)
        (Derives.ax (by simp))
    · exact Derives.impE
        (derives_weaken (source := []) (target := right :: [.or left right])
          (by intro formula hmem; simp at hmem) hright)
        (Derives.ax (by simp))

theorem Formula.logicalBottom_le {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalBottom ≤ formula := by
  refine Quotient.inductionOn formula ?_
  intro formula
  apply (logicalEntails_mk_iff_derives .bot formula).2
  apply Derives.impI
  exact Derives.botE (Derives.ax (by simp))

theorem Formula.le_logicalTop {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    formula ≤ Formula.logicalTop := by
  refine Quotient.inductionOn formula ?_
  intro formula
  apply (logicalEntails_mk_iff_derives formula .top).2
  apply Derives.impI
  exact Derives.topI

theorem Formula.le_logicalOr_left {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    left ≤ Formula.logicalOr left right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply (logicalEntails_mk_iff_derives left (.or left right)).2
  apply Derives.impI
  exact Derives.orIL (Derives.ax (by simp))

theorem Formula.le_logicalOr_right {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    right ≤ Formula.logicalOr left right := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  apply (logicalEntails_mk_iff_derives right (.or left right)).2
  apply Derives.impI
  exact Derives.orIR (Derives.ax (by simp))

theorem inconsistent_extension_iff_derives_neg {Atom : Type u}
    {context : List (Formula Atom)} {formula : Formula Atom} :
    Derives (formula :: context) .bot ↔ Derives context formula.neg :=
  derives_imp_iff.symm

theorem derives_and_top_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.and formula .top) formula) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.andEL (p := formula) (q := .top) (Derives.ax (by simp))
  · apply Derives.impI
    exact Derives.andI (Derives.ax (by simp)) Derives.topI

theorem derives_or_bottom_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.or formula .bot) formula) := by
  apply derives_iffI
  · apply Derives.impI
    refine Derives.orE (p := formula) (q := .bot) (r := formula)
      (Derives.ax (by simp)) ?_ ?_
    · exact Derives.ax (by simp)
    · exact Derives.botE (Derives.ax (by simp))
  · apply Derives.impI
    exact Derives.orIL (Derives.ax (by simp))

theorem Formula.logicalAnd_top {Atom : Type u} (formula : Formula Atom) :
    Formula.logicalAnd (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula)
      Formula.logicalTop = Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula := by
  exact Quotient.sound (derives_and_top_iff formula)

theorem Formula.logicalOr_bottom {Atom : Type u} (formula : Formula Atom) :
    Formula.logicalOr (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula)
      Formula.logicalBottom = Quotient.mk (Formula.derivablyEquivalentSetoid Atom) formula := by
  exact Quotient.sound (derives_or_bottom_iff formula)

theorem derives_and_bottom_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.and formula .bot) .bot) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.andER (p := formula) (q := .bot) (Derives.ax (by simp))
  · apply Derives.impI
    exact Derives.botE (Derives.ax (by simp))

theorem derives_or_top_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.or formula .top) .top) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.topI
  · apply Derives.impI
    exact Derives.orIR Derives.topI

theorem Formula.logicalAnd_bottom {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd formula Formula.logicalBottom = Formula.logicalBottom := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Quotient.sound (derives_and_bottom_iff formula)

theorem Formula.logicalOr_top {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr formula Formula.logicalTop = Formula.logicalTop := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Quotient.sound (derives_or_top_iff formula)

theorem Formula.logicalAnd_top_all {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd formula Formula.logicalTop = formula := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Formula.logicalAnd_top formula

theorem Formula.logicalOr_bottom_all {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr formula Formula.logicalBottom = formula := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Formula.logicalOr_bottom formula

/- The first nontrivial connective law needed to read incidence products and
   sums as logical structure.  Both directions are natural-deduction
   derivations, rather than an appeal to a Boolean meta-semantics, so the law
   remains valid for the intuitionistic/Kripke internal logic. -/
theorem derives_and_or_distributive {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (.imp (.and p (.or q r))
      (.or (.and p q) (.and p r))) ∧
    Derives [] (.imp (.or (.and p q) (.and p r))
      (.and p (.or q r))) := by
  constructor
  · apply Derives.impI
    refine Derives.orE (p := q) (q := r)
      (r := .or (.and p q) (.and p r))
      (Derives.andER (p := p) (q := .or q r) (Derives.ax (by simp))) ?_ ?_
    · apply Derives.orIL
      apply Derives.andI
      · exact Derives.andEL (p := p) (q := .or q r) (Derives.ax (by simp))
      · exact Derives.ax (by simp)
    · apply Derives.orIR
      apply Derives.andI
      · exact Derives.andEL (p := p) (q := .or q r) (Derives.ax (by simp))
      · exact Derives.ax (by simp)
  · apply Derives.impI
    refine Derives.orE (p := .and p q) (q := .and p r)
      (r := .and p (.or q r)) (Derives.ax (by simp)) ?_ ?_
    · apply Derives.andI
      · exact Derives.andEL (p := p) (q := q) (Derives.ax (by simp))
      · apply Derives.orIL
        exact Derives.andER (p := p) (q := q) (Derives.ax (by simp))
    · apply Derives.andI
      · exact Derives.andEL (p := p) (q := r) (Derives.ax (by simp))
      · apply Derives.orIR
        exact Derives.andER (p := p) (q := r) (Derives.ax (by simp))

theorem derives_and_commutative_iff {Atom : Type u}
    (left right : Formula Atom) :
    Derives [] (Formula.iff (.and left right) (.and right left)) := by
  apply derives_iffI
  · apply Derives.impI
    apply Derives.andI
    · exact Derives.andER (p := left) (q := right) (Derives.ax (by simp))
    · exact Derives.andEL (p := left) (q := right) (Derives.ax (by simp))
  · apply Derives.impI
    apply Derives.andI
    · exact Derives.andER (p := right) (q := left) (Derives.ax (by simp))
    · exact Derives.andEL (p := right) (q := left) (Derives.ax (by simp))

theorem Formula.logicalAnd_commutative {Atom : Type u}
    (left right : Formula Atom) :
    Formula.logicalAnd (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left)
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right) =
      Formula.logicalAnd (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right)
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left) := by
  exact Quotient.sound (derives_and_commutative_iff left right)

theorem Formula.logicalAnd_comm {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd left right = Formula.logicalAnd right left := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  exact Formula.logicalAnd_commutative left right

theorem derives_or_commutative_iff {Atom : Type u}
    (left right : Formula Atom) :
    Derives [] (Formula.iff (.or left right) (.or right left)) := by
  apply derives_iffI
  · apply Derives.impI
    refine Derives.orE (p := left) (q := right) (r := .or right left)
      (Derives.ax (by simp)) ?_ ?_
    · exact Derives.orIR (Derives.ax (by simp))
    · exact Derives.orIL (Derives.ax (by simp))
  · apply Derives.impI
    refine Derives.orE (p := right) (q := left) (r := .or left right)
      (Derives.ax (by simp)) ?_ ?_
    · exact Derives.orIR (Derives.ax (by simp))
    · exact Derives.orIL (Derives.ax (by simp))

theorem Formula.logicalOr_commutative {Atom : Type u}
    (left right : Formula Atom) :
    Formula.logicalOr (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left)
      (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right) =
      Formula.logicalOr (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) right)
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) left) := by
  exact Quotient.sound (derives_or_commutative_iff left right)

theorem Formula.logicalOr_comm {Atom : Type u}
    (left right : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr left right = Formula.logicalOr right left := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  exact Formula.logicalOr_commutative left right

theorem Formula.logicalTop_and {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd Formula.logicalTop formula = formula := by
  rw [Formula.logicalAnd_comm, Formula.logicalAnd_top_all]

theorem Formula.logicalBottom_or {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr Formula.logicalBottom formula = formula := by
  rw [Formula.logicalOr_comm, Formula.logicalOr_bottom_all]

theorem Formula.logicalBottom_and {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd Formula.logicalBottom formula = Formula.logicalBottom := by
  rw [Formula.logicalAnd_comm, Formula.logicalAnd_bottom]

theorem Formula.logicalTop_or {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr Formula.logicalTop formula = Formula.logicalTop := by
  rw [Formula.logicalOr_comm, Formula.logicalOr_top]

theorem derives_and_associative_iff {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (Formula.iff (.and (.and p q) r) (.and p (.and q r))) := by
  apply derives_iffI
  · apply Derives.impI
    apply Derives.andI
    · exact Derives.andEL (p := p) (q := q)
        (Derives.andEL (p := .and p q) (q := r) (Derives.ax (by simp)))
    · apply Derives.andI
      · exact Derives.andER (p := p) (q := q)
          (Derives.andEL (p := .and p q) (q := r) (Derives.ax (by simp)))
      · exact Derives.andER (p := .and p q) (q := r) (Derives.ax (by simp))
  · apply Derives.impI
    apply Derives.andI
    · apply Derives.andI
      · exact Derives.andEL (p := p) (q := .and q r) (Derives.ax (by simp))
      · exact Derives.andEL (p := q) (q := r)
          (Derives.andER (p := p) (q := .and q r) (Derives.ax (by simp)))
    · exact Derives.andER (p := q) (q := r)
        (Derives.andER (p := p) (q := .and q r) (Derives.ax (by simp)))

theorem Formula.logicalAnd_associative {Atom : Type u} (p q r : Formula Atom) :
    Formula.logicalAnd
        (Formula.logicalAnd
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q))
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r) =
      Formula.logicalAnd
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
        (Formula.logicalAnd
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r)) := by
  exact Quotient.sound (derives_and_associative_iff p q r)

theorem Formula.logicalAnd_assoc {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd (Formula.logicalAnd p q) r =
      Formula.logicalAnd p (Formula.logicalAnd q r) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  exact Formula.logicalAnd_associative p q r

theorem derives_or_associative_iff {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (Formula.iff (.or (.or p q) r) (.or p (.or q r))) := by
  apply derives_iffI
  · apply Derives.impI
    refine Derives.orE (p := .or p q) (q := r) (r := .or p (.or q r))
      (Derives.ax (by simp)) ?_ ?_
    · refine Derives.orE (p := p) (q := q) (r := .or p (.or q r))
        (Derives.ax (by simp)) ?_ ?_
      · exact Derives.orIL (Derives.ax (by simp))
      · exact Derives.orIR (Derives.orIL (Derives.ax (by simp)))
    · exact Derives.orIR (Derives.orIR (Derives.ax (by simp)))
  · apply Derives.impI
    refine Derives.orE (p := p) (q := .or q r) (r := .or (.or p q) r)
      (Derives.ax (by simp)) ?_ ?_
    · exact Derives.orIL (Derives.orIL (Derives.ax (by simp)))
    · refine Derives.orE (p := q) (q := r) (r := .or (.or p q) r)
        (Derives.ax (by simp)) ?_ ?_
      · exact Derives.orIL (Derives.orIR (Derives.ax (by simp)))
      · exact Derives.orIR (Derives.ax (by simp))

theorem Formula.logicalOr_associative {Atom : Type u} (p q r : Formula Atom) :
    Formula.logicalOr
        (Formula.logicalOr
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q))
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r) =
      Formula.logicalOr
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
        (Formula.logicalOr
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r)) := by
  exact Quotient.sound (derives_or_associative_iff p q r)

theorem Formula.logicalOr_assoc {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr (Formula.logicalOr p q) r =
      Formula.logicalOr p (Formula.logicalOr q r) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  exact Formula.logicalOr_associative p q r

theorem derives_and_idempotent_iff {Atom : Type u} (p : Formula Atom) :
    Derives [] (Formula.iff (.and p p) p) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.andEL (p := p) (q := p) (Derives.ax (by simp))
  · apply Derives.impI
    exact Derives.andI (Derives.ax (by simp)) (Derives.ax (by simp))

theorem derives_or_idempotent_iff {Atom : Type u} (p : Formula Atom) :
    Derives [] (Formula.iff (.or p p) p) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.orE (p := p) (q := p) (r := p) (Derives.ax (by simp))
      (Derives.ax (by simp)) (Derives.ax (by simp))
  · apply Derives.impI
    exact Derives.orIL (Derives.ax (by simp))

theorem Formula.logicalAnd_idempotent {Atom : Type u}
    (p : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd p p = p := by
  refine Quotient.inductionOn p ?_
  intro p
  exact Quotient.sound (derives_and_idempotent_iff p)

theorem Formula.logicalOr_idempotent {Atom : Type u}
    (p : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr p p = p := by
  refine Quotient.inductionOn p ?_
  intro p
  exact Quotient.sound (derives_or_idempotent_iff p)

theorem derives_and_absorbs_or_iff {Atom : Type u} (p q : Formula Atom) :
    Derives [] (Formula.iff (.and p (.or p q)) p) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.andEL (p := p) (q := .or p q) (Derives.ax (by simp))
  · apply Derives.impI
    exact Derives.andI (Derives.ax (by simp))
      (Derives.orIL (Derives.ax (by simp)))

theorem derives_or_absorbs_and_iff {Atom : Type u} (p q : Formula Atom) :
    Derives [] (Formula.iff (.or p (.and p q)) p) := by
  apply derives_iffI
  · apply Derives.impI
    refine Derives.orE (p := p) (q := .and p q) (r := p)
      (Derives.ax (by simp)) (Derives.ax (by simp)) ?_
    exact Derives.andEL (p := p) (q := q) (Derives.ax (by simp))
  · apply Derives.impI
    exact Derives.orIL (Derives.ax (by simp))

theorem Formula.logicalAnd_absorbs_or {Atom : Type u}
    (p q : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd p (Formula.logicalOr p q) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  exact Quotient.sound (derives_and_absorbs_or_iff p q)

theorem Formula.logicalOr_absorbs_and {Atom : Type u}
    (p q : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr p (Formula.logicalAnd p q) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  exact Quotient.sound (derives_or_absorbs_and_iff p q)

theorem satisfies_and_or_distributive {Atom : Type u} (valuation : Atom → Prop)
    (p q r : Formula Atom) :
    Satisfies valuation (.and p (.or q r)) ↔
      Satisfies valuation (.or (.and p q) (.and p r)) := by
  constructor
  · rintro ⟨hp, hq | hr⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

theorem derives_and_or_distributive_iff {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (Formula.iff (.and p (.or q r))
      (.or (.and p q) (.and p r))) :=
  derives_iffI (derives_and_or_distributive p q r).left
    (derives_and_or_distributive p q r).right

theorem Formula.logicalAnd_distributes_over_or {Atom : Type u}
    (p q r : Formula Atom) :
    Formula.logicalAnd (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
      (Formula.logicalOr (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q)
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r)) =
      Formula.logicalOr
        (Formula.logicalAnd (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q))
        (Formula.logicalAnd (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r)) := by
  exact Quotient.sound (derives_and_or_distributive_iff p q r)

theorem Formula.logicalAnd_distrib_or {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd p (Formula.logicalOr q r) =
      Formula.logicalOr (Formula.logicalAnd p q) (Formula.logicalAnd p r) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  exact Formula.logicalAnd_distributes_over_or p q r

theorem satisfies_and_or_distributive_iff {Atom : Type u}
    (valuation : Atom → Prop) (p q r : Formula Atom) :
    Satisfies valuation (Formula.iff (.and p (.or q r))
      (.or (.and p q) (.and p r))) :=
  (satisfies_iff valuation _ _).mpr (satisfies_and_or_distributive valuation p q r)

theorem derives_or_and_distributive {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (.imp (.or p (.and q r))
      (.and (.or p q) (.or p r))) ∧
    Derives [] (.imp (.and (.or p q) (.or p r))
      (.or p (.and q r))) := by
  constructor
  · apply Derives.impI
    refine Derives.orE (p := p) (q := .and q r)
      (r := .and (.or p q) (.or p r)) (Derives.ax (by simp)) ?_ ?_
    · apply Derives.andI <;> apply Derives.orIL <;> exact Derives.ax (by simp)
    · apply Derives.andI
      · apply Derives.orIR
        exact Derives.andEL (p := q) (q := r) (Derives.ax (by simp))
      · apply Derives.orIR
        exact Derives.andER (p := q) (q := r) (Derives.ax (by simp))
  · apply Derives.impI
    refine Derives.orE (p := p) (q := q) (r := .or p (.and q r))
      (Derives.andEL (p := .or p q) (q := .or p r) (Derives.ax (by simp))) ?_ ?_
    · apply Derives.orIL
      exact Derives.ax (by simp)
    · refine Derives.orE (p := p) (q := r) (r := .or p (.and q r))
        (Derives.andER (p := .or p q) (q := .or p r) (Derives.ax (by simp))) ?_ ?_
      · apply Derives.orIL
        exact Derives.ax (by simp)
      · apply Derives.orIR
        apply Derives.andI
        · exact Derives.ax (by simp)
        · exact Derives.ax (by simp)

theorem satisfies_or_and_distributive {Atom : Type u} (valuation : Atom → Prop)
    (p q r : Formula Atom) :
    Satisfies valuation (.or p (.and q r)) ↔
      Satisfies valuation (.and (.or p q) (.or p r)) := by
  constructor
  · rintro (hp | ⟨hq, hr⟩)
    · exact ⟨Or.inl hp, Or.inl hp⟩
    · exact ⟨Or.inr hq, Or.inr hr⟩
  · rintro ⟨hp | hq, hp' | hr⟩
    · exact Or.inl hp
    · exact Or.inl hp
    · exact Or.inl hp'
    · exact Or.inr ⟨hq, hr⟩

theorem derives_or_and_distributive_iff {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (Formula.iff (.or p (.and q r))
      (.and (.or p q) (.or p r))) :=
  derives_iffI (derives_or_and_distributive p q r).left
    (derives_or_and_distributive p q r).right

theorem Formula.logicalOr_distributes_over_and {Atom : Type u}
    (p q r : Formula Atom) :
    Formula.logicalOr (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
      (Formula.logicalAnd (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q)
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r)) =
      Formula.logicalAnd
        (Formula.logicalOr (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) q))
        (Formula.logicalOr (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) p)
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) r)) := by
  exact Quotient.sound (derives_or_and_distributive_iff p q r)

theorem Formula.logicalOr_distrib_and {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalOr p (Formula.logicalAnd q r) =
      Formula.logicalAnd (Formula.logicalOr p q) (Formula.logicalOr p r) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  exact Formula.logicalOr_distributes_over_and p q r

structure Formula.LogicalHeytingAlgebraLaws (Atom : Type u) : Prop where
  order : Formula.LogicalPartialOrderLaws Atom
  bottom_le : ∀ formula : Formula.LogicalEquivalenceClass Atom,
    Formula.logicalBottom ≤ formula
  le_top : ∀ formula : Formula.LogicalEquivalenceClass Atom,
    formula ≤ Formula.logicalTop
  meet : ∀ lower left right : Formula.LogicalEquivalenceClass Atom,
    lower ≤ Formula.logicalAnd left right ↔ lower ≤ left ∧ lower ≤ right
  join : ∀ left right upper : Formula.LogicalEquivalenceClass Atom,
    Formula.logicalOr left right ≤ upper ↔ left ≤ upper ∧ right ≤ upper
  distributive : ∀ p q r : Formula.LogicalEquivalenceClass Atom,
    Formula.logicalAnd p (Formula.logicalOr q r) =
      Formula.logicalOr (Formula.logicalAnd p q) (Formula.logicalAnd p r)
  implication : ∀ p q r : Formula.LogicalEquivalenceClass Atom,
    Formula.logicalAnd p q ≤ r ↔ p ≤ Formula.logicalImp q r

theorem Formula.logicalHeytingAlgebraLaws (Atom : Type u) :
    Formula.LogicalHeytingAlgebraLaws Atom where
  order := Formula.logicalEntailsOrderLaws Atom
  bottom_le := Formula.logicalBottom_le
  le_top := Formula.le_logicalTop
  meet := Formula.le_logicalAnd_iff
  join := Formula.logicalOr_le_iff
  distributive := Formula.logicalAnd_distrib_or
  implication := Formula.logicalAnd_le_iff_le_logicalImp

theorem Formula.logicalAnd_le_bottom_iff_le_neg {Atom : Type u}
    (q p : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd q p ≤ Formula.logicalBottom ↔ q ≤ Formula.logicalNeg p := by
  exact Formula.logicalAnd_le_iff_le_logicalImp q p Formula.logicalBottom

theorem Formula.logicalAnd_neg_le_bottom {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd formula (Formula.logicalNeg formula) ≤
      Formula.logicalBottom := by
  rw [Formula.logicalAnd_comm]
  apply (Formula.logicalAnd_le_bottom_iff_le_neg
    (Formula.logicalNeg formula) formula).2
  exact Formula.logicalEntails_refl _

theorem Formula.logicalAnd_neg {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd formula (Formula.logicalNeg formula) =
      Formula.logicalBottom := by
  apply Formula.logicalEntails_antisymm
  · exact Formula.logicalAnd_neg_le_bottom formula
  · exact Formula.logicalBottom_le _

theorem Formula.le_doubleNeg {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    formula ≤ Formula.logicalNeg (Formula.logicalNeg formula) := by
  apply (Formula.logicalAnd_le_bottom_iff_le_neg formula
    (Formula.logicalNeg formula)).1
  rw [Formula.logicalAnd_neg]
  exact Formula.logicalEntails_refl _

theorem Formula.logicalNeg_antitone {Atom : Type u}
    {left right : Formula.LogicalEquivalenceClass Atom} :
    left ≤ right → Formula.logicalNeg right ≤ Formula.logicalNeg left := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right leftRight
  have hleftRight : Derives [] (.imp left right) :=
    (logicalEntails_mk_iff_derives left right).1 leftRight
  apply (logicalEntails_mk_iff_derives right.neg left.neg).2
  apply Derives.impI
  apply Derives.impI
  apply Derives.impE
  · exact Derives.ax (p := right.neg) (by simp)
  · apply Derives.impE
    · exact derives_weaken (source := []) (target := left :: [right.neg])
        (by intro formula hmem; simp at hmem) hleftRight
    · exact Derives.ax (p := left) (by simp)

theorem Formula.tripleNeg_le_neg {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalNeg (Formula.logicalNeg (Formula.logicalNeg formula)) ≤
      Formula.logicalNeg formula :=
  Formula.logicalNeg_antitone (Formula.le_doubleNeg formula)

theorem Formula.neg_le_tripleNeg {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalNeg formula ≤
      Formula.logicalNeg (Formula.logicalNeg (Formula.logicalNeg formula)) :=
  Formula.le_doubleNeg (Formula.logicalNeg formula)

theorem Formula.logicalTripleNeg {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalNeg (Formula.logicalNeg (Formula.logicalNeg formula)) =
      Formula.logicalNeg formula :=
  Formula.logicalEntails_antisymm
    (Formula.tripleNeg_le_neg formula) (Formula.neg_le_tripleNeg formula)

theorem derives_neg_or_deMorgan_iff {Atom : Type u} (p q : Formula Atom) :
    Derives [] (Formula.iff (Formula.neg (.or p q)) (.and p.neg q.neg)) := by
  apply derives_iffI
  · apply Derives.impI
    apply Derives.andI
    · apply Derives.impI
      apply Derives.impE
      · exact Derives.ax (p := Formula.neg (.or p q)) (by simp)
      · exact Derives.orIL (Derives.ax (p := p) (by simp))
    · apply Derives.impI
      apply Derives.impE
      · exact Derives.ax (p := Formula.neg (.or p q)) (by simp)
      · exact Derives.orIR (Derives.ax (p := q) (by simp))
  · apply Derives.impI
    apply Derives.impI
    refine Derives.orE (p := p) (q := q) (r := .bot)
      (Derives.ax (by simp)) ?_ ?_
    · exact Derives.impE
        (Derives.andEL (p := p.neg) (q := q.neg) (Derives.ax (by simp)))
        (Derives.ax (p := p) (by simp))
    · exact Derives.impE
        (Derives.andER (p := p.neg) (q := q.neg) (Derives.ax (by simp)))
        (Derives.ax (p := q) (by simp))

theorem Formula.logicalNeg_or {Atom : Type u}
    (p q : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalNeg (Formula.logicalOr p q) =
      Formula.logicalAnd (Formula.logicalNeg p) (Formula.logicalNeg q) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  exact Quotient.sound (derives_neg_or_deMorgan_iff p q)

theorem derives_top_imp_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.imp .top formula) formula) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.impE (Derives.ax (by simp)) Derives.topI
  · apply Derives.impI
    apply Derives.impI
    exact Derives.ax (p := formula) (by simp)

theorem derives_imp_top_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.imp formula .top) .top) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.topI
  · apply Derives.impI
    apply Derives.impI
    exact Derives.topI

theorem derives_bottom_imp_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.imp .bot formula) .top) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.topI
  · apply Derives.impI
    apply Derives.impI
    exact Derives.botE (Derives.ax (by simp))

theorem derives_imp_self_iff {Atom : Type u} (formula : Formula Atom) :
    Derives [] (Formula.iff (.imp formula formula) .top) := by
  apply derives_iffI
  · apply Derives.impI
    exact Derives.topI
  · apply Derives.impI
    apply Derives.impI
    exact Derives.ax (p := formula) (by simp)

theorem Formula.logicalTop_imp {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalImp Formula.logicalTop formula = formula := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Quotient.sound (derives_top_imp_iff formula)

theorem Formula.logicalImp_top {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalImp formula Formula.logicalTop = Formula.logicalTop := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Quotient.sound (derives_imp_top_iff formula)

theorem Formula.logicalBottom_imp {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalImp Formula.logicalBottom formula = Formula.logicalTop := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Quotient.sound (derives_bottom_imp_iff formula)

theorem Formula.logicalImp_self {Atom : Type u}
    (formula : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalImp formula formula = Formula.logicalTop := by
  refine Quotient.inductionOn formula ?_
  intro formula
  exact Quotient.sound (derives_imp_self_iff formula)

theorem Formula.logicalNeg_top {Atom : Type u} :
    Formula.logicalNeg (Formula.logicalTop : Formula.LogicalEquivalenceClass Atom) =
      Formula.logicalBottom := by
  exact Formula.logicalTop_imp Formula.logicalBottom

theorem Formula.logicalNeg_bottom {Atom : Type u} :
    Formula.logicalNeg (Formula.logicalBottom : Formula.LogicalEquivalenceClass Atom) =
      Formula.logicalTop := by
  exact Formula.logicalBottom_imp Formula.logicalBottom

theorem Formula.logicalImp_mono {Atom : Type u}
    {left left' right right' : Formula.LogicalEquivalenceClass Atom} :
    left' ≤ left → right ≤ right' →
      Formula.logicalImp left right ≤ Formula.logicalImp left' right' := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn left' ?_
  intro left'
  refine Quotient.inductionOn right ?_
  intro right
  refine Quotient.inductionOn right' ?_
  intro right' hleft hright
  have derivesLeft : Derives [] (.imp left' left) :=
    (logicalEntails_mk_iff_derives left' left).1 hleft
  have derivesRight : Derives [] (.imp right right') :=
    (logicalEntails_mk_iff_derives right right').1 hright
  apply (logicalEntails_mk_iff_derives (.imp left right) (.imp left' right')).2
  apply Derives.impI
  apply Derives.impI
  apply Derives.impE
  · exact derives_weaken (source := [])
      (target := left' :: [.imp left right])
      (by intro formula hmem; simp at hmem) derivesRight
  · apply Derives.impE
    · exact Derives.ax (p := .imp left right) (by simp)
    · apply Derives.impE
      · exact derives_weaken (source := [])
          (target := left' :: [.imp left right])
          (by intro formula hmem; simp at hmem) derivesLeft
      · exact Derives.ax (p := left') (by simp)

theorem Formula.logicalImp_antitone_left {Atom : Type u}
    {left left' right : Formula.LogicalEquivalenceClass Atom}
    (hleft : left' ≤ left) :
    Formula.logicalImp left right ≤ Formula.logicalImp left' right :=
  Formula.logicalImp_mono hleft (Formula.logicalEntails_refl right)

theorem Formula.logicalImp_monotone_right {Atom : Type u}
    {left right right' : Formula.LogicalEquivalenceClass Atom}
    (hright : right ≤ right') :
    Formula.logicalImp left right ≤ Formula.logicalImp left right' :=
  Formula.logicalImp_mono (Formula.logicalEntails_refl left) hright

theorem derives_imp_and_distributive_iff {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (Formula.iff (.imp p (.and q r))
      (.and (.imp p q) (.imp p r))) := by
  apply derives_iffI
  · apply Derives.impI
    apply Derives.andI
    · apply Derives.impI
      exact Derives.andEL (p := q) (q := r)
        (Derives.impE (Derives.ax (p := .imp p (.and q r)) (by simp))
          (Derives.ax (p := p) (by simp)))
    · apply Derives.impI
      exact Derives.andER (p := q) (q := r)
        (Derives.impE (Derives.ax (p := .imp p (.and q r)) (by simp))
          (Derives.ax (p := p) (by simp)))
  · apply Derives.impI
    apply Derives.impI
    apply Derives.andI
    · exact Derives.impE
        (Derives.andEL (p := .imp p q) (q := .imp p r) (Derives.ax (by simp)))
        (Derives.ax (p := p) (by simp))
    · exact Derives.impE
        (Derives.andER (p := .imp p q) (q := .imp p r) (Derives.ax (by simp)))
        (Derives.ax (p := p) (by simp))

theorem Formula.logicalImp_and {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalImp p (Formula.logicalAnd q r) =
      Formula.logicalAnd (Formula.logicalImp p q) (Formula.logicalImp p r) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  exact Quotient.sound (derives_imp_and_distributive_iff p q r)

theorem derives_or_imp_distributive_iff {Atom : Type u}
    (p q r : Formula Atom) :
    Derives [] (Formula.iff (.imp (.or p q) r)
      (.and (.imp p r) (.imp q r))) := by
  apply derives_iffI
  · apply Derives.impI
    apply Derives.andI
    · apply Derives.impI
      exact Derives.impE (Derives.ax (p := .imp (.or p q) r) (by simp))
        (Derives.orIL (Derives.ax (p := p) (by simp)))
    · apply Derives.impI
      exact Derives.impE (Derives.ax (p := .imp (.or p q) r) (by simp))
        (Derives.orIR (Derives.ax (p := q) (by simp)))
  · apply Derives.impI
    apply Derives.impI
    refine Derives.orE (p := p) (q := q) (r := r)
      (Derives.ax (by simp)) ?_ ?_
    · exact Derives.impE
        (Derives.andEL (p := .imp p r) (q := .imp q r) (Derives.ax (by simp)))
        (Derives.ax (p := p) (by simp))
    · exact Derives.impE
        (Derives.andER (p := .imp p r) (q := .imp q r) (Derives.ax (by simp)))
        (Derives.ax (p := q) (by simp))

theorem Formula.logicalOr_imp {Atom : Type u}
    (p q r : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalImp (Formula.logicalOr p q) r =
      Formula.logicalAnd (Formula.logicalImp p r) (Formula.logicalImp q r) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  exact Quotient.sound (derives_or_imp_distributive_iff p q r)

theorem Formula.logicalAnd_imp_le {Atom : Type u}
    (p q : Formula.LogicalEquivalenceClass Atom) :
    Formula.logicalAnd p (Formula.logicalImp p q) ≤ q := by
  rw [Formula.logicalAnd_comm]
  apply (Formula.logicalAnd_le_iff_le_logicalImp
    (Formula.logicalImp p q) p q).2
  exact Formula.logicalEntails_refl _

theorem Formula.le_logicalImp_and {Atom : Type u}
    (p q : Formula.LogicalEquivalenceClass Atom) :
    p ≤ Formula.logicalImp q (Formula.logicalAnd p q) := by
  apply (Formula.logicalAnd_le_iff_le_logicalImp p q
    (Formula.logicalAnd p q)).1
  exact Formula.logicalEntails_refl _

theorem satisfies_or_and_distributive_iff {Atom : Type u}
    (valuation : Atom → Prop) (p q r : Formula Atom) :
    Satisfies valuation (Formula.iff (.or p (.and q r))
      (.and (.or p q) (.or p r))) :=
  (satisfies_iff valuation _ _).mpr (satisfies_or_and_distributive valuation p q r)

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

/- Every ordinary enumeration yields a recurrent enumeration by scanning finite
   initial segments in successively larger triangular blocks:
   `0; 0,1; 0,1,2; …`.  The state keeps the position and the current block
   length, which avoids assuming any library pairing function. -/
def diagonalState : Nat → Nat × Nat
  | 0 => (0, 0)
  | stage + 1 =>
    let state := diagonalState stage
    if state.1 < state.2 then (state.1 + 1, state.2) else (0, state.2 + 1)

def diagonalIndex (stage : Nat) : Nat := (diagonalState stage).1

def diagonalTriangle : Nat → Nat
  | 0 => 0
  | level + 1 => diagonalTriangle level + (level + 1)

theorem diagonalState_spec : ∀ level : Nat,
    diagonalState (diagonalTriangle level) = (0, level) ∧
      ∀ position, position ≤ level →
        diagonalState (diagonalTriangle level + position) = (position, level) := by
  intro level
  induction level with
  | zero =>
    constructor
    · rfl
    · intro position hposition
      have hzero : position = 0 := Nat.eq_zero_of_le_zero hposition
      subst position
      rfl
  | succ level ih =>
    have hlast : diagonalState (diagonalTriangle level + level) = (level, level) :=
      ih.2 level (Nat.le_refl _)
    have hboundary : diagonalState (diagonalTriangle (level + 1)) = (0, level + 1) := by
      rw [diagonalTriangle]
      change diagonalState ((diagonalTriangle level + level) + 1) = _
      rw [diagonalState]
      simp [hlast]
    constructor
    · exact hboundary
    · intro position hposition
      induction position with
      | zero => simpa using hboundary
      | succ position ihposition =>
        have hprevLe : position ≤ level := Nat.le_of_succ_le_succ hposition
        have hprev := ihposition (Nat.le_trans hprevLe (Nat.le_succ _))
        have hlt : position < level + 1 := Nat.lt_succ_of_le hprevLe
        rw [show diagonalTriangle (level + 1) + (position + 1) =
          (diagonalTriangle (level + 1) + position) + 1 by omega]
        rw [diagonalState]
        simp [hprev, hlt]

theorem diagonalTriangle_ge_self : ∀ level : Nat,
    level ≤ diagonalTriangle level := by
  intro level
  induction level with
  | zero => exact Nat.zero_le _
  | succ level ih =>
    rw [diagonalTriangle]
    omega

noncomputable def FormulaEnumeration.recurrentSchedule {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) : RecurrentFormulaSchedule Atom where
  formulaAt := fun stage => enumeration.enumerate (diagonalIndex stage)
  revisits := by
    intro formula stage
    rcases enumeration.exhaustive formula with ⟨index, hindex⟩
    refine ⟨diagonalTriangle (stage + index + 1) + index, ?_, ?_⟩
    · have htriangle := diagonalTriangle_ge_self (stage + index + 1)
      omega
    · rw [show diagonalIndex (diagonalTriangle (stage + index + 1) + index) = index by
          exact congrArg Prod.fst ((diagonalState_spec (stage + index + 1)).2 index (by omega))]
      exact hindex

/- Schedules are intentionally independent from a particular enumeration.  The
   following operations make that boundary practical: a construction that
   needs to reserve finitely many initial stages can do so without having to
   rebuild the recurrent part of the schedule. -/
theorem RecurrentFormulaSchedule.revisits_strictly_after {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (formula : Formula Atom)
    (stage : Nat) :
    ∃ later, stage < later ∧ schedule.formulaAt later = formula := by
  rcases schedule.revisits formula (stage + 1) with ⟨later, hlater, hformula⟩
  exact ⟨later, Nat.lt_of_succ_le hlater, hformula⟩

noncomputable def RecurrentFormulaSchedule.tail {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (offset : Nat) :
    RecurrentFormulaSchedule Atom where
  formulaAt := fun stage => schedule.formulaAt (offset + stage)
  revisits := by
    intro formula stage
    rcases schedule.revisits formula (offset + stage) with
      ⟨later, hlater, hformula⟩
    refine ⟨later - offset, ?_, ?_⟩
    · apply Nat.le_sub_of_add_le
      simpa [Nat.add_comm] using hlater
    · rw [Nat.add_sub_of_le (Nat.le_trans (Nat.le_add_right _ _) hlater)]
      exact hformula

theorem RecurrentFormulaSchedule.tail_formulaAt {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (offset stage : Nat) :
    (schedule.tail offset).formulaAt stage = schedule.formulaAt (offset + stage) :=
  rfl

/- Insert one prescribed formula before a recurrent tail.  This is useful for
   schedules whose first saturation step must be chosen by hand. -/
noncomputable def RecurrentFormulaSchedule.prepend {Atom : Type u}
    (head : Formula Atom) (schedule : RecurrentFormulaSchedule Atom) :
    RecurrentFormulaSchedule Atom where
  formulaAt := fun
    | 0 => head
    | stage + 1 => schedule.formulaAt stage
  revisits := by
    intro formula stage
    cases stage with
    | zero =>
      rcases schedule.revisits formula 0 with ⟨later, hlater, hformula⟩
      exact ⟨later + 1, Nat.zero_le _, hformula⟩
    | succ stage =>
      rcases schedule.revisits formula stage with ⟨later, hlater, hformula⟩
      exact ⟨later + 1, Nat.succ_le_succ hlater, hformula⟩

theorem RecurrentFormulaSchedule.prepend_zero {Atom : Type u}
    (head : Formula Atom) (schedule : RecurrentFormulaSchedule Atom) :
    (schedule.prepend head).formulaAt 0 = head :=
  rfl

theorem RecurrentFormulaSchedule.prepend_succ {Atom : Type u}
    (head : Formula Atom) (schedule : RecurrentFormulaSchedule Atom) (stage : Nat) :
    (schedule.prepend head).formulaAt (stage + 1) = schedule.formulaAt stage :=
  rfl

/- A finite delay is a repeated `top` prefix.  Its tail is definitionally the
   original schedule, so finite preliminary construction does not change the
   eventual disjunction-saturation behaviour. -/
noncomputable def RecurrentFormulaSchedule.delay {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) : Nat → RecurrentFormulaSchedule Atom
  | 0 => schedule
  | delay + 1 => (schedule.delay delay).prepend .top

theorem RecurrentFormulaSchedule.delay_zero {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) : schedule.delay 0 = schedule :=
  rfl

theorem RecurrentFormulaSchedule.delay_tail {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) :
    ∀ delay stage,
      (schedule.delay delay).formulaAt (delay + stage) = schedule.formulaAt stage := by
  intro delay
  induction delay with
  | zero =>
    intro stage
    simp [RecurrentFormulaSchedule.delay]
  | succ delay ih =>
    intro stage
    change ((schedule.delay delay).prepend .top).formulaAt ((delay + 1) + stage) = _
    rw [show delay + 1 + stage = (delay + stage) + 1 by omega]
    rw [RecurrentFormulaSchedule.prepend_succ]
    exact ih stage

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

/-! Pullback is a strict contravariant action on Kripke models. -/
theorem KripkeModel.pullback_id {Atom : Type u} (model : KripkeModel Atom) :
    KripkeModel.pullback id model = model := by
  rfl

theorem KripkeModel.pullback_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (model : KripkeModel Atom'') :
    KripkeModel.pullback f (KripkeModel.pullback g model) =
      KripkeModel.pullback (g ∘ f) model := by
  rfl

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

theorem kripke_forces_map_id {Atom : Type u} (model : KripkeModel Atom)
    (world : model.World) (formula : Formula Atom) :
    KripkeForces model world (formula.map id) ↔ KripkeForces model world formula := by
  rw [Formula.map_id]

theorem kripke_forces_map_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (model : KripkeModel Atom'') (world : model.World)
    (formula : Formula Atom) :
    KripkeForces model world ((formula.map f).map g) ↔
      KripkeForces (KripkeModel.pullback (g ∘ f) model) world formula := by
  rw [Formula.map_comp]
  exact kripke_forces_map_iff (g ∘ f) model world formula

/- A retraction also reflects forcing.  Thus a faithful change of incidence
   atoms preserves the intuitionistic semantics, including implication's
   quantification over all future worlds. -/
theorem kripke_forces_map_leftInverse {Atom Atom' : Type u} (f : Atom → Atom')
    (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    (model : KripkeModel Atom) (world : model.World) :
    ∀ formula : Formula Atom,
      KripkeForces (KripkeModel.pullback g model) world (formula.map f) ↔
        KripkeForces model world formula := by
  intro formula
  induction formula generalizing world with
  | atom atom =>
    change model.valuation world (g (f atom)) ↔ model.valuation world atom
    rw [hgf atom]
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

theorem kripke_context_forces_map_id {Atom : Type u} (model : KripkeModel Atom)
    (world : model.World) (context : List (Formula Atom)) :
    KripkeContextForces model world (Formula.mapContext id context) ↔
      KripkeContextForces model world context := by
  rw [Formula.mapContext_id]

theorem kripke_context_forces_map_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (model : KripkeModel Atom'') (world : model.World)
    (context : List (Formula Atom)) :
    KripkeContextForces model world (Formula.mapContext g (Formula.mapContext f context)) ↔
      KripkeContextForces (KripkeModel.pullback (g ∘ f) model) world context := by
  rw [Formula.mapContext_comp]
  exact kripke_context_forces_map_iff (g ∘ f) model world context

theorem kripke_context_forces_map_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    (model : KripkeModel Atom) (world : model.World) (context : List (Formula Atom)) :
    KripkeContextForces (KripkeModel.pullback g model) world
        (Formula.mapContext f context) ↔
      KripkeContextForces model world context := by
  constructor
  · intro holds formula hmem
    have hmapped : formula.map f ∈ Formula.mapContext f context :=
      List.mem_map.mpr ⟨formula, hmem, rfl⟩
    exact (kripke_forces_map_leftInverse f g hgf model world formula).mp (holds _ hmapped)
  · intro holds mapped hmem
    rcases List.mem_map.mp hmem with ⟨formula, hformula, rfl⟩
    exact (kripke_forces_map_leftInverse f g hgf model world formula).mpr
      (holds formula hformula)

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

/- Semantic consequence transports covariantly along an incidence/atom map.
   A target model is reindexed to a source model; the preceding two equivalences
   then identify both its assumptions and its conclusion exactly. -/
theorem kripke_entails_map {Atom Atom' : Type u} (f : Atom → Atom')
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hentails : KripkeEntails.{u, v} context formula) :
    KripkeEntails.{u, v} (Formula.mapContext f context) (formula.map f) := by
  intro model world hcontext
  have hpullback : KripkeContextForces (KripkeModel.pullback f model) world context :=
    (kripke_context_forces_map_iff f model world context).mp hcontext
  exact (kripke_forces_map_iff f model world formula).mpr
    (hentails (KripkeModel.pullback f model) world hpullback)

theorem kripke_entails_map_reflect_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    KripkeEntails.{u, v} (Formula.mapContext f context) (formula.map f) →
      KripkeEntails.{u, v} context formula := by
  intro hentails model world holds
  have hmapped : KripkeContextForces (KripkeModel.pullback g model) world
      (Formula.mapContext f context) :=
    (kripke_context_forces_map_leftInverse f g hgf model world context).mpr holds
  exact (kripke_forces_map_leftInverse f g hgf model world formula).mp
    (hentails (KripkeModel.pullback g model) world hmapped)

theorem kripke_entails_map_iff_of_leftInverse {Atom Atom' : Type u}
    (f : Atom → Atom') (g : Atom' → Atom) (hgf : ∀ atom, g (f atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    KripkeEntails.{u, v} (Formula.mapContext f context) (formula.map f) ↔
      KripkeEntails.{u, v} context formula := by
  constructor
  · exact kripke_entails_map_reflect_of_leftInverse f g hgf
  · exact kripke_entails_map f

theorem kripke_entails_map_id {Atom : Type u}
    (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, v} (Formula.mapContext id context) (formula.map id) ↔
      KripkeEntails.{u, v} context formula := by
  rw [Formula.mapContext_id, Formula.map_id]

/-! Mapping a Kripke consequence in two steps is propositionally identical to
   mapping it once by the composite.  Together with the preceding
   split-injective reflection theorem, this gives the functorial transport and
   reflection interface for incidence translations. -/
theorem kripke_entails_map_comp {Atom Atom' Atom'' : Type u} (g : Atom' → Atom'')
    (f : Atom → Atom') (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, v} (Formula.mapContext g (Formula.mapContext f context))
        ((formula.map f).map g) ↔
      KripkeEntails.{u, v} (Formula.mapContext (g ∘ f) context)
        (formula.map (g ∘ f)) := by
  rw [Formula.mapContext_comp, Formula.map_comp]

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

theorem double_neg_elimination_not_derivable {Atom : Type u} (atom : Atom) :
    ¬ Derives ([] : List (Formula Atom))
      (.imp (Formula.neg (Formula.neg (.atom atom))) (.atom atom)) := by
  intro derivation
  let model := delayedAtomKripkeModel Atom atom
  have forces := derives_kripke_sound derivation model false (by
    intro formula hmem
    simp at hmem)
  have doubleNeg : KripkeForces model false
      (Formula.neg (Formula.neg (.atom atom))) := by
    intro world hle negAtom
    exact negAtom true (Or.inr rfl) ⟨rfl, rfl⟩
  have atomAtFalse := forces false (model.le_refl false) doubleNeg
  exact Bool.noConfusion atomAtFalse.left

theorem Formula.logicalBottom_ne_top (Atom : Type u) :
    (Formula.logicalBottom : Formula.LogicalEquivalenceClass Atom) ≠
      Formula.logicalTop := by
  intro equal
  have equivalent : Formula.DerivablyEquivalent (.bot : Formula Atom) .top :=
    Quotient.exact equal
  exact empty_context_consistent Atom
    (Derives.impE (derives_iffER equivalent) Derives.topI)

theorem Formula.logicalExcludedMiddle_ne_top {Atom : Type u} (atom : Atom) :
    Formula.logicalOr
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.atom atom))
        (Formula.logicalNeg
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.atom atom))) ≠
      Formula.logicalTop := by
  intro equal
  have equivalent : Formula.DerivablyEquivalent
      (.or (.atom atom) (Formula.neg (.atom atom))) .top := by
    exact Quotient.exact equal
  exact excluded_middle_not_derivable atom
    (Derives.impE (derives_iffER equivalent) Derives.topI)

theorem Formula.logicalDoubleNeg_not_le_atom {Atom : Type u} (atom : Atom) :
    ¬ Formula.logicalNeg (Formula.logicalNeg
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.atom atom))) ≤
      Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.atom atom) := by
  intro order
  exact double_neg_elimination_not_derivable atom
    ((logicalEntails_mk_iff_derives
      (Formula.neg (Formula.neg (.atom atom))) (.atom atom)).1 order)

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

theorem Formula.logicalDoubleNegExcludedMiddle_eq_top {Atom : Type u} (atom : Atom) :
    Formula.logicalNeg (Formula.logicalNeg
      (Formula.logicalOr
        (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.atom atom))
        (Formula.logicalNeg
          (Quotient.mk (Formula.derivablyEquivalentSetoid Atom) (.atom atom))))) =
      Formula.logicalTop := by
  apply (logicalClass_eq_top_iff_derives
    (Formula.neg (Formula.neg
      (.or (.atom atom) (Formula.neg (.atom atom)))))).2
  exact double_neg_excluded_middle_derivable atom

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

/- A prime theory cannot contain both a formula and its intuitionistic
   negation.  The contrapositive form is useful when a relative Lindenbaum
   extension is used as a canonical counterexample. -/
theorem primeTheory_neg_excludes {Atom : Type u} (theory : PrimeTheory Atom)
    {p : Formula Atom} :
    theory.contains (Formula.neg p) → ¬ theory.contains p := by
  intro hneg hp
  apply theory.consistent
  exact primeTheory_imp_apply theory hneg hp

/- This is the local converse needed in the implication case: a world which
   contains the antecedent but omits the consequent also omits the
   implication. -/
theorem primeTheory_not_imp_of_contains_not_contains {Atom : Type u}
    (theory : PrimeTheory Atom) {p q : Formula Atom}
    (hp : theory.contains p) (hnq : ¬ theory.contains q) :
    ¬ theory.contains (.imp p q) := by
  intro himp
  exact hnq (primeTheory_imp_apply theory himp hp)

/- The finite-base relative construction is conservative for *all* finite
   derivations from its base, not only for the assumptions explicitly listed.
   Thus an underivable implication has a prime-theory counterexample which
   retains every consequence of the starting context. -/
theorem finite_implication_failure_prime_extension_conservative {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom)
    (context : List (Formula Atom)) (premise conclusion : Formula Atom)
    (havoid : DerivationallyAvoids context (.imp premise conclusion)) :
    ∃ theory : PrimeTheory Atom,
      (∀ formula, Derives context formula → theory.contains formula) ∧
        theory.contains premise ∧ ¬ theory.contains conclusion ∧
          ¬ theory.contains (.imp premise conclusion) := by
  rcases finite_implication_failure_prime_extension schedule context premise conclusion havoid with
    ⟨theory, hcontext, hp, hnq⟩
  refine ⟨theory, ?_, hp, hnq,
    primeTheory_not_imp_of_contains_not_contains theory hp hnq⟩
  intro formula hderives
  apply theory.closed (context := context)
  · intro assumption hassumption
    exact hcontext assumption hassumption
  · exact hderives

theorem primeTheoryLe_refl {Atom : Type u} (theory : PrimeTheory Atom) :
    primeTheoryLe theory theory := fun _ h => h

theorem primeTheoryLe_trans {Atom : Type u} {r s t : PrimeTheory Atom} :
    primeTheoryLe r s → primeTheoryLe s t → primeTheoryLe r t := by
  intro hrs hst formula hr
  exact hst formula (hrs formula hr)

/- Every finite part of an arbitrary prime theory can already be retained by
   an implication-failure witness.  This is the finitary compactness half of
   the unrestricted extension problem: the only remaining step is to take a
   coherent limit over all such finite supports. -/
theorem primeTheory_finite_fragment_implication_failure_extension {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (theory : PrimeTheory Atom)
    (support : List (Formula Atom))
    (hsupport : ∀ formula, formula ∈ support → theory.contains formula)
    (premise conclusion : Formula Atom)
    (hnot : ¬ theory.contains (.imp premise conclusion)) :
    ∃ extension : PrimeTheory Atom,
      (∀ formula, formula ∈ support → extension.contains formula) ∧
        extension.contains premise ∧ ¬ extension.contains conclusion := by
  have havoid : DerivationallyAvoids support (.imp premise conclusion) := by
    intro hderives
    apply hnot
    apply theory.closed (context := support)
    · exact hsupport
    · exact hderives
  exact finite_implication_failure_prime_extension
    schedule support premise conclusion havoid

/- The finite-fragment witness preserves the whole finite *deductive
   closure*, not merely the displayed support.  This is the exact compact
   approximation of an arbitrary canonical world that is available without
   assuming that the world itself has a finite presentation. -/
theorem primeTheory_finite_fragment_implication_failure_extension_conservative
    {Atom : Type u} (schedule : RecurrentFormulaSchedule Atom)
    (theory : PrimeTheory Atom) (support : List (Formula Atom))
    (hsupport : ∀ formula, formula ∈ support → theory.contains formula)
    (premise conclusion : Formula Atom)
    (hnot : ¬ theory.contains (.imp premise conclusion)) :
    ∃ extension : PrimeTheory Atom,
      (∀ formula, Derives support formula → extension.contains formula) ∧
        extension.contains premise ∧ ¬ extension.contains conclusion ∧
          ¬ extension.contains (.imp premise conclusion) := by
  have havoid : DerivationallyAvoids support (.imp premise conclusion) := by
    intro hderives
    apply hnot
    apply theory.closed (context := support)
    · exact hsupport
    · exact hderives
  exact finite_implication_failure_prime_extension_conservative
    schedule support premise conclusion havoid

/- In particular, every finite list of facts of an arbitrary prime theory is
   retained by a failure witness together with all consequences of that list.
   The theorem separates the still-missing coherent-limit argument from its
   already formalized finitary compactness content. -/
theorem primeTheory_finite_facts_implication_failure_extension
    {Atom : Type u} (schedule : RecurrentFormulaSchedule Atom)
    (theory : PrimeTheory Atom) (facts : List (Formula Atom))
    (hfacts : ∀ formula, formula ∈ facts → theory.contains formula)
    (premise conclusion : Formula Atom)
    (hnot : ¬ theory.contains (.imp premise conclusion)) :
    ∃ extension : PrimeTheory Atom,
      (∀ formula, Derives facts formula → extension.contains formula) ∧
        extension.contains premise ∧ ¬ extension.contains conclusion := by
  rcases primeTheory_finite_fragment_implication_failure_extension_conservative
    schedule theory facts hfacts premise conclusion hnot with
    ⟨extension, hclosure, hpremise, hnconclusion, _⟩
  exact ⟨extension, hclosure, hpremise, hnconclusion⟩

/- A canonical theory need not in general have a finite presentation.  When
   it does, however, the finite relative Lindenbaum construction already gives
   the *full* extension required by the implication case, rather than merely
   an extension of a selected finite fragment. -/
structure PrimeTheoryFiniteBasis {Atom : Type u} (theory : PrimeTheory Atom) where
  formulas : List (Formula Atom)
  complete : ∀ formula, theory.contains formula ↔ Derives formulas formula

theorem primeTheory_implication_failure_extension_of_finite_basis {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (theory : PrimeTheory Atom)
    (basis : PrimeTheoryFiniteBasis theory) (premise conclusion : Formula Atom)
    (hnot : ¬ theory.contains (.imp premise conclusion)) :
    ∃ extension : PrimeTheory Atom,
      primeTheoryLe theory extension ∧ extension.contains premise ∧
        ¬ extension.contains conclusion := by
  have havoid : DerivationallyAvoids basis.formulas (.imp premise conclusion) := by
    intro hderives
    exact hnot ((basis.complete (.imp premise conclusion)).mpr hderives)
  rcases finite_implication_failure_prime_extension_conservative
    schedule basis.formulas premise conclusion havoid with
    ⟨extension, hpreserves, hpremise, hnconclusion, _⟩
  refine ⟨extension, ?_, hpremise, hnconclusion⟩
  intro formula hformula
  exact hpreserves formula ((basis.complete formula).mp hformula)

/- This packages the preceding theorem in exactly the shape of the canonical
   witness, for the finitely presented sub-class of canonical worlds.  The
   remaining unrestricted theorem is precisely the passage from a general
   prime theory to such a relative saturation. -/
theorem primeTheoryFiniteBasis_extension_witness {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (theory : PrimeTheory Atom)
    (basis : PrimeTheoryFiniteBasis theory) :
    ∀ (premise conclusion : Formula Atom),
      ¬ theory.contains (.imp premise conclusion) →
        ∃ extension : PrimeTheory Atom, primeTheoryLe theory extension ∧
          extension.contains premise ∧ ¬ extension.contains conclusion := by
  intro premise conclusion hnot
  exact primeTheory_implication_failure_extension_of_finite_basis
    schedule theory basis premise conclusion hnot

/- `theoryDerives T Δ φ` means that a derivation uses all of its persistent
   assumptions from `T`, and only finitely many additional assumptions `Δ`.
   Making this finite support explicit is what permits the relative
   Lindenbaum construction to start from an arbitrary (possibly infinite)
   canonical theory. -/
def theoryDerives {Atom : Type u} (theory : PrimeTheory Atom)
    (extra : List (Formula Atom)) (formula : Formula Atom) : Prop :=
  ∃ support : List (Formula Atom),
    (∀ assumption, assumption ∈ support → theory.contains assumption) ∧
      Derives (extra ++ support) formula

def theoryAvoids {Atom : Type u} (theory : PrimeTheory Atom)
    (extra : List (Formula Atom)) (forbidden : Formula Atom) : Prop :=
  ¬ theoryDerives theory extra forbidden

theorem theoryDerives_extra_mono {Atom : Type u} (theory : PrimeTheory Atom)
    {source target : List (Formula Atom)} {formula : Formula Atom}
    (hsubset : ContextSubset source target) :
    theoryDerives theory source formula → theoryDerives theory target formula := by
  rintro ⟨support, hsupport, hderives⟩
  refine ⟨support, hsupport, ?_⟩
  apply derives_weaken
  · intro assumption hassumption
    rcases List.mem_append.mp hassumption with hsource | hsupportMem
    · exact List.mem_append.mpr (Or.inl (hsubset assumption hsource))
    · exact List.mem_append.mpr (Or.inr hsupportMem)
  · exact hderives

theorem theoryDerives_finite_support {Atom : Type u} (theory : PrimeTheory Atom)
    (extra context : List (Formula Atom))
    (hcontains : ∀ assumption, assumption ∈ context →
      theoryDerives theory extra assumption) :
    ∃ support : List (Formula Atom),
      (∀ assumption, assumption ∈ support → theory.contains assumption) ∧
        ∀ assumption, assumption ∈ context → Derives (extra ++ support) assumption := by
  induction context with
  | nil =>
    refine ⟨[], ?_, ?_⟩
    · intro assumption hmem
      simp at hmem
    · intro assumption hmem
      simp at hmem
  | cons head tail ih =>
    rcases hcontains head (by simp) with ⟨headSupport, hheadSupport, hhead⟩
    rcases ih (by
      intro assumption hassumption
      exact hcontains assumption (List.mem_cons_of_mem _ hassumption))
      with ⟨tailSupport, htailSupport, htail⟩
    refine ⟨headSupport ++ tailSupport, ?_, ?_⟩
    · intro assumption hassumption
      rcases List.mem_append.mp hassumption with hhead | htail
      · exact hheadSupport assumption hhead
      · exact htailSupport assumption htail
    · intro assumption hassumption
      rcases List.mem_cons.mp hassumption with rfl | htailMem
      · apply derives_weaken (source := extra ++ headSupport)
        · intro member hmember
          rcases List.mem_append.mp hmember with hextra | hhead
          · exact List.mem_append.mpr (Or.inl hextra)
          · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hhead)))
        · exact hhead
      · apply derives_weaken (source := extra ++ tailSupport)
        · intro member hmember
          rcases List.mem_append.mp hmember with hextra | htail'
          · exact List.mem_append.mpr (Or.inl hextra)
          · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr htail')))
        · exact htail assumption htailMem

theorem theoryDerives_closed {Atom : Type u} (theory : PrimeTheory Atom)
    {extra context : List (Formula Atom)} {formula : Formula Atom}
    (hcontains : ∀ assumption, assumption ∈ context →
      theoryDerives theory extra assumption)
    (hderives : Derives context formula) : theoryDerives theory extra formula := by
  rcases theoryDerives_finite_support theory extra context hcontains with
    ⟨support, hsupport, hderivesSupport⟩
  refine ⟨support, hsupport, ?_⟩
  exact derives_substitute hderivesSupport hderives

theorem theoryAvoids_imp_extension {Atom : Type u} (theory : PrimeTheory Atom)
    {premise conclusion : Formula Atom}
    (hnot : ¬ theory.contains (.imp premise conclusion)) :
    theoryAvoids theory [premise] conclusion := by
  rintro ⟨support, hsupport, hderives⟩
  apply hnot
  apply theory.closed (context := support)
  · exact hsupport
  · exact Derives.impI hderives

theorem theoryDerives_or_elim {Atom : Type u} (theory : PrimeTheory Atom)
    (current : List (Formula Atom)) (left right forbidden : Formula Atom)
    (hor : theoryDerives theory current (.or left right))
    (hleft : theoryDerives theory (left :: current) forbidden)
    (hright : theoryDerives theory (right :: current) forbidden) :
    theoryDerives theory current forbidden := by
  rcases hor with ⟨orSupport, horSupport, hor⟩
  rcases hleft with ⟨leftSupport, hleftSupport, hleft⟩
  rcases hright with ⟨rightSupport, hrightSupport, hright⟩
  let support := orSupport ++ leftSupport ++ rightSupport
  have hsupport : ∀ assumption, assumption ∈ support → theory.contains assumption := by
    intro assumption hassumption
    rcases List.mem_append.mp hassumption with hfirst | hrightMem
    · rcases List.mem_append.mp hfirst with horMem | hleftMem
      · exact horSupport assumption horMem
      · exact hleftSupport assumption hleftMem
    · exact hrightSupport assumption hrightMem
  refine ⟨support, hsupport, ?_⟩
  apply Derives.orE (p := left) (q := right)
  · apply derives_weaken (source := current ++ orSupport)
    · intro assumption hassumption
      rcases List.mem_append.mp hassumption with hcurrent | horMem
      · exact List.mem_append.mpr (Or.inl hcurrent)
      · exact List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl horMem)))))
    · exact hor
  · apply derives_weaken (source := (left :: current) ++ leftSupport)
    · intro assumption hassumption
      rcases List.mem_append.mp hassumption with hleftCurrent | hleftMem
      · rcases List.mem_cons.mp hleftCurrent with rfl | hcurrent
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hcurrent))
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hleftMem))))))
    · exact hleft
  · apply derives_weaken (source := (right :: current) ++ rightSupport)
    · intro assumption hassumption
      rcases List.mem_append.mp hassumption with hrightCurrent | hrightMem
      · rcases List.mem_cons.mp hrightCurrent with rfl | hcurrent
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hcurrent))
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inr hrightMem))))
    · exact hright

theorem theoryAvoids_or_extension_left_or_right {Atom : Type u}
    (theory : PrimeTheory Atom) (current : List (Formula Atom))
    (left right forbidden : Formula Atom)
    (havoid : theoryAvoids theory current forbidden)
    (hor : theoryDerives theory current (.or left right)) :
    theoryAvoids theory (left :: current) forbidden ∨
      theoryAvoids theory (right :: current) forbidden := by
  by_cases hleft : theoryAvoids theory (left :: current) forbidden
  · exact Or.inl hleft
  · right
    intro hright
    apply havoid
    apply theoryDerives_or_elim theory current left right forbidden hor
    · exact Classical.byContradiction hleft
    · exact hright

noncomputable def theoryAvoidanceStep {Atom : Type u} (theory : PrimeTheory Atom)
    (forbidden : Formula Atom) (current : List (Formula Atom)) :
    Formula Atom → List (Formula Atom)
  | .or left right => by
    classical
    exact if hor : theoryDerives theory current (.or left right)
      then if hleft : theoryAvoids theory (left :: current) forbidden
        then left :: current
        else right :: current
      else current
  | _ => current

noncomputable def theoryAvoidanceChain {Atom : Type u}
    (theory : PrimeTheory Atom) (schedule : RecurrentFormulaSchedule Atom)
    (forbidden : Formula Atom) (base : List (Formula Atom)) : Nat → List (Formula Atom)
  | 0 => base
  | n + 1 => theoryAvoidanceStep theory forbidden
      (theoryAvoidanceChain theory schedule forbidden base n) (schedule.formulaAt n)

theorem theoryAvoidanceStep_subset {Atom : Type u} (theory : PrimeTheory Atom)
    (forbidden : Formula Atom) (current : List (Formula Atom)) (candidate : Formula Atom) :
    ContextSubset current (theoryAvoidanceStep theory forbidden current candidate) := by
  cases candidate with
  | atom => exact fun _ h => h
  | top => exact fun _ h => h
  | bot => exact fun _ h => h
  | and left right => exact fun _ h => h
  | imp left right => exact fun _ h => h
  | or left right =>
    simp only [theoryAvoidanceStep]
    split
    · split <;> exact fun _ h => List.mem_cons_of_mem _ h
    · exact fun _ h => h

theorem theoryAvoidanceStep_avoids {Atom : Type u} (theory : PrimeTheory Atom)
    (forbidden : Formula Atom) (current : List (Formula Atom)) (candidate : Formula Atom)
    (hcurrent : theoryAvoids theory current forbidden) :
    theoryAvoids theory (theoryAvoidanceStep theory forbidden current candidate) forbidden := by
  cases candidate with
  | atom => exact hcurrent
  | top => exact hcurrent
  | bot => exact hcurrent
  | and left right => exact hcurrent
  | imp left right => exact hcurrent
  | or left right =>
    simp only [theoryAvoidanceStep]
    split
    · rename_i hor
      split
      · assumption
      · rename_i hnotleft
        rcases theoryAvoids_or_extension_left_or_right theory current left right forbidden
          hcurrent hor with hleft | hright
        · exact False.elim (hnotleft hleft)
        · exact hright
    · exact hcurrent

theorem theoryAvoidanceChain_subset_succ {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (n : Nat) :
    ContextSubset (theoryAvoidanceChain theory schedule forbidden base n)
      (theoryAvoidanceChain theory schedule forbidden base (n + 1)) := by
  change ContextSubset _ (theoryAvoidanceStep theory forbidden _ (schedule.formulaAt n))
  exact theoryAvoidanceStep_subset theory forbidden _ _

theorem theoryAvoidanceChain_avoids {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (hbase : theoryAvoids theory base forbidden) :
    ∀ n, theoryAvoids theory (theoryAvoidanceChain theory schedule forbidden base n) forbidden := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    change theoryAvoids theory (theoryAvoidanceStep theory forbidden
      (theoryAvoidanceChain theory schedule forbidden base n) (schedule.formulaAt n)) forbidden
    exact theoryAvoidanceStep_avoids theory forbidden _ _ ih

theorem theoryAvoidanceChain_subset_of_le {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {source target : Nat} : source ≤ target →
      ContextSubset (theoryAvoidanceChain theory schedule forbidden base source)
        (theoryAvoidanceChain theory schedule forbidden base target) := by
  intro hle
  induction target generalizing source with
  | zero =>
    have hzero : source = 0 := Nat.eq_zero_of_le_zero hle
    subst source
    exact fun _ h => h
  | succ target ih =>
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · intro formula hmem
      exact theoryAvoidanceChain_subset_succ theory schedule forbidden base target formula
        (ih (Nat.le_of_lt_succ hlt) formula hmem)
    · exact fun _ h => h

theorem theoryAvoidanceChain_derives_mono {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {source target : Nat} (hle : source ≤ target)
    {formula : Formula Atom} :
    theoryDerives theory (theoryAvoidanceChain theory schedule forbidden base source) formula →
      theoryDerives theory (theoryAvoidanceChain theory schedule forbidden base target) formula :=
  theoryDerives_extra_mono theory
    (theoryAvoidanceChain_subset_of_le theory schedule forbidden base hle)

def theoryAvoidanceLimitDerives {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (formula : Formula Atom) : Prop :=
  ∃ stage, theoryDerives theory (theoryAvoidanceChain theory schedule forbidden base stage) formula

theorem theoryAvoidanceLimitDerives_from_extra {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {formula : Formula Atom} :
    formula ∈ base → theoryAvoidanceLimitDerives theory schedule forbidden base formula := by
  intro hmem
  refine ⟨0, [], ?_, ?_⟩
  · intro assumption hassumption
    simp at hassumption
  · simpa [theoryAvoidanceChain] using (Derives.ax hmem : Derives base formula)

theorem theoryAvoidanceLimitDerives_contains_theory {Atom : Type u}
    (theory : PrimeTheory Atom) (schedule : RecurrentFormulaSchedule Atom)
    (forbidden : Formula Atom) (base : List (Formula Atom)) {formula : Formula Atom} :
    theory.contains formula → theoryAvoidanceLimitDerives theory schedule forbidden base formula := by
  intro hformula
  refine ⟨0, [formula], ?_, ?_⟩
  · intro assumption hassumption
    have h : assumption = formula := by simpa using hassumption
    subst assumption
    exact hformula
  · change Derives (base ++ [formula]) formula
    exact Derives.ax (List.mem_append.mpr (Or.inr (by simp)))

theorem theoryDerives_of_mem_extra {Atom : Type u} (theory : PrimeTheory Atom)
    (extra : List (Formula Atom)) {formula : Formula Atom} :
    formula ∈ extra → theoryDerives theory extra formula := by
  intro hmem
  refine ⟨[], ?_, ?_⟩
  · intro assumption hassumption
    simp at hassumption
  · simpa using (Derives.ax hmem : Derives extra formula)

theorem theoryAvoidance_finite_context_bound {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) :
    ∀ context : List (Formula Atom),
      (∀ assumption, assumption ∈ context →
        theoryAvoidanceLimitDerives theory schedule forbidden base assumption) →
        ∃ stage, ∀ assumption, assumption ∈ context →
          theoryDerives theory (theoryAvoidanceChain theory schedule forbidden base stage) assumption := by
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
    rcases List.mem_cons.mp hassumption with rfl | htailMem
    · exact theoryAvoidanceChain_derives_mono theory schedule forbidden base
        (Nat.le_max_left _ _) hhead
    · exact theoryAvoidanceChain_derives_mono theory schedule forbidden base
        (Nat.le_max_right _ _) (htail assumption htailMem)

theorem theoryAvoidanceLimitDerives_closed {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) : ∀ {context formula},
      (∀ assumption, assumption ∈ context →
        theoryAvoidanceLimitDerives theory schedule forbidden base assumption) →
      Derives context formula →
        theoryAvoidanceLimitDerives theory schedule forbidden base formula := by
  intro context formula hcontains hderives
  rcases theoryAvoidance_finite_context_bound theory schedule forbidden base context hcontains with
    ⟨stage, hstage⟩
  exact ⟨stage, theoryDerives_closed theory hstage hderives⟩

theorem theoryAvoidanceLimitDerives_avoids {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (hbase : theoryAvoids theory base forbidden) :
    ¬ theoryAvoidanceLimitDerives theory schedule forbidden base forbidden := by
  rintro ⟨stage, hforbidden⟩
  exact theoryAvoidanceChain_avoids theory schedule forbidden base hbase stage hforbidden

theorem theoryAvoidanceChain_or_choice {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (stage : Nat) (p q : Formula Atom)
    (hscheduled : schedule.formulaAt stage = .or p q)
    (hor : theoryDerives theory (theoryAvoidanceChain theory schedule forbidden base stage) (.or p q)) :
    p ∈ theoryAvoidanceChain theory schedule forbidden base (stage + 1) ∨
      q ∈ theoryAvoidanceChain theory schedule forbidden base (stage + 1) := by
  change p ∈ theoryAvoidanceStep theory forbidden
      (theoryAvoidanceChain theory schedule forbidden base stage) (schedule.formulaAt stage) ∨
        q ∈ theoryAvoidanceStep theory forbidden
          (theoryAvoidanceChain theory schedule forbidden base stage) (schedule.formulaAt stage)
  rw [hscheduled]
  simp only [theoryAvoidanceStep]
  split
  · split
    · exact Or.inl List.mem_cons_self
    · exact Or.inr List.mem_cons_self
  · rename_i hnot
    exact False.elim (hnot hor)

theorem theoryAvoidanceLimitDerives_prime {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) {p q : Formula Atom} :
    theoryAvoidanceLimitDerives theory schedule forbidden base (.or p q) →
      theoryAvoidanceLimitDerives theory schedule forbidden base p ∨
        theoryAvoidanceLimitDerives theory schedule forbidden base q := by
  rintro ⟨stage, hor⟩
  rcases schedule.revisits (.or p q) stage with ⟨later, hle, hscheduled⟩
  have horLater : theoryDerives theory
      (theoryAvoidanceChain theory schedule forbidden base later) (.or p q) :=
    theoryAvoidanceChain_derives_mono theory schedule forbidden base hle hor
  rcases theoryAvoidanceChain_or_choice theory schedule forbidden base later p q
    hscheduled horLater with hp | hq
  · exact Or.inl ⟨later + 1,
      theoryDerives_of_mem_extra theory _ hp⟩
  · exact Or.inr ⟨later + 1,
      theoryDerives_of_mem_extra theory _ hq⟩

theorem theoryAvoidanceLimitDerives_consistent {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (hbase : theoryAvoids theory base forbidden) :
    ¬ theoryAvoidanceLimitDerives theory schedule forbidden base .bot := by
  rintro ⟨stage, hbot⟩
  apply theoryAvoidanceLimitDerives_avoids theory schedule forbidden base hbase
  exact ⟨stage, match hbot with
    | ⟨support, hsupport, derives⟩ => ⟨support, hsupport, Derives.botE derives⟩⟩

def theoryAvoidanceLimitPrimeTheory {Atom : Type u} (theory : PrimeTheory Atom)
    (schedule : RecurrentFormulaSchedule Atom) (forbidden : Formula Atom)
    (base : List (Formula Atom)) (hbase : theoryAvoids theory base forbidden) :
    PrimeTheory Atom where
  contains := theoryAvoidanceLimitDerives theory schedule forbidden base
  closed := theoryAvoidanceLimitDerives_closed theory schedule forbidden base
  consistent := theoryAvoidanceLimitDerives_consistent theory schedule forbidden base hbase
  prime := fun hor => theoryAvoidanceLimitDerives_prime theory schedule forbidden base hor

/- The relative prime-extension theorem, now with an arbitrary prime source
   rather than a finite presentation. -/
theorem arbitrary_prime_implication_failure_extension {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (theory : PrimeTheory Atom)
    (premise conclusion : Formula Atom)
    (hnot : ¬ theory.contains (.imp premise conclusion)) :
    ∃ extension : PrimeTheory Atom,
      primeTheoryLe theory extension ∧ extension.contains premise ∧
        ¬ extension.contains conclusion := by
  let base : List (Formula Atom) := [premise]
  have hbase : theoryAvoids theory base conclusion := by
    simpa [base] using theoryAvoids_imp_extension theory hnot
  let extension := theoryAvoidanceLimitPrimeTheory theory schedule conclusion base hbase
  refine ⟨extension, ?_, ?_, ?_⟩
  · intro formula hformula
    exact theoryAvoidanceLimitDerives_contains_theory theory schedule conclusion base hformula
  · exact theoryAvoidanceLimitDerives_from_extra theory schedule conclusion base (by simp [base])
  · exact theoryAvoidanceLimitDerives_avoids theory schedule conclusion base hbase

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

/- The finite-support relative chain above discharges the formerly
   conditional Lindenbaum obligation. -/
def primeExtensionWitnessOfSchedule {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) : PrimeExtensionWitness Atom where
  extend_imp_failure := fun theory premise conclusion hnot =>
    arbitrary_prime_implication_failure_extension schedule theory premise conclusion hnot

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

/- Semantic entailment in the canonical model is useful independently of the
   universe-polymorphic notion `KripkeEntails`: it exposes exactly which
   Lindenbaum principle is used by the converse direction below. -/
def CanonicalKripkeEntails {Atom : Type u} (context : List (Formula Atom))
    (formula : Formula Atom) : Prop :=
  ∀ theory : PrimeTheory Atom,
    KripkeContextForces (canonicalKripkeModel Atom) theory context →
      KripkeForces (canonicalKripkeModel Atom) theory formula

theorem derives_canonical_kripke_entails {Atom : Type u}
    {context : List (Formula Atom)} {formula : Formula Atom}
    (derivation : Derives context formula) :
    CanonicalKripkeEntails context formula :=
  fun theory holds => derives_kripke_sound derivation
    (canonicalKripkeModel Atom) theory holds

/- Once implication failures extend to prime theories, the relative avoidance
   construction supplies a canonical counterworld for every underivable
   finite sequent.  This is the canonical-model completeness direction; the
   witness parameter makes its sole remaining non-finitary requirement
   explicit rather than postulating it. -/
theorem canonical_kripke_entails_complete {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (witness : PrimeExtensionWitness Atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    CanonicalKripkeEntails context formula → Derives context formula := by
  intro hentails
  apply Classical.byContradiction
  intro hnot
  rcases relative_prime_extension schedule formula context hnot with
    ⟨theory, hcontext, hformula⟩
  have hforcesContext :
      KripkeContextForces (canonicalKripkeModel Atom) theory context := by
    intro assumption hassumption
    exact (canonical_truth_lemma witness theory assumption).mpr
      (hcontext assumption hassumption)
  have hforcesFormula :
      KripkeForces (canonicalKripkeModel Atom) theory formula :=
    hentails theory hforcesContext
  exact hformula ((canonical_truth_lemma witness theory formula).mp hforcesFormula)

theorem canonical_kripke_entails_iff_derives {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (witness : PrimeExtensionWitness Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    CanonicalKripkeEntails context formula ↔ Derives context formula := by
  constructor
  · exact canonical_kripke_entails_complete schedule witness
  · exact derives_canonical_kripke_entails

/- Conditional full Kripke completeness follows immediately, since the
   canonical prime-theory model is one of the Kripke models quantified by
   `KripkeEntails`.  Soundness itself remains unconditional. -/
theorem kripke_entails_complete_of_prime_extension {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (witness : PrimeExtensionWitness Atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    KripkeEntails.{u, u} context formula → Derives context formula := by
  intro hentails
  apply canonical_kripke_entails_complete schedule witness
  intro theory hcontext
  exact hentails (canonicalKripkeModel Atom) theory hcontext

theorem kripke_entails_iff_derives_of_prime_extension {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (witness : PrimeExtensionWitness Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula := by
  constructor
  · exact kripke_entails_complete_of_prime_extension schedule witness
  · exact derives_kripke_entails

/- The canonical truth lemma and both completeness statements no longer need
   an externally supplied extension postulate: recurrence of the formula schedule
   is the only enumeration data used by the construction. -/
theorem canonical_truth_lemma_of_schedule {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom) (theory : PrimeTheory Atom) :
    ∀ formula : Formula Atom,
      KripkeForces (canonicalKripkeModel Atom) theory formula ↔ theory.contains formula :=
  canonical_truth_lemma (primeExtensionWitnessOfSchedule schedule) theory

theorem canonical_kripke_entails_complete_of_schedule {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    CanonicalKripkeEntails context formula → Derives context formula :=
  canonical_kripke_entails_complete schedule (primeExtensionWitnessOfSchedule schedule)

theorem canonical_kripke_entails_iff_derives_of_schedule {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    CanonicalKripkeEntails context formula ↔ Derives context formula :=
  canonical_kripke_entails_iff_derives schedule (primeExtensionWitnessOfSchedule schedule)
    context formula

theorem kripke_entails_complete_of_schedule {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    KripkeEntails.{u, u} context formula → Derives context formula :=
  kripke_entails_complete_of_prime_extension schedule (primeExtensionWitnessOfSchedule schedule)

theorem kripke_entails_iff_derives_of_schedule {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_prime_extension schedule
    (primeExtensionWitnessOfSchedule schedule) context formula

/- An ordinary exhaustive enumeration is therefore sufficient for the full
   canonical argument: `recurrentSchedule` is a concrete recurrence witness,
   rather than a second infinitary hypothesis supplied by a client. -/
theorem canonical_truth_lemma_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom) (theory : PrimeTheory Atom) :
    ∀ formula : Formula Atom,
      KripkeForces (canonicalKripkeModel Atom) theory formula ↔ theory.contains formula :=
  canonical_truth_lemma_of_schedule enumeration.recurrentSchedule theory

theorem canonical_kripke_entails_complete_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    CanonicalKripkeEntails context formula → Derives context formula :=
  canonical_kripke_entails_complete_of_schedule enumeration.recurrentSchedule

theorem canonical_kripke_entails_iff_derives_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    CanonicalKripkeEntails context formula ↔ Derives context formula :=
  canonical_kripke_entails_iff_derives_of_schedule enumeration.recurrentSchedule context formula

theorem kripke_entails_complete_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    {context : List (Formula Atom)} {formula : Formula Atom} :
    KripkeEntails.{u, u} context formula → Derives context formula :=
  kripke_entails_complete_of_schedule enumeration.recurrentSchedule

theorem kripke_entails_iff_derives_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_schedule enumeration.recurrentSchedule context formula

/-! The completeness proof has a constructive-looking contraposed form that
   is often more useful to clients: an underivable finite sequent has a named
   world in the canonical prime-theory model which forces every assumption and
   refutes the conclusion. -/
theorem canonical_countermodel_of_not_derives_of_schedule {Atom : Type u}
    (schedule : RecurrentFormulaSchedule Atom)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory Atom,
      KripkeContextForces (canonicalKripkeModel Atom) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel Atom) theory formula := by
  rcases relative_prime_extension schedule formula context hnot with
    ⟨theory, hcontext, hnotcontains⟩
  refine ⟨theory, ?_, ?_⟩
  · intro assumption hassumption
    exact (canonical_truth_lemma_of_schedule schedule theory assumption).mpr
      (hcontext assumption hassumption)
  · intro hforces
    exact hnotcontains
      ((canonical_truth_lemma_of_schedule schedule theory formula).mp hforces)

theorem canonical_countermodel_of_not_derives_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory Atom,
      KripkeContextForces (canonicalKripkeModel Atom) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel Atom) theory formula :=
  canonical_countermodel_of_not_derives_of_schedule enumeration.recurrentSchedule hnot

theorem not_canonical_kripke_entails_of_not_derives_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hnot : ¬ Derives context formula) :
    ¬ CanonicalKripkeEntails context formula := by
  rintro hentails
  rcases canonical_countermodel_of_not_derives_of_enumeration enumeration hnot with
    ⟨theory, hcontext, hnotforces⟩
  exact hnotforces (hentails theory hcontext)

theorem not_kripke_entails_of_not_derives_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hnot : ¬ Derives context formula) :
    ¬ KripkeEntails.{u, u} context formula := by
  intro hentails
  exact hnot ((kripke_entails_iff_derives_of_enumeration enumeration context formula).mp hentails)

theorem not_derives_iff_has_kripke_countermodel_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    ¬ Derives context formula ↔
      ∃ model : KripkeModel.{u, u} Atom,
        ∃ world : model.World,
          KripkeContextForces model world context ∧
            ¬ KripkeForces model world formula := by
  constructor
  · intro hnot
    obtain ⟨theory, hcontext, hformula⟩ :=
      canonical_countermodel_of_not_derives_of_enumeration enumeration hnot
    exact ⟨canonicalKripkeModel Atom, theory, hcontext, hformula⟩
  · rintro ⟨model, world, hcontext, hnotformula⟩ derives
    have entails : KripkeEntails.{u, u} context formula :=
      derives_kripke_entails derives
    exact hnotformula (entails model world hcontext)

theorem derives_iff_no_kripke_countermodel_of_enumeration {Atom : Type u}
    (enumeration : FormulaEnumeration Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    Derives context formula ↔
      ¬ (∃ model : KripkeModel.{u, u} Atom,
        ∃ world : model.World,
          KripkeContextForces model world context ∧
            ¬ KripkeForces model world formula) := by
  constructor
  · intro derives
    rintro ⟨model, world, hcontext, hnotformula⟩
    exact hnotformula ((derives_kripke_entails derives) model world hcontext)
  · intro noCountermodel
    apply Classical.byContradiction
    intro hnot
    exact noCountermodel
      ((not_derives_iff_has_kripke_countermodel_of_enumeration
        enumeration context formula).mp hnot)

def KripkeSatisfiable {Atom : Type u} (context : List (Formula Atom)) : Prop :=
  ∃ model : KripkeModel.{u, u} Atom,
    ∃ world : model.World, KripkeContextForces model world context

theorem derivationallyConsistent_iff_kripkeSatisfiable_of_enumeration
    {Atom : Type u} (enumeration : FormulaEnumeration Atom)
    (context : List (Formula Atom)) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context := by
  constructor
  · intro consistent
    obtain ⟨model, world, holds, notBot⟩ :=
      (not_derives_iff_has_kripke_countermodel_of_enumeration
        enumeration context Formula.bot).mp consistent
    exact ⟨model, world, holds⟩
  · rintro ⟨model, world, holds⟩
    exact kripke_satisfiable_consistent holds

theorem derivationallyConsistent_iff_has_canonical_world_of_enumeration
    {Atom : Type u} (enumeration : FormulaEnumeration Atom)
    (context : List (Formula Atom)) :
    DerivationallyConsistent context ↔
      ∃ theory : PrimeTheory Atom,
        KripkeContextForces (canonicalKripkeModel Atom) theory context := by
  constructor
  · intro consistent
    obtain ⟨theory, holds, notBot⟩ :=
      canonical_countermodel_of_not_derives_of_enumeration
        enumeration consistent
    exact ⟨theory, holds⟩
  · rintro ⟨theory, holds⟩
    exact kripke_satisfiable_consistent holds

/- Incidence-specialized notation for clients of the core structure. -/
abbrev IncidenceFormula (I : Type u) := Formula I

/-! ## A concrete enumeration for two incidence atoms

The completeness theorem above deliberately takes an enumeration as an
explicit hypothesis, because arbitrary incidence types need not be countable.
For the smallest genuinely nontrivial incidence language, however, that input
can be constructed in the library.  The following decoder uses the triangular
scan already used by `recurrentSchedule` as a surjection from natural numbers
onto pairs of natural numbers.  Formula constructors are tagged modulo seven;
the recursive calls are made only on a strictly smaller code. -/

theorem diagonalState_first_le_second : ∀ stage : Nat,
    (diagonalState stage).1 ≤ (diagonalState stage).2 := by
  intro stage
  induction stage with
  | zero => exact Nat.le_refl _
  | succ stage ih =>
    simp only [diagonalState]
    split <;> omega

theorem diagonalState_second_le_stage : ∀ stage : Nat,
    (diagonalState stage).2 ≤ stage := by
  intro stage
  induction stage with
  | zero => exact Nat.le_refl _
  | succ stage ih =>
    simp only [diagonalState]
    split <;> omega

def diagonalRemainder (stage : Nat) : Nat :=
  (diagonalState stage).2 - (diagonalState stage).1

theorem diagonalIndex_le_stage (stage : Nat) : diagonalIndex stage ≤ stage :=
  Nat.le_trans (diagonalState_first_le_second stage)
    (diagonalState_second_le_stage stage)

theorem diagonalRemainder_le_stage (stage : Nat) : diagonalRemainder stage ≤ stage :=
  Nat.le_trans (Nat.sub_le _ _) (diagonalState_second_le_stage stage)

def diagonalPair (left right : Nat) : Nat :=
  diagonalTriangle (left + right) + left

theorem diagonalIndex_pair (left right : Nat) :
    diagonalIndex (diagonalPair left right) = left := by
  unfold diagonalIndex diagonalPair
  exact congrArg Prod.fst ((diagonalState_spec (left + right)).2 left (by omega))

theorem diagonalRemainder_pair (left right : Nat) :
    diagonalRemainder (diagonalPair left right) = right := by
  unfold diagonalRemainder diagonalPair
  rw [((diagonalState_spec (left + right)).2 left (by omega))]
  omega

/-! A countable supply of atoms gives a countable supply of formulas.  We use
   an explicit retraction rather than a type-class countability assumption, so
   this construction is also convenient for finite atom types. -/

noncomputable def formulaDecodeOfAtomCoding {Atom : Type u}
    (decodeAtom : Nat → Atom) : Nat → Formula Atom
  | 0 => .atom (decodeAtom 0)
  | code + 1 =>
    let payload := code / 6
    match code % 6 with
    | 0 => .atom (decodeAtom payload)
    | 1 => .top
    | 2 => .bot
    | 3 => .and (formulaDecodeOfAtomCoding decodeAtom (diagonalIndex payload))
        (formulaDecodeOfAtomCoding decodeAtom (diagonalRemainder payload))
    | 4 => .or (formulaDecodeOfAtomCoding decodeAtom (diagonalIndex payload))
        (formulaDecodeOfAtomCoding decodeAtom (diagonalRemainder payload))
    | _ => .imp (formulaDecodeOfAtomCoding decodeAtom (diagonalIndex payload))
        (formulaDecodeOfAtomCoding decodeAtom (diagonalRemainder payload))
termination_by code => code

decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    apply Nat.le_trans
    · first | exact diagonalIndex_le_stage _ | exact diagonalRemainder_le_stage _
    · exact Nat.div_le_self _ _

noncomputable def formulaCodeOfAtomCoding {Atom : Type u}
    (codeAtom : Atom → Nat) : Formula Atom → Nat
  | .atom atom => 6 * codeAtom atom + 1
  | .top => 2
  | .bot => 3
  | .and p q => 6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
      (formulaCodeOfAtomCoding codeAtom q) + 4
  | .or p q => 6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
      (formulaCodeOfAtomCoding codeAtom q) + 5
  | .imp p q => 6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
      (formulaCodeOfAtomCoding codeAtom q) + 6

theorem formulaDecodeOfAtomCoding_code {Atom : Type u}
    (decodeAtom : Nat → Atom) (codeAtom : Atom → Nat)
    (hcode : ∀ atom, decodeAtom (codeAtom atom) = atom) :
    ∀ formula : Formula Atom,
      formulaDecodeOfAtomCoding decodeAtom (formulaCodeOfAtomCoding codeAtom formula) = formula := by
  intro formula
  induction formula with
  | atom atom =>
    simp only [formulaCodeOfAtomCoding, formulaDecodeOfAtomCoding]
    rw [show (6 * codeAtom atom) / 6 = codeAtom atom by omega]
    rw [show (6 * codeAtom atom) % 6 = 0 by omega]
    simpa using congrArg Formula.atom (hcode atom)
  | top => simp [formulaCodeOfAtomCoding, formulaDecodeOfAtomCoding]
  | bot => simp [formulaCodeOfAtomCoding, formulaDecodeOfAtomCoding]
  | and p q ihp ihq =>
    simp only [formulaCodeOfAtomCoding, formulaDecodeOfAtomCoding]
    rw [show (6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
        (formulaCodeOfAtomCoding codeAtom q) + 3) / 6 =
        diagonalPair (formulaCodeOfAtomCoding codeAtom p) (formulaCodeOfAtomCoding codeAtom q) by omega]
    rw [show (6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
        (formulaCodeOfAtomCoding codeAtom q) + 3) % 6 = 3 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]
  | or p q ihp ihq =>
    simp only [formulaCodeOfAtomCoding, formulaDecodeOfAtomCoding]
    rw [show (6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
        (formulaCodeOfAtomCoding codeAtom q) + 4) / 6 =
        diagonalPair (formulaCodeOfAtomCoding codeAtom p) (formulaCodeOfAtomCoding codeAtom q) by omega]
    rw [show (6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
        (formulaCodeOfAtomCoding codeAtom q) + 4) % 6 = 4 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]
  | imp p q ihp ihq =>
    simp only [formulaCodeOfAtomCoding, formulaDecodeOfAtomCoding]
    rw [show (6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
        (formulaCodeOfAtomCoding codeAtom q) + 5) / 6 =
        diagonalPair (formulaCodeOfAtomCoding codeAtom p) (formulaCodeOfAtomCoding codeAtom q) by omega]
    rw [show (6 * diagonalPair (formulaCodeOfAtomCoding codeAtom p)
        (formulaCodeOfAtomCoding codeAtom q) + 5) % 6 = 5 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]

noncomputable def formulaEnumerationOfAtomCoding {Atom : Type u}
    (decodeAtom : Nat → Atom) (codeAtom : Atom → Nat)
    (hcode : ∀ atom, decodeAtom (codeAtom atom) = atom) : FormulaEnumeration Atom where
  enumerate := formulaDecodeOfAtomCoding decodeAtom
  exhaustive := fun formula => ⟨formulaCodeOfAtomCoding codeAtom formula,
    formulaDecodeOfAtomCoding_code decodeAtom codeAtom hcode formula⟩

/- A complete propositional internal language packages its only infinitary
   requirement—the ability to enumerate formulas.  Completeness is therefore
   unconditional for every value of this structure, rather than silently
   assuming that arbitrary incidence atoms are countable. -/
structure CompletePropositionalInternalLogic (Atom : Type u) where
  enumeration : FormulaEnumeration Atom

theorem CompletePropositionalInternalLogic.kripke_complete
    {Atom : Type u} (logic : CompletePropositionalInternalLogic Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_enumeration logic.enumeration context formula

noncomputable def completeLogicOfAtomCoding {Atom : Type u}
    (decodeAtom : Nat → Atom) (codeAtom : Atom → Nat)
    (hcode : ∀ atom, decodeAtom (codeAtom atom) = atom) :
    CompletePropositionalInternalLogic Atom where
  enumeration := formulaEnumerationOfAtomCoding decodeAtom codeAtom hcode

/- A reusable countable atom presentation.  Keeping the retraction as data
   makes countability closed under the same sum and product constructors used
   by incidence structures, and therefore makes completeness compositional. -/
structure CountableAtomCoding (Atom : Type u) where
  decode : Nat → Atom
  code : Atom → Nat
  decode_code : ∀ atom, decode (code atom) = atom

noncomputable def CountableAtomCoding.formulaEnumeration {Atom : Type u}
    (coding : CountableAtomCoding Atom) : FormulaEnumeration Atom :=
  formulaEnumerationOfAtomCoding coding.decode coding.code coding.decode_code

noncomputable def CountableAtomCoding.completeLogic {Atom : Type u}
    (coding : CountableAtomCoding Atom) : CompletePropositionalInternalLogic Atom :=
  completeLogicOfAtomCoding coding.decode coding.code coding.decode_code

noncomputable def CountableAtomCoding.sum {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right) :
    CountableAtomCoding (Sum Left Right) where
  decode index := if index % 2 = 0 then .inl (left.decode (index / 2))
    else .inr (right.decode (index / 2))
  code
    | .inl atom => 2 * left.code atom
    | .inr atom => 2 * right.code atom + 1
  decode_code := by
    intro atom
    cases atom with
    | inl atom =>
      simp [left.decode_code]
    | inr atom =>
      simp [show (2 * right.code atom + 1) / 2 = right.code atom by omega,
        right.decode_code]

noncomputable def CountableAtomCoding.prod {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right) :
    CountableAtomCoding (Left × Right) where
  decode index :=
    (left.decode (diagonalIndex index), right.decode (diagonalRemainder index))
  code pair := diagonalPair (left.code pair.1) (right.code pair.2)
  decode_code := by
    intro pair
    apply Prod.ext
    · simp [diagonalIndex_pair, left.decode_code]
    · simp [diagonalRemainder_pair, right.decode_code]

theorem CountableAtomCoding.kripke_complete {Atom : Type u}
    (coding : CountableAtomCoding Atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_enumeration coding.formulaEnumeration context formula

theorem CountableAtomCoding.sum_kripke_complete {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right)
    (context : List (Formula (Sum Left Right)))
    (formula : Formula (Sum Left Right)) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  (left.sum right).kripke_complete context formula

theorem CountableAtomCoding.prod_kripke_complete {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right)
    (context : List (Formula (Left × Right)))
    (formula : Formula (Left × Right)) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  (left.prod right).kripke_complete context formula

theorem CountableAtomCoding.consistent_iff_kripkeSatisfiable {Atom : Type u}
    (coding : CountableAtomCoding Atom) (context : List (Formula Atom)) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  derivationallyConsistent_iff_kripkeSatisfiable_of_enumeration
    coding.formulaEnumeration context

theorem CountableAtomCoding.consistent_iff_has_canonical_world {Atom : Type u}
    (coding : CountableAtomCoding Atom) (context : List (Formula Atom)) :
    DerivationallyConsistent context ↔
      ∃ theory : PrimeTheory Atom,
        KripkeContextForces (canonicalKripkeModel Atom) theory context :=
  derivationallyConsistent_iff_has_canonical_world_of_enumeration
    coding.formulaEnumeration context

theorem CountableAtomCoding.canonical_countermodel_of_not_derives
    {Atom : Type u} (coding : CountableAtomCoding Atom)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory Atom,
      KripkeContextForces (canonicalKripkeModel Atom) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel Atom) theory formula :=
  canonical_countermodel_of_not_derives_of_enumeration
    coding.formulaEnumeration hnot

theorem CountableAtomCoding.sum_consistent_iff_kripkeSatisfiable
    {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right)
    (context : List (Formula (Sum Left Right))) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  (left.sum right).consistent_iff_kripkeSatisfiable context

theorem CountableAtomCoding.prod_consistent_iff_kripkeSatisfiable
    {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right)
    (context : List (Formula (Left × Right))) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  (left.prod right).consistent_iff_kripkeSatisfiable context

theorem CountableAtomCoding.sum_canonical_countermodel_of_not_derives
    {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right)
    {context : List (Formula (Sum Left Right))}
    {formula : Formula (Sum Left Right)} (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory (Sum Left Right),
      KripkeContextForces (canonicalKripkeModel (Sum Left Right)) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel (Sum Left Right)) theory formula :=
  (left.sum right).canonical_countermodel_of_not_derives hnot

theorem CountableAtomCoding.prod_canonical_countermodel_of_not_derives
    {Left Right : Type u}
    (left : CountableAtomCoding Left) (right : CountableAtomCoding Right)
    {context : List (Formula (Left × Right))}
    {formula : Formula (Left × Right)} (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory (Left × Right),
      KripkeContextForces (canonicalKripkeModel (Left × Right)) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel (Left × Right)) theory formula :=
  (left.prod right).canonical_countermodel_of_not_derives hnot

/- A countably presented incidence is an incidence structure together with
   exactly the coding data needed by its propositional internal language.
   This is the direct bridge between the geometric carrier and the generic
   soundness/completeness development above. -/
structure CountablyPresentedIncidence (I R T : Type u) [DecidableEq I] where
  incidence : Incidence I R T
  atoms : CountableAtomCoding I

/- A concrete incidence semantics: an atomic proposition holds exactly when
   the represented incidence has an observed boundary endpoint.  Unlike the
   arbitrary valuations used for generic soundness/completeness, this truth
   assignment is computed directly from the `Incidence` object. -/
def IncidenceBoundaryValuation {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) : Prop :=
  ∃ endpoint, endpoint ∈ incidence.boundary atom

def IncidenceLeafValuation {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) : Prop :=
  incidence.boundary atom = []

def IncidenceLeafSatisfies {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (formula : Formula I) : Prop :=
  Satisfies (IncidenceLeafValuation incidence) formula

def IncidenceLeafContextSatisfies {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (context : List (Formula I)) : Prop :=
  ContextSatisfies (IncidenceLeafValuation incidence) context

theorem incidenceBoundaryValuation_iff_not_leaf
    {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) :
    IncidenceBoundaryValuation incidence atom ↔
      ¬ IncidenceLeafValuation incidence atom := by
  constructor
  · rintro ⟨endpoint, member⟩ leaf
    unfold IncidenceLeafValuation at leaf
    rw [leaf] at member
    simp at member
  · intro notLeaf
    unfold IncidenceBoundaryValuation
    unfold IncidenceLeafValuation at notLeaf
    cases boundaryEq : incidence.boundary atom with
    | nil => exact False.elim (notLeaf boundaryEq)
    | cons endpoint rest =>
      exact ⟨endpoint, by simp⟩

theorem incidenceLeafValuation_iff_not_boundary
    {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) :
    IncidenceLeafValuation incidence atom ↔
      ¬ IncidenceBoundaryValuation incidence atom := by
  constructor
  · intro leaf boundary
    exact ((incidenceBoundaryValuation_iff_not_leaf incidence atom).mp boundary) leaf
  · intro notBoundary
    cases boundaryEq : incidence.boundary atom with
    | nil => exact boundaryEq
    | cons endpoint rest =>
      exfalso
      apply notBoundary
      exact ⟨endpoint, by simp [boundaryEq]⟩

def IncidenceBoundarySatisfies {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (formula : Formula I) : Prop :=
  Satisfies (IncidenceBoundaryValuation incidence) formula

def IncidenceBoundaryContextSatisfies {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (context : List (Formula I)) : Prop :=
  ContextSatisfies (IncidenceBoundaryValuation incidence) context

theorem incidenceBoundaryAtom_iff_not_leafAtom
    {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) :
    IncidenceBoundarySatisfies incidence (.atom atom) ↔
      ¬ IncidenceLeafSatisfies incidence (.atom atom) :=
  incidenceBoundaryValuation_iff_not_leaf incidence atom

def IncidenceBoundaryEntails {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (context : List (Formula I))
    (formula : Formula I) : Prop :=
  IncidenceBoundaryContextSatisfies incidence context →
    IncidenceBoundarySatisfies incidence formula

theorem incidenceBoundarySatisfies_atom_iff
    {I R T : Type u} [DecidableEq I] (incidence : Incidence I R T) (atom : I) :
    IncidenceBoundarySatisfies incidence (.atom atom) ↔
      ∃ endpoint, endpoint ∈ incidence.boundary atom := by
  rfl

theorem derives_incidenceBoundary_sound
    {I R T : Type u} [DecidableEq I] {incidence : Incidence I R T}
    {context : List (Formula I)} {formula : Formula I}
    (derivation : Derives context formula)
    (holds : IncidenceBoundaryContextSatisfies incidence context) :
    IncidenceBoundarySatisfies incidence formula :=
  derives_sound derivation holds

theorem derives_incidenceLeaf_sound
    {I R T : Type u} [DecidableEq I] {incidence : Incidence I R T}
    {context : List (Formula I)} {formula : Formula I}
    (derivation : Derives context formula)
    (holds : IncidenceLeafContextSatisfies incidence context) :
    IncidenceLeafSatisfies incidence formula :=
  derives_sound derivation holds

theorem derives_incidenceBoundary_entails
    {I R T : Type u} [DecidableEq I] {incidence : Incidence I R T}
    {context : List (Formula I)} {formula : Formula I}
    (derivation : Derives context formula) :
    IncidenceBoundaryEntails incidence context formula :=
  fun holds => derives_incidenceBoundary_sound derivation holds

theorem incidenceBoundary_excludedMiddle_holds
    {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) :
    IncidenceBoundarySatisfies incidence
      (.or (.atom atom) (Formula.neg (.atom atom))) := by
  change IncidenceBoundaryValuation incidence atom ∨
    (IncidenceBoundaryValuation incidence atom → False)
  exact Classical.em (IncidenceBoundaryValuation incidence atom)

theorem incidenceBoundary_excludedMiddle_entails
    {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) :
    IncidenceBoundaryEntails incidence []
      (.or (.atom atom) (Formula.neg (.atom atom))) := by
  intro _
  exact incidenceBoundary_excludedMiddle_holds incidence atom

theorem incidenceBoundary_semantics_not_complete
    {I R T : Type u} [DecidableEq I]
    (incidence : Incidence I R T) (atom : I) :
    IncidenceBoundaryEntails incidence []
        (.or (.atom atom) (Formula.neg (.atom atom))) ∧
      ¬ Derives ([] : List (Formula I))
        (.or (.atom atom) (Formula.neg (.atom atom))) :=
  ⟨incidenceBoundary_excludedMiddle_entails incidence atom,
    excluded_middle_not_derivable atom⟩

theorem incidenceBoundarySatisfies_map_iff
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    (source : Incidence I R T) (target : Incidence I' R' T')
    (translate : I → I')
    (preservesBoundaryObservation : ∀ atom,
      IncidenceBoundaryValuation target (translate atom) ↔
        IncidenceBoundaryValuation source atom)
    (formula : Formula I) :
    IncidenceBoundarySatisfies target (formula.map translate) ↔
      IncidenceBoundarySatisfies source formula := by
  unfold IncidenceBoundarySatisfies
  rw [satisfies_map]
  exact satisfies_congr preservesBoundaryObservation formula

theorem incidenceBoundaryContextSatisfies_map_iff
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    (source : Incidence I R T) (target : Incidence I' R' T')
    (translate : I → I')
    (preservesBoundaryObservation : ∀ atom,
      IncidenceBoundaryValuation target (translate atom) ↔
        IncidenceBoundaryValuation source atom)
    (context : List (Formula I)) :
    IncidenceBoundaryContextSatisfies target (Formula.mapContext translate context) ↔
      IncidenceBoundaryContextSatisfies source context := by
  unfold IncidenceBoundaryContextSatisfies
  rw [context_satisfies_map_iff]
  exact contextSatisfies_congr preservesBoundaryObservation context

structure IncidenceBoundaryObservationEmbedding
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    (source : Incidence I R T) (target : Incidence I' R' T') where
  map : I → I'
  boundary_iff : ∀ atom,
    IncidenceBoundaryValuation target (map atom) ↔
      IncidenceBoundaryValuation source atom

def IncidenceBoundaryObservationEmbedding.identity
    {I R T : Type u} [DecidableEq I] (incidence : Incidence I R T) :
    IncidenceBoundaryObservationEmbedding incidence incidence where
  map := id
  boundary_iff := fun _ => Iff.rfl

def IncidenceBoundaryObservationEmbedding.comp
    {I I' I'' R T R' T' R'' T'' : Type u}
    [DecidableEq I] [DecidableEq I'] [DecidableEq I'']
    {source : Incidence I R T} {middle : Incidence I' R' T'}
    {target : Incidence I'' R'' T''}
    (second : IncidenceBoundaryObservationEmbedding middle target)
    (first : IncidenceBoundaryObservationEmbedding source middle) :
    IncidenceBoundaryObservationEmbedding source target where
  map := second.map ∘ first.map
  boundary_iff := fun atom => (second.boundary_iff (first.map atom)).trans
    (first.boundary_iff atom)

theorem IncidenceBoundaryObservationEmbedding.satisfies_iff
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (embedding : IncidenceBoundaryObservationEmbedding source target)
    (formula : Formula I) :
    IncidenceBoundarySatisfies target (formula.map embedding.map) ↔
      IncidenceBoundarySatisfies source formula :=
  incidenceBoundarySatisfies_map_iff source target embedding.map
    embedding.boundary_iff formula

theorem IncidenceBoundaryObservationEmbedding.contextSatisfies_iff
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (embedding : IncidenceBoundaryObservationEmbedding source target)
    (context : List (Formula I)) :
    IncidenceBoundaryContextSatisfies target
        (Formula.mapContext embedding.map context) ↔
      IncidenceBoundaryContextSatisfies source context :=
  incidenceBoundaryContextSatisfies_map_iff source target embedding.map
    embedding.boundary_iff context

theorem IncidenceBoundaryObservationEmbedding.entails_iff
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (embedding : IncidenceBoundaryObservationEmbedding source target)
    (context : List (Formula I)) (formula : Formula I) :
    IncidenceBoundaryEntails target (Formula.mapContext embedding.map context)
        (formula.map embedding.map) ↔
      IncidenceBoundaryEntails source context formula := by
  constructor
  · intro targetEntails sourceHolds
    apply (embedding.satisfies_iff formula).mp
    apply targetEntails
    exact (embedding.contextSatisfies_iff context).mpr sourceHolds
  · intro sourceEntails targetHolds
    apply (embedding.satisfies_iff formula).mpr
    apply sourceEntails
    exact (embedding.contextSatisfies_iff context).mp targetHolds

theorem IncidenceBoundaryObservationEmbedding.satisfies_comp
    {I I' I'' R T R' T' R'' T'' : Type u}
    [DecidableEq I] [DecidableEq I'] [DecidableEq I'']
    {source : Incidence I R T} {middle : Incidence I' R' T'}
    {target : Incidence I'' R'' T''}
    (second : IncidenceBoundaryObservationEmbedding middle target)
    (first : IncidenceBoundaryObservationEmbedding source middle)
    (formula : Formula I) :
    IncidenceBoundarySatisfies target
        (formula.map (second.map ∘ first.map)) ↔
      IncidenceBoundarySatisfies source formula :=
  (second.comp first).satisfies_iff formula

abbrev CountablyPresentedIncidence.InternalFormula {I R T : Type u}
    [DecidableEq I] (_presentation : CountablyPresentedIncidence I R T) := Formula I

theorem CountablyPresentedIncidence.internalLogic_complete
    {I R T : Type u} [DecidableEq I]
    (presentation : CountablyPresentedIncidence I R T)
    (context : List (Formula I)) (formula : Formula I) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  presentation.atoms.kripke_complete context formula

theorem CountablyPresentedIncidence.internalLogic_consistent_iff_model
    {I R T : Type u} [DecidableEq I]
    (presentation : CountablyPresentedIncidence I R T)
    (context : List (Formula I)) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  presentation.atoms.consistent_iff_kripkeSatisfiable context

theorem CountablyPresentedIncidence.internalLogic_consistent_iff_canonical_world
    {I R T : Type u} [DecidableEq I]
    (presentation : CountablyPresentedIncidence I R T)
    (context : List (Formula I)) :
    DerivationallyConsistent context ↔
      ∃ theory : PrimeTheory I,
        KripkeContextForces (canonicalKripkeModel I) theory context :=
  presentation.atoms.consistent_iff_has_canonical_world context

theorem CountablyPresentedIncidence.internalLogic_countermodel
    {I R T : Type u} [DecidableEq I]
    (presentation : CountablyPresentedIncidence I R T)
    {context : List (Formula I)} {formula : Formula I}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory I,
      KripkeContextForces (canonicalKripkeModel I) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel I) theory formula :=
  presentation.atoms.canonical_countermodel_of_not_derives hnot

/-! The coding retraction is precisely the data needed to apply the generic
   enumeration-based completeness construction.  Keeping this theorem at the
   coding interface makes every countably retracted atom language an immediate
   instance, without exposing a client to the intermediate enumeration. -/
theorem kripke_entails_iff_derives_of_atom_coding {Atom : Type u}
    (decodeAtom : Nat → Atom) (codeAtom : Atom → Nat)
    (hcode : ∀ atom, decodeAtom (codeAtom atom) = atom)
    (context : List (Formula Atom)) (formula : Formula Atom) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_enumeration
    (formulaEnumerationOfAtomCoding decodeAtom codeAtom hcode) context formula

/-! Countable atom codings expose the canonical countermodel directly, not
   only the logically equivalent completeness statement. -/
theorem canonical_countermodel_of_not_derives_of_atom_coding {Atom : Type u}
    (decodeAtom : Nat → Atom) (codeAtom : Atom → Nat)
    (hcode : ∀ atom, decodeAtom (codeAtom atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory Atom,
      KripkeContextForces (canonicalKripkeModel Atom) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel Atom) theory formula :=
  canonical_countermodel_of_not_derives_of_enumeration
    (formulaEnumerationOfAtomCoding decodeAtom codeAtom hcode) hnot

theorem not_kripke_entails_of_not_derives_of_atom_coding {Atom : Type u}
    (decodeAtom : Nat → Atom) (codeAtom : Atom → Nat)
    (hcode : ∀ atom, decodeAtom (codeAtom atom) = atom)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (hnot : ¬ Derives context formula) :
    ¬ KripkeEntails.{u, u} context formula :=
  not_kripke_entails_of_not_derives_of_enumeration
    (formulaEnumerationOfAtomCoding decodeAtom codeAtom hcode) hnot

noncomputable def finSuccAtomDecode (n : Nat) : Nat → Fin (n + 1) :=
  fun index => ⟨index % (n + 1), Nat.mod_lt _ (by omega)⟩

theorem finSuccAtomDecode_code (n : Nat) (atom : Fin (n + 1)) :
    finSuccAtomDecode n atom.val = atom := by
  apply Fin.ext
  simp [finSuccAtomDecode, Nat.mod_eq_of_lt atom.isLt]

noncomputable def finSuccFormulaEnumeration (n : Nat) : FormulaEnumeration (Fin (n + 1)) :=
  formulaEnumerationOfAtomCoding (finSuccAtomDecode n) Fin.val (finSuccAtomDecode_code n)

theorem finSucc_kripke_entails_iff_derives (n : Nat)
    (context : List (Formula (Fin (n + 1)))) (formula : Formula (Fin (n + 1))) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_atom_coding (finSuccAtomDecode n) Fin.val
    (finSuccAtomDecode_code n) context formula

/- The zero-element finite type has no atom constructor to encode.  Its
   formula language nevertheless remains countable, using the five remaining
   propositional constructors. -/
noncomputable def emptyFormulaDecode : Nat → Formula (Fin 0)
  | 0 => .top
  | code + 1 =>
    let payload := code / 5
    match code % 5 with
    | 0 => .top
    | 1 => .bot
    | 2 => .and (emptyFormulaDecode (diagonalIndex payload))
        (emptyFormulaDecode (diagonalRemainder payload))
    | 3 => .or (emptyFormulaDecode (diagonalIndex payload))
        (emptyFormulaDecode (diagonalRemainder payload))
    | _ => .imp (emptyFormulaDecode (diagonalIndex payload))
        (emptyFormulaDecode (diagonalRemainder payload))
termination_by code => code

decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    apply Nat.le_trans
    · first | exact diagonalIndex_le_stage _ | exact diagonalRemainder_le_stage _
    · exact Nat.div_le_self _ _

noncomputable def emptyFormulaCode : Formula (Fin 0) → Nat
  | .atom atom => Fin.elim0 atom
  | .top => 1
  | .bot => 2
  | .and p q => 5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 3
  | .or p q => 5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 4
  | .imp p q => 5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 5

theorem emptyFormulaDecode_code : ∀ formula : Formula (Fin 0),
    emptyFormulaDecode (emptyFormulaCode formula) = formula := by
  intro formula
  induction formula with
  | atom atom => exact Fin.elim0 atom
  | top => simp [emptyFormulaCode, emptyFormulaDecode]
  | bot => simp [emptyFormulaCode, emptyFormulaDecode]
  | and p q ihp ihq =>
    simp only [emptyFormulaCode, emptyFormulaDecode]
    rw [show (5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 2) / 5 =
        diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) by omega]
    rw [show (5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 2) % 5 = 2 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]
  | or p q ihp ihq =>
    simp only [emptyFormulaCode, emptyFormulaDecode]
    rw [show (5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 3) / 5 =
        diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) by omega]
    rw [show (5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 3) % 5 = 3 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]
  | imp p q ihp ihq =>
    simp only [emptyFormulaCode, emptyFormulaDecode]
    rw [show (5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 4) / 5 =
        diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) by omega]
    rw [show (5 * diagonalPair (emptyFormulaCode p) (emptyFormulaCode q) + 4) % 5 = 4 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]

noncomputable def emptyFormulaEnumeration : FormulaEnumeration (Fin 0) where
  enumerate := emptyFormulaDecode
  exhaustive := fun formula => ⟨emptyFormulaCode formula, emptyFormulaDecode_code formula⟩

noncomputable def finFormulaEnumeration : (n : Nat) → FormulaEnumeration (Fin n)
  | 0 => emptyFormulaEnumeration
  | n + 1 => finSuccFormulaEnumeration n

theorem fin_kripke_entails_iff_derives (n : Nat)
    (context : List (Formula (Fin n))) (formula : Formula (Fin n)) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_enumeration (finFormulaEnumeration n) context formula

theorem fin_derivationallyConsistent_iff_kripkeSatisfiable
    (n : Nat) (context : List (Formula (Fin n))) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  derivationallyConsistent_iff_kripkeSatisfiable_of_enumeration
    (finFormulaEnumeration n) context

theorem fin_derivationallyConsistent_iff_has_canonical_world
    (n : Nat) (context : List (Formula (Fin n))) :
    DerivationallyConsistent context ↔
      ∃ theory : PrimeTheory (Fin n),
        KripkeContextForces (canonicalKripkeModel (Fin n)) theory context :=
  derivationallyConsistent_iff_has_canonical_world_of_enumeration
    (finFormulaEnumeration n) context

/-! Every finite atom language has a user-facing canonical counterworld
   theorem, including the empty language (`n = 0`). -/
theorem fin_canonical_countermodel_of_not_derives (n : Nat)
    {context : List (Formula (Fin n))} {formula : Formula (Fin n)}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory (Fin n),
      KripkeContextForces (canonicalKripkeModel (Fin n)) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel (Fin n)) theory formula :=
  canonical_countermodel_of_not_derives_of_enumeration (finFormulaEnumeration n) hnot

theorem fin_not_kripke_entails_of_not_derives (n : Nat)
    {context : List (Formula (Fin n))} {formula : Formula (Fin n)}
    (hnot : ¬ Derives context formula) :
    ¬ KripkeEntails.{0, 0} context formula :=
  not_kripke_entails_of_not_derives_of_enumeration (finFormulaEnumeration n) hnot

/-! Natural-number atoms give a concrete countably infinite language.  Unlike
   the finite cases above, its atom coding needs no quotient or wraparound: a
   natural number is both its own code and its own decoding. -/
noncomputable def natFormulaEnumeration : FormulaEnumeration Nat :=
  formulaEnumerationOfAtomCoding id id (fun _ => rfl)

theorem nat_kripke_entails_iff_derives
    (context : List (Formula Nat)) (formula : Formula Nat) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_atom_coding id id (fun _ => rfl) context formula

theorem nat_derivationallyConsistent_iff_kripkeSatisfiable
    (context : List (Formula Nat)) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  derivationallyConsistent_iff_kripkeSatisfiable_of_enumeration
    natFormulaEnumeration context

theorem nat_derivationallyConsistent_iff_has_canonical_world
    (context : List (Formula Nat)) :
    DerivationallyConsistent context ↔
      ∃ theory : PrimeTheory Nat,
        KripkeContextForces (canonicalKripkeModel Nat) theory context :=
  derivationallyConsistent_iff_has_canonical_world_of_enumeration
    natFormulaEnumeration context

theorem nat_canonical_countermodel_of_not_derives
    {context : List (Formula Nat)} {formula : Formula Nat}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory Nat,
      KripkeContextForces (canonicalKripkeModel Nat) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel Nat) theory formula :=
  canonical_countermodel_of_not_derives_of_atom_coding id id (fun _ => rfl) hnot

theorem nat_not_kripke_entails_of_not_derives
    {context : List (Formula Nat)} {formula : Formula Nat}
    (hnot : ¬ Derives context formula) :
    ¬ KripkeEntails.{0, 0} context formula :=
  not_kripke_entails_of_not_derives_of_atom_coding id id (fun _ => rfl) hnot

noncomputable def boolFormulaDecode : Nat → Formula Bool
  | 0 => .atom false
  | code + 1 =>
    let payload := code / 7
    match code % 7 with
    | 0 => .atom false
    | 1 => .atom true
    | 2 => .top
    | 3 => .bot
    | 4 => .and (boolFormulaDecode (diagonalIndex payload))
        (boolFormulaDecode (diagonalRemainder payload))
    | 5 => .or (boolFormulaDecode (diagonalIndex payload))
        (boolFormulaDecode (diagonalRemainder payload))
    | _ => .imp (boolFormulaDecode (diagonalIndex payload))
        (boolFormulaDecode (diagonalRemainder payload))
termination_by code => code

decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    apply Nat.le_trans
    · first | exact diagonalIndex_le_stage _ | exact diagonalRemainder_le_stage _
    · exact Nat.div_le_self _ _

noncomputable def boolFormulaCode : Formula Bool → Nat
  | .atom false => 1
  | .atom true => 2
  | .top => 3
  | .bot => 4
  | .and p q => 7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 5
  | .or p q => 7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 6
  | .imp p q => 7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 7

theorem boolFormulaDecode_code : ∀ formula : Formula Bool,
    boolFormulaDecode (boolFormulaCode formula) = formula := by
  intro formula
  induction formula with
  | atom atom => cases atom <;> simp [boolFormulaCode, boolFormulaDecode]
  | top => simp [boolFormulaCode, boolFormulaDecode]
  | bot => simp [boolFormulaCode, boolFormulaDecode]
  | and p q ihp ihq =>
    simp only [boolFormulaCode, boolFormulaDecode]
    rw [show (7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 4) / 7 =
        diagonalPair (boolFormulaCode p) (boolFormulaCode q) by omega]
    rw [show (7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 4) % 7 = 4 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]
  | or p q ihp ihq =>
    simp only [boolFormulaCode, boolFormulaDecode]
    rw [show (7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 5) / 7 =
        diagonalPair (boolFormulaCode p) (boolFormulaCode q) by omega]
    rw [show (7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 5) % 7 = 5 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]
  | imp p q ihp ihq =>
    simp only [boolFormulaCode, boolFormulaDecode]
    rw [show (7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 6) / 7 =
        diagonalPair (boolFormulaCode p) (boolFormulaCode q) by omega]
    rw [show (7 * diagonalPair (boolFormulaCode p) (boolFormulaCode q) + 6) % 7 = 6 by omega]
    rw [diagonalIndex_pair, diagonalRemainder_pair, ihp, ihq]

noncomputable def boolFormulaEnumeration : FormulaEnumeration Bool where
  enumerate := boolFormulaDecode
  exhaustive := fun formula => ⟨boolFormulaCode formula, boolFormulaDecode_code formula⟩

/- The abstract canonical completeness theorem is consequently immediately
   usable for a language with two distinguishable incidence atoms. -/
theorem bool_kripke_entails_iff_derives
    (context : List (Formula Bool)) (formula : Formula Bool) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_enumeration boolFormulaEnumeration context formula

theorem bool_derivationallyConsistent_iff_kripkeSatisfiable
    (context : List (Formula Bool)) :
    DerivationallyConsistent context ↔ KripkeSatisfiable context :=
  derivationallyConsistent_iff_kripkeSatisfiable_of_enumeration
    boolFormulaEnumeration context

theorem bool_derivationallyConsistent_iff_has_canonical_world
    (context : List (Formula Bool)) :
    DerivationallyConsistent context ↔
      ∃ theory : PrimeTheory Bool,
        KripkeContextForces (canonicalKripkeModel Bool) theory context :=
  derivationallyConsistent_iff_has_canonical_world_of_enumeration
    boolFormulaEnumeration context

theorem bool_canonical_countermodel_of_not_derives
    {context : List (Formula Bool)} {formula : Formula Bool}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory Bool,
      KripkeContextForces (canonicalKripkeModel Bool) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel Bool) theory formula :=
  canonical_countermodel_of_not_derives_of_enumeration boolFormulaEnumeration hnot

theorem bool_not_kripke_entails_of_not_derives
    {context : List (Formula Bool)} {formula : Formula Bool}
    (hnot : ¬ Derives context formula) :
    ¬ KripkeEntails.{0, 0} context formula :=
  not_kripke_entails_of_not_derives_of_enumeration boolFormulaEnumeration hnot

end IncidenceCore
