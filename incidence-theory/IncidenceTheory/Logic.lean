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

/-! Natural-number atoms give a concrete countably infinite language.  Unlike
   the finite cases above, its atom coding needs no quotient or wraparound: a
   natural number is both its own code and its own decoding. -/
noncomputable def natFormulaEnumeration : FormulaEnumeration Nat :=
  formulaEnumerationOfAtomCoding id id (fun _ => rfl)

theorem nat_kripke_entails_iff_derives
    (context : List (Formula Nat)) (formula : Formula Nat) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_atom_coding id id (fun _ => rfl) context formula

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

end IncidenceCore
