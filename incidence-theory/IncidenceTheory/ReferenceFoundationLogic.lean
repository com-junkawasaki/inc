import IncidenceTheory.ReferenceFoundation

/-!
  Renaming/substitution algebra and Tarski semantics for the reference
  first-order language.  This is the constructive semantic envelope used by
  the G1 soundness proof; no classical axiom is introduced here.
-/

namespace IncidenceCore.ReferenceFoundation

universe u

def extend {D : Type u} (head : D) (tail : Nat → D) : Nat → D
  | 0 => head
  | n + 1 => tail n

@[simp] theorem extend_zero {D : Type u} (head : D) (tail : Nat → D) :
    extend head tail 0 = head := rfl

@[simp] theorem extend_succ {D : Type u} (head : D) (tail : Nat → D) (n : Nat) :
    extend head tail (n + 1) = tail n := rfl

theorem liftRenaming_id : liftRenaming id = id := by
  funext n
  cases n <;> rfl

theorem liftRenaming_comp (ρ τ : Nat → Nat) :
    liftRenaming (τ ∘ ρ) = liftRenaming τ ∘ liftRenaming ρ := by
  funext n
  cases n <;> rfl

@[simp] theorem Term.rename_id (term : Term) : term.rename id = term := by
  induction term <;> simp [Term.rename, *]

theorem Term.rename_comp (term : Term) (ρ τ : Nat → Nat) :
    (term.rename ρ).rename τ = term.rename (τ ∘ ρ) := by
  induction term <;> simp [Term.rename, *, Function.comp_def]

@[simp] theorem Formula.rename_id (formula : Formula) : formula.rename id = formula := by
  induction formula with
  | mem a b => simp [Formula.rename]
  | eq a b => simp [Formula.rename]
  | bot => rfl
  | and p q ihp ihq => simp [Formula.rename, ihp, ihq]
  | or p q ihp ihq => simp [Formula.rename, ihp, ihq]
  | imp p q ihp ihq => simp [Formula.rename, ihp, ihq]
  | all p ih => simpa [Formula.rename, liftRenaming_id] using ih
  | ex p ih => simpa [Formula.rename, liftRenaming_id] using ih

theorem Formula.rename_comp (formula : Formula) (ρ τ : Nat → Nat) :
    (formula.rename ρ).rename τ = formula.rename (τ ∘ ρ) := by
  induction formula generalizing ρ τ with
  | mem a b => simp [Formula.rename, Term.rename_comp]
  | eq a b => simp [Formula.rename, Term.rename_comp]
  | bot => rfl
  | and p q ihp ihq => simp [Formula.rename, ihp, ihq]
  | or p q ihp ihq => simp [Formula.rename, ihp, ihq]
  | imp p q ihp ihq => simp [Formula.rename, ihp, ihq]
  | all p ih =>
      simp only [Formula.rename]
      rw [ih, liftRenaming_comp]
  | ex p ih =>
      simp only [Formula.rename]
      rw [ih, liftRenaming_comp]

def identitySubstitution : Nat → Term := Term.var

@[simp] theorem Term.substitute_id (term : Term) :
    term.substitute identitySubstitution = term := by
  induction term <;> simp_all [Term.substitute, identitySubstitution]

theorem liftSubstitution_id :
    liftSubstitution identitySubstitution = identitySubstitution := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [liftSubstitution, identitySubstitution, Term.rename]

@[simp] theorem Formula.substitute_id (formula : Formula) :
    formula.substitute identitySubstitution = formula := by
  induction formula with
  | mem a b => simp [Formula.substitute]
  | eq a b => simp [Formula.substitute]
  | bot => rfl
  | and p q ihp ihq => simp [Formula.substitute, ihp, ihq]
  | or p q ihp ihq => simp [Formula.substitute, ihp, ihq]
  | imp p q ihp ihq => simp [Formula.substitute, ihp, ihq]
  | all p ih => simpa [Formula.substitute, liftSubstitution_id] using ih
  | ex p ih => simpa [Formula.substitute, liftSubstitution_id] using ih

theorem liftSubstitution_after_liftRenaming
    (substitution : Nat → Term) (rho : Nat → Nat) :
    liftSubstitution substitution ∘ liftRenaming rho =
      liftSubstitution (substitution ∘ rho) := by
  funext index
  cases index <;> rfl

theorem Term.rename_then_substitute (term : Term)
    (rho : Nat → Nat) (substitution : Nat → Term) :
    (term.rename rho).substitute substitution =
      term.substitute (substitution ∘ rho) := by
  induction term <;> simp [Term.rename, Term.substitute, *]

theorem Formula.rename_then_substitute (formula : Formula)
    (rho : Nat → Nat) (substitution : Nat → Term) :
    (formula.rename rho).substitute substitution =
      formula.substitute (substitution ∘ rho) := by
  induction formula generalizing rho substitution with
  | mem left right => simp [Formula.rename, Formula.substitute,
      Term.rename_then_substitute]
  | eq left right => simp [Formula.rename, Formula.substitute,
      Term.rename_then_substitute]
  | bot => rfl
  | and left right ihLeft ihRight => simp [Formula.rename,
      Formula.substitute, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [Formula.rename,
      Formula.substitute, ihLeft, ihRight]
  | imp left right ihLeft ihRight => simp [Formula.rename,
      Formula.substitute, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.rename, Formula.substitute]
      rw [ih, liftSubstitution_after_liftRenaming]
  | ex body ih =>
      simp only [Formula.rename, Formula.substitute]
      rw [ih, liftSubstitution_after_liftRenaming]

theorem liftSubstitution_rename
    (substitution : Nat → Term) (rho : Nat → Nat) :
    (fun index => (liftSubstitution substitution index).rename
      (liftRenaming rho)) =
    liftSubstitution (fun index => (substitution index).rename rho) := by
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      simp only [liftSubstitution, Term.rename_comp]
      congr 1

theorem Term.substitute_then_rename (term : Term)
    (substitution : Nat → Term) (rho : Nat → Nat) :
    (term.substitute substitution).rename rho =
      term.substitute (fun index => (substitution index).rename rho) := by
  induction term <;> simp [Term.rename, Term.substitute, *]

theorem Formula.substitute_then_rename (formula : Formula)
    (substitution : Nat → Term) (rho : Nat → Nat) :
    (formula.substitute substitution).rename rho =
      formula.substitute (fun index => (substitution index).rename rho) := by
  induction formula generalizing substitution rho with
  | mem left right => simp [Formula.rename, Formula.substitute,
      Term.substitute_then_rename]
  | eq left right => simp [Formula.rename, Formula.substitute,
      Term.substitute_then_rename]
  | bot => rfl
  | and left right ihLeft ihRight => simp [Formula.rename,
      Formula.substitute, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [Formula.rename,
      Formula.substitute, ihLeft, ihRight]
  | imp left right ihLeft ihRight => simp [Formula.rename,
      Formula.substitute, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.rename, Formula.substitute]
      rw [ih, liftSubstitution_rename]
  | ex body ih =>
      simp only [Formula.rename, Formula.substitute]
      rw [ih, liftSubstitution_rename]

theorem Formula.rename_succ_substitute_lift (formula : Formula)
    (substitution : Nat → Term) :
    (formula.rename Nat.succ).substitute (liftSubstitution substitution) =
      (formula.substitute substitution).rename Nat.succ := by
  rw [Formula.rename_then_substitute, Formula.substitute_then_rename]
  apply congrArg (fun mapped => formula.substitute mapped)
  funext index
  rfl

theorem Context.rename_succ_substitute_lift (context : Context)
    (substitution : Nat → Term) :
    (context.map (Formula.rename Nat.succ)).map
        (Formula.substitute (liftSubstitution substitution)) =
      (context.map (Formula.substitute substitution)).map
        (Formula.rename Nat.succ) := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      simp [Formula.rename_succ_substitute_lift, ih]

theorem liftSubstitution_comp (first second : Nat → Term) :
    (fun index => (liftSubstitution first index).substitute
      (liftSubstitution second)) =
    liftSubstitution (fun index => (first index).substitute second) := by
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      rw [liftSubstitution, liftSubstitution,
        Term.rename_then_substitute]
      rw [Term.substitute_then_rename]
      apply congrArg (fun mapped => (first index).substitute mapped)
      funext value
      rfl

theorem Term.substitute_comp (term : Term) (first second : Nat → Term) :
    (term.substitute first).substitute second =
      term.substitute (fun index => (first index).substitute second) := by
  induction term <;> simp [Term.substitute, *]

theorem Formula.substitute_comp (formula : Formula)
    (first second : Nat → Term) :
    (formula.substitute first).substitute second =
      formula.substitute (fun index => (first index).substitute second) := by
  induction formula generalizing first second with
  | mem left right => simp [Formula.substitute, Term.substitute_comp]
  | eq left right => simp [Formula.substitute, Term.substitute_comp]
  | bot => rfl
  | and left right ihLeft ihRight =>
      simp [Formula.substitute, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [Formula.substitute, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.substitute, ihLeft, ihRight]
  | all body ih =>
      simp only [Formula.substitute]
      rw [ih, liftSubstitution_comp]
  | ex body ih =>
      simp only [Formula.substitute]
      rw [ih, liftSubstitution_comp]

def instantiateSubstitution (term : Term) : Nat → Term
  | 0 => term
  | index + 1 => .var index

theorem Formula.instantiate_eq (body : Formula) (term : Term) :
    body.instantiate term = body.substitute (instantiateSubstitution term) := by
  rfl

theorem Formula.substitute_instantiate (body : Formula) (term : Term)
    (substitution : Nat → Term) :
    (body.instantiate term).substitute substitution =
      (body.substitute (liftSubstitution substitution)).instantiate
        (term.substitute substitution) := by
  simp only [Formula.instantiate_eq, Formula.substitute_comp]
  apply congrArg (fun mapped => body.substitute mapped)
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      simp only [instantiateSubstitution, liftSubstitution]
      rw [Term.rename_then_substitute]
      change (substitution index) =
        (substitution index).substitute identitySubstitution
      exact (Term.substitute_id _).symm

theorem Formula.substitute_lift_instantiate (body : Formula)
    (substitution : Nat → Term) (term : Term) :
    (body.substitute (liftSubstitution substitution)).instantiate term =
      body.substitute (extend term substitution) := by
  simp only [Formula.instantiate_eq, Formula.substitute_comp]
  apply congrArg (fun mapped => body.substitute mapped)
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      simp only [liftSubstitution, extend]
      rw [Term.rename_then_substitute]
      change (substitution index).substitute identitySubstitution =
        substitution index
      exact Term.substitute_id _

/-! ## Semantics -/

structure Structure where
  Carrier : Type u
  membership : Carrier → Carrier → Prop
  constant : Nat → Carrier
  empty : Carrier
  pair : Carrier → Carrier → Carrier
  union : Carrier → Carrier
  powerset : Carrier → Carrier

def Term.evaluate (model : Structure) (valuation : Nat → model.Carrier) :
    Term → model.Carrier
  | .var n => valuation n
  | .const n => model.constant n
  | .empty => model.empty
  | .pair a b => model.pair (a.evaluate model valuation) (b.evaluate model valuation)
  | .union a => model.union (a.evaluate model valuation)
  | .powerset a => model.powerset (a.evaluate model valuation)

def Formula.Realize (model : Structure) (valuation : Nat → model.Carrier) :
    Formula → Prop
  | .mem a b => model.membership (a.evaluate model valuation) (b.evaluate model valuation)
  | .eq a b => a.evaluate model valuation = b.evaluate model valuation
  | .bot => False
  | .and p q => p.Realize model valuation ∧ q.Realize model valuation
  | .or p q => p.Realize model valuation ∨ q.Realize model valuation
  | .imp p q => p.Realize model valuation → q.Realize model valuation
  | .all p => ∀ value, p.Realize model (extend value valuation)
  | .ex p => ∃ value, p.Realize model (extend value valuation)

def Context.Realize (model : Structure) (valuation : Nat → model.Carrier)
    (context : Context) : Prop :=
  ∀ formula ∈ context, formula.Realize model valuation

theorem Term.evaluate_rename (model : Structure) (valuation : Nat → model.Carrier)
    (ρ : Nat → Nat) (term : Term) :
    (term.rename ρ).evaluate model valuation =
      term.evaluate model (valuation ∘ ρ) := by
  induction term <;> simp [Term.rename, Term.evaluate, *, Function.comp_def]

theorem extend_comp_liftRenaming {D : Type u} (value : D)
    (valuation : Nat → D) (ρ : Nat → Nat) :
    extend value valuation ∘ liftRenaming ρ = extend value (valuation ∘ ρ) := by
  funext n
  cases n <;> rfl

theorem Formula.realize_rename (model : Structure)
    (valuation : Nat → model.Carrier) (ρ : Nat → Nat) (formula : Formula) :
    (formula.rename ρ).Realize model valuation ↔
      formula.Realize model (valuation ∘ ρ) := by
  induction formula generalizing valuation ρ with
  | mem a b => simp [Formula.rename, Formula.Realize, Term.evaluate_rename]
  | eq a b => simp [Formula.rename, Formula.Realize, Term.evaluate_rename]
  | bot => rfl
  | and p q ihp ihq => simp [Formula.rename, Formula.Realize, ihp, ihq]
  | or p q ihp ihq => simp [Formula.rename, Formula.Realize, ihp, ihq]
  | imp p q ihp ihq => simp [Formula.rename, Formula.Realize, ihp, ihq]
  | all p ih =>
      simp only [Formula.rename, Formula.Realize]
      constructor
      · intro h value
        have result := (ih (extend value valuation) (liftRenaming ρ)).mp (h value)
        simpa only [extend_comp_liftRenaming] using result
      · intro h value
        apply (ih (extend value valuation) (liftRenaming ρ)).mpr
        simpa only [extend_comp_liftRenaming] using h value
  | ex p ih =>
      simp only [Formula.rename, Formula.Realize]
      constructor
      · rintro ⟨value, h⟩
        refine ⟨value, ?_⟩
        rw [ih, extend_comp_liftRenaming] at h
        exact h
      · rintro ⟨value, h⟩
        refine ⟨value, ?_⟩
        rw [ih, extend_comp_liftRenaming]
        exact h

theorem Term.evaluate_substitute (model : Structure)
    (valuation : Nat → model.Carrier) (σ : Nat → Term) (term : Term) :
    (term.substitute σ).evaluate model valuation =
      term.evaluate model (fun n => (σ n).evaluate model valuation) := by
  induction term <;> simp [Term.substitute, Term.evaluate, *]

theorem evaluate_liftSubstitution (model : Structure)
    (valuation : Nat → model.Carrier) (value : model.Carrier) (σ : Nat → Term) :
    (fun n => (liftSubstitution σ n).evaluate model (extend value valuation)) =
      extend value (fun n => (σ n).evaluate model valuation) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp [liftSubstitution, Term.evaluate_rename, Function.comp_def]

theorem Formula.realize_substitute (model : Structure)
    (valuation : Nat → model.Carrier) (σ : Nat → Term) (formula : Formula) :
    (formula.substitute σ).Realize model valuation ↔
      formula.Realize model (fun n => (σ n).evaluate model valuation) := by
  induction formula generalizing valuation σ with
  | mem a b => simp [Formula.substitute, Formula.Realize, Term.evaluate_substitute]
  | eq a b => simp [Formula.substitute, Formula.Realize, Term.evaluate_substitute]
  | bot => rfl
  | and p q ihp ihq => simp [Formula.substitute, Formula.Realize, ihp, ihq]
  | or p q ihp ihq => simp [Formula.substitute, Formula.Realize, ihp, ihq]
  | imp p q ihp ihq => simp [Formula.substitute, Formula.Realize, ihp, ihq]
  | all p ih =>
      simp only [Formula.substitute, Formula.Realize]
      constructor
      · intro h value
        have result := (ih (extend value valuation) (liftSubstitution σ)).mp (h value)
        simpa only [evaluate_liftSubstitution] using result
      · intro h value
        apply (ih (extend value valuation) (liftSubstitution σ)).mpr
        simpa only [evaluate_liftSubstitution] using h value
  | ex p ih =>
      simp only [Formula.substitute, Formula.Realize]
      constructor
      · rintro ⟨value, h⟩
        refine ⟨value, ?_⟩
        rw [ih, evaluate_liftSubstitution] at h
        exact h
      · rintro ⟨value, h⟩
        refine ⟨value, ?_⟩
        rw [ih, evaluate_liftSubstitution]
        exact h

theorem Formula.realize_instantiate (model : Structure)
    (valuation : Nat → model.Carrier) (body : Formula) (term : Term) :
    (body.instantiate term).Realize model valuation ↔
      body.Realize model (extend (term.evaluate model valuation) valuation) := by
  unfold Formula.instantiate
  rw [Formula.realize_substitute]
  apply iff_of_eq
  congr 2
  funext n
  cases n <;> rfl

/-! ## Model validity and derivational soundness -/

structure Model (infinity : InfinitySchema) extends Structure where
  axiom_valid : ∀ {formula}, Axiom infinity formula →
    ∀ valuation, formula.Realize toStructure valuation

def Model.Valid {infinity : InfinitySchema} (model : Model infinity)
    (formula : Sentence) : Prop :=
  ∀ valuation, formula.Realize model.toStructure valuation

def Model.Entails {infinity : InfinitySchema} (model : Model infinity)
    (context : Context) (formula : Formula) : Prop :=
  ∀ valuation, context.Realize model.toStructure valuation →
    formula.Realize model.toStructure valuation

theorem Context.realize_cons (model : Structure) (valuation : Nat → model.Carrier)
    (formula : Formula) (context : Context) :
    Context.Realize model valuation (formula :: context) ↔
      formula.Realize model valuation ∧ context.Realize model valuation := by
  constructor
  · intro h
    exact ⟨h formula (by simp), fun q hq => h q (by simp [hq])⟩
  · rintro ⟨hformula, hcontext⟩ q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hformula
    · exact hcontext q hq

theorem extend_comp_succ {D : Type u} (value : D) (valuation : Nat → D) :
    extend value valuation ∘ Nat.succ = valuation := by
  funext n
  rfl

theorem Context.realize_rename_succ (model : Structure)
    (valuation : Nat → model.Carrier) (value : model.Carrier) (context : Context) :
    context.Realize model valuation →
      Context.Realize model (extend value valuation)
        (context.map (Formula.rename Nat.succ)) := by
  intro h formula hformula
  simp only [List.mem_map] at hformula
  rcases hformula with ⟨source, sourceMember, rfl⟩
  apply (Formula.realize_rename model (extend value valuation) Nat.succ source).mpr
  simpa only [extend_comp_succ] using h source sourceMember

theorem derives_sound {infinity : InfinitySchema}
    (model : Model infinity) {context : Context} {formula : Formula}
    (derivation : Derives infinity context formula) :
    model.Entails context formula := by
  induction derivation with
  | assumption member =>
      intro valuation contextValid
      exact contextValid _ member
  | «axiom» valid =>
      intro valuation _
      exact model.axiom_valid valid valuation
  | topIntro =>
      intro valuation _
      simp [Formula.top, Formula.Realize]
  | botElim premise ih =>
      intro valuation contextValid
      exact False.elim (ih valuation contextValid)
  | andIntro left right ihLeft ihRight =>
      intro valuation contextValid
      exact ⟨ihLeft valuation contextValid, ihRight valuation contextValid⟩
  | andElimLeft premise ih =>
      intro valuation contextValid
      exact (ih valuation contextValid).left
  | andElimRight premise ih =>
      intro valuation contextValid
      exact (ih valuation contextValid).right
  | orIntroLeft premise ih =>
      intro valuation contextValid
      exact Or.inl (ih valuation contextValid)
  | orIntroRight premise ih =>
      intro valuation contextValid
      exact Or.inr (ih valuation contextValid)
  | orElim disjunction left right ihDisjunction ihLeft ihRight =>
      intro valuation contextValid
      rcases ihDisjunction valuation contextValid with hp | hq
      · exact ihLeft valuation ((Context.realize_cons _ _ _ _).mpr ⟨hp, contextValid⟩)
      · exact ihRight valuation ((Context.realize_cons _ _ _ _).mpr ⟨hq, contextValid⟩)
  | impIntro premise ih =>
      intro valuation contextValid hp
      exact ih valuation ((Context.realize_cons _ _ _ _).mpr ⟨hp, contextValid⟩)
  | impElim implication premise ihImplication ihPremise =>
      intro valuation contextValid
      exact ihImplication valuation contextValid (ihPremise valuation contextValid)
  | allIntro premise ih =>
      intro valuation contextValid value
      exact ih (extend value valuation)
        (Context.realize_rename_succ _ valuation value _ contextValid)
  | allElim premise term ih =>
      intro valuation contextValid
      apply (Formula.realize_instantiate _ valuation _ term).mpr
      exact ih valuation contextValid (term.evaluate model.toStructure valuation)
  | exIntro term premise ih =>
      intro valuation contextValid
      refine ⟨term.evaluate model.toStructure valuation, ?_⟩
      exact (Formula.realize_instantiate _ valuation _ term).mp
        (ih valuation contextValid)
  | exElim existential branch ihExistential ihBranch =>
      intro valuation contextValid
      rcases ihExistential valuation contextValid with ⟨value, bodyValid⟩
      have shiftedContext :=
        Context.realize_rename_succ _ valuation value _ contextValid
      have branchContext :=
        (Context.realize_cons _ _ _ _).mpr ⟨bodyValid, shiftedContext⟩
      have shiftedResult := ihBranch (extend value valuation) branchContext
      exact (Formula.realize_rename _ (extend value valuation) Nat.succ _).mp shiftedResult

theorem theory_proof_valid_in_model {infinity : InfinitySchema}
    (model : Model infinity) {formula : Sentence}
    (proof : Derives infinity [] formula) : model.Valid formula := by
  intro valuation
  exact derives_sound model proof valuation (by simp [Context.Realize])

end IncidenceCore.ReferenceFoundation
