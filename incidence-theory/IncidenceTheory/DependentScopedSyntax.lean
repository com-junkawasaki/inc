import IncidenceTheory.DependentTypeTermPresheaf

namespace IncidenceCore

mutual
  def IncDepRawType.Scoped (depth : Nat) : IncDepRawType → Prop
    | .base _ => True
    | .unit => True
    | .pi domain codomain => domain.Scoped depth ∧ codomain.Scoped (depth + 1)
    | .sigma domain codomain => domain.Scoped depth ∧ codomain.Scoped (depth + 1)
    | .identity type left right =>
        type.Scoped depth ∧ left.Scoped depth ∧ right.Scoped depth

  def IncDepRawTerm.Scoped (depth : Nat) : IncDepRawTerm → Prop
    | .var index => index < depth
    | .unit => True
    | .lambda domain body => domain.Scoped depth ∧ body.Scoped (depth + 1)
    | .apply function argument => function.Scoped depth ∧ argument.Scoped depth
    | .pair first second => first.Scoped depth ∧ second.Scoped depth
    | .first pair => pair.Scoped depth
    | .second pair => pair.Scoped depth
    | .refl term => term.Scoped depth
end

theorem IncDepRawLookup.position_lt
    {context position type} (lookup : IncDepRawLookup context position type) :
    position < context.length := by
  induction lookup with
  | here => simp
  | there previous ih => simp only [List.length_cons]; omega

private theorem liftReplacement_agrees
    {depth : Nat} {first second : Nat → IncDepRawTerm}
    (agree : ∀ index, index < depth → first index = second index) :
    ∀ index, index < depth + 1 →
      IncDepRawTerm.liftReplacement first index =
        IncDepRawTerm.liftReplacement second index := by
  intro index indexLt
  cases index with
  | zero => rfl
  | succ index =>
      simp only [IncDepRawTerm.liftReplacement]
      rw [agree index (by omega)]

mutual
  theorem IncDepRawType.substitute_congr_of_scoped
      {depth : Nat} {type : IncDepRawType}
      (scopeProof : type.Scoped depth)
      {first second : Nat → IncDepRawTerm}
      (agree : ∀ index, index < depth → first index = second index) :
      type.substitute first = type.substitute second := by
    cases type with
    | base => rfl
    | unit => rfl
    | pi domain codomain =>
        rcases scopeProof with ⟨domainScoped, codomainScoped⟩
        simp only [IncDepRawType.substitute]
        rw [domain.substitute_congr_of_scoped domainScoped agree]
        rw [codomain.substitute_congr_of_scoped codomainScoped
          (liftReplacement_agrees agree)]
    | sigma domain codomain =>
        rcases scopeProof with ⟨domainScoped, codomainScoped⟩
        simp only [IncDepRawType.substitute]
        rw [domain.substitute_congr_of_scoped domainScoped agree]
        rw [codomain.substitute_congr_of_scoped codomainScoped
          (liftReplacement_agrees agree)]
    | identity type left right =>
        rcases scopeProof with ⟨typeScoped, leftScoped, rightScoped⟩
        simp only [IncDepRawType.substitute]
        rw [type.substitute_congr_of_scoped typeScoped agree]
        rw [left.substitute_congr_of_scoped leftScoped agree]
        rw [right.substitute_congr_of_scoped rightScoped agree]

  theorem IncDepRawTerm.substitute_congr_of_scoped
      {depth : Nat} {term : IncDepRawTerm}
      (scopeProof : term.Scoped depth)
      {first second : Nat → IncDepRawTerm}
      (agree : ∀ index, index < depth → first index = second index) :
      term.substitute first = term.substitute second := by
    cases term with
    | var index => exact agree index scopeProof
    | unit => rfl
    | lambda domain body =>
        rcases scopeProof with ⟨domainScoped, bodyScoped⟩
        simp only [IncDepRawTerm.substitute]
        rw [domain.substitute_congr_of_scoped domainScoped agree]
        rw [body.substitute_congr_of_scoped bodyScoped
          (liftReplacement_agrees agree)]
    | apply function argument =>
        rcases scopeProof with ⟨functionScoped, argumentScoped⟩
        simp only [IncDepRawTerm.substitute]
        rw [function.substitute_congr_of_scoped functionScoped agree]
        rw [argument.substitute_congr_of_scoped argumentScoped agree]
    | pair firstTerm secondTerm =>
        rcases scopeProof with ⟨firstScoped, secondScoped⟩
        simp only [IncDepRawTerm.substitute]
        rw [firstTerm.substitute_congr_of_scoped firstScoped agree]
        rw [secondTerm.substitute_congr_of_scoped secondScoped agree]
    | first pair =>
        simp only [IncDepRawTerm.substitute]
        rw [pair.substitute_congr_of_scoped scopeProof agree]
    | second pair =>
        simp only [IncDepRawTerm.substitute]
        rw [pair.substitute_congr_of_scoped scopeProof agree]
    | refl term =>
        simp only [IncDepRawTerm.substitute]
        rw [term.substitute_congr_of_scoped scopeProof agree]
end

mutual
  theorem IncDepRawWellFormed.scoped
      {context type} (formation : IncDepRawWellFormed context type) :
      type.Scoped context.length := by
    cases formation with
    | base => trivial
    | unit => trivial
    | pi domain codomain =>
        exact ⟨domain.scoped, by simpa using codomain.scoped⟩
    | sigma domain codomain =>
        exact ⟨domain.scoped, by simpa using codomain.scoped⟩
    | identity typeFormation leftTyping rightTyping =>
        exact ⟨typeFormation.scoped, leftTyping.term_scoped,
          rightTyping.term_scoped⟩

  theorem IncDepRawHasType.term_scoped
      {context term type} (typing : IncDepRawHasType context term type) :
      term.Scoped context.length := by
    cases typing with
    | varRule lookup => exact lookup.position_lt
    | unitRule => trivial
    | lambdaRule domainFormation bodyTyping =>
        exact ⟨domainFormation.scoped, by simpa using bodyTyping.term_scoped⟩
    | applyRule functionTyping argumentTyping =>
        exact ⟨functionTyping.term_scoped, argumentTyping.term_scoped⟩
    | pairRule firstTyping secondTyping =>
        exact ⟨firstTyping.term_scoped, secondTyping.term_scoped⟩
    | firstRule pairTyping => exact pairTyping.term_scoped
    | secondRule pairTyping => exact pairTyping.term_scoped
    | reflRule termTyping => exact termTyping.term_scoped
end

theorem IncDepRawWellFormed.substitute_eq_of_context_agreement
    {context type} (formation : IncDepRawWellFormed context type)
    {first second : Nat → IncDepRawTerm}
    (agree : ∀ index, index < context.length → first index = second index) :
    type.substitute first = type.substitute second :=
  IncDepRawType.substitute_congr_of_scoped formation.scoped agree

theorem IncDepRawHasType.substitute_term_eq_of_context_agreement
    {context term type} (typing : IncDepRawHasType context term type)
    {first second : Nat → IncDepRawTerm}
    (agree : ∀ index, index < context.length → first index = second index) :
    term.substitute first = term.substitute second :=
  IncDepRawTerm.substitute_congr_of_scoped typing.term_scoped agree

structure IncDepRawScopedSyntaxTheorem : Prop where
  lookup_bound : ∀ {context position type},
    IncDepRawLookup context position type → position < context.length
  formation_scope : ∀ {context type},
    IncDepRawWellFormed context type → type.Scoped context.length
  typing_scope : ∀ {context term type},
    IncDepRawHasType context term type → term.Scoped context.length
  type_substitution_extensional : ∀ {context type}
    (_formation : IncDepRawWellFormed context type)
    {first second : Nat → IncDepRawTerm},
    (∀ index, index < context.length → first index = second index) →
      type.substitute first = type.substitute second
  term_substitution_extensional : ∀ {context term type}
    (_typing : IncDepRawHasType context term type)
    {first second : Nat → IncDepRawTerm},
    (∀ index, index < context.length → first index = second index) →
      term.substitute first = term.substitute second

theorem incDepRawScopedSyntaxTheorem : IncDepRawScopedSyntaxTheorem where
  lookup_bound := IncDepRawLookup.position_lt
  formation_scope := IncDepRawWellFormed.scoped
  typing_scope := IncDepRawHasType.term_scoped
  type_substitution_extensional :=
    IncDepRawWellFormed.substitute_eq_of_context_agreement
  term_substitution_extensional :=
    IncDepRawHasType.substitute_term_eq_of_context_agreement

end IncidenceCore
