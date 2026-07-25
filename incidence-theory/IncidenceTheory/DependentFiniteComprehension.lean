import IncidenceTheory.DependentFinitePresheaf

namespace IncidenceCore

open CategoryTheory

noncomputable def IncDepRawFiniteType.extendContext
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) : IncDepRawFiniteContextObject where
  context := type.raw :: context.context
  wellFormed := .extend context.wellFormed (Classical.choice type.formation)

noncomputable def IncDepRawFiniteType.projection
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) : type.extendContext ⟶ context :=
  Quotient.mk _
    (IncDepRawExtensionalSubstitution.projection context.context type.raw)

def IncDepRawFiniteSubstitution.substituteScopedTerm
    {source target : List IncDepRawType}
    (substitution : IncDepRawFiniteSubstitution source target)
    (term : IncDepRawTerm) (scopeProof : term.Scoped target.length) :
    IncDepRawTerm :=
  Quotient.liftOn substitution
    (fun representative => term.substitute representative.term)
    (by
      intro first second equivalent
      exact term.substitute_congr_of_scoped scopeProof equivalent)

@[simp] theorem IncDepRawFiniteSubstitution.substituteScopedTerm_mk
    {source target} (substitution : IncDepRawExtensionalSubstitution source target)
    (term : IncDepRawTerm) (scopeProof : term.Scoped target.length) :
    IncDepRawFiniteSubstitution.substituteScopedTerm
        (Quotient.mk _ substitution : IncDepRawFiniteSubstitution source target)
        term scopeProof =
      term.substitute substitution.term := rfl

def IncDepRawFiniteType.genericScope
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) :
    (IncDepRawTerm.var 0).Scoped type.extendContext.context.length := by
  simp [IncDepRawFiniteType.extendContext, IncDepRawTerm.Scoped]

noncomputable def IncDepRawFiniteType.genericTerm
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) : IncDepRawFiniteTypedTerm type.extendContext where
  type := type.raw.rename Nat.succ
  term := .var 0
  formation := by
    rcases type.formation with ⟨formation⟩
    let weakening :=
      (IncDepRawRenaming.identity context.context).weakenTarget type.raw
    exact ⟨formation.rename weakening⟩
  typing := ⟨incDepRawContextGenericVariable context.context type.raw⟩

noncomputable def IncDepRawFiniteType.pair
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source.context term
      (type.reindexFinite substitution).raw)) :
    source ⟶ type.extendContext :=
  let representative := Quotient.out substitution
  let typeEq : (type.reindexFinite substitution).raw =
      type.raw.substitute representative.term := by
    rw [← Quotient.out_eq substitution]
    rfl
  let representativeTyping : Nonempty (IncDepRawHasType source.context term
      (type.raw.substitute representative.term)) := typeEq ▸ typing
  Quotient.mk _ (representative.extendPair type.raw term representativeTyping)

@[simp] theorem IncDepRawFiniteType.pair_projection
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source.context term
      (type.reindexFinite substitution).raw)) :
    type.pair substitution term typing ≫ type.projection = substitution := by
  unfold IncDepRawFiniteType.pair
  dsimp only
  calc
    Quotient.mk _ ((Quotient.out substitution).extendPair type.raw term _) ≫
          type.projection = Quotient.mk _ (Quotient.out substitution) :=
      congrArg (Quotient.mk _)
        ((Quotient.out substitution).extendPair_projection type.raw term _)
    _ = substitution := Quotient.out_eq substitution

@[simp] theorem IncDepRawFiniteType.pair_generic
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source.context term
      (type.reindexFinite substitution).raw)) :
    (type.pair substitution term typing).substituteScopedTerm
        (.var 0) type.genericScope = term := by
  unfold IncDepRawFiniteType.pair
  rfl

theorem IncDepRawFiniteType.pair_unique
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source.context term
      (type.reindexFinite substitution).raw))
    (candidate : source ⟶ type.extendContext)
    (projectionEq : candidate ≫ type.projection = substitution)
    (genericEq : candidate.substituteScopedTerm (.var 0) type.genericScope = term) :
    candidate = type.pair substitution term typing := by
  induction candidate using Quotient.inductionOn with
  | _ candidateRepresentative =>
      unfold IncDepRawFiniteType.pair
      apply Quotient.sound
      intro index indexLt
      cases index with
      | zero => exact genericEq
      | succ index =>
          have baseLt : index < target.context.length := by
            change index + 1 < (type.raw :: target.context).length at indexLt
            simp only [List.length_cons] at indexLt
            omega
          have projectionEq' :
              Quotient.mk (incDepRawFiniteSubstitutionSetoid
                source.context target.context) (candidateRepresentative.comp
                (IncDepRawExtensionalSubstitution.projection
                  target.context type.raw)) =
                Quotient.mk (incDepRawFiniteSubstitutionSetoid
                  source.context target.context) (Quotient.out substitution) := by
            calc
              Quotient.mk (incDepRawFiniteSubstitutionSetoid
                  source.context target.context) (candidateRepresentative.comp
                  (IncDepRawExtensionalSubstitution.projection
                    target.context type.raw)) =
                  (Quotient.mk _ candidateRepresentative :
                    source ⟶ type.extendContext) ≫ type.projection := rfl
              _ = substitution := projectionEq
              _ = Quotient.mk (incDepRawFiniteSubstitutionSetoid
                    source.context target.context) (Quotient.out substitution) :=
                (Quotient.out_eq substitution).symm
          have projectedEquivalent := Quotient.exact projectionEq'
          exact projectedEquivalent index baseLt

structure IncDepRawFiniteComprehensionTheorem : Prop where
  projection : ∀ {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context), Nonempty (type.extendContext ⟶ context)
  generic : ∀ {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context),
    Nonempty (IncDepRawFiniteTypedTerm type.extendContext)
  pairing : ∀ {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawTerm)
    (typing : Nonempty (IncDepRawHasType source.context term
      (type.reindexFinite substitution).raw)),
    let paired := type.pair substitution term typing
    paired ≫ type.projection = substitution ∧
      paired.substituteScopedTerm (.var 0) type.genericScope = term ∧
      ∀ candidate : source ⟶ type.extendContext,
        candidate ≫ type.projection = substitution →
        candidate.substituteScopedTerm (.var 0) type.genericScope = term →
        candidate = paired

theorem incDepRawFiniteComprehensionTheorem :
    IncDepRawFiniteComprehensionTheorem where
  projection := fun type => ⟨type.projection⟩
  generic := fun type => ⟨type.genericTerm⟩
  pairing := by
    intro source target type substitution term typing
    exact ⟨type.pair_projection substitution term typing,
      type.pair_generic substitution term typing,
      fun candidate projectionEq genericEq =>
        type.pair_unique substitution term typing candidate projectionEq genericEq⟩

end IncidenceCore
