import IncidenceTheory.ReferenceFoundationLogic

/-! Structural metatheory for the reference natural-deduction calculus. -/

namespace IncidenceCore.ReferenceFoundation

theorem Axiom.substitution_closed {infinity : InfinitySchema}
    {formula : Formula} (valid : Axiom infinity formula)
    (substitution : Nat → Term) :
    formula.substitute substitution = formula := by
  cases valid with
  | extensionality => rfl
  | emptySet => rfl
  | pairing => rfl
  | unionSet => rfl
  | powerSet => rfl
  | boundedSeparation bounded scopedBody constFree closed => exact closed substitution
  | infinity => exact infinity.substitution_closed substitution

theorem Derives.weaken {infinity : InfinitySchema}
    {source target : Context} {formula : Formula}
    (proof : Derives infinity source formula)
    (included : ∀ {item}, item ∈ source → item ∈ target) :
    Derives infinity target formula := by
  induction proof generalizing target with
  | assumption member =>
      exact Derives.assumption (included member)
  | «axiom» valid => exact Derives.axiom valid
  | topIntro => exact Derives.topIntro
  | botElim premise ih => exact Derives.botElim (ih included)
  | andIntro left right ihLeft ihRight =>
      exact Derives.andIntro (ihLeft included) (ihRight included)
  | andElimLeft premise ih => exact Derives.andElimLeft (ih included)
  | andElimRight premise ih => exact Derives.andElimRight (ih included)
  | orIntroLeft premise ih => exact Derives.orIntroLeft (ih included)
  | orIntroRight premise ih => exact Derives.orIntroRight (ih included)
  | orElim disjunction left right ihDisjunction ihLeft ihRight =>
      exact Derives.orElim (ihDisjunction included)
        (ihLeft (target := _ :: target) (by
          intro item member
          simp only [List.mem_cons] at member ⊢
          exact member.elim Or.inl (fun tail => Or.inr (included tail))))
        (ihRight (target := _ :: target) (by
          intro item member
          simp only [List.mem_cons] at member ⊢
          exact member.elim Or.inl (fun tail => Or.inr (included tail))))
  | impIntro premise ih =>
      exact Derives.impIntro
        (ih (target := _ :: target) (by
          intro item member
          simp only [List.mem_cons] at member ⊢
          exact member.elim Or.inl (fun tail => Or.inr (included tail))))
  | impElim implication premise ihImplication ihPremise =>
      exact Derives.impElim (ihImplication included) (ihPremise included)
  | allIntro premise ih =>
      apply Derives.allIntro
      apply ih
      intro item member
      rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      exact List.mem_map_of_mem (included originalMember)
  | allElim premise term ih =>
      exact Derives.allElim (ih included) term
  | exIntro term premise ih =>
      exact Derives.exIntro term (ih included)
  | exElim existential branch ihExistential ihBranch =>
      apply Derives.exElim (ihExistential included)
      apply ihBranch
      intro item member
      simp only [List.mem_cons] at member ⊢
      rcases member with rfl | member
      · exact Or.inl rfl
      · rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
        exact Or.inr (List.mem_map_of_mem (included originalMember))

theorem Derives.weaken_head {infinity : InfinitySchema}
    {context : Context} {formula : Formula}
    (proof : Derives infinity context formula) (extra : Formula) :
    Derives infinity (extra :: context) formula :=
  proof.weaken (fun member => List.mem_cons_of_mem extra member)

theorem Derives.weaken_prefix {infinity : InfinitySchema}
    {context : Context} {formula : Formula}
    (proof : Derives infinity context formula) (extraContext : Context) :
    Derives infinity (extraContext ++ context) formula := by
  induction extraContext with
  | nil => simpa using proof
  | cons head tail ih =>
      exact Derives.weaken_head ih head

theorem Derives.cut {infinity : InfinitySchema}
    {context : Context} {cutFormula result : Formula}
    (cutProof : Derives infinity context cutFormula)
    (bodyProof : Derives infinity (cutFormula :: context) result) :
    Derives infinity context result :=
  Derives.impElim (Derives.impIntro bodyProof) cutProof

theorem Derives.substitute {infinity : InfinitySchema}
    {context : Context} {formula : Formula}
    (proof : Derives infinity context formula)
    (substitution : Nat → Term) :
    Derives infinity (context.map (Formula.substitute substitution))
      (formula.substitute substitution) := by
  induction proof generalizing substitution with
  | assumption member =>
      exact Derives.assumption (List.mem_map_of_mem member)
  | «axiom» valid =>
      rw [valid.substitution_closed substitution]
      exact Derives.axiom valid
  | topIntro => exact Derives.topIntro
  | botElim premise ih => exact Derives.botElim (ih substitution)
  | andIntro left right ihLeft ihRight =>
      exact Derives.andIntro (ihLeft substitution) (ihRight substitution)
  | andElimLeft premise ih => exact Derives.andElimLeft (ih substitution)
  | andElimRight premise ih => exact Derives.andElimRight (ih substitution)
  | orIntroLeft premise ih => exact Derives.orIntroLeft (ih substitution)
  | orIntroRight premise ih => exact Derives.orIntroRight (ih substitution)
  | orElim disjunction left right ihDisjunction ihLeft ihRight =>
      exact Derives.orElim (ihDisjunction substitution)
        (ihLeft substitution) (ihRight substitution)
  | impIntro premise ih =>
      exact Derives.impIntro (ih substitution)
  | impElim implication premise ihImplication ihPremise =>
      exact Derives.impElim (ihImplication substitution)
        (ihPremise substitution)
  | allIntro premise ih =>
      apply Derives.allIntro
      rw [← Context.rename_succ_substitute_lift]
      exact ih (liftSubstitution substitution)
  | allElim premise term ih =>
      have instantiated := Derives.allElim (ih substitution)
        (term.substitute substitution)
      rw [Formula.substitute_instantiate]
      exact instantiated
  | exIntro term premise ih =>
      apply Derives.exIntro (term.substitute substitution)
      rw [← Formula.substitute_instantiate]
      exact ih substitution
  | exElim existential branch ihExistential ihBranch =>
      apply Derives.exElim (ihExistential substitution)
      rw [← Formula.rename_succ_substitute_lift]
      rw [← Context.rename_succ_substitute_lift]
      exact ihBranch (liftSubstitution substitution)

end IncidenceCore.ReferenceFoundation
