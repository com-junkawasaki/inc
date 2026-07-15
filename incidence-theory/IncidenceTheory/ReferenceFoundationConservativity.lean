import IncidenceTheory.FoundationIncidenceWitness

/-!
  A conservative Inc proof layer over the reference foundation.

  The extension adds closed physical resonance atoms for `hfIncidence` and
  intuitionistic propositional reasoning between reference statements and
  those atoms.  There is deliberately no elimination rule that turns a
  resonance fact into an unrelated set-theoretic assertion.  `forget` maps
  physical atoms to truth, yielding a syntactic retraction and a checked
  conservativity theorem for every embedded reference sentence.
-/

namespace IncidenceCore.ReferenceFoundation.IncProof

open IncidenceCore

inductive Formula where
  | reference : ReferenceFoundation.Formula → Formula
  | resonance : HFSet → HFSet → HFSet → Formula
  | top : Formula
  | bot : Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula

abbrev Context := List Formula

def Formula.forget : Formula → ReferenceFoundation.Formula
  | .reference formula => formula
  | .resonance _ _ _ => .top
  | .top => .top
  | .bot => .bot
  | .and left right => .and left.forget right.forget
  | .or left right => .or left.forget right.forget
  | .imp left right => .imp left.forget right.forget

def Context.forget (context : Context) : ReferenceFoundation.Context :=
  context.map Formula.forget

def encodeContext (context : ReferenceFoundation.Context) : Context :=
  context.map Formula.reference

@[simp] theorem Formula.forget_reference
    (formula : ReferenceFoundation.Formula) :
    (Formula.reference formula).forget = formula := rfl

@[simp] theorem forget_encodeContext
    (context : ReferenceFoundation.Context) :
    (encodeContext context).forget = context := by
  simp [encodeContext, Context.forget, Function.comp_def]

inductive Derives (infinity : InfinitySchema) : Context → Formula → Prop where
  | assumption {context formula} : formula ∈ context →
      Derives infinity context formula
  | referenceRule {context formula} :
      ReferenceFoundation.Derives infinity context formula →
      Derives infinity (encodeContext context) (.reference formula)
  | resonanceRule {context left right output} :
      hfIncidence.resonance left right output →
      Derives infinity context (.resonance left right output)
  | topIntro {context} : Derives infinity context .top
  | botElim {context formula} : Derives infinity context .bot →
      Derives infinity context formula
  | andIntro {context left right} :
      Derives infinity context left → Derives infinity context right →
      Derives infinity context (.and left right)
  | andElimLeft {context left right} :
      Derives infinity context (.and left right) → Derives infinity context left
  | andElimRight {context left right} :
      Derives infinity context (.and left right) → Derives infinity context right
  | orIntroLeft {context left right} : Derives infinity context left →
      Derives infinity context (.or left right)
  | orIntroRight {context left right} : Derives infinity context right →
      Derives infinity context (.or left right)
  | orElim {context left right result} :
      Derives infinity context (.or left right) →
      Derives infinity (left :: context) result →
      Derives infinity (right :: context) result →
      Derives infinity context result
  | impIntro {context left right} : Derives infinity (left :: context) right →
      Derives infinity context (.imp left right)
  | impElim {context left right} : Derives infinity context (.imp left right) →
      Derives infinity context left → Derives infinity context right

theorem encode_derivation_sound {infinity : InfinitySchema}
    {context : ReferenceFoundation.Context}
    {formula : ReferenceFoundation.Formula}
    (proof : ReferenceFoundation.Derives infinity context formula) :
    Derives infinity (encodeContext context) (.reference formula) :=
  Derives.referenceRule proof

theorem forget_derivation {infinity : InfinitySchema}
    {context : Context} {formula : Formula}
    (proof : Derives infinity context formula) :
    ReferenceFoundation.Derives infinity context.forget formula.forget := by
  induction proof with
  | assumption member =>
      exact ReferenceFoundation.Derives.assumption
        (List.mem_map_of_mem member)
  | referenceRule proof =>
      simpa only [forget_encodeContext, Formula.forget_reference] using proof
  | resonanceRule physical =>
      exact ReferenceFoundation.Derives.topIntro
  | topIntro => exact ReferenceFoundation.Derives.topIntro
  | botElim premise ih => exact ReferenceFoundation.Derives.botElim ih
  | andIntro left right ihLeft ihRight =>
      exact ReferenceFoundation.Derives.andIntro ihLeft ihRight
  | andElimLeft premise ih => exact ReferenceFoundation.Derives.andElimLeft ih
  | andElimRight premise ih => exact ReferenceFoundation.Derives.andElimRight ih
  | orIntroLeft premise ih => exact ReferenceFoundation.Derives.orIntroLeft ih
  | orIntroRight premise ih => exact ReferenceFoundation.Derives.orIntroRight ih
  | orElim disjunction left right ihDisjunction ihLeft ihRight =>
      exact ReferenceFoundation.Derives.orElim ihDisjunction ihLeft ihRight
  | impIntro premise ih => exact ReferenceFoundation.Derives.impIntro ih
  | impElim implication premise ihImplication ihPremise =>
      exact ReferenceFoundation.Derives.impElim ihImplication ihPremise

theorem encode_conservative {infinity : InfinitySchema}
    {formula : ReferenceFoundation.Formula}
    (proof : Derives infinity [] (.reference formula)) :
    ReferenceFoundation.Derives infinity [] formula := by
  exact forget_derivation proof

theorem encode_derivation_iff {infinity : InfinitySchema}
    (formula : ReferenceFoundation.Formula) :
    Derives infinity [] (.reference formula) ↔
      ReferenceFoundation.Derives infinity [] formula := by
  exact ⟨encode_conservative, encode_derivation_sound⟩

def oneRaw : HFSet := HFSet.vonNeumann 1

theorem one_resonates_with_unit :
    hfIncidence.resonance hfIncidence.unit oneRaw oneRaw :=
  resonance_left_unit hfIncidence oneRaw

theorem derives_nontrivial_resonance :
    Derives finiteInfinitySchema []
      (.resonance hfIncidence.unit oneRaw oneRaw) :=
  Derives.resonanceRule one_resonates_with_unit

theorem resonance_atom_not_reference
    (formula : ReferenceFoundation.Formula) :
    Formula.resonance hfIncidence.unit oneRaw oneRaw ≠ .reference formula := by
  intro equal
  cases equal

structure ConservativeIncExtensionCertificate where
  preserve : ∀ {formula},
    ReferenceFoundation.Derives finiteInfinitySchema [] formula →
      Derives finiteInfinitySchema [] (.reference formula)
  reflect : ∀ {formula},
    Derives finiteInfinitySchema [] (.reference formula) →
      ReferenceFoundation.Derives finiteInfinitySchema [] formula
  physicalWitness : Derives finiteInfinitySchema []
    (.resonance hfIncidence.unit oneRaw oneRaw)

def conservativeIncExtension : ConservativeIncExtensionCertificate where
  preserve := encode_derivation_sound
  reflect := encode_conservative
  physicalWitness := derives_nontrivial_resonance

end IncidenceCore.ReferenceFoundation.IncProof
