import IncidenceTheory.FoundationCompletion
import IncidenceTheory.ReferenceFoundationConservativity
import IncidenceTheory.ReferenceFoundationLayeredCanonical
import IncidenceTheory.ReferenceFoundationZFModel

/-!
  Completion certificates for the fixed reference fragments in
  ADR-2607141850.  The final certificate keeps the precise constant-free
  boundary required to separate object syntax from auxiliary Henkin constants.
-/

namespace IncidenceCore.ReferenceFoundation

open IncProof

structure FiniteFoundationCertificate where
  referenceModel : Model finiteInfinitySchema
  referenceConsistent : Theory.Consistent { infinity := finiteInfinitySchema }
  conservativeExtension : ConservativeIncExtensionCertificate
  incidenceWitness : HFReferenceIncidenceWitness
  incidenceWitnessNontrivial :
    incidenceWitness.rawEncode 0 ≠ incidenceWitness.rawEncode 1

def finiteFoundationCertificate : FiniteFoundationCertificate where
  referenceModel := hfRecursiveModel
  referenceConsistent := hfReferenceFoundation_consistent
  conservativeExtension := conservativeIncExtension
  incidenceWitness := hfReferenceIncidenceWitness
  incidenceWitnessNontrivial := hfReferenceIncidenceWitness_nontrivial

theorem finiteFoundation_preserves_and_reflects
    (formula : Formula) :
    IncProof.Derives finiteInfinitySchema [] (.reference formula) ↔
      Derives finiteInfinitySchema [] formula :=
  encode_derivation_iff formula

theorem referenceFoundation_kripke_complete
    {infinity : InfinitySchema} {context : Context} {formula : Formula}
    (contextFree : ∀ item ∈ context, item.ConstFree)
    (formulaFree : formula.ConstFree)
    (entails : LayeredCanonical.KripkeEntails infinity context formula) :
    Derives infinity context formula :=
  LayeredCanonical.complete contextFree formulaFree entails

structure CompleteFoundationCertificate where
  finiteFragment : FiniteFoundationCertificate
  actualInfinityModel : Model actualInfinitySchema
  actualInfinityConsistent :
    Theory.Consistent { infinity := actualInfinitySchema }
  kripkeComplete : ∀ {infinity : InfinitySchema}
      {context : Context} {formula : Formula},
    (∀ item ∈ context, item.ConstFree) → formula.ConstFree →
    LayeredCanonical.KripkeEntails infinity context formula →
    Derives infinity context formula

noncomputable def completeFoundationCertificate : CompleteFoundationCertificate where
  finiteFragment := finiteFoundationCertificate
  actualInfinityModel := zfActualInfinityModel
  actualInfinityConsistent := zfActualInfinityFoundation_consistent
  kripkeComplete := referenceFoundation_kripke_complete

end IncidenceCore.ReferenceFoundation
