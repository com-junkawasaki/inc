import IncidenceTheory.GraphModel
import IncidenceTheory.ReferenceFoundationHFModel

/-!
  A nontrivial incidence-specific witness for the reference interpretation.

  Finite von Neumann ordinals are constructed by object-language terms in the
  extensional HF model, while their raw representatives live in `hfIncidence`.
  The quotient map agrees with term evaluation, and incidence bisimulation on
  these representatives reflects exactly the encoded natural number.
-/

namespace IncidenceCore.ReferenceFoundation

open IncidenceCore

def Term.successor (term : Term) : Term :=
  .union (.pair term (.pair term term))

def Term.numeral : Nat → Term
  | 0 => .empty
  | n + 1 => (numeral n).successor

theorem Term.evaluate_numeral
    (valuation : Nat → HFRecursiveSet) (n : Nat) :
    (Term.numeral n).evaluate hfRecursiveStructure valuation = hfRecursiveNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Term.numeral, Term.successor, Term.evaluate, ih]
      change hfRecursiveBigUnion
        (hfRecursivePair (hfRecursiveNat n)
          (hfRecursivePair (hfRecursiveNat n) (hfRecursiveNat n))) = _
      rw [hfRecursiveBigUnion_pair]
      exact (hfRecursiveNat_succ_eq n).symm

theorem numeral_raw_quotient_agrees
    (valuation : Nat → HFRecursiveSet) (n : Nat) :
    Quotient.mk hfRecursiveSetoid (HFSet.vonNeumann n) =
      (Term.numeral n).evaluate hfRecursiveStructure valuation := by
  exact (Term.evaluate_numeral valuation n).symm

theorem numeral_zero_is_incidence_unit :
    HFSet.vonNeumann 0 = hfIncidence.unit :=
  hfNatIncidenceEmbedding.zero_is_unit

theorem numeral_successor_has_incidence_boundary (n : Nat) :
    hfIncidence.boundary (HFSet.vonNeumann (n + 1)) =
      hfNatPredecessorBoundary n :=
  hfNatIncidenceEmbedding.successor_boundary n

theorem numeral_incidence_bisim_iff (m n : Nat) :
    approxBisim hfIncidence (HFSet.vonNeumann m) (HFSet.vonNeumann n) ↔
      (Term.numeral m).evaluate hfRecursiveStructure (fun _ => hfRecursiveEmpty) =
        (Term.numeral n).evaluate hfRecursiveStructure (fun _ => hfRecursiveEmpty) := by
  rw [Term.evaluate_numeral, Term.evaluate_numeral,
    hf_vonNeumann_approxBisim_iff_eq]
  exact ⟨fun equal => congrArg hfRecursiveNat equal,
    hfRecursiveNat_injective⟩

structure HFReferenceIncidenceWitness where
  rawEncode : Nat → HFSet
  logicalEncode : Nat → Term
  quotientAgreement : ∀ n,
    Quotient.mk hfRecursiveSetoid (rawEncode n) =
      (logicalEncode n).evaluate hfRecursiveStructure
        (fun _ => hfRecursiveEmpty)
  zeroUnit : rawEncode 0 = hfIncidence.unit
  successorBoundary : ∀ n,
    hfIncidence.boundary (rawEncode (n + 1)) = hfNatPredecessorBoundary n
  bisimulationReflection : ∀ m n,
    approxBisim hfIncidence (rawEncode m) (rawEncode n) ↔
      (logicalEncode m).evaluate hfRecursiveStructure
          (fun _ => hfRecursiveEmpty) =
        (logicalEncode n).evaluate hfRecursiveStructure
          (fun _ => hfRecursiveEmpty)

def hfReferenceIncidenceWitness : HFReferenceIncidenceWitness where
  rawEncode := HFSet.vonNeumann
  logicalEncode := Term.numeral
  quotientAgreement := numeral_raw_quotient_agrees _
  zeroUnit := numeral_zero_is_incidence_unit
  successorBoundary := numeral_successor_has_incidence_boundary
  bisimulationReflection := numeral_incidence_bisim_iff

theorem hfReferenceIncidenceWitness_nontrivial :
    hfReferenceIncidenceWitness.rawEncode 0 ≠
      hfReferenceIncidenceWitness.rawEncode 1 := by
  intro equal
  exact Nat.zero_ne_one (hf_vonNeumann_injective equal)

end IncidenceCore.ReferenceFoundation
