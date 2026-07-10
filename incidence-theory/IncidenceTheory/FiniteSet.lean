/-!
  Extensional finite sets over an arbitrary finite basis `Fin n`.
  This is the scalable successor to the concrete two-atom set fragment.
-/

namespace IncidenceCore

structure BitSet (n : Nat) where
  contains : Fin n → Bool

def bitSetEmpty (n : Nat) : BitSet n := { contains := fun _ => false }

def bitSetFull (n : Nat) : BitSet n := { contains := fun _ => true }

def bitSetUnion {n : Nat} (s t : BitSet n) : BitSet n :=
  { contains := fun i => s.contains i || t.contains i }

def bitSetInter {n : Nat} (s t : BitSet n) : BitSet n :=
  { contains := fun i => s.contains i && t.contains i }

def bitSetComplement {n : Nat} (s : BitSet n) : BitSet n :=
  { contains := fun i => !s.contains i }

def bitSetDifference {n : Nat} (s t : BitSet n) : BitSet n :=
  bitSetInter s (bitSetComplement t)

def bitSetBoundary {n : Nat} (s : BitSet n) : List (Fin n) :=
  (List.finRange n).filter s.contains

theorem bitSet_mem_finRange {n : Nat} (i : Fin n) : i ∈ List.finRange n := by
  have hi : i.val < (List.finRange n).length := by
    simp
  have hmem := List.getElem_mem (l := List.finRange n) hi
  simpa using hmem

theorem bitSet_mem_boundary_iff {n : Nat} (s : BitSet n) (i : Fin n) :
    i ∈ bitSetBoundary s ↔ s.contains i = true := by
  constructor
  · intro h
    exact (List.mem_filter.mp h).right
  · intro h
    exact List.mem_filter.mpr ⟨bitSet_mem_finRange i, h⟩

theorem bitSet_ext {n : Nat} (s t : BitSet n)
    (h : ∀ i, s.contains i = t.contains i) : s = t := by
  cases s with
  | mk sc =>
    cases t with
    | mk tc =>
      congr
      funext i
      exact h i

theorem bitSet_boundary_extensional {n : Nat} {s t : BitSet n}
    (hboundary : bitSetBoundary s = bitSetBoundary t) : s = t := by
  apply bitSet_ext
  intro i
  have hmem : i ∈ bitSetBoundary s ↔ i ∈ bitSetBoundary t := by
    rw [hboundary]
  rw [bitSet_mem_boundary_iff, bitSet_mem_boundary_iff] at hmem
  cases hs : s.contains i <;> cases ht : t.contains i <;>
    simp [hs, ht] at hmem ⊢

theorem bitSet_boundary_eq_iff {n : Nat} (s t : BitSet n) :
    bitSetBoundary s = bitSetBoundary t ↔ s = t := by
  constructor
  · exact bitSet_boundary_extensional
  · intro h
    subst t
    rfl

theorem bitSetUnion_contains {n : Nat} (s t : BitSet n) (i : Fin n) :
    (bitSetUnion s t).contains i = (s.contains i || t.contains i) := rfl

theorem bitSetInter_contains {n : Nat} (s t : BitSet n) (i : Fin n) :
    (bitSetInter s t).contains i = (s.contains i && t.contains i) := rfl

theorem bitSetComplement_contains {n : Nat} (s : BitSet n) (i : Fin n) :
    (bitSetComplement s).contains i = !s.contains i := rfl

theorem bitSetDifference_contains {n : Nat} (s t : BitSet n) (i : Fin n) :
    (bitSetDifference s t).contains i = (s.contains i && !t.contains i) := rfl

theorem bitSetUnion_empty_left {n : Nat} (s : BitSet n) :
    bitSetUnion (bitSetEmpty n) s = s := by
  apply bitSet_ext
  intro i
  cases h : s.contains i <;> simp [bitSetUnion, bitSetEmpty, h]

theorem bitSetUnion_empty_right {n : Nat} (s : BitSet n) :
    bitSetUnion s (bitSetEmpty n) = s := by
  apply bitSet_ext
  intro i
  cases h : s.contains i <;> simp [bitSetUnion, bitSetEmpty, h]

theorem bitSetUnion_commutative {n : Nat} (s t : BitSet n) :
    bitSetUnion s t = bitSetUnion t s := by
  apply bitSet_ext
  intro i
  cases hs : s.contains i <;> cases ht : t.contains i <;> simp [bitSetUnion, hs, ht]

theorem bitSetUnion_associative {n : Nat} (s t u : BitSet n) :
    bitSetUnion (bitSetUnion s t) u = bitSetUnion s (bitSetUnion t u) := by
  apply bitSet_ext
  intro i
  cases hs : s.contains i <;> cases ht : t.contains i <;> cases hu : u.contains i <;>
    simp [bitSetUnion, hs, ht, hu]

theorem bitSetUnion_idempotent {n : Nat} (s : BitSet n) : bitSetUnion s s = s := by
  apply bitSet_ext
  intro i
  cases h : s.contains i <;> simp [bitSetUnion, h]

theorem bitSetInter_empty_left {n : Nat} (s : BitSet n) :
    bitSetInter (bitSetEmpty n) s = bitSetEmpty n := by
  apply bitSet_ext
  intro i
  simp [bitSetInter, bitSetEmpty]

theorem bitSetInter_full_left {n : Nat} (s : BitSet n) :
    bitSetInter (bitSetFull n) s = s := by
  apply bitSet_ext
  intro i
  cases h : s.contains i <;> simp [bitSetInter, bitSetFull, h]

theorem bitSetInter_commutative {n : Nat} (s t : BitSet n) :
    bitSetInter s t = bitSetInter t s := by
  apply bitSet_ext
  intro i
  cases hs : s.contains i <;> cases ht : t.contains i <;> simp [bitSetInter, hs, ht]

theorem bitSetComplement_involutive {n : Nat} (s : BitSet n) :
    bitSetComplement (bitSetComplement s) = s := by
  apply bitSet_ext
  intro i
  cases h : s.contains i <;> simp [bitSetComplement, h]

theorem bitSetUnion_complement {n : Nat} (s : BitSet n) :
    bitSetUnion s (bitSetComplement s) = bitSetFull n := by
  apply bitSet_ext
  intro i
  cases s.contains i <;> simp [bitSetUnion, bitSetComplement, bitSetFull]

theorem bitSetInter_union_distrib {n : Nat} (s t u : BitSet n) :
    bitSetInter s (bitSetUnion t u) =
      bitSetUnion (bitSetInter s t) (bitSetInter s u) := by
  apply bitSet_ext
  intro i
  cases hs : s.contains i <;> cases ht : t.contains i <;> cases hu : u.contains i <;>
    simp [bitSetInter, bitSetUnion, hs, ht, hu]

theorem bitSetComplement_union {n : Nat} (s t : BitSet n) :
    bitSetComplement (bitSetUnion s t) =
      bitSetInter (bitSetComplement s) (bitSetComplement t) := by
  apply bitSet_ext
  intro i
  cases hs : s.contains i <;> cases ht : t.contains i <;>
    simp [bitSetComplement, bitSetInter, bitSetUnion, hs, ht]

theorem bitSetBoundary_union_membership {n : Nat} (s t : BitSet n) (i : Fin n) :
    i ∈ bitSetBoundary (bitSetUnion s t) ↔
      i ∈ bitSetBoundary s ∨ i ∈ bitSetBoundary t := by
  rw [bitSet_mem_boundary_iff, bitSet_mem_boundary_iff, bitSet_mem_boundary_iff]
  cases hs : s.contains i <;> cases ht : t.contains i <;>
    simp [bitSetUnion, hs, ht]

theorem bitSetBoundary_inter_membership {n : Nat} (s t : BitSet n) (i : Fin n) :
    i ∈ bitSetBoundary (bitSetInter s t) ↔
      i ∈ bitSetBoundary s ∧ i ∈ bitSetBoundary t := by
  rw [bitSet_mem_boundary_iff, bitSet_mem_boundary_iff, bitSet_mem_boundary_iff]
  cases hs : s.contains i <;> cases ht : t.contains i <;>
    simp [bitSetInter, hs, ht]

theorem bitSetBoundary_complement_membership {n : Nat} (s : BitSet n) (i : Fin n) :
    i ∈ bitSetBoundary (bitSetComplement s) ↔ ¬ i ∈ bitSetBoundary s := by
  rw [bitSet_mem_boundary_iff, bitSet_mem_boundary_iff]
  cases hs : s.contains i <;> simp [bitSetComplement, hs]

end IncidenceCore
