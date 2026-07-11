/-!
  Hereditarily finite set syntax.  `HFSet` is a well-founded presentation;
  extensional equality is stated separately because `insert` retains order and
  duplicate syntax.
-/

namespace IncidenceCore

inductive HFSet where
  | empty
  | insert (head tail : HFSet)
deriving DecidableEq, Repr

def HFSet.rank : HFSet → Nat
  | .empty => 0
  | .insert head tail => Nat.max head.rank tail.rank + 1

inductive HFMember : HFSet → HFSet → Prop where
  | head (x tail : HFSet) : HFMember x (.insert x tail)
  | tail {x head tail : HFSet} : HFMember x tail → HFMember x (.insert head tail)

theorem hf_not_member_empty {x : HFSet} : ¬ HFMember x .empty := by
  intro h
  cases h

theorem hf_member_insert {x head tail : HFSet} :
    HFMember x (.insert head tail) ↔ x = head ∨ HFMember x tail := by
  constructor
  · intro h
    cases h with
    | head tail => exact Or.inl rfl
    | tail h => exact Or.inr h
  · rintro (rfl | h)
    · exact HFMember.head _ _
    · exact HFMember.tail h

theorem hf_member_rank_lt {x s : HFSet} : HFMember x s → x.rank < s.rank := by
  intro h
  induction h with
  | head tail =>
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  | tail h ih =>
    exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt ih) (Nat.le_max_right _ _))

def HFSet.union : HFSet → HFSet → HFSet
  | .empty, t => t
  | .insert head tail, t => .insert head (tail.union t)

def HFSet.bigUnion : HFSet → HFSet
  | .empty => .empty
  | .insert head tail => head.union tail.bigUnion

def HFSet.insertImage (head : HFSet) : HFSet → HFSet
  | .empty => .empty
  | .insert member tail => .insert (.insert head member) (insertImage head tail)

/- A finite powerset presentation.  Each member of `power` is either an old
   subset candidate or is obtained by adjoining the new head. -/
def HFSet.power : HFSet → HFSet
  | .empty => .insert .empty .empty
  | .insert head tail => (power tail).union (insertImage head (power tail))

/- Remove every syntactic occurrence of an element.  This auxiliary operation
   lets the finite powerset presentation account for duplicate syntax up to
   extensional equality. -/
def HFSet.erase (a : HFSet) : HFSet → HFSet
  | .empty => .empty
  | .insert head tail =>
      if head = a then erase a tail else .insert head (erase a tail)

def HFSet.pair (s t : HFSet) : HFSet := .insert s (.insert t .empty)

def HFSet.singleton (s : HFSet) : HFSet := .insert s .empty

/- Kuratowski's representation `⟨s,t⟩ = {{s},{s,t}}`. -/
def HFSet.orderedPair (s t : HFSet) : HFSet :=
  (singleton s).pair (s.pair t)

def HFSet.pairWith (left : HFSet) : HFSet → HFSet
  | .empty => .empty
  | .insert right tail => .insert (orderedPair left right) (pairWith left tail)

def HFSet.product : HFSet → HFSet → HFSet
  | .empty, _ => .empty
  | .insert head tail, right => (pairWith head right).union (product tail right)

/- Von Neumann naturals: `n + 1 = n ∪ {n}` is represented by inserting `n`
   into its own member list. -/
def HFSet.vonNeumann : Nat → HFSet
  | 0 => .empty
  | n + 1 => .insert (vonNeumann n) (vonNeumann n)

theorem hf_member_vonNeumann_succ {x : HFSet} {n : Nat} :
    HFMember x (HFSet.vonNeumann (n + 1)) ↔
      x = HFSet.vonNeumann n ∨ HFMember x (HFSet.vonNeumann n) := by
  exact hf_member_insert

theorem hf_member_pair {x s t : HFSet} :
    HFMember x (s.pair t) ↔ x = s ∨ x = t := by
  rw [HFSet.pair, hf_member_insert, hf_member_insert]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · rcases h with h | h
      · exact Or.inr h
      · exact False.elim (hf_not_member_empty h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem hf_member_singleton {x s : HFSet} :
    HFMember x s.singleton ↔ x = s := by
  rw [HFSet.singleton, hf_member_insert]
  constructor
  · rintro (h | hempty)
    · exact h
    · exact False.elim (hf_not_member_empty hempty)
  · intro h
    exact Or.inl h

theorem hf_member_pairWith {x left right : HFSet} :
    HFMember x (HFSet.pairWith left right) ↔
      ∃ member, HFMember member right ∧ x = HFSet.orderedPair left member := by
  induction right with
  | empty =>
    constructor
    · intro h
      exact False.elim (hf_not_member_empty h)
    · rintro ⟨member, hmember, _⟩
      exact False.elim (hf_not_member_empty hmember)
  | insert head tail head_ih tail_ih =>
    rw [HFSet.pairWith, hf_member_insert, tail_ih]
    constructor
    · rintro (h | ⟨member, hmember, hpair⟩)
      · exact ⟨head, HFMember.head _ _, h⟩
      · exact ⟨member, HFMember.tail hmember, hpair⟩
    · rintro ⟨member, hmember, hpair⟩
      rcases hf_member_insert.mp hmember with rfl | hmember
      · exact Or.inl hpair
      · exact Or.inr ⟨member, hmember, hpair⟩

def HFSet.filter (p : HFSet → Bool) : HFSet → HFSet
  | .empty => .empty
  | .insert head tail =>
      if p head then .insert head (tail.filter p) else tail.filter p

theorem hf_member_filter_iff {p : HFSet → Bool} {x s : HFSet} :
    HFMember x (s.filter p) ↔ HFMember x s ∧ p x = true := by
  induction s with
  | empty =>
    constructor
    · intro h
      change HFMember x .empty at h
      exact False.elim (hf_not_member_empty h)
    · rintro ⟨h, _⟩
      exact False.elim (hf_not_member_empty h)
  | insert head tail head_ih tail_ih =>
    by_cases hhead : p head = true
    · rw [HFSet.filter, if_pos hhead, hf_member_insert, tail_ih, hf_member_insert]
      constructor
      · rintro (rfl | h)
        · exact ⟨Or.inl rfl, hhead⟩
        · exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h, hp⟩
        rcases h with rfl | h
        · exact Or.inl rfl
        · exact Or.inr ⟨h, hp⟩
    · rw [HFSet.filter, if_neg hhead, tail_ih, hf_member_insert]
      constructor
      · rintro ⟨h, hp⟩
        exact ⟨Or.inr h, hp⟩
      · rintro ⟨h, hp⟩
        rcases h with rfl | h
        · exact False.elim (hhead hp)
        · exact ⟨h, hp⟩

theorem hf_member_union {x s t : HFSet} :
    HFMember x (s.union t) ↔ HFMember x s ∨ HFMember x t := by
  induction s with
  | empty =>
    constructor
    · intro h
      exact Or.inr h
    · rintro (h | h)
      · exact False.elim (hf_not_member_empty h)
      · exact h
  | insert head tail head_ih tail_ih =>
    simp only [HFSet.union, hf_member_insert, tail_ih]
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · rcases h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rintro (h | h)
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/- Finite Cartesian product has the expected ordered-pair membership law. -/
theorem hf_member_product {x left right : HFSet} :
    HFMember x (HFSet.product left right) ↔
      ∃ leftMember, HFMember leftMember left ∧
        ∃ rightMember, HFMember rightMember right ∧
          x = HFSet.orderedPair leftMember rightMember := by
  induction left with
  | empty =>
    constructor
    · intro h
      exact False.elim (hf_not_member_empty h)
    · rintro ⟨member, hmember, _⟩
      exact False.elim (hf_not_member_empty hmember)
  | insert head tail head_ih tail_ih =>
    rw [HFSet.product, hf_member_union, hf_member_pairWith, tail_ih]
    constructor
    · rintro (⟨rightMember, hright, hpair⟩ |
        ⟨leftMember, hleft, rightMember, hright, hpair⟩)
      · exact ⟨head, HFMember.head _ _, rightMember, hright, hpair⟩
      · exact ⟨leftMember, HFMember.tail hleft, rightMember, hright, hpair⟩
    · rintro ⟨leftMember, hleft, rightMember, hright, hpair⟩
      rcases hf_member_insert.mp hleft with rfl | hleft
      · exact Or.inl ⟨rightMember, hright, hpair⟩
      · exact Or.inr ⟨leftMember, hleft, rightMember, hright, hpair⟩

theorem hf_member_bigUnion {x s : HFSet} :
    HFMember x s.bigUnion ↔ ∃ y, HFMember y s ∧ HFMember x y := by
  induction s with
  | empty =>
    constructor
    · intro h
      exact False.elim (hf_not_member_empty h)
    · rintro ⟨y, hy, _⟩
      exact False.elim (hf_not_member_empty hy)
  | insert head tail head_ih tail_ih =>
    rw [HFSet.bigUnion, hf_member_union]
    constructor
    · rintro (hx | hx)
      · exact ⟨head, hf_member_insert.mpr (Or.inl rfl), hx⟩
      · rcases tail_ih.mp hx with ⟨y, hy, hxy⟩
        exact ⟨y, hf_member_insert.mpr (Or.inr hy), hxy⟩
    · rintro ⟨y, hy, hxy⟩
      rcases hf_member_insert.mp hy with rfl | hy
      · exact Or.inl hxy
      · exact Or.inr (tail_ih.mpr ⟨y, hy, hxy⟩)

theorem hf_member_insertImage {x head s : HFSet} :
    HFMember x (HFSet.insertImage head s) ↔
      ∃ y, HFMember y s ∧ x = .insert head y := by
  induction s with
  | empty =>
    simp [HFSet.insertImage, hf_not_member_empty]
  | insert member tail member_ih tail_ih =>
    rw [HFSet.insertImage, hf_member_insert, tail_ih]
    constructor
    · rintro (rfl | ⟨y, hy, hxy⟩)
      · exact ⟨member, HFMember.head _ _, rfl⟩
      · exact ⟨y, HFMember.tail hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      rcases hf_member_insert.mp hy with rfl | hy
      · exact Or.inl hxy
      · exact Or.inr ⟨y, hy, hxy⟩

theorem hf_member_power_insert {x head tail : HFSet} :
    HFMember x (HFSet.power (.insert head tail)) ↔
      HFMember x (HFSet.power tail) ∨
        ∃ y, HFMember y (HFSet.power tail) ∧ x = .insert head y := by
  rw [HFSet.power, hf_member_union, hf_member_insertImage]

theorem hf_member_erase (a x s : HFSet) :
    HFMember x (HFSet.erase a s) ↔ HFMember x s ∧ x ≠ a := by
  induction s with
  | empty =>
    constructor
    · intro h
      exact False.elim (hf_not_member_empty h)
    · rintro ⟨h, _⟩
      exact False.elim (hf_not_member_empty h)
  | insert head tail head_ih tail_ih =>
    by_cases hhead : head = a
    · subst head
      simp only [HFSet.erase, ite_true]
      rw [tail_ih, hf_member_insert]
      constructor
      · rintro ⟨hxt, hxa⟩
        exact ⟨Or.inr hxt, hxa⟩
      · rintro ⟨hxa | hxt, hne⟩
        · exact False.elim (hne hxa)
        · exact ⟨hxt, hne⟩
    · simp only [HFSet.erase, if_neg hhead]
      rw [hf_member_insert, tail_ih, hf_member_insert]
      constructor
      · rintro (rfl | ⟨hxt, hxa⟩)
        · exact ⟨Or.inl rfl, hhead⟩
        · exact ⟨Or.inr hxt, hxa⟩
      · rintro ⟨hxa | hxt, hne⟩
        · exact Or.inl hxa
        · exact Or.inr ⟨hxt, hne⟩

def HFSubset (s t : HFSet) : Prop :=
  ∀ x, HFMember x s → HFMember x t

theorem hf_power_member_subset {u s : HFSet} :
    HFMember u s.power → HFSubset u s := by
  induction s generalizing u with
  | empty =>
    intro hu x hx
    have hcases : u = .empty ∨ HFMember u .empty := by
      simpa [HFSet.power] using (hf_member_insert.mp hu)
    rcases hcases with rfl | hu
    · exact False.elim (hf_not_member_empty hx)
    · exact False.elim (hf_not_member_empty hu)
  | insert head tail head_ih tail_ih =>
    intro hu z hz
    rcases hf_member_power_insert.mp hu with hOld | ⟨v, hv, huEq⟩
    · exact HFMember.tail (tail_ih hOld z hz)
    · subst u
      rcases hf_member_insert.mp hz with rfl | hz
      ·
        exact HFMember.head _ _
      ·
        exact HFMember.tail (tail_ih hv z hz)

def HFExtensionalEq (s t : HFSet) : Prop :=
  ∀ x, HFMember x s ↔ HFMember x t

theorem hfExtensionalEq_refl (s : HFSet) : HFExtensionalEq s s := fun _ => Iff.rfl

theorem hfExtensionalEq_symm {s t : HFSet} :
    HFExtensionalEq s t → HFExtensionalEq t s := by
  intro h x
  exact (h x).symm

theorem hfExtensionalEq_trans {r s t : HFSet} :
    HFExtensionalEq r s → HFExtensionalEq s t → HFExtensionalEq r t := by
  intro hrs hst x
  exact Iff.trans (hrs x) (hst x)

/- Finite powerset completeness, stated at the correct extensional level:
   every syntactic subset has an extensionally equal representative in the
   explicitly enumerated powerset. -/
theorem hf_power_complete_extensional {u s : HFSet} :
    HFSubset u s → ∃ v, HFMember v s.power ∧ HFExtensionalEq u v := by
  induction s generalizing u with
  | empty =>
    intro hus
    refine ⟨.empty, ?_, ?_⟩
    · exact HFMember.head _ _
    · intro x
      constructor
      · intro hx
        exact False.elim (hf_not_member_empty (hus x hx))
      · intro hx
        exact False.elim (hf_not_member_empty hx)
  | insert head tail head_ih tail_ih =>
    intro hus
    by_cases hhu : HFMember head u
    · have herase : HFSubset (HFSet.erase head u) tail := by
        intro x hx
        rcases (hf_member_erase head x u).mp hx with ⟨hxu, hxne⟩
        rcases hf_member_insert.mp (hus x hxu) with hxeq | hxt
        · exact False.elim (hxne hxeq)
        · exact hxt
      rcases tail_ih herase with ⟨v, hv, huv⟩
      refine ⟨.insert head v, (hf_member_power_insert.mpr (Or.inr ⟨v, hv, rfl⟩)), ?_⟩
      intro x
      constructor
      · intro hxu
        by_cases hxeq : x = head
        · exact hf_member_insert.mpr (Or.inl hxeq)
        · exact hf_member_insert.mpr (Or.inr ((huv x).mp
            ((hf_member_erase head x u).mpr ⟨hxu, hxeq⟩)))
      · intro hxv
        rcases hf_member_insert.mp hxv with hxeq | hxv
        · subst x
          exact hhu
        · have hxerase : HFMember x (HFSet.erase head u) := (huv x).mpr hxv
          exact (hf_member_erase head x u).mp hxerase |>.left
    · have htail : HFSubset u tail := by
        intro x hxu
        rcases hf_member_insert.mp (hus x hxu) with hxeq | hxt
        · exact False.elim (hhu (by simpa [hxeq] using hxu))
        · exact hxt
      rcases tail_ih htail with ⟨v, hv, huv⟩
      exact ⟨v, (hf_member_power_insert.mpr (Or.inl hv)), huv⟩

def hfSetoid : Setoid HFSet where
  r := HFExtensionalEq
  iseqv :=
    { refl := hfExtensionalEq_refl
      symm := by intro s t; exact hfExtensionalEq_symm
      trans := by intro r s t; exact hfExtensionalEq_trans }

abbrev HFExtensionalSet := Quotient hfSetoid

theorem hf_extensional_quotient_sound {s t : HFSet} (h : HFExtensionalEq s t) :
    (Quotient.mk hfSetoid s : HFExtensionalSet) = Quotient.mk hfSetoid t :=
  Quotient.sound h

theorem hf_union_preserves_extensional_eq {s s' t t' : HFSet}
    (hs : HFExtensionalEq s s') (ht : HFExtensionalEq t t') :
    HFExtensionalEq (s.union t) (s'.union t') := by
  intro x
  rw [hf_member_union, hf_member_union, hs x, ht x]

def hfExtensionalUnion (s t : HFExtensionalSet) : HFExtensionalSet :=
  Quotient.liftOn₂ s t
    (fun s t => Quotient.mk hfSetoid (s.union t))
    (by
      intro s t s' t' hs ht
      exact hf_extensional_quotient_sound (hf_union_preserves_extensional_eq hs ht))

theorem hfExtensionalUnion_mk (s t : HFSet) :
    hfExtensionalUnion (Quotient.mk hfSetoid s) (Quotient.mk hfSetoid t) =
      Quotient.mk hfSetoid (s.union t) := rfl

/- Rank-indexed extensional approximation.  At depth `n+1`, every member has
   a matching member related at depth `n`, in both directions. -/
def HFApprox : Nat → HFSet → HFSet → Prop
  | 0, _, _ => True
  | n + 1, s, t =>
      (∀ x, HFMember x s → ∃ y, HFMember y t ∧ HFApprox n x y) ∧
      (∀ y, HFMember y t → ∃ x, HFMember x s ∧ HFApprox n x y)

theorem hfApprox_refl (n : Nat) (s : HFSet) : HFApprox n s s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro x hx
      exact ⟨x, hx, ih x⟩
    · intro x hx
      exact ⟨x, hx, ih x⟩

theorem hfApprox_symm {n : Nat} {s t : HFSet} : HFApprox n s t → HFApprox n t s := by
  intro h
  cases n with
  | zero => trivial
  | succ n =>
    constructor
    · intro x hx
      rcases h.right x hx with ⟨y, hy, hyx⟩
      exact ⟨y, hy, hfApprox_symm hyx⟩
    · intro y hy
      rcases h.left y hy with ⟨x, hx, hyx⟩
      exact ⟨x, hx, hfApprox_symm hyx⟩

theorem hfApprox_trans {n : Nat} {r s t : HFSet} :
    HFApprox n r s → HFApprox n s t → HFApprox n r t := by
  intro hrs hst
  induction n generalizing r s t with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro x hx
      rcases hrs.left x hx with ⟨y, hy, hxy⟩
      rcases hst.left y hy with ⟨z, hz, hyz⟩
      exact ⟨z, hz, ih hxy hyz⟩
    · intro z hz
      rcases hst.right z hz with ⟨y, hy, hyz⟩
      rcases hrs.right y hy with ⟨x, hx, hxy⟩
      exact ⟨x, hx, ih hxy hyz⟩

theorem hfApprox_down {n : Nat} {s t : HFSet} :
    HFApprox (n + 1) s t → HFApprox n s t := by
  intro h
  induction n generalizing s t with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro x hx
      rcases h.left x hx with ⟨y, hy, hxy⟩
      exact ⟨y, hy, ih hxy⟩
    · intro y hy
      rcases h.right y hy with ⟨x, hx, hxy⟩
      exact ⟨x, hx, ih hxy⟩

theorem hfApprox_down_to {n m : Nat} {s t : HFSet}
    (hle : m ≤ n) (h : HFApprox n s t) : HFApprox m s t := by
  cases n with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero hle
    subst m
    exact h
  | succ n =>
    by_cases heq : m = n + 1
    · subst m
      exact h
    · have hm : m ≤ n := by omega
      exact hfApprox_down_to hm (hfApprox_down h)
termination_by n
decreasing_by omega

theorem hfApprox_bigUnion {n : Nat} {s t : HFSet} :
    HFApprox (n + 2) s t → HFApprox n s.bigUnion t.bigUnion := by
  intro h
  cases n with
  | zero => trivial
  | succ n =>
    constructor
    · intro x hx
      rcases hf_member_bigUnion.mp hx with ⟨y, hy, hxy⟩
      rcases h.left y hy with ⟨y', hy', hyy'⟩
      rcases hyy'.left x hxy with ⟨x', hx', hxx'⟩
      exact ⟨x', hf_member_bigUnion.mpr ⟨y', hy', hx'⟩, hfApprox_down hxx'⟩
    · intro x hx
      rcases hf_member_bigUnion.mp hx with ⟨y, hy, hxy⟩
      rcases h.right y hy with ⟨y', hy', hyy'⟩
      rcases hyy'.right x hxy with ⟨x', hx', hxx'⟩
      exact ⟨x', hf_member_bigUnion.mpr ⟨y', hy', hx'⟩, hfApprox_down hxx'⟩

/- `rank` records presentation depth; `memberRank` instead measures the
   extensional membership tree and is the right rank for foundation. -/
def HFSet.memberRank : HFSet → Nat
  | .empty => 0
  | .insert head tail => Nat.max (head.memberRank + 1) tail.memberRank

theorem hf_memberRank_vonNeumann (n : Nat) :
    (HFSet.vonNeumann n).memberRank = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [HFSet.vonNeumann, HFSet.memberRank, ih]

theorem hf_vonNeumann_injective {m n : Nat} :
    HFSet.vonNeumann m = HFSet.vonNeumann n → m = n := by
  intro h
  have hrank := congrArg HFSet.memberRank h
  simpa [hf_memberRank_vonNeumann] using hrank

theorem hf_member_vonNeumann_iff (m n : Nat) :
    HFMember (HFSet.vonNeumann m) (HFSet.vonNeumann n) ↔ m < n := by
  induction n with
  | zero => simp [HFSet.vonNeumann, hf_not_member_empty]
  | succ n ih =>
    rw [HFSet.vonNeumann, hf_member_insert, ih]
    constructor
    · rintro (heq | hlt)
      · have hmn : m = n := hf_vonNeumann_injective heq
        subst m
        exact Nat.lt_succ_self n
      · exact Nat.lt_succ_of_lt hlt
    · intro h
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hlt | heq
      · exact Or.inr hlt
      · subst m
        exact Or.inl rfl

/- Every syntactic member of a finite von Neumann ordinal is itself one of
   its earlier ordinals.  This finite classification transfers ordinal
   arguments through the recursive quotient below. -/
theorem hf_member_vonNeumann_exists (x : HFSet) (n : Nat) :
    HFMember x (HFSet.vonNeumann n) ↔
      ∃ m, m < n ∧ x = HFSet.vonNeumann m := by
  induction n with
  | zero =>
    simp [HFSet.vonNeumann, hf_not_member_empty]
  | succ n ih =>
    rw [HFSet.vonNeumann, hf_member_insert, ih]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · exact ⟨m, Nat.lt_trans hm (Nat.lt_succ_self n), rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hmn | rfl
      · exact Or.inr ⟨m, hmn, rfl⟩
      · exact Or.inl rfl

theorem hf_member_memberRank_lt {x s : HFSet} :
    HFMember x s → x.memberRank < s.memberRank := by
  intro h
  induction h with
  | head tail =>
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  | tail h ih =>
    exact Nat.lt_of_lt_of_le ih (Nat.le_max_right _ _)

theorem hf_exists_max_memberRank_member {s : HFSet} (hne : s ≠ .empty) :
    ∃ x, HFMember x s ∧ x.memberRank + 1 = s.memberRank := by
  induction s with
  | empty => exact False.elim (hne rfl)
  | insert head tail head_ih tail_ih =>
    by_cases hle : tail.memberRank ≤ head.memberRank + 1
    · refine ⟨head, HFMember.head _ _, ?_⟩
      simp [HFSet.memberRank, Nat.max_eq_left hle]
    · have hlt : head.memberRank + 1 < tail.memberRank := Nat.lt_of_not_ge hle
      have htail : tail ≠ .empty := by
        intro h
        subst tail
        simp [HFSet.memberRank] at hlt
      rcases tail_ih htail with ⟨x, hx, hrank⟩
      refine ⟨x, HFMember.tail hx, ?_⟩
      simpa [HFSet.memberRank, Nat.max_eq_right (Nat.le_of_lt hlt)] using hrank

theorem hfApprox_memberRank_le (s t : HFSet)
    (h : HFApprox (s.memberRank + 1) s t) : s.memberRank ≤ t.memberRank := by
  by_cases hempty : s = .empty
  · subst s
    exact Nat.zero_le _
  · rcases hf_exists_max_memberRank_member hempty with ⟨x, hx, hrank⟩
    rcases h.left x hx with ⟨y, hy, hxy⟩
    have hxy' : HFApprox (x.memberRank + 1) x y := by
      simpa [hrank] using hxy
    have hle : x.memberRank ≤ y.memberRank := hfApprox_memberRank_le x y hxy'
    calc
      s.memberRank = x.memberRank + 1 := hrank.symm
      _ ≤ y.memberRank + 1 := Nat.succ_le_succ hle
      _ ≤ t.memberRank := Nat.succ_le_of_lt (hf_member_memberRank_lt hy)
termination_by s.memberRank
decreasing_by exact hf_member_memberRank_lt hx

theorem hfApprox_pair {n : Nat} {s s' t t' : HFSet}
    (hs : HFApprox n s s') (ht : HFApprox n t t') :
    HFApprox (n + 1) (s.pair t) (s'.pair t') := by
  constructor
  · intro x hx
    rcases hf_member_pair.mp hx with rfl | rfl
    · exact ⟨s', hf_member_pair.mpr (Or.inl rfl), hs⟩
    · exact ⟨t', hf_member_pair.mpr (Or.inr rfl), ht⟩
  · intro x hx
    rcases hf_member_pair.mp hx with rfl | rfl
    · exact ⟨s, hf_member_pair.mpr (Or.inl rfl), hs⟩
    · exact ⟨t, hf_member_pair.mpr (Or.inr rfl), ht⟩

/- Adjoining recursively equal heads to recursively equal tails preserves one
   more approximation layer.  This is the basic constructor used below to
   normalize an extensional finite subset against a chosen presentation. -/
theorem hfApprox_insert {n : Nat} {head head' tail tail' : HFSet}
    (hhead : HFApprox n head head') (htail : HFApprox (n + 1) tail tail') :
    HFApprox (n + 1) (.insert head tail) (.insert head' tail') := by
  constructor
  · intro x hx
    rcases hf_member_insert.mp hx with rfl | hx
    · exact ⟨head', HFMember.head _ _, hhead⟩
    · rcases htail.left x hx with ⟨y, hy, hxy⟩
      exact ⟨y, HFMember.tail hy, hxy⟩
  · intro x hx
    rcases hf_member_insert.mp hx with rfl | hx
    · exact ⟨head, HFMember.head _ _, hhead⟩
    · rcases htail.right x hx with ⟨y, hy, hxy⟩
      exact ⟨y, HFMember.tail hy, hxy⟩

/- Stable recursive extensional equality: agreement at every finite depth. -/
def HFRecursiveEq (s t : HFSet) : Prop := ∀ n, HFApprox n s t

theorem hfRecursiveEq_refl (s : HFSet) : HFRecursiveEq s s :=
  fun n => hfApprox_refl n s

theorem hfRecursiveEq_symm {s t : HFSet} :
    HFRecursiveEq s t → HFRecursiveEq t s := by
  intro h n
  exact hfApprox_symm (h n)

theorem hfRecursiveEq_trans {r s t : HFSet} :
    HFRecursiveEq r s → HFRecursiveEq s t → HFRecursiveEq r t := by
  intro hrs hst n
  exact hfApprox_trans (hrs n) (hst n)

/- Literal extensional equality is, in particular, equality at every finite
   approximation depth. -/
theorem hfExtensionalEq_recursive {s t : HFSet}
    (h : HFExtensionalEq s t) : HFRecursiveEq s t := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    constructor
    · intro x hx
      exact ⟨x, (h x).mp hx, hfApprox_refl n x⟩
    · intro x hx
      exact ⟨x, (h x).mpr hx, hfApprox_refl n x⟩

theorem hfRecursiveEq_memberRank_eq {s t : HFSet} :
    HFRecursiveEq s t → s.memberRank = t.memberRank := by
  intro h
  apply Nat.le_antisymm
  · exact hfApprox_memberRank_le s t (h (s.memberRank + 1))
  · exact hfApprox_memberRank_le t s ((hfRecursiveEq_symm h) (t.memberRank + 1))

def hfRecursiveSetoid : Setoid HFSet where
  r := HFRecursiveEq
  iseqv :=
    { refl := hfRecursiveEq_refl
      symm := by intro s t; exact hfRecursiveEq_symm
      trans := by intro r s t; exact hfRecursiveEq_trans }

abbrev HFRecursiveSet := Quotient hfRecursiveSetoid

def hfRecursiveMemberRank (s : HFRecursiveSet) : Nat :=
  Quotient.liftOn s HFSet.memberRank
    (by
      intro s t h
      exact hfRecursiveEq_memberRank_eq h)

theorem hfRecursiveMemberRank_mk (s : HFSet) :
    hfRecursiveMemberRank (Quotient.mk hfRecursiveSetoid s) = s.memberRank := rfl

def hfRecursiveNat (n : Nat) : HFRecursiveSet :=
  Quotient.mk hfRecursiveSetoid (HFSet.vonNeumann n)

theorem hfRecursiveNat_rank (n : Nat) : hfRecursiveMemberRank (hfRecursiveNat n) = n :=
  hf_memberRank_vonNeumann n

theorem hfRecursiveNat_injective {m n : Nat} :
    hfRecursiveNat m = hfRecursiveNat n → m = n := by
  intro h
  have hrank := congrArg hfRecursiveMemberRank h
  simpa [hfRecursiveNat_rank] using hrank

theorem hf_recursive_pair_congruent {s s' t t' : HFSet}
    (hs : HFRecursiveEq s s') (ht : HFRecursiveEq t t') :
    HFRecursiveEq (s.pair t) (s'.pair t') := by
  intro n
  cases n with
  | zero => trivial
  | succ n => exact hfApprox_pair (hs n) (ht n)

def hfRecursivePair (s t : HFRecursiveSet) : HFRecursiveSet :=
  Quotient.liftOn₂ s t
    (fun s t => Quotient.mk hfRecursiveSetoid (s.pair t))
    (by
      intro s t s' t' hs ht
      exact Quotient.sound (hf_recursive_pair_congruent hs ht))

theorem hfRecursivePair_mk (s t : HFSet) :
    hfRecursivePair (Quotient.mk hfRecursiveSetoid s) (Quotient.mk hfRecursiveSetoid t) =
      Quotient.mk hfRecursiveSetoid (s.pair t) := rfl

def hfRecursiveSingleton (s : HFRecursiveSet) : HFRecursiveSet :=
  hfRecursivePair s s

/- Kuratowski ordered pairs descend because both constituent pairing operations
   are already well-defined on the recursive extensional quotient. -/
def hfRecursiveOrderedPair (s t : HFRecursiveSet) : HFRecursiveSet :=
  hfRecursivePair (hfRecursiveSingleton s) (hfRecursivePair s t)

theorem hfApprox_union {n : Nat} {s s' t t' : HFSet}
    (hs : HFApprox n s s') (ht : HFApprox n t t') :
    HFApprox n (s.union t) (s'.union t') := by
  cases n with
  | zero => trivial
  | succ n =>
    constructor
    · intro x hx
      rcases hf_member_union.mp hx with hx | hx
      · rcases hs.left x hx with ⟨y, hy, hxy⟩
        exact ⟨y, hf_member_union.mpr (Or.inl hy), hxy⟩
      · rcases ht.left x hx with ⟨y, hy, hxy⟩
        exact ⟨y, hf_member_union.mpr (Or.inr hy), hxy⟩
    · intro y hy
      rcases hf_member_union.mp hy with hy | hy
      · rcases hs.right y hy with ⟨x, hx, hxy⟩
        exact ⟨x, hf_member_union.mpr (Or.inl hx), hxy⟩
      · rcases ht.right y hy with ⟨x, hx, hxy⟩
        exact ⟨x, hf_member_union.mpr (Or.inr hx), hxy⟩

theorem hfRecursive_union_congruent {s s' t t' : HFSet}
    (hs : HFRecursiveEq s s') (ht : HFRecursiveEq t t') :
    HFRecursiveEq (s.union t) (s'.union t') :=
  fun n => hfApprox_union (hs n) (ht n)

def hfRecursiveUnion (s t : HFRecursiveSet) : HFRecursiveSet :=
  Quotient.liftOn₂ s t
    (fun s t => Quotient.mk hfRecursiveSetoid (s.union t))
    (by
      intro s t s' t' hs ht
      exact Quotient.sound (hfRecursive_union_congruent hs ht))

theorem hfRecursiveUnion_mk (s t : HFSet) :
    hfRecursiveUnion (Quotient.mk hfRecursiveSetoid s) (Quotient.mk hfRecursiveSetoid t) =
      Quotient.mk hfRecursiveSetoid (s.union t) := rfl

theorem hfRecursive_bigUnion_congruent {s t : HFSet}
    (h : HFRecursiveEq s t) : HFRecursiveEq s.bigUnion t.bigUnion :=
  fun n => hfApprox_bigUnion (h (n + 2))

def hfRecursiveBigUnion (s : HFRecursiveSet) : HFRecursiveSet :=
  Quotient.liftOn s
    (fun s => Quotient.mk hfRecursiveSetoid s.bigUnion)
    (by
      intro s t h
      exact Quotient.sound (hfRecursive_bigUnion_congruent h))

theorem hfRecursiveBigUnion_mk (s : HFSet) :
    hfRecursiveBigUnion (Quotient.mk hfRecursiveSetoid s) =
      Quotient.mk hfRecursiveSetoid s.bigUnion := rfl

theorem hfApprox_union_comm (n : Nat) (s t : HFSet) :
    HFApprox n (s.union t) (t.union s) := by
  cases n with
  | zero => trivial
  | succ n =>
    constructor <;> intro x hx
    · rcases hf_member_union.mp hx with hx | hx
      · exact ⟨x, hf_member_union.mpr (Or.inr hx), hfApprox_refl n x⟩
      · exact ⟨x, hf_member_union.mpr (Or.inl hx), hfApprox_refl n x⟩
    · rcases hf_member_union.mp hx with hx | hx
      · exact ⟨x, hf_member_union.mpr (Or.inr hx), hfApprox_refl n x⟩
      · exact ⟨x, hf_member_union.mpr (Or.inl hx), hfApprox_refl n x⟩

theorem hfRecursive_union_comm (s t : HFSet) :
    HFRecursiveEq (s.union t) (t.union s) := fun n => hfApprox_union_comm n s t

theorem hfApprox_union_assoc (n : Nat) (s t u : HFSet) :
    HFApprox n ((s.union t).union u) (s.union (t.union u)) := by
  cases n with
  | zero => trivial
  | succ n =>
    constructor <;> intro x hx
    · rcases hf_member_union.mp hx with hx | hx
      · rcases hf_member_union.mp hx with hx | hx
        · exact ⟨x, hf_member_union.mpr (Or.inl hx), hfApprox_refl n x⟩
        · exact ⟨x, hf_member_union.mpr (Or.inr (hf_member_union.mpr (Or.inl hx))), hfApprox_refl n x⟩
      · exact ⟨x, hf_member_union.mpr (Or.inr (hf_member_union.mpr (Or.inr hx))), hfApprox_refl n x⟩
    · rcases hf_member_union.mp hx with hx | hx
      · exact ⟨x, hf_member_union.mpr (Or.inl (hf_member_union.mpr (Or.inl hx))), hfApprox_refl n x⟩
      · rcases hf_member_union.mp hx with hx | hx
        · exact ⟨x, hf_member_union.mpr (Or.inl (hf_member_union.mpr (Or.inr hx))), hfApprox_refl n x⟩
        · exact ⟨x, hf_member_union.mpr (Or.inr hx), hfApprox_refl n x⟩

theorem hfRecursive_union_assoc (s t u : HFSet) :
    HFRecursiveEq ((s.union t).union u) (s.union (t.union u)) :=
  fun n => hfApprox_union_assoc n s t u

theorem hfRecursiveUnion_comm_mk (s t : HFSet) :
    hfRecursiveUnion (Quotient.mk hfRecursiveSetoid s) (Quotient.mk hfRecursiveSetoid t) =
      hfRecursiveUnion (Quotient.mk hfRecursiveSetoid t) (Quotient.mk hfRecursiveSetoid s) := by
  simp only [hfRecursiveUnion_mk]
  exact Quotient.sound (hfRecursive_union_comm s t)

theorem hfRecursiveUnion_assoc_mk (s t u : HFSet) :
    hfRecursiveUnion (hfRecursiveUnion (Quotient.mk hfRecursiveSetoid s)
      (Quotient.mk hfRecursiveSetoid t)) (Quotient.mk hfRecursiveSetoid u) =
    hfRecursiveUnion (Quotient.mk hfRecursiveSetoid s)
      (hfRecursiveUnion (Quotient.mk hfRecursiveSetoid t) (Quotient.mk hfRecursiveSetoid u)) := by
  simp only [hfRecursiveUnion_mk]
  exact Quotient.sound (hfRecursive_union_assoc s t u)

theorem hf_union_empty_right (s : HFSet) : s.union .empty = s := by
  induction s with
  | empty => rfl
  | insert head tail head_ih tail_ih =>
    simp [HFSet.union, tail_ih]

def hfRecursiveEmpty : HFRecursiveSet := Quotient.mk hfRecursiveSetoid .empty

theorem hfRecursiveUnion_empty_left_mk (s : HFSet) :
    hfRecursiveUnion hfRecursiveEmpty (Quotient.mk hfRecursiveSetoid s) =
      Quotient.mk hfRecursiveSetoid s := rfl

theorem hfRecursiveUnion_empty_right_mk (s : HFSet) :
    hfRecursiveUnion (Quotient.mk hfRecursiveSetoid s) hfRecursiveEmpty =
      Quotient.mk hfRecursiveSetoid s := by
  simp only [hfRecursiveUnion_mk, hfRecursiveEmpty]
  rw [hf_union_empty_right]

theorem hfRecursiveUnion_comm (s t : HFRecursiveSet) :
    hfRecursiveUnion s t = hfRecursiveUnion t s :=
  Quotient.ind₂ (fun s t => hfRecursiveUnion_comm_mk s t) s t

theorem hfRecursiveUnion_assoc (s t u : HFRecursiveSet) :
    hfRecursiveUnion (hfRecursiveUnion s t) u =
      hfRecursiveUnion s (hfRecursiveUnion t u) :=
  Quotient.inductionOn₃ s t u (fun s t u => hfRecursiveUnion_assoc_mk s t u)

theorem hfRecursiveUnion_empty_left (s : HFRecursiveSet) :
    hfRecursiveUnion hfRecursiveEmpty s = s := by
  refine Quotient.inductionOn s ?_
  intro s
  exact hfRecursiveUnion_empty_left_mk s

theorem hfRecursiveUnion_empty_right (s : HFRecursiveSet) :
    hfRecursiveUnion s hfRecursiveEmpty = s := by
  refine Quotient.inductionOn s ?_
  intro s
  exact hfRecursiveUnion_empty_right_mk s

/- Ordered pairs preserve every available approximation, despite using two
   nested unordered pairs in their Kuratowski presentation. -/
theorem hfApprox_orderedPair {n : Nat} {s s' t t' : HFSet}
    (hs : HFApprox n s s') (ht : HFApprox n t t') :
    HFApprox n (HFSet.orderedPair s t) (HFSet.orderedPair s' t') := by
  have hsingleton : HFApprox n s.singleton s'.singleton :=
    hfApprox_down (hfApprox_insert hs (hfApprox_refl (n + 1) .empty))
  exact hfApprox_down
    (hfApprox_pair hsingleton (hfApprox_down (hfApprox_pair hs ht)))

/- Ordered pairs respect recursive extensional equality.  Keeping this raw
   lemma separate makes the Cartesian-product construction below genuinely
   descend through the quotient, rather than depending on presentations. -/
theorem hfRecursive_orderedPair_congruent {s s' t t' : HFSet}
    (hs : HFRecursiveEq s s') (ht : HFRecursiveEq t t') :
    HFRecursiveEq (HFSet.orderedPair s t) (HFSet.orderedPair s' t') := by
  intro n
  exact hfApprox_orderedPair (hs n) (ht n)

/- Cartesian product also respects recursive equality in both coordinates.
   The proof uses the syntactic membership theorem only as a presentation
   lemma; the witnesses are transported at every approximation depth. -/
theorem hfRecursive_product_congruent {left left' right right' : HFSet}
    (hleft : HFRecursiveEq left left') (hright : HFRecursiveEq right right') :
    HFRecursiveEq (left.product right) (left'.product right') := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    constructor
    · intro x hx
      rcases hf_member_product.mp hx with
        ⟨a, ha, b, hb, rfl⟩
      rcases (hleft (n + 1)).left a ha with ⟨a', ha', haa'⟩
      rcases (hright (n + 1)).left b hb with ⟨b', hb', hbb'⟩
      refine ⟨HFSet.orderedPair a' b',
        hf_member_product.mpr ⟨a', ha', b', hb', rfl⟩, ?_⟩
      exact hfApprox_orderedPair haa' hbb'
    · intro x hx
      rcases hf_member_product.mp hx with
        ⟨a', ha', b', hb', rfl⟩
      rcases ((hfRecursiveEq_symm hleft) (n + 1)).left a' ha' with ⟨a, ha, ha'a⟩
      rcases ((hfRecursiveEq_symm hright) (n + 1)).left b' hb' with ⟨b, hb, hb'a⟩
      refine ⟨HFSet.orderedPair a b,
        hf_member_product.mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
      exact hfApprox_orderedPair (hfApprox_symm ha'a) (hfApprox_symm hb'a)

/- Quotient-level finite Cartesian product. -/
def hfRecursiveProduct (left right : HFRecursiveSet) : HFRecursiveSet :=
  Quotient.liftOn₂ left right
    (fun left right => Quotient.mk hfRecursiveSetoid (left.product right))
    (by
      intro left right left' right' hleft hright
      exact Quotient.sound (hfRecursive_product_congruent hleft hright))

theorem hfRecursiveProduct_mk (left right : HFSet) :
    hfRecursiveProduct (Quotient.mk hfRecursiveSetoid left)
      (Quotient.mk hfRecursiveSetoid right) =
        Quotient.mk hfRecursiveSetoid (left.product right) := rfl

theorem hfRecursiveOrderedPair_mk (s t : HFSet) :
    hfRecursiveOrderedPair (Quotient.mk hfRecursiveSetoid s)
      (Quotient.mk hfRecursiveSetoid t) =
        Quotient.mk hfRecursiveSetoid (HFSet.orderedPair s t) := by
  apply Quotient.sound
  apply hf_recursive_pair_congruent
  · apply hfExtensionalEq_recursive
    intro x
    rw [hf_member_pair, hf_member_singleton]
    constructor
    · rintro (h | h) <;> exact h
    · intro h
      exact Or.inl h
  · exact hfRecursiveEq_refl _

def HFApproxRespectful (p : HFSet → Bool) : Prop :=
  ∀ {n x y}, HFApprox n x y → p x = p y

theorem hfApprox_filter {p : HFSet → Bool} (hp : HFApproxRespectful p)
    {n : Nat} {s t : HFSet} (h : HFApprox n s t) :
    HFApprox n (s.filter p) (t.filter p) := by
  cases n with
  | zero => trivial
  | succ n =>
    constructor
    · intro x hx
      rcases hf_member_filter_iff.mp hx with ⟨hxS, px⟩
      rcases h.left x hxS with ⟨y, hyT, hxy⟩
      have py : p y = true := by
        rw [← hp hxy]
        exact px
      exact ⟨y, hf_member_filter_iff.mpr ⟨hyT, py⟩, hxy⟩
    · intro y hy
      rcases hf_member_filter_iff.mp hy with ⟨hyT, py⟩
      rcases h.right y hyT with ⟨x, hxS, hxy⟩
      have px : p x = true := by
        rw [hp hxy]
        exact py
      exact ⟨x, hf_member_filter_iff.mpr ⟨hxS, px⟩, hxy⟩

theorem hfRecursive_filter_congruent {p : HFSet → Bool}
    (hp : HFApproxRespectful p) {s t : HFSet} (h : HFRecursiveEq s t) :
    HFRecursiveEq (s.filter p) (t.filter p) :=
  fun n => hfApprox_filter hp (h n)

structure HFRecursivePredicate where
  run : HFSet → Bool
  respectful : HFApproxRespectful run

def hfRecursiveFilter (p : HFRecursivePredicate) (s : HFRecursiveSet) : HFRecursiveSet :=
  Quotient.liftOn s
    (fun s => Quotient.mk hfRecursiveSetoid (s.filter p.run))
    (by
      intro s t h
      exact Quotient.sound (hfRecursive_filter_congruent p.respectful h))

theorem hfRecursiveFilter_mk (p : HFRecursivePredicate) (s : HFSet) :
    hfRecursiveFilter p (Quotient.mk hfRecursiveSetoid s) =
      Quotient.mk hfRecursiveSetoid (s.filter p.run) := rfl

/- Membership on the recursive quotient.  A member is represented up to the
   same all-depth equality as sets themselves. -/
def HFRecursiveMemberRaw (x s : HFSet) : Prop :=
  ∀ n, ∃ y, HFMember y s ∧ HFApprox n x y

theorem hfRecursiveMemberRaw_irreflexive (s : HFSet) :
    ¬ HFRecursiveMemberRaw s s := by
  intro h
  rcases h (s.memberRank + 1) with ⟨y, hy, hsy⟩
  have hle : s.memberRank ≤ y.memberRank := hfApprox_memberRank_le s y hsy
  exact (Nat.not_le_of_gt (hf_member_memberRank_lt hy)) hle

theorem hfRecursiveMemberRaw_insert_iff (x head tail : HFSet) :
    HFRecursiveMemberRaw x (.insert head tail) ↔
      HFRecursiveEq x head ∨ HFRecursiveMemberRaw x tail := by
  constructor
  · intro h
    by_cases hhead : HFRecursiveEq x head
    · exact Or.inl hhead
    · right
      have hcounter : ∃ n, ¬ HFApprox n x head := by
        apply Classical.byContradiction
        intro hnone
        apply hhead
        intro n
        apply Classical.byContradiction
        intro hn
        exact hnone ⟨n, hn⟩
      rcases hcounter with ⟨n, hn⟩
      intro m
      rcases h (Nat.max m n) with ⟨y, hy, hxy⟩
      rcases hf_member_insert.mp hy with rfl | hy
      · exact False.elim (hn (hfApprox_down_to (Nat.le_max_right _ _) hxy))
      · exact ⟨y, hy, hfApprox_down_to (Nat.le_max_left _ _) hxy⟩
  · rintro (hhead | htail)
    · intro n
      exact ⟨head, HFMember.head _ _, hhead n⟩
    · intro n
      rcases htail n with ⟨y, hy, hxy⟩
      exact ⟨y, HFMember.tail hy, hxy⟩

theorem hfRecursiveMemberRaw_iff_exists {x s : HFSet} :
    HFRecursiveMemberRaw x s ↔ ∃ y, HFMember y s ∧ HFRecursiveEq x y := by
  induction s with
  | empty =>
    constructor
    · intro h
      rcases h 0 with ⟨y, hy, _⟩
      exact False.elim (hf_not_member_empty hy)
    · rintro ⟨y, hy, _⟩
      exact False.elim (hf_not_member_empty hy)
  | insert head tail head_ih tail_ih =>
    rw [hfRecursiveMemberRaw_insert_iff, tail_ih]
    constructor
    · rintro (hhead | ⟨y, hy, hxy⟩)
      · exact ⟨head, HFMember.head _ _, hhead⟩
      · exact ⟨y, HFMember.tail hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      rcases hf_member_insert.mp hy with rfl | hy
      · exact Or.inl hxy
      · exact Or.inr ⟨y, hy, hxy⟩

/- A syntactic presentation of subset on the recursive quotient: each member
   of the source has a recursively equal representative in the target. -/
def HFRecursiveSubsetRaw (u s : HFSet) : Prop :=
  ∀ x, HFMember x u → ∃ y, HFMember y s ∧ HFRecursiveEq x y

/- Any recursively represented finite subset can be normalized to a literal
   syntactic subset of its chosen target presentation. -/
theorem hfRecursiveSubsetRaw_refine {u s : HFSet} :
    HFRecursiveSubsetRaw u s →
      ∃ v, HFSubset v s ∧ HFRecursiveEq u v := by
  induction u generalizing s with
  | empty =>
    intro _
    refine ⟨.empty, ?_, hfRecursiveEq_refl .empty⟩
    intro x hx
    exact False.elim (hf_not_member_empty hx)
  | insert head tail head_ih tail_ih =>
    intro hsubset
    rcases hsubset head (HFMember.head _ _) with ⟨head', hhead', hheadEq⟩
    have htailSubset : HFRecursiveSubsetRaw tail s := by
      intro x hx
      exact hsubset x (HFMember.tail hx)
    rcases tail_ih htailSubset with ⟨tail', htail', htailEq⟩
    refine ⟨.insert head' tail', ?_, ?_⟩
    · intro x hx
      rcases hf_member_insert.mp hx with rfl | hx
      · exact hhead'
      · exact htail' x hx
    · intro n
      cases n with
      | zero => trivial
      | succ n => exact hfApprox_insert (hheadEq n) (htailEq (n + 1))

theorem hfRecursiveMemberRaw_memberRank_lt {x s : HFSet}
    (h : HFRecursiveMemberRaw x s) : x.memberRank < s.memberRank := by
  rcases h (x.memberRank + 1) with ⟨y, hy, hxy⟩
  exact Nat.lt_of_le_of_lt (hfApprox_memberRank_le x y hxy)
    (hf_member_memberRank_lt hy)

theorem hfRecursiveMemberRaw_source_congruent {s t x : HFSet}
    (hst : HFRecursiveEq s t) :
    HFRecursiveMemberRaw x s ↔ HFRecursiveMemberRaw x t := by
  constructor
  · intro h
    intro n
    rcases h n with ⟨y, hy, hxy⟩
    rcases (hst (n + 1)).left y hy with ⟨z, hz, hyz⟩
    exact ⟨z, hz, hfApprox_trans hxy hyz⟩
  · intro h n
    rcases h n with ⟨y, hy, hxy⟩
    rcases ((hfRecursiveEq_symm hst) (n + 1)).left y hy with ⟨z, hz, hyz⟩
    exact ⟨z, hz, hfApprox_trans hxy hyz⟩

theorem hfRecursiveMemberRaw_target_congruent {x y s : HFSet}
    (hxy : HFRecursiveEq x y) :
    HFRecursiveMemberRaw x s ↔ HFRecursiveMemberRaw y s := by
  constructor
  · intro h n
    rcases h n with ⟨z, hz, hxz⟩
    exact ⟨z, hz, hfApprox_trans (hfApprox_symm (hxy n)) hxz⟩
  · intro h n
    rcases h n with ⟨z, hz, hyz⟩
    exact ⟨z, hz, hfApprox_trans (hxy n) hyz⟩

def HFRecursiveMember (x s : HFRecursiveSet) : Prop :=
  Quotient.liftOn₂ x s HFRecursiveMemberRaw
    (by
      intro x s y t hxy hst
      apply propext
      exact Iff.trans (hfRecursiveMemberRaw_target_congruent hxy)
        (hfRecursiveMemberRaw_source_congruent hst))

theorem hfRecursiveMember_mk (x s : HFSet) :
    HFRecursiveMember (Quotient.mk hfRecursiveSetoid x)
      (Quotient.mk hfRecursiveSetoid s) ↔ HFRecursiveMemberRaw x s := Iff.rfl

theorem hfRecursiveMember_iff_exists_direct {x s : HFRecursiveSet} :
    HFRecursiveMember x s ↔
      ∃ y, HFRecursiveMember y s ∧ x = y := by
  constructor
  · intro hx
    revert hx
    refine Quotient.inductionOn₂ x s ?_
    intro x s hx
    rcases hfRecursiveMemberRaw_iff_exists.mp hx with ⟨y, hy, hxy⟩
    refine ⟨Quotient.mk hfRecursiveSetoid y, ?_, Quotient.sound hxy⟩
    intro n
    exact ⟨y, hy, hfApprox_refl n y⟩
  · rintro ⟨y, hys, rfl⟩
    exact hys

theorem hfRecursiveMember_pair_iff (x s t : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursivePair s t) ↔ x = s ∨ x = t := by
  refine Quotient.inductionOn₃ x s t ?_
  intro x s t
  constructor
  · intro h
    rcases hfRecursiveMemberRaw_iff_exists.mp h with ⟨y, hy, hxy⟩
    rcases hf_member_pair.mp hy with rfl | rfl
    · exact Or.inl (Quotient.sound hxy)
    · exact Or.inr (Quotient.sound hxy)
  · rintro (hxs | hxt)
    · rw [hxs]
      intro n
      exact ⟨s, hf_member_pair.mpr (Or.inl rfl), hfApprox_refl n s⟩
    · rw [hxt]
      intro n
      exact ⟨t, hf_member_pair.mpr (Or.inr rfl), hfApprox_refl n t⟩

theorem hfRecursiveMember_singleton_iff (x s : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveSingleton s) ↔ x = s := by
  rw [hfRecursiveSingleton, hfRecursiveMember_pair_iff]
  constructor
  · rintro (h | h) <;> exact h
  · intro h
    exact Or.inl h

theorem hfRecursiveMember_orderedPair_iff (x s t : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveOrderedPair s t) ↔
      x = hfRecursiveSingleton s ∨ x = hfRecursivePair s t := by
  rw [hfRecursiveOrderedPair, hfRecursiveMember_pair_iff]

theorem hfRecursiveSingleton_injective {s t : HFRecursiveSet} :
    hfRecursiveSingleton s = hfRecursiveSingleton t → s = t := by
  intro h
  have hs : HFRecursiveMember s (hfRecursiveSingleton t) := by
    rw [← h]
    exact (hfRecursiveMember_singleton_iff s s).mpr rfl
  exact (hfRecursiveMember_singleton_iff s t).mp hs

theorem hfRecursiveMember_union_iff (x s t : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveUnion s t) ↔
      HFRecursiveMember x s ∨ HFRecursiveMember x t := by
  refine Quotient.inductionOn₃ x s t ?_
  intro x s t
  constructor
  · intro h
    rcases hfRecursiveMemberRaw_iff_exists.mp h with ⟨y, hy, hxy⟩
    rcases hf_member_union.mp hy with hy | hy
    · exact Or.inl (hfRecursiveMemberRaw_iff_exists.mpr ⟨y, hy, hxy⟩)
    · exact Or.inr (hfRecursiveMemberRaw_iff_exists.mpr ⟨y, hy, hxy⟩)
  · rintro (hs | ht)
    · rcases hfRecursiveMemberRaw_iff_exists.mp hs with ⟨y, hy, hxy⟩
      exact hfRecursiveMemberRaw_iff_exists.mpr
        ⟨y, hf_member_union.mpr (Or.inl hy), hxy⟩
    · rcases hfRecursiveMemberRaw_iff_exists.mp ht with ⟨y, hy, hxy⟩
      exact hfRecursiveMemberRaw_iff_exists.mpr
        ⟨y, hf_member_union.mpr (Or.inr hy), hxy⟩

/- Membership in the quotient Cartesian product is characterized by its two
   projections.  This is quotient-safe: equality of presentations is used
   only through `HFRecursiveEq`, never syntactic equality of components. -/
theorem hfRecursiveMember_product_iff (x left right : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveProduct left right) ↔
      ∃ leftMember, HFRecursiveMember leftMember left ∧
        ∃ rightMember, HFRecursiveMember rightMember right ∧
          x = hfRecursiveOrderedPair leftMember rightMember := by
  refine Quotient.inductionOn₃ x left right ?_
  intro x left right
  constructor
  · intro hx
    rcases hfRecursiveMemberRaw_iff_exists.mp hx with ⟨pair, hpair, hxpair⟩
    rcases hf_member_product.mp hpair with ⟨a, ha, b, hb, rfl⟩
    refine ⟨Quotient.mk hfRecursiveSetoid a,
      hfRecursiveMemberRaw_iff_exists.mpr ⟨a, ha, hfRecursiveEq_refl a⟩,
      Quotient.mk hfRecursiveSetoid b,
      hfRecursiveMemberRaw_iff_exists.mpr ⟨b, hb, hfRecursiveEq_refl b⟩, ?_⟩
    simpa only [hfRecursiveOrderedPair_mk] using
      (Quotient.sound hxpair :
        Quotient.mk hfRecursiveSetoid x =
          Quotient.mk hfRecursiveSetoid (HFSet.orderedPair a b))
  · rintro ⟨a, ha, b, hb, hxab⟩
    revert ha hb hxab
    refine Quotient.inductionOn₂ a b ?_
    intro a b ha hb hxab
    rcases hfRecursiveMemberRaw_iff_exists.mp ha with ⟨a', ha', haa'⟩
    rcases hfRecursiveMemberRaw_iff_exists.mp hb with ⟨b', hb', hbb'⟩
    have hxabRaw : HFRecursiveEq x (HFSet.orderedPair a b) := by
      exact Quotient.exact (hxab.trans (hfRecursiveOrderedPair_mk a b))
    have hxab' : HFRecursiveEq x (HFSet.orderedPair a' b') :=
      hfRecursiveEq_trans hxabRaw
        (hfRecursive_orderedPair_congruent
          haa' hbb')
    apply (hfRecursiveMemberRaw_target_congruent hxab').mpr
    intro n
    exact ⟨HFSet.orderedPair a' b',
      hf_member_product.mpr ⟨a', ha', b', hb', rfl⟩, hfApprox_refl n _⟩

theorem hfRecursiveMember_bigUnion_iff (x s : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveBigUnion s) ↔
      ∃ y, HFRecursiveMember y s ∧ HFRecursiveMember x y := by
  constructor
  · intro h
    revert h
    refine Quotient.inductionOn₂ x s ?_
    intro x s h
    rcases hfRecursiveMemberRaw_iff_exists.mp h with ⟨z, hz, hxz⟩
    rcases hf_member_bigUnion.mp hz with ⟨y, hy, hzy⟩
    refine ⟨Quotient.mk hfRecursiveSetoid y, ?_, ?_⟩
    · exact hfRecursiveMemberRaw_iff_exists.mpr ⟨y, hy, hfRecursiveEq_refl y⟩
    · exact hfRecursiveMemberRaw_iff_exists.mpr ⟨z, hzy, hxz⟩
  · rintro ⟨y, hys, hxy⟩
    revert hys hxy
    refine Quotient.inductionOn₃ x y s ?_
    intro x y s hys hxy n
    rcases hys (n + 2) with ⟨y', hy', hyy'⟩
    rcases hxy (n + 1) with ⟨x', hx', hxx'⟩
    rcases hyy'.left x' hx' with ⟨z, hz, hxxz⟩
    exact ⟨z, hf_member_bigUnion.mpr ⟨y', hy', hz⟩,
      hfApprox_trans (hfApprox_down hxx') (hfApprox_down hxxz)⟩

theorem hfRecursiveMember_irreflexive (s : HFRecursiveSet) :
    ¬ HFRecursiveMember s s := by
  refine Quotient.inductionOn s ?_
  intro s h
  exact hfRecursiveMemberRaw_irreflexive s h

theorem hfRecursiveNat_succ_member (n : Nat) :
    HFRecursiveMember (hfRecursiveNat n) (hfRecursiveNat (n + 1)) := by
  intro k
  exact ⟨HFSet.vonNeumann n, HFMember.head _ _, hfApprox_refl k _⟩

theorem hfRecursiveMember_rank_lt {x s : HFRecursiveSet}
    (h : HFRecursiveMember x s) :
    hfRecursiveMemberRank x < hfRecursiveMemberRank s := by
  revert h
  refine Quotient.inductionOn₂ x s ?_
  intro x s h
  exact hfRecursiveMemberRaw_memberRank_lt h

theorem hfRecursiveNat_member_iff (m n : Nat) :
    HFRecursiveMember (hfRecursiveNat m) (hfRecursiveNat n) ↔ m < n := by
  constructor
  · intro h
    have hrank := hfRecursiveMember_rank_lt h
    simpa [hfRecursiveNat_rank] using hrank
  · intro h
    intro k
    exact ⟨HFSet.vonNeumann m, (hf_member_vonNeumann_iff m n).mpr h,
      hfApprox_refl k _⟩

/- The quotient contains no additional members of a finite ordinal: every
   member is exactly an earlier internally represented natural number. -/
theorem hfRecursiveMember_nat_iff_exists (x : HFRecursiveSet) (n : Nat) :
    HFRecursiveMember x (hfRecursiveNat n) ↔
      ∃ m, m < n ∧ x = hfRecursiveNat m := by
  refine Quotient.inductionOn x ?_
  intro x
  constructor
  · intro hx
    rcases hfRecursiveMemberRaw_iff_exists.mp hx with ⟨y, hy, hxy⟩
    rcases hf_member_vonNeumann_exists y n |>.mp hy with ⟨m, hm, rfl⟩
    exact ⟨m, hm, Quotient.sound hxy⟩
  · rintro ⟨m, hm, hxm⟩
    rw [hxm]
    exact (hfRecursiveNat_member_iff m n).mpr hm

theorem hfRecursiveMember_wellFounded :
    WellFounded (fun x s : HFRecursiveSet => HFRecursiveMember x s) :=
  Subrelation.wf
    (q := fun x s : HFRecursiveSet => HFRecursiveMember x s)
    (r := fun x s : HFRecursiveSet => hfRecursiveMemberRank x < hfRecursiveMemberRank s)
    (by
      intro x s h
      exact hfRecursiveMember_rank_lt h)
    (measure hfRecursiveMemberRank).wf

/- Set-theoretic foundation: every nonempty set has a member with no member
   lying in the original set. -/
theorem hfRecursive_foundation {s : HFRecursiveSet}
    (hnonempty : ∃ x, HFRecursiveMember x s) :
    ∃ y, HFRecursiveMember y s ∧
      ∀ z, ¬ (HFRecursiveMember z s ∧ HFRecursiveMember z y) := by
  let rel : HFRecursiveSet → HFRecursiveSet → Prop :=
    fun z y => HFRecursiveMember z s ∧ HFRecursiveMember z y
  have relWf : WellFounded rel :=
    Subrelation.wf
      (q := rel)
      (r := fun z y : HFRecursiveSet => HFRecursiveMember z y)
      (by
        intro z y h
        exact h.right)
      hfRecursiveMember_wellFounded
  have minimalFrom : ∀ x, Acc rel x → HFRecursiveMember x s →
      ∃ y, HFRecursiveMember y s ∧ ∀ z, ¬ rel z y := by
    intro x hx
    induction hx with
    | intro x hacc ih =>
      intro hxS
      by_cases hminimal : ∀ z, ¬ rel z x
      · exact ⟨x, hxS, hminimal⟩
      · have hpred : ∃ z, rel z x := by
          apply Classical.byContradiction
          intro hnone
          apply hminimal
          intro z hz
          exact hnone ⟨z, hz⟩
        rcases hpred with ⟨z, hzx⟩
        exact ih z hzx hzx.left
  rcases hnonempty with ⟨x, hx⟩
  rcases minimalFrom x (relWf.apply x) hx with ⟨y, hy, hmin⟩
  exact ⟨y, hy, fun z hz => hmin z hz⟩

theorem hfRecursiveMember_empty (x : HFRecursiveSet) :
    ¬ HFRecursiveMember x hfRecursiveEmpty := by
  refine Quotient.inductionOn x ?_
  intro x hx
  rcases hx 0 with ⟨y, hy, _⟩
  exact hf_not_member_empty hy

theorem hfRecursiveMember_pair_left (s t : HFRecursiveSet) :
    HFRecursiveMember s (hfRecursivePair s t) := by
  refine Quotient.inductionOn₂ s t ?_
  intro s t n
  exact ⟨s, hf_member_pair.mpr (Or.inl rfl), hfApprox_refl n s⟩

theorem hfRecursiveMember_pair_right (s t : HFRecursiveSet) :
    HFRecursiveMember t (hfRecursivePair s t) := by
  refine Quotient.inductionOn₂ s t ?_
  intro s t n
  exact ⟨t, hf_member_pair.mpr (Or.inr rfl), hfApprox_refl n t⟩

theorem hfRecursiveMember_bigUnion_intro {x y s : HFRecursiveSet}
    (hys : HFRecursiveMember y s) (hxy : HFRecursiveMember x y) :
    HFRecursiveMember x (hfRecursiveBigUnion s) := by
  revert hys hxy
  refine Quotient.inductionOn₃ x y s ?_
  intro x y s hys hxy n
  rcases hys (n + 2) with ⟨y', hy', hyy'⟩
  rcases hxy (n + 1) with ⟨x', hx', hxx'⟩
  rcases hyy'.left x' hx' with ⟨z, hz, hxxz⟩
  exact ⟨z, hf_member_bigUnion.mpr ⟨y', hy', hz⟩,
    hfApprox_trans (hfApprox_down hxx') (hfApprox_down hxxz)⟩

def HFRecursivePredicate.holds (p : HFRecursivePredicate) (x : HFRecursiveSet) : Prop :=
  Quotient.liftOn x (fun x => p.run x = true)
    (by
      intro x y hxy
      apply propext
      change p.run x = true ↔ p.run y = true
      rw [p.respectful (hxy 0)])

theorem hfRecursivePredicate_holds_mk (p : HFRecursivePredicate) (x : HFSet) :
    p.holds (Quotient.mk hfRecursiveSetoid x) ↔ p.run x = true := Iff.rfl

theorem hfRecursiveMemberRaw_filter_iff (p : HFRecursivePredicate) (x s : HFSet) :
    HFRecursiveMemberRaw x (s.filter p.run) ↔
      HFRecursiveMemberRaw x s ∧ p.run x = true := by
  constructor
  · intro h
    constructor
    · intro n
      rcases h n with ⟨y, hy, hxy⟩
      exact ⟨y, (hf_member_filter_iff.mp hy).left, hxy⟩
    · rcases h 1 with ⟨y, hy, hxy⟩
      have py : p.run y = true := (hf_member_filter_iff.mp hy).right
      rw [p.respectful hxy]
      exact py
  · rintro ⟨h, px⟩ n
    rcases h n with ⟨y, hy, hxy⟩
    have py : p.run y = true := by
      rw [← p.respectful hxy]
      exact px
    exact ⟨y, hf_member_filter_iff.mpr ⟨hy, py⟩, hxy⟩

theorem hfRecursiveMember_filter_iff (p : HFRecursivePredicate)
    (x s : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveFilter p s) ↔
      HFRecursiveMember x s ∧ p.holds x := by
  refine Quotient.inductionOn₂ x s ?_
  intro x s
  exact hfRecursiveMemberRaw_filter_iff p x s

theorem hfRecursiveMember_into_union_left (x s t : HFRecursiveSet) :
    HFRecursiveMember x s → HFRecursiveMember x (hfRecursiveUnion s t) := by
  refine Quotient.inductionOn₃ x s t ?_
  intro x s t
  intro hs n
  rcases hs n with ⟨y, hy, hyx⟩
  exact ⟨y, hf_member_union.mpr (Or.inl hy), hyx⟩

theorem hfRecursiveMember_into_union_right (x s t : HFRecursiveSet) :
    HFRecursiveMember x t → HFRecursiveMember x (hfRecursiveUnion s t) := by
  refine Quotient.inductionOn₃ x s t ?_
  intro x s t ht n
  rcases ht n with ⟨y, hy, hyx⟩
  exact ⟨y, hf_member_union.mpr (Or.inr hy), hyx⟩

/- Extensionality is derived for the recursive quotient, rather than postulated. -/
theorem hfRecursive_extensionality {s t : HFSet}
    (h : ∀ x : HFSet, HFRecursiveMemberRaw x s ↔ HFRecursiveMemberRaw x t) :
    HFRecursiveEq s t := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    constructor
    · intro x hx
      have hxRaw : HFRecursiveMemberRaw x s :=
        fun k => ⟨x, hx, hfApprox_refl k x⟩
      rcases ((h x).mp hxRaw) n with ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
    · intro y hy
      have hyRaw : HFRecursiveMemberRaw y t :=
        fun k => ⟨y, hy, hfApprox_refl k y⟩
      rcases ((h y).mpr hyRaw) n with ⟨x, hx, hyx⟩
      exact ⟨x, hx, hfApprox_symm hyx⟩

theorem hfRecursiveSet_extensionality {s t : HFRecursiveSet}
    (h : ∀ x, HFRecursiveMember x s ↔ HFRecursiveMember x t) : s = t := by
  revert h
  refine Quotient.inductionOn₂ s t ?_
  intro s t h
  apply Quotient.sound
  apply hfRecursive_extensionality
  intro x
  simpa only [hfRecursiveMember_mk] using h (Quotient.mk hfRecursiveSetoid x)

theorem hfRecursivePair_comm (s t : HFRecursiveSet) :
    hfRecursivePair s t = hfRecursivePair t s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_pair_iff, hfRecursiveMember_pair_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

/- Extensional unordered pairs have exactly the expected two matchings. -/
theorem hfRecursivePair_eq_iff (s t u v : HFRecursiveSet) :
    hfRecursivePair s t = hfRecursivePair u v ↔
      (s = u ∧ t = v) ∨ (s = v ∧ t = u) := by
  constructor
  · intro h
    have hs : s = u ∨ s = v := by
      apply (hfRecursiveMember_pair_iff s u v).mp
      rw [← h]
      exact (hfRecursiveMember_pair_iff s s t).mpr (Or.inl rfl)
    rcases hs with hsu | hsv
    · by_cases htveq : t = v
      · exact Or.inl ⟨hsu, htveq⟩
      · have htueq : t = u := by
          rcases (hfRecursiveMember_pair_iff t u v).mp (by
            rw [← h]
            exact (hfRecursiveMember_pair_iff t s t).mpr (Or.inr rfl)) with htu | htv
          · exact htu
          · exact False.elim (htveq htv)
        have hvseq : v = s := by
          rcases (hfRecursiveMember_pair_iff v s t).mp (by
            rw [h]
            exact (hfRecursiveMember_pair_iff v u v).mpr (Or.inr rfl)) with hvseq | hvteq
          · exact hvseq
          · exact False.elim (htveq hvteq.symm)
        exact False.elim (htveq (htueq.trans (hsu.symm.trans hvseq.symm)))
    · by_cases htueq : t = u
      · exact Or.inr ⟨hsv, htueq⟩
      · have htveq : t = v := by
          rcases (hfRecursiveMember_pair_iff t u v).mp (by
            rw [← h]
            exact (hfRecursiveMember_pair_iff t s t).mpr (Or.inr rfl)) with htu | htv
          · exact False.elim (htueq htu)
          · exact htv
        have huseq : u = s := by
          rcases (hfRecursiveMember_pair_iff u s t).mp (by
            rw [h]
            exact (hfRecursiveMember_pair_iff u u v).mpr (Or.inl rfl)) with huseq | huteq
          · exact huseq
          · exact False.elim (htueq huteq.symm)
        exact False.elim (htueq (htveq.trans (hsv.symm.trans huseq.symm)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact hfRecursivePair_comm _ _

/- Kuratowski pairs are injective, so they can serve as graph elements for
   internally represented finite relations and functions. -/
theorem hfRecursiveOrderedPair_injective {s t u v : HFRecursiveSet} :
    hfRecursiveOrderedPair s t = hfRecursiveOrderedPair u v → s = u ∧ t = v := by
  intro h
  have houter := hfRecursivePair_eq_iff
    (hfRecursiveSingleton s) (hfRecursivePair s t)
    (hfRecursiveSingleton u) (hfRecursivePair u v)
  rcases houter.mp (by simpa [hfRecursiveOrderedPair] using h) with
    ⟨hss, hpairs⟩ | ⟨hspair, hpairs⟩
  · have hsu : s = u := hfRecursiveSingleton_injective hss
    subst u
    rcases (hfRecursivePair_eq_iff s t s v).mp hpairs with
      ⟨_, htv⟩ | ⟨hsv, hts⟩
    · exact ⟨rfl, htv⟩
    · exact ⟨rfl, hts.trans hsv⟩
  · have hus : u = s := by
      apply (hfRecursiveMember_singleton_iff u s).mp
      rw [hspair]
      exact (hfRecursiveMember_pair_iff u u v).mpr (Or.inl rfl)
    have hvs : v = s := by
      apply (hfRecursiveMember_singleton_iff v s).mp
      rw [hspair]
      exact (hfRecursiveMember_pair_iff v u v).mpr (Or.inr rfl)
    have htu : t = u := by
      apply (hfRecursiveMember_singleton_iff t u).mp
      rw [← hpairs]
      exact (hfRecursiveMember_pair_iff t s t).mpr (Or.inr rfl)
    exact ⟨hus.symm, htu.trans (hus.trans hvs.symm)⟩

/- Signed integers are encoded internally by a sign tag and a magnitude.
   `ofNat n` uses tag 0 and `negSucc n` (the integer `-(n+1)`) uses tag 1. -/
def hfRecursiveInteger : Int → HFRecursiveSet
  | .ofNat n => hfRecursiveOrderedPair (hfRecursiveNat 0) (hfRecursiveNat n)
  | .negSucc n => hfRecursiveOrderedPair (hfRecursiveNat 1) (hfRecursiveNat n)

theorem hfRecursiveInteger_ofNat (n : Nat) :
    hfRecursiveInteger (Int.ofNat n) =
      hfRecursiveOrderedPair (hfRecursiveNat 0) (hfRecursiveNat n) := rfl

theorem hfRecursiveInteger_negSucc (n : Nat) :
    hfRecursiveInteger (Int.negSucc n) =
      hfRecursiveOrderedPair (hfRecursiveNat 1) (hfRecursiveNat n) := rfl

theorem hfRecursiveInteger_positive_negative_disjoint (m n : Nat) :
    hfRecursiveInteger (Int.ofNat m) ≠ hfRecursiveInteger (Int.negSucc n) := by
  intro equal
  have tags := (hfRecursiveOrderedPair_injective equal).left
  have impossible : 0 = 1 := hfRecursiveNat_injective tags
  cases impossible

theorem hfRecursiveInteger_injective {first second : Int} :
    hfRecursiveInteger first = hfRecursiveInteger second → first = second := by
  intro equal
  cases first with
  | ofNat first =>
      cases second with
      | ofNat second =>
          have magnitudes := (hfRecursiveOrderedPair_injective equal).right
          have indexEq : first = second := hfRecursiveNat_injective magnitudes
          cases indexEq
          rfl
      | negSucc second =>
          exact False.elim
            (hfRecursiveInteger_positive_negative_disjoint first second equal)
  | negSucc first =>
      cases second with
      | ofNat second =>
          exact False.elim
            (hfRecursiveInteger_positive_negative_disjoint second first equal.symm)
      | negSucc second =>
          have magnitudes := (hfRecursiveOrderedPair_injective equal).right
          have indexEq : first = second := hfRecursiveNat_injective magnitudes
          cases indexEq
          rfl

def HFRecursiveIntegerCode (value : HFRecursiveSet) : Prop :=
  ∃ integer : Int, value = hfRecursiveInteger integer

theorem hfRecursiveInteger_isCode (integer : Int) :
    HFRecursiveIntegerCode (hfRecursiveInteger integer) :=
  ⟨integer, rfl⟩

theorem hfRecursiveInteger_representation_unique
    {value : HFRecursiveSet} {first second : Int}
    (firstRep : value = hfRecursiveInteger first)
    (secondRep : value = hfRecursiveInteger second) :
    first = second :=
  hfRecursiveInteger_injective (firstRep.symm.trans secondRep)

theorem hfRecursiveIntegerCode_has_unique_representation
    (value : HFRecursiveSet) (isCode : HFRecursiveIntegerCode value) :
    ∃ integer : Int,
      value = hfRecursiveInteger integer ∧
      ∀ other : Int, value = hfRecursiveInteger other → other = integer := by
  rcases isCode with ⟨integer, representation⟩
  refine ⟨integer, representation, ?_⟩
  intro other otherRep
  exact hfRecursiveInteger_representation_unique otherRep representation

/- A relation is represented internally as a set of Kuratowski ordered pairs. -/
def HFRecursiveRelation (relation : HFRecursiveSet) : Prop :=
  ∀ element, HFRecursiveMember element relation →
    ∃ input output, element = hfRecursiveOrderedPair input output

def HFRecursiveFunctional (relation : HFRecursiveSet) : Prop :=
  ∀ input output₁ output₂,
    HFRecursiveMember (hfRecursiveOrderedPair input output₁) relation →
      HFRecursiveMember (hfRecursiveOrderedPair input output₂) relation →
        output₁ = output₂

/- Finite unions of graph presentations are again relations. -/
theorem hfRecursiveRelation_union {left right : HFRecursiveSet}
    (hleft : HFRecursiveRelation left) (hright : HFRecursiveRelation right) :
    HFRecursiveRelation (hfRecursiveUnion left right) := by
  intro element helement
  rcases (hfRecursiveMember_union_iff element left right).mp helement with hleftMember | hrightMember
  · exact hleft element hleftMember
  · exact hright element hrightMember

def hfRecursiveSingletonGraph (input output : HFRecursiveSet) : HFRecursiveSet :=
  hfRecursiveSingleton (hfRecursiveOrderedPair input output)

theorem hfRecursiveSingletonGraph_relation (input output : HFRecursiveSet) :
    HFRecursiveRelation (hfRecursiveSingletonGraph input output) := by
  intro element helement
  rw [hfRecursiveSingletonGraph, hfRecursiveMember_singleton_iff] at helement
  exact ⟨input, output, helement⟩

theorem hfRecursiveSingletonGraph_apply_iff
    (input output queryInput queryOutput : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair queryInput queryOutput)
      (hfRecursiveSingletonGraph input output) ↔
        queryInput = input ∧ queryOutput = output := by
  rw [hfRecursiveSingletonGraph, hfRecursiveMember_singleton_iff]
  constructor
  · intro h
    exact hfRecursiveOrderedPair_injective h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem hfRecursiveSingletonGraph_functional (input output : HFRecursiveSet) :
    HFRecursiveFunctional (hfRecursiveSingletonGraph input output) := by
  intro queryInput output₁ output₂ h₁ h₂
  have h₁' := (hfRecursiveSingletonGraph_apply_iff input output queryInput output₁).mp h₁
  have h₂' := (hfRecursiveSingletonGraph_apply_iff input output queryInput output₂).mp h₂
  exact h₁'.right.trans h₂'.right.symm

def HFRecursiveIntegerWithin (bound : Nat) : Int → Prop
  | .ofNat magnitude => magnitude < bound
  | .negSucc magnitude => magnitude < bound

def hfRecursiveIntegerNonnegativeNegationGraph : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | bound + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph
        (hfRecursiveInteger (Int.ofNat bound))
        (hfRecursiveInteger (-Int.ofNat bound)))
      (hfRecursiveIntegerNonnegativeNegationGraph bound)

theorem hfRecursiveIntegerNonnegativeNegationGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerNonnegativeNegationGraph bound) ↔
      ∃ magnitude, magnitude < bound ∧
        input = hfRecursiveInteger (Int.ofNat magnitude) ∧
        output = hfRecursiveInteger (-Int.ofNat magnitude) := by
  induction bound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨magnitude, less, _, _⟩
        exact False.elim (Nat.not_lt_zero magnitude less)
  | succ bound ih =>
      rw [hfRecursiveIntegerNonnegativeNegationGraph,
        hfRecursiveMember_union_iff, hfRecursiveSingletonGraph_apply_iff, ih]
      constructor
      · rintro (⟨inputEq, outputEq⟩ | ⟨magnitude, less, inputEq, outputEq⟩)
        · exact ⟨bound, Nat.lt_succ_self bound, inputEq, outputEq⟩
        · exact ⟨magnitude, Nat.lt_trans less (Nat.lt_succ_self bound),
            inputEq, outputEq⟩
      · rintro ⟨magnitude, less, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ less) with earlier | rfl
        · exact Or.inr ⟨magnitude, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨inputEq, outputEq⟩

def hfRecursiveIntegerNegativeNegationGraph : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | bound + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph
        (hfRecursiveInteger (Int.negSucc bound))
        (hfRecursiveInteger (-Int.negSucc bound)))
      (hfRecursiveIntegerNegativeNegationGraph bound)

theorem hfRecursiveIntegerNegativeNegationGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerNegativeNegationGraph bound) ↔
      ∃ magnitude, magnitude < bound ∧
        input = hfRecursiveInteger (Int.negSucc magnitude) ∧
        output = hfRecursiveInteger (-Int.negSucc magnitude) := by
  induction bound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨magnitude, less, _, _⟩
        exact False.elim (Nat.not_lt_zero magnitude less)
  | succ bound ih =>
      rw [hfRecursiveIntegerNegativeNegationGraph,
        hfRecursiveMember_union_iff, hfRecursiveSingletonGraph_apply_iff, ih]
      constructor
      · rintro (⟨inputEq, outputEq⟩ | ⟨magnitude, less, inputEq, outputEq⟩)
        · exact ⟨bound, Nat.lt_succ_self bound, inputEq, outputEq⟩
        · exact ⟨magnitude, Nat.lt_trans less (Nat.lt_succ_self bound),
            inputEq, outputEq⟩
      · rintro ⟨magnitude, less, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ less) with earlier | rfl
        · exact Or.inr ⟨magnitude, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨inputEq, outputEq⟩

def hfRecursiveIntegerNegationGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveUnion
    (hfRecursiveIntegerNonnegativeNegationGraph bound)
    (hfRecursiveIntegerNegativeNegationGraph bound)

theorem hfRecursiveIntegerNegationGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerNegationGraph bound) ↔
      ∃ integer, HFRecursiveIntegerWithin bound integer ∧
        input = hfRecursiveInteger integer ∧
        output = hfRecursiveInteger (-integer) := by
  rw [hfRecursiveIntegerNegationGraph, hfRecursiveMember_union_iff,
    hfRecursiveIntegerNonnegativeNegationGraph_apply_iff,
    hfRecursiveIntegerNegativeNegationGraph_apply_iff]
  constructor
  · rintro (⟨magnitude, less, inputEq, outputEq⟩ |
      ⟨magnitude, less, inputEq, outputEq⟩)
    · exact ⟨Int.ofNat magnitude, less, inputEq, outputEq⟩
    · exact ⟨Int.negSucc magnitude, less, inputEq, outputEq⟩
  · rintro ⟨integer, within, inputEq, outputEq⟩
    cases integer with
    | ofNat magnitude => exact Or.inl ⟨magnitude, within, inputEq, outputEq⟩
    | negSucc magnitude => exact Or.inr ⟨magnitude, within, inputEq, outputEq⟩

theorem hfRecursiveIntegerNegationGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveIntegerNegationGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveIntegerNegationGraph_apply_iff bound input output₁).mp first with
    ⟨integer₁, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveIntegerNegationGraph_apply_iff bound input output₂).mp second with
    ⟨integer₂, _, inputEq₂, outputEq₂⟩
  have integerEq : integer₁ = integer₂ :=
    hfRecursiveInteger_injective (inputEq₁.symm.trans inputEq₂)
  subst integer₂
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveIntegerNegationGraph_total
    (bound : Nat) (integer : Int) (within : HFRecursiveIntegerWithin bound integer) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair (hfRecursiveInteger integer) output)
        (hfRecursiveIntegerNegationGraph bound) := by
  refine ⟨hfRecursiveInteger (-integer), ?_⟩
  exact (hfRecursiveIntegerNegationGraph_apply_iff bound _ _).mpr
    ⟨integer, within, rfl, rfl⟩

theorem hfRecursiveInteger_neg_neg (integer : Int) :
    hfRecursiveInteger (-(-integer)) = hfRecursiveInteger integer := by
  rw [Int.neg_neg]

def hfRecursiveIntegerWindow (bound : Nat) : List Int :=
  (List.range bound).map Int.ofNat ++
    (List.range bound).map Int.negSucc

theorem hfRecursiveInteger_mem_window_iff (bound : Nat) (integer : Int) :
    integer ∈ hfRecursiveIntegerWindow bound ↔
      HFRecursiveIntegerWithin bound integer := by
  cases integer with
  | ofNat magnitude =>
      constructor
      · intro member
        rcases List.mem_append.mp member with nonnegative | negative
        · rcases List.mem_map.mp nonnegative with ⟨index, indexMember, equal⟩
          injection equal with indexEq
          exact indexEq ▸ (List.mem_range.mp indexMember)
        · rcases List.mem_map.mp negative with ⟨index, _, equal⟩
          cases equal
      · intro less
        apply List.mem_append.mpr
        left
        exact List.mem_map.mpr ⟨magnitude, List.mem_range.mpr less, rfl⟩
  | negSucc magnitude =>
      constructor
      · intro member
        rcases List.mem_append.mp member with nonnegative | negative
        · rcases List.mem_map.mp nonnegative with ⟨index, _, equal⟩
          cases equal
        · rcases List.mem_map.mp negative with ⟨index, indexMember, equal⟩
          injection equal with indexEq
          exact indexEq ▸ (List.mem_range.mp indexMember)
      · intro less
        apply List.mem_append.mpr
        right
        exact List.mem_map.mpr ⟨magnitude, List.mem_range.mpr less, rfl⟩

def hfRecursiveIntegerBinaryRow
    (operation : Int → Int → Int) (right : Int) : List Int → HFRecursiveSet
  | [] => hfRecursiveEmpty
  | left :: rest =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph
        (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
        (hfRecursiveInteger (operation left right)))
      (hfRecursiveIntegerBinaryRow operation right rest)

theorem hfRecursiveIntegerBinaryRow_apply_iff
    (operation : Int → Int → Int) (right : Int) (lefts : List Int)
    (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerBinaryRow operation right lefts) ↔
      ∃ left, left ∈ lefts ∧
        input = hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right) ∧
        output = hfRecursiveInteger (operation left right) := by
  induction lefts with
  | nil =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨left, member, _, _⟩
        simp at member
  | cons head tail ih =>
      rw [hfRecursiveIntegerBinaryRow, hfRecursiveMember_union_iff,
        hfRecursiveSingletonGraph_apply_iff, ih]
      constructor
      · rintro (⟨inputEq, outputEq⟩ | ⟨left, member, inputEq, outputEq⟩)
        · exact ⟨head, by simp, inputEq, outputEq⟩
        · exact ⟨left, by simp [member], inputEq, outputEq⟩
      · rintro ⟨left, member, inputEq, outputEq⟩
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact Or.inl ⟨inputEq, outputEq⟩
        · exact Or.inr ⟨left, tailMember, inputEq, outputEq⟩

def hfRecursiveIntegerBinaryRows
    (operation : Int → Int → Int) (lefts : List Int) : List Int → HFRecursiveSet
  | [] => hfRecursiveEmpty
  | right :: rest =>
    hfRecursiveUnion
      (hfRecursiveIntegerBinaryRow operation right lefts)
      (hfRecursiveIntegerBinaryRows operation lefts rest)

theorem hfRecursiveIntegerBinaryRows_apply_iff
    (operation : Int → Int → Int) (lefts rights : List Int)
    (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerBinaryRows operation lefts rights) ↔
      ∃ left right, left ∈ lefts ∧ right ∈ rights ∧
        input = hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right) ∧
        output = hfRecursiveInteger (operation left right) := by
  induction rights with
  | nil =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨left, right, _, member, _, _⟩
        simp at member
  | cons head tail ih =>
      rw [hfRecursiveIntegerBinaryRows, hfRecursiveMember_union_iff,
        hfRecursiveIntegerBinaryRow_apply_iff, ih]
      constructor
      · rintro (⟨left, leftMember, inputEq, outputEq⟩ |
          ⟨left, right, leftMember, rightMember, inputEq, outputEq⟩)
        · exact ⟨left, head, leftMember, by simp, inputEq, outputEq⟩
        · exact ⟨left, right, leftMember, by simp [rightMember],
            inputEq, outputEq⟩
      · rintro ⟨left, right, leftMember, rightMember, inputEq, outputEq⟩
        rcases List.mem_cons.mp rightMember with rfl | tailMember
        · exact Or.inl ⟨left, leftMember, inputEq, outputEq⟩
        · exact Or.inr ⟨left, right, leftMember, tailMember, inputEq, outputEq⟩

def hfRecursiveIntegerAdditionGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveIntegerBinaryRows (fun left right => left + right)
    (hfRecursiveIntegerWindow bound) (hfRecursiveIntegerWindow bound)

theorem hfRecursiveIntegerAdditionGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerAdditionGraph bound) ↔
      ∃ left right,
        HFRecursiveIntegerWithin bound left ∧
        HFRecursiveIntegerWithin bound right ∧
        input = hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right) ∧
        output = hfRecursiveInteger (left + right) := by
  rw [hfRecursiveIntegerAdditionGraph,
    hfRecursiveIntegerBinaryRows_apply_iff]
  constructor
  · rintro ⟨left, right, leftMember, rightMember, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mp leftMember,
      (hfRecursiveInteger_mem_window_iff bound right).mp rightMember,
      inputEq, outputEq⟩
  · rintro ⟨left, right, leftWithin, rightWithin, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mpr leftWithin,
      (hfRecursiveInteger_mem_window_iff bound right).mpr rightWithin,
      inputEq, outputEq⟩

theorem hfRecursiveIntegerAdditionGraph_on_integers_iff
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerAdditionGraph bound) ↔
      output = hfRecursiveInteger (left + right) := by
  constructor
  · intro applies
    rcases (hfRecursiveIntegerAdditionGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveInteger_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveInteger_injective rightEq
    subst actualLeft
    subst actualRight
    exact outputEq
  · intro outputEq
    exact (hfRecursiveIntegerAdditionGraph_apply_iff bound _ _).mpr
      ⟨left, right, leftWithin, rightWithin, rfl, outputEq⟩

theorem hfRecursiveIntegerAdditionGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveIntegerAdditionGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveIntegerAdditionGraph_apply_iff bound input output₁).mp first with
    ⟨left₁, right₁, _, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveIntegerAdditionGraph_apply_iff bound input output₂).mp second with
    ⟨left₂, right₂, _, _, inputEq₂, outputEq₂⟩
  have pairEq := inputEq₁.symm.trans inputEq₂
  rcases hfRecursiveOrderedPair_injective pairEq with ⟨leftEq, rightEq⟩
  have leftIndexEq : left₁ = left₂ := hfRecursiveInteger_injective leftEq
  have rightIndexEq : right₁ = right₂ := hfRecursiveInteger_injective rightEq
  subst left₂
  subst right₂
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveIntegerAdditionGraph_total
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerAdditionGraph bound) := by
  refine ⟨hfRecursiveInteger (left + right), ?_⟩
  exact (hfRecursiveIntegerAdditionGraph_apply_iff bound _ _).mpr
    ⟨left, right, leftWithin, rightWithin, rfl, rfl⟩

def hfRecursiveIntegerSubtractionGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveIntegerBinaryRows (fun left right => left - right)
    (hfRecursiveIntegerWindow bound) (hfRecursiveIntegerWindow bound)

theorem hfRecursiveIntegerSubtractionGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerSubtractionGraph bound) ↔
      ∃ left right,
        HFRecursiveIntegerWithin bound left ∧
        HFRecursiveIntegerWithin bound right ∧
        input = hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right) ∧
        output = hfRecursiveInteger (left - right) := by
  rw [hfRecursiveIntegerSubtractionGraph,
    hfRecursiveIntegerBinaryRows_apply_iff]
  constructor
  · rintro ⟨left, right, leftMember, rightMember, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mp leftMember,
      (hfRecursiveInteger_mem_window_iff bound right).mp rightMember,
      inputEq, outputEq⟩
  · rintro ⟨left, right, leftWithin, rightWithin, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mpr leftWithin,
      (hfRecursiveInteger_mem_window_iff bound right).mpr rightWithin,
      inputEq, outputEq⟩

theorem hfRecursiveIntegerSubtractionGraph_on_integers_iff
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerSubtractionGraph bound) ↔
      output = hfRecursiveInteger (left - right) := by
  constructor
  · intro applies
    rcases (hfRecursiveIntegerSubtractionGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveInteger_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveInteger_injective rightEq
    subst actualLeft
    subst actualRight
    exact outputEq
  · intro outputEq
    exact (hfRecursiveIntegerSubtractionGraph_apply_iff bound _ _).mpr
      ⟨left, right, leftWithin, rightWithin, rfl, outputEq⟩

theorem hfRecursiveIntegerSubtractionGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveIntegerSubtractionGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveIntegerSubtractionGraph_apply_iff bound input output₁).mp first with
    ⟨left₁, right₁, _, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveIntegerSubtractionGraph_apply_iff bound input output₂).mp second with
    ⟨left₂, right₂, _, _, inputEq₂, outputEq₂⟩
  have pairEq := inputEq₁.symm.trans inputEq₂
  rcases hfRecursiveOrderedPair_injective pairEq with ⟨leftEq, rightEq⟩
  have leftIndexEq : left₁ = left₂ := hfRecursiveInteger_injective leftEq
  have rightIndexEq : right₁ = right₂ := hfRecursiveInteger_injective rightEq
  subst left₂
  subst right₂
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveIntegerSubtractionGraph_total
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerSubtractionGraph bound) := by
  refine ⟨hfRecursiveInteger (left - right), ?_⟩
  exact (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound left right leftWithin rightWithin _).mpr rfl

theorem hfRecursiveIntegerSubtractionGraph_self
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger integer)
            (hfRecursiveInteger integer)) output)
        (hfRecursiveIntegerSubtractionGraph bound) ↔
      output = hfRecursiveInteger 0 := by
  simpa using (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound integer integer within within output)

theorem hfRecursiveIntegerSubtractionGraph_zero_right
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer)
    (zeroWithin : HFRecursiveIntegerWithin bound 0) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger integer)
            (hfRecursiveInteger 0)) output)
        (hfRecursiveIntegerSubtractionGraph bound) ↔
      output = hfRecursiveInteger integer := by
  simpa using (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound integer 0 within zeroWithin output)

theorem hfRecursiveIntegerSubtractionGraph_add_cancel
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (differenceWithin : HFRecursiveIntegerWithin bound (left - right)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
          (hfRecursiveInteger (left - right)))
        (hfRecursiveIntegerSubtractionGraph bound) ∧
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (left - right))
            (hfRecursiveInteger right))
          (hfRecursiveInteger left))
        (hfRecursiveIntegerAdditionGraph bound) := by
  constructor
  · exact (hfRecursiveIntegerSubtractionGraph_on_integers_iff
      bound left right leftWithin rightWithin _).mpr rfl
  · apply (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound (left - right) right differenceWithin rightWithin _).mpr
    apply congrArg hfRecursiveInteger
    omega

theorem hfRecursiveIntegerSubtractionGraph_zero_left
    (bound : Nat) (integer : Int)
    (zeroWithin : HFRecursiveIntegerWithin bound 0)
    (within : HFRecursiveIntegerWithin bound integer) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger 0)
            (hfRecursiveInteger integer)) output)
        (hfRecursiveIntegerSubtractionGraph bound) ↔
      output = hfRecursiveInteger (-integer) := by
  simpa using (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound 0 integer zeroWithin within output)

theorem hfRecursiveIntegerSubtractionGraph_eq_add_neg
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (negRightWithin : HFRecursiveIntegerWithin bound (-right)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair (hfRecursiveInteger right)
          (hfRecursiveInteger (-right)))
        (hfRecursiveIntegerNegationGraph bound) ∧
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger (-right)))
          (hfRecursiveInteger (left - right)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right))
          (hfRecursiveInteger (left - right)))
        (hfRecursiveIntegerSubtractionGraph bound) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hfRecursiveIntegerNegationGraph_apply_iff bound _ _).mpr
      ⟨right, rightWithin, rfl, rfl⟩
  · apply (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound left (-right) leftWithin negRightWithin _).mpr
    apply congrArg hfRecursiveInteger
    omega
  · exact (hfRecursiveIntegerSubtractionGraph_on_integers_iff
      bound left right leftWithin rightWithin _).mpr rfl

theorem hfRecursiveIntegerSubtractionGraph_right_cancel
    (bound : Nat) (left₁ left₂ right : Int)
    (left₁Within : HFRecursiveIntegerWithin bound left₁)
    (left₂Within : HFRecursiveIntegerWithin bound left₂)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left₁)
          (hfRecursiveInteger right)) output)
      (hfRecursiveIntegerSubtractionGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left₂)
          (hfRecursiveInteger right)) output)
      (hfRecursiveIntegerSubtractionGraph bound)) :
    left₁ = left₂ := by
  have firstValue := (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound left₁ right left₁Within rightWithin output).mp first
  have secondValue := (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound left₂ right left₂Within rightWithin output).mp second
  have differenceEq : left₁ - right = left₂ - right :=
    hfRecursiveInteger_injective (firstValue.symm.trans secondValue)
  omega

theorem hfRecursiveIntegerSubtractionGraph_left_cancel
    (bound : Nat) (left right₁ right₂ : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (right₁Within : HFRecursiveIntegerWithin bound right₁)
    (right₂Within : HFRecursiveIntegerWithin bound right₂)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left)
          (hfRecursiveInteger right₁)) output)
      (hfRecursiveIntegerSubtractionGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left)
          (hfRecursiveInteger right₂)) output)
      (hfRecursiveIntegerSubtractionGraph bound)) :
    right₁ = right₂ := by
  have firstValue := (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound left right₁ leftWithin right₁Within output).mp first
  have secondValue := (hfRecursiveIntegerSubtractionGraph_on_integers_iff
    bound left right₂ leftWithin right₂Within output).mp second
  have differenceEq : left - right₁ = left - right₂ :=
    hfRecursiveInteger_injective (firstValue.symm.trans secondValue)
  omega

def hfRecursiveIntegerOrderGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveIntegerBinaryRows (fun left right => if left ≤ right then 1 else 0)
    (hfRecursiveIntegerWindow bound) (hfRecursiveIntegerWindow bound)

theorem hfRecursiveIntegerOrderGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerOrderGraph bound) ↔
      ∃ left right,
        HFRecursiveIntegerWithin bound left ∧
        HFRecursiveIntegerWithin bound right ∧
        input = hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right) ∧
        output = hfRecursiveInteger (if left ≤ right then 1 else 0) := by
  rw [hfRecursiveIntegerOrderGraph, hfRecursiveIntegerBinaryRows_apply_iff]
  constructor
  · rintro ⟨left, right, leftMember, rightMember, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mp leftMember,
      (hfRecursiveInteger_mem_window_iff bound right).mp rightMember,
      inputEq, outputEq⟩
  · rintro ⟨left, right, leftWithin, rightWithin, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mpr leftWithin,
      (hfRecursiveInteger_mem_window_iff bound right).mpr rightWithin,
      inputEq, outputEq⟩

theorem hfRecursiveIntegerOrderGraph_on_integers_iff
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerOrderGraph bound) ↔
      output = hfRecursiveInteger (if left ≤ right then 1 else 0) := by
  constructor
  · intro applies
    rcases (hfRecursiveIntegerOrderGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveInteger_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveInteger_injective rightEq
    subst actualLeft
    subst actualRight
    exact outputEq
  · intro outputEq
    exact (hfRecursiveIntegerOrderGraph_apply_iff bound _ _).mpr
      ⟨left, right, leftWithin, rightWithin, rfl, outputEq⟩

theorem hfRecursiveIntegerOrderGraph_holds_iff
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right)) (hfRecursiveInteger 1))
        (hfRecursiveIntegerOrderGraph bound) ↔ left ≤ right := by
  rw [hfRecursiveIntegerOrderGraph_on_integers_iff
    bound left right leftWithin rightWithin]
  constructor
  · intro encoded
    by_cases hle : left ≤ right
    · exact hle
    · have oneEqZero : (1 : Int) = 0 := by
        apply hfRecursiveInteger_injective
        simpa [hle] using encoded
      exact False.elim (by omega)
  · intro hle
    simp [hle]

theorem hfRecursiveIntegerOrderGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveIntegerOrderGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveIntegerOrderGraph_apply_iff bound input output₁).mp first with
    ⟨left₁, right₁, _, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveIntegerOrderGraph_apply_iff bound input output₂).mp second with
    ⟨left₂, right₂, _, _, inputEq₂, outputEq₂⟩
  have pairEq := inputEq₁.symm.trans inputEq₂
  rcases hfRecursiveOrderedPair_injective pairEq with ⟨leftEq, rightEq⟩
  have leftIndexEq : left₁ = left₂ := hfRecursiveInteger_injective leftEq
  have rightIndexEq : right₁ = right₂ := hfRecursiveInteger_injective rightEq
  subst left₂
  subst right₂
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveIntegerOrderGraph_total
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    ∃ output, HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right)) output)
      (hfRecursiveIntegerOrderGraph bound) := by
  refine ⟨hfRecursiveInteger (if left ≤ right then 1 else 0), ?_⟩
  exact (hfRecursiveIntegerOrderGraph_on_integers_iff
    bound left right leftWithin rightWithin _).mpr rfl

theorem hfRecursiveIntegerOrderGraph_refl
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer) :
    HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger integer) (hfRecursiveInteger integer))
        (hfRecursiveInteger 1))
      (hfRecursiveIntegerOrderGraph bound) :=
  (hfRecursiveIntegerOrderGraph_holds_iff bound integer integer within within).mpr
    (Int.le_refl integer)

theorem hfRecursiveIntegerOrderGraph_trans
    (bound : Nat) (left middle right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (middleWithin : HFRecursiveIntegerWithin bound middle)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger middle))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) →
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger middle) (hfRecursiveInteger right))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) →
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) := by
  intro leftMiddle middleRight
  apply (hfRecursiveIntegerOrderGraph_holds_iff
    bound left right leftWithin rightWithin).mpr
  exact Int.le_trans
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound left middle leftWithin middleWithin).mp leftMiddle)
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound middle right middleWithin rightWithin).mp middleRight)

theorem hfRecursiveIntegerOrderGraph_antisymm
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (leftRight : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
        (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound))
    (rightLeft : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger right) (hfRecursiveInteger left))
        (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound)) :
    left = right := by
  exact Int.le_antisymm
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound left right leftWithin rightWithin).mp leftRight)
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound right left rightWithin leftWithin).mp rightLeft)

theorem hfRecursiveIntegerOrderGraph_add_right
    (bound : Nat) (left right offset : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (sumLeftWithin : HFRecursiveIntegerWithin bound (left + offset))
    (sumRightWithin : HFRecursiveIntegerWithin bound (right + offset)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) →
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (left + offset))
            (hfRecursiveInteger (right + offset)))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) := by
  intro ordered
  apply (hfRecursiveIntegerOrderGraph_holds_iff bound
    (left + offset) (right + offset) sumLeftWithin sumRightWithin).mpr
  exact Int.add_le_add_right
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound left right leftWithin rightWithin).mp ordered) offset

theorem hfRecursiveIntegerOrderGraph_neg_reverses
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (negLeftWithin : HFRecursiveIntegerWithin bound (-left))
    (negRightWithin : HFRecursiveIntegerWithin bound (-right)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) →
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (-right))
            (hfRecursiveInteger (-left)))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) := by
  intro ordered
  apply (hfRecursiveIntegerOrderGraph_holds_iff bound
    (-right) (-left) negRightWithin negLeftWithin).mpr
  exact Int.neg_le_neg
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound left right leftWithin rightWithin).mp ordered)

theorem hfRecursiveIntegerOrderGraph_mul_nonnegative_right
    (bound : Nat) (left right factor : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (zeroWithin : HFRecursiveIntegerWithin bound 0)
    (factorWithin : HFRecursiveIntegerWithin bound factor)
    (leftProductWithin : HFRecursiveIntegerWithin bound (left * factor))
    (rightProductWithin : HFRecursiveIntegerWithin bound (right * factor))
    (ordered : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
        (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound))
    (nonnegative : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger 0) (hfRecursiveInteger factor))
        (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound)) :
    HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger (left * factor))
          (hfRecursiveInteger (right * factor)))
        (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) := by
  apply (hfRecursiveIntegerOrderGraph_holds_iff bound
    (left * factor) (right * factor) leftProductWithin rightProductWithin).mpr
  exact Int.mul_le_mul_of_nonneg_right
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound left right leftWithin rightWithin).mp ordered)
    ((hfRecursiveIntegerOrderGraph_holds_iff
      bound 0 factor zeroWithin factorWithin).mp nonnegative)

theorem hfRecursiveIntegerOrderGraph_total_order
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) ∨
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger right) (hfRecursiveInteger left))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) := by
  by_cases ordered : left ≤ right
  · exact Or.inl ((hfRecursiveIntegerOrderGraph_holds_iff
      bound left right leftWithin rightWithin).mpr ordered)
  · apply Or.inr
    apply (hfRecursiveIntegerOrderGraph_holds_iff
      bound right left rightWithin leftWithin).mpr
    omega

theorem hfRecursiveIntegerOrderGraph_both_iff_eq
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    (HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) ∧
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger right) (hfRecursiveInteger left))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound)) ↔
      left = right := by
  constructor
  · rintro ⟨leftRight, rightLeft⟩
    exact hfRecursiveIntegerOrderGraph_antisymm bound left right
      leftWithin rightWithin leftRight rightLeft
  · intro equal
    subst right
    exact ⟨hfRecursiveIntegerOrderGraph_refl bound left leftWithin,
      hfRecursiveIntegerOrderGraph_refl bound left leftWithin⟩

theorem hfRecursiveIntegerOrderGraph_add_right_iff
    (bound : Nat) (left right offset : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (sumLeftWithin : HFRecursiveIntegerWithin bound (left + offset))
    (sumRightWithin : HFRecursiveIntegerWithin bound (right + offset)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (left + offset))
            (hfRecursiveInteger (right + offset)))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) ↔
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
          (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) := by
  rw [hfRecursiveIntegerOrderGraph_holds_iff bound
      (left + offset) (right + offset) sumLeftWithin sumRightWithin,
    hfRecursiveIntegerOrderGraph_holds_iff bound
      left right leftWithin rightWithin]
  omega

def HFRecursiveIntegerStrictlyOrdered
    (bound : Nat) (left right : Int) : Prop :=
  HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right))
        (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound) ∧
    ¬ HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger right) (hfRecursiveInteger left))
        (hfRecursiveInteger 1)) (hfRecursiveIntegerOrderGraph bound)

theorem hfRecursiveIntegerStrictlyOrdered_iff
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    HFRecursiveIntegerStrictlyOrdered bound left right ↔ left < right := by
  unfold HFRecursiveIntegerStrictlyOrdered
  rw [hfRecursiveIntegerOrderGraph_holds_iff
      bound left right leftWithin rightWithin,
    hfRecursiveIntegerOrderGraph_holds_iff
      bound right left rightWithin leftWithin]
  omega

theorem hfRecursiveIntegerStrictlyOrdered_irrefl
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer) :
    ¬ HFRecursiveIntegerStrictlyOrdered bound integer integer := by
  rw [hfRecursiveIntegerStrictlyOrdered_iff bound integer integer within within]
  exact Int.lt_irrefl integer

theorem hfRecursiveIntegerStrictlyOrdered_trans
    (bound : Nat) (left middle right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (middleWithin : HFRecursiveIntegerWithin bound middle)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    HFRecursiveIntegerStrictlyOrdered bound left middle →
      HFRecursiveIntegerStrictlyOrdered bound middle right →
        HFRecursiveIntegerStrictlyOrdered bound left right := by
  rw [hfRecursiveIntegerStrictlyOrdered_iff
      bound left middle leftWithin middleWithin,
    hfRecursiveIntegerStrictlyOrdered_iff
      bound middle right middleWithin rightWithin,
    hfRecursiveIntegerStrictlyOrdered_iff
      bound left right leftWithin rightWithin]
  exact Int.lt_trans

theorem hfRecursiveIntegerStrictlyOrdered_asymm
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    HFRecursiveIntegerStrictlyOrdered bound left right →
      ¬ HFRecursiveIntegerStrictlyOrdered bound right left := by
  rw [hfRecursiveIntegerStrictlyOrdered_iff
      bound left right leftWithin rightWithin,
    hfRecursiveIntegerStrictlyOrdered_iff
      bound right left rightWithin leftWithin]
  exact Int.lt_asymm

theorem hfRecursiveIntegerStrictlyOrdered_add_right_iff
    (bound : Nat) (left right offset : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (sumLeftWithin : HFRecursiveIntegerWithin bound (left + offset))
    (sumRightWithin : HFRecursiveIntegerWithin bound (right + offset)) :
    HFRecursiveIntegerStrictlyOrdered bound (left + offset) (right + offset) ↔
      HFRecursiveIntegerStrictlyOrdered bound left right := by
  rw [hfRecursiveIntegerStrictlyOrdered_iff bound
      (left + offset) (right + offset) sumLeftWithin sumRightWithin,
    hfRecursiveIntegerStrictlyOrdered_iff bound
      left right leftWithin rightWithin]
  omega

def hfRecursiveIntegerMultiplicationGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveIntegerBinaryRows (fun left right => left * right)
    (hfRecursiveIntegerWindow bound) (hfRecursiveIntegerWindow bound)

theorem hfRecursiveIntegerMultiplicationGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveIntegerMultiplicationGraph bound) ↔
      ∃ left right,
        HFRecursiveIntegerWithin bound left ∧
        HFRecursiveIntegerWithin bound right ∧
        input = hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right) ∧
        output = hfRecursiveInteger (left * right) := by
  rw [hfRecursiveIntegerMultiplicationGraph,
    hfRecursiveIntegerBinaryRows_apply_iff]
  constructor
  · rintro ⟨left, right, leftMember, rightMember, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mp leftMember,
      (hfRecursiveInteger_mem_window_iff bound right).mp rightMember,
      inputEq, outputEq⟩
  · rintro ⟨left, right, leftWithin, rightWithin, inputEq, outputEq⟩
    exact ⟨left, right,
      (hfRecursiveInteger_mem_window_iff bound left).mpr leftWithin,
      (hfRecursiveInteger_mem_window_iff bound right).mpr rightWithin,
      inputEq, outputEq⟩

theorem hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) ↔
      output = hfRecursiveInteger (left * right) := by
  constructor
  · intro applies
    rcases (hfRecursiveIntegerMultiplicationGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveInteger_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveInteger_injective rightEq
    subst actualLeft
    subst actualRight
    exact outputEq
  · intro outputEq
    exact (hfRecursiveIntegerMultiplicationGraph_apply_iff bound _ _).mpr
      ⟨left, right, leftWithin, rightWithin, rfl, outputEq⟩

theorem hfRecursiveIntegerMultiplicationGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveIntegerMultiplicationGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveIntegerMultiplicationGraph_apply_iff bound input output₁).mp first with
    ⟨left₁, right₁, _, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveIntegerMultiplicationGraph_apply_iff bound input output₂).mp second with
    ⟨left₂, right₂, _, _, inputEq₂, outputEq₂⟩
  have pairEq := inputEq₁.symm.trans inputEq₂
  rcases hfRecursiveOrderedPair_injective pairEq with ⟨leftEq, rightEq⟩
  have leftIndexEq : left₁ = left₂ := hfRecursiveInteger_injective leftEq
  have rightIndexEq : right₁ = right₂ := hfRecursiveInteger_injective rightEq
  subst left₂
  subst right₂
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveIntegerMultiplicationGraph_total
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left) (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) := by
  refine ⟨hfRecursiveInteger (left * right), ?_⟩
  exact (hfRecursiveIntegerMultiplicationGraph_apply_iff bound _ _).mpr
    ⟨left, right, leftWithin, rightWithin, rfl, rfl⟩

theorem hfRecursiveIntegerAdditionGraph_comm
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerAdditionGraph bound) ↔
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger right)
            (hfRecursiveInteger left)) output)
        (hfRecursiveIntegerAdditionGraph bound) := by
  rw [hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound left right leftWithin rightWithin,
    hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound right left rightWithin leftWithin,
    Int.add_comm left right]

theorem hfRecursiveIntegerMultiplicationGraph_comm
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) ↔
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger right)
            (hfRecursiveInteger left)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) := by
  rw [hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound left right leftWithin rightWithin,
    hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound right left rightWithin leftWithin,
    Int.mul_comm left right]

theorem hfRecursiveIntegerAdditionGraph_add_neg
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer)
    (negWithin : HFRecursiveIntegerWithin bound (-integer))
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger integer)
            (hfRecursiveInteger (-integer))) output)
        (hfRecursiveIntegerAdditionGraph bound) ↔
      output = hfRecursiveInteger 0 := by
  rw [hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound integer (-integer) within negWithin]
  have cancels : integer + -integer = 0 := by omega
  rw [cancels]

theorem hfRecursiveIntegerAdditionGraph_neg_add
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer)
    (negWithin : HFRecursiveIntegerWithin bound (-integer))
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (-integer))
            (hfRecursiveInteger integer)) output)
        (hfRecursiveIntegerAdditionGraph bound) ↔
      output = hfRecursiveInteger 0 := by
  rw [hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound (-integer) integer negWithin within]
  have cancels : -integer + integer = 0 := by omega
  rw [cancels]

theorem hfRecursiveIntegerAdditionGraph_zero_right
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer)
    (zeroWithin : HFRecursiveIntegerWithin bound 0)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger integer)
            (hfRecursiveInteger 0)) output)
        (hfRecursiveIntegerAdditionGraph bound) ↔
      output = hfRecursiveInteger integer := by
  rw [hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound integer 0 within zeroWithin, Int.add_zero]

theorem hfRecursiveIntegerAdditionGraph_zero_left
    (bound : Nat) (integer : Int)
    (zeroWithin : HFRecursiveIntegerWithin bound 0)
    (within : HFRecursiveIntegerWithin bound integer)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger 0)
            (hfRecursiveInteger integer)) output)
        (hfRecursiveIntegerAdditionGraph bound) ↔
      output = hfRecursiveInteger integer := by
  rw [hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound 0 integer zeroWithin within, Int.zero_add]

theorem hfRecursiveIntegerMultiplicationGraph_zero_right
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer)
    (zeroWithin : HFRecursiveIntegerWithin bound 0)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger integer)
            (hfRecursiveInteger 0)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) ↔
      output = hfRecursiveInteger 0 := by
  rw [hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound integer 0 within zeroWithin, Int.mul_zero]

theorem hfRecursiveIntegerMultiplicationGraph_zero_left
    (bound : Nat) (integer : Int)
    (zeroWithin : HFRecursiveIntegerWithin bound 0)
    (within : HFRecursiveIntegerWithin bound integer)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger 0)
            (hfRecursiveInteger integer)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) ↔
      output = hfRecursiveInteger 0 := by
  rw [hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound 0 integer zeroWithin within, Int.zero_mul]

theorem hfRecursiveIntegerMultiplicationGraph_one_right
    (bound : Nat) (integer : Int)
    (within : HFRecursiveIntegerWithin bound integer)
    (oneWithin : HFRecursiveIntegerWithin bound 1)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger integer)
            (hfRecursiveInteger 1)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) ↔
      output = hfRecursiveInteger integer := by
  rw [hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound integer 1 within oneWithin, Int.mul_one]

theorem hfRecursiveIntegerMultiplicationGraph_one_left
    (bound : Nat) (integer : Int)
    (oneWithin : HFRecursiveIntegerWithin bound 1)
    (within : HFRecursiveIntegerWithin bound integer)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger 1)
            (hfRecursiveInteger integer)) output)
        (hfRecursiveIntegerMultiplicationGraph bound) ↔
      output = hfRecursiveInteger integer := by
  rw [hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound 1 integer oneWithin within, Int.one_mul]

theorem hfRecursiveIntegerAdditionGraph_associative
    (bound : Nat) (a b c : Int)
    (aWithin : HFRecursiveIntegerWithin bound a)
    (bWithin : HFRecursiveIntegerWithin bound b)
    (cWithin : HFRecursiveIntegerWithin bound c)
    (abWithin : HFRecursiveIntegerWithin bound (a + b))
    (bcWithin : HFRecursiveIntegerWithin bound (b + c)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger b))
          (hfRecursiveInteger (a + b)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (a + b)) (hfRecursiveInteger c))
          (hfRecursiveInteger ((a + b) + c)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger b) (hfRecursiveInteger c))
          (hfRecursiveInteger (b + c)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger (b + c)))
          (hfRecursiveInteger (a + (b + c))))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    hfRecursiveInteger ((a + b) + c) = hfRecursiveInteger (a + (b + c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound a b aWithin bWithin _).mpr rfl
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound (a + b) c abWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound b c bWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound a (b + c) aWithin bcWithin _).mpr rfl
  · exact congrArg hfRecursiveInteger (Int.add_assoc a b c)

theorem hfRecursiveIntegerMultiplicationGraph_associative
    (bound : Nat) (a b c : Int)
    (aWithin : HFRecursiveIntegerWithin bound a)
    (bWithin : HFRecursiveIntegerWithin bound b)
    (cWithin : HFRecursiveIntegerWithin bound c)
    (abWithin : HFRecursiveIntegerWithin bound (a * b))
    (bcWithin : HFRecursiveIntegerWithin bound (b * c)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger b))
          (hfRecursiveInteger (a * b)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (a * b)) (hfRecursiveInteger c))
          (hfRecursiveInteger ((a * b) * c)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger b) (hfRecursiveInteger c))
          (hfRecursiveInteger (b * c)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger (b * c)))
          (hfRecursiveInteger (a * (b * c))))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    hfRecursiveInteger ((a * b) * c) = hfRecursiveInteger (a * (b * c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound a b aWithin bWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound (a * b) c abWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound b c bWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound a (b * c) aWithin bcWithin _).mpr rfl
  · exact congrArg hfRecursiveInteger (Int.mul_assoc a b c)

theorem hfRecursiveIntegerMultiplicationGraph_distributes_over_addition
    (bound : Nat) (a b c : Int)
    (aWithin : HFRecursiveIntegerWithin bound a)
    (bWithin : HFRecursiveIntegerWithin bound b)
    (cWithin : HFRecursiveIntegerWithin bound c)
    (bcWithin : HFRecursiveIntegerWithin bound (b + c))
    (abWithin : HFRecursiveIntegerWithin bound (a * b))
    (acWithin : HFRecursiveIntegerWithin bound (a * c)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger b) (hfRecursiveInteger c))
          (hfRecursiveInteger (b + c)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger (b + c)))
          (hfRecursiveInteger (a * (b + c))))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger b))
          (hfRecursiveInteger (a * b)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger c))
          (hfRecursiveInteger (a * c)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (a * b))
            (hfRecursiveInteger (a * c)))
          (hfRecursiveInteger (a * b + a * c)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    hfRecursiveInteger (a * (b + c)) =
      hfRecursiveInteger (a * b + a * c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound b c bWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound a (b + c) aWithin bcWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound a b aWithin bWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound a c aWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound (a * b) (a * c) abWithin acWithin _).mpr rfl
  · exact congrArg hfRecursiveInteger (Int.mul_add a b c)

theorem hfRecursiveIntegerMultiplicationGraph_right_distributes_over_addition
    (bound : Nat) (a b c : Int)
    (aWithin : HFRecursiveIntegerWithin bound a)
    (bWithin : HFRecursiveIntegerWithin bound b)
    (cWithin : HFRecursiveIntegerWithin bound c)
    (abWithin : HFRecursiveIntegerWithin bound (a + b))
    (acWithin : HFRecursiveIntegerWithin bound (a * c))
    (bcWithin : HFRecursiveIntegerWithin bound (b * c)) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger b))
          (hfRecursiveInteger (a + b)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (a + b)) (hfRecursiveInteger c))
          (hfRecursiveInteger ((a + b) * c)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger a) (hfRecursiveInteger c))
          (hfRecursiveInteger (a * c)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger b) (hfRecursiveInteger c))
          (hfRecursiveInteger (b * c)))
        (hfRecursiveIntegerMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger (a * c))
            (hfRecursiveInteger (b * c)))
          (hfRecursiveInteger (a * c + b * c)))
        (hfRecursiveIntegerAdditionGraph bound) ∧
    hfRecursiveInteger ((a + b) * c) =
      hfRecursiveInteger (a * c + b * c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound a b aWithin bWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound (a + b) c abWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound a c aWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
      bound b c bWithin cWithin _).mpr rfl
  · exact (hfRecursiveIntegerAdditionGraph_on_integers_iff
      bound (a * c) (b * c) acWithin bcWithin _).mpr rfl
  · exact congrArg hfRecursiveInteger (Int.add_mul a b c)

theorem hfRecursiveIntegerAdditionGraph_right_cancel
    (bound : Nat) (left₁ left₂ right : Int)
    (left₁Within : HFRecursiveIntegerWithin bound left₁)
    (left₂Within : HFRecursiveIntegerWithin bound left₂)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left₁)
          (hfRecursiveInteger right)) output)
      (hfRecursiveIntegerAdditionGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left₂)
          (hfRecursiveInteger right)) output)
      (hfRecursiveIntegerAdditionGraph bound)) :
    left₁ = left₂ := by
  have firstValue := (hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound left₁ right left₁Within rightWithin output).mp first
  have secondValue := (hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound left₂ right left₂Within rightWithin output).mp second
  have sumEq : left₁ + right = left₂ + right :=
    hfRecursiveInteger_injective (firstValue.symm.trans secondValue)
  omega

theorem hfRecursiveIntegerAdditionGraph_left_cancel
    (bound : Nat) (left right₁ right₂ : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (right₁Within : HFRecursiveIntegerWithin bound right₁)
    (right₂Within : HFRecursiveIntegerWithin bound right₂)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left)
          (hfRecursiveInteger right₁)) output)
      (hfRecursiveIntegerAdditionGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left)
          (hfRecursiveInteger right₂)) output)
      (hfRecursiveIntegerAdditionGraph bound)) :
    right₁ = right₂ := by
  have firstValue := (hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound left right₁ leftWithin right₁Within output).mp first
  have secondValue := (hfRecursiveIntegerAdditionGraph_on_integers_iff
    bound left right₂ leftWithin right₂Within output).mp second
  have sumEq : left + right₁ = left + right₂ :=
    hfRecursiveInteger_injective (firstValue.symm.trans secondValue)
  exact Int.add_left_cancel sumEq

theorem hfRecursiveIntegerMultiplicationGraph_right_cancel
    (bound : Nat) (left₁ left₂ right : Int)
    (left₁Within : HFRecursiveIntegerWithin bound left₁)
    (left₂Within : HFRecursiveIntegerWithin bound left₂)
    (rightWithin : HFRecursiveIntegerWithin bound right)
    (rightNonzero : right ≠ 0) (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left₁)
          (hfRecursiveInteger right)) output)
      (hfRecursiveIntegerMultiplicationGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left₂)
          (hfRecursiveInteger right)) output)
      (hfRecursiveIntegerMultiplicationGraph bound)) :
    left₁ = left₂ := by
  have firstValue := (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound left₁ right left₁Within rightWithin output).mp first
  have secondValue := (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound left₂ right left₂Within rightWithin output).mp second
  have productEq : left₁ * right = left₂ * right :=
    hfRecursiveInteger_injective (firstValue.symm.trans secondValue)
  exact Int.eq_of_mul_eq_mul_right rightNonzero productEq

theorem hfRecursiveIntegerMultiplicationGraph_left_cancel
    (bound : Nat) (left right₁ right₂ : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (leftNonzero : left ≠ 0)
    (right₁Within : HFRecursiveIntegerWithin bound right₁)
    (right₂Within : HFRecursiveIntegerWithin bound right₂)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left)
          (hfRecursiveInteger right₁)) output)
      (hfRecursiveIntegerMultiplicationGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveInteger left)
          (hfRecursiveInteger right₂)) output)
      (hfRecursiveIntegerMultiplicationGraph bound)) :
    right₁ = right₂ := by
  have firstValue := (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound left right₁ leftWithin right₁Within output).mp first
  have secondValue := (hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound left right₂ leftWithin right₂Within output).mp second
  have productEq : left * right₁ = left * right₂ :=
    hfRecursiveInteger_injective (firstValue.symm.trans secondValue)
  exact Int.eq_of_mul_eq_mul_left leftNonzero productEq

theorem hfRecursiveIntegerMultiplicationGraph_eq_zero_iff
    (bound : Nat) (left right : Int)
    (leftWithin : HFRecursiveIntegerWithin bound left)
    (rightWithin : HFRecursiveIntegerWithin bound right) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveInteger left)
            (hfRecursiveInteger right))
          (hfRecursiveInteger 0))
        (hfRecursiveIntegerMultiplicationGraph bound) ↔
      left = 0 ∨ right = 0 := by
  rw [hfRecursiveIntegerMultiplicationGraph_on_integers_iff
    bound left right leftWithin rightWithin]
  constructor
  · intro valueEq
    have indexEq : 0 = left * right := hfRecursiveInteger_injective valueEq
    exact Int.mul_eq_zero.mp indexEq.symm
  · intro zeroFactor
    apply congrArg hfRecursiveInteger
    exact (Int.mul_eq_zero.mpr zeroFactor).symm

/- The graph of the identity function on the internally represented finite
   ordinal `n`. -/
def hfRecursiveNatIdentityGraph : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | n + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph (hfRecursiveNat n) (hfRecursiveNat n))
      (hfRecursiveNatIdentityGraph n)

theorem hfRecursiveNatIdentityGraph_apply_iff
    (n : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatIdentityGraph n) ↔
        ∃ m, m < n ∧ input = hfRecursiveNat m ∧ output = hfRecursiveNat m := by
  induction n with
  | zero =>
    constructor
    · intro h
      exact False.elim (hfRecursiveMember_empty _ h)
    · rintro ⟨m, hm, _, _⟩
      exact False.elim (Nat.not_lt_zero _ hm)
  | succ n ih =>
    rw [hfRecursiveNatIdentityGraph, hfRecursiveMember_union_iff,
      hfRecursiveSingletonGraph_apply_iff, ih]
    constructor
    · rintro (⟨hinput, houtput⟩ | ⟨m, hm, hinput, houtput⟩)
      · exact ⟨n, Nat.lt_succ_self n, hinput, houtput⟩
      · exact ⟨m, Nat.lt_trans hm (Nat.lt_succ_self n), hinput, houtput⟩
    · rintro ⟨m, hm, hinput, houtput⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hmn | rfl
      · exact Or.inr ⟨m, hmn, hinput, houtput⟩
      · exact Or.inl ⟨hinput, houtput⟩

theorem hfRecursiveNatIdentityGraph_relation (n : Nat) :
    HFRecursiveRelation (hfRecursiveNatIdentityGraph n) := by
  induction n with
  | zero =>
    intro element helement
    exact False.elim (hfRecursiveMember_empty _ helement)
  | succ n ih =>
    intro element helement
    rcases (hfRecursiveMember_union_iff element
      (hfRecursiveSingletonGraph (hfRecursiveNat n) (hfRecursiveNat n))
      (hfRecursiveNatIdentityGraph n)).mp helement with hsingle | htail
    · exact ⟨hfRecursiveNat n, hfRecursiveNat n,
        (hfRecursiveMember_singleton_iff element
          (hfRecursiveOrderedPair (hfRecursiveNat n) (hfRecursiveNat n))).mp hsingle⟩
    · exact ih element htail

theorem hfRecursiveNatIdentityGraph_functional (n : Nat) :
    HFRecursiveFunctional (hfRecursiveNatIdentityGraph n) := by
  intro input output₁ output₂ h₁ h₂
  rcases (hfRecursiveNatIdentityGraph_apply_iff n input output₁).mp h₁ with
    ⟨m, hm, him, hom⟩
  rcases (hfRecursiveNatIdentityGraph_apply_iff n input output₂).mp h₂ with
    ⟨k, hk, hik, hok⟩
  have hmk : m = k := hfRecursiveNat_injective (him.symm.trans hik)
  subst k
  exact hom.trans hok.symm

theorem hfRecursiveNatIdentityGraph_total (n m : Nat) (hm : m < n) :
    ∃ output,
      HFRecursiveMember (hfRecursiveOrderedPair (hfRecursiveNat m) output)
        (hfRecursiveNatIdentityGraph n) := by
  refine ⟨hfRecursiveNat m, ?_⟩
  exact (hfRecursiveNatIdentityGraph_apply_iff n (hfRecursiveNat m)
    (hfRecursiveNat m)).mpr ⟨m, hm, rfl, rfl⟩

/- The successor graph on the finite ordinal `n`: it maps each `m < n` to
   the internally represented ordinal `m + 1`. -/
def hfRecursiveNatSuccessorGraph : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | n + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph (hfRecursiveNat n) (hfRecursiveNat (n + 1)))
      (hfRecursiveNatSuccessorGraph n)

theorem hfRecursiveNatSuccessorGraph_apply_iff
    (n : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatSuccessorGraph n) ↔
        ∃ m, m < n ∧ input = hfRecursiveNat m ∧ output = hfRecursiveNat (m + 1) := by
  induction n with
  | zero =>
    constructor
    · intro h
      exact False.elim (hfRecursiveMember_empty _ h)
    · rintro ⟨m, hm, _, _⟩
      exact False.elim (Nat.not_lt_zero _ hm)
  | succ n ih =>
    rw [hfRecursiveNatSuccessorGraph, hfRecursiveMember_union_iff,
      hfRecursiveSingletonGraph_apply_iff, ih]
    constructor
    · rintro (⟨hinput, houtput⟩ | ⟨m, hm, hinput, houtput⟩)
      · exact ⟨n, Nat.lt_succ_self n, hinput, houtput⟩
      · exact ⟨m, Nat.lt_trans hm (Nat.lt_succ_self n), hinput, houtput⟩
    · rintro ⟨m, hm, hinput, houtput⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hmn | rfl
      · exact Or.inr ⟨m, hmn, hinput, houtput⟩
      · exact Or.inl ⟨hinput, houtput⟩

theorem hfRecursiveNatSuccessorGraph_functional (n : Nat) :
    HFRecursiveFunctional (hfRecursiveNatSuccessorGraph n) := by
  intro input output₁ output₂ h₁ h₂
  rcases (hfRecursiveNatSuccessorGraph_apply_iff n input output₁).mp h₁ with
    ⟨m, hm, him, hom⟩
  rcases (hfRecursiveNatSuccessorGraph_apply_iff n input output₂).mp h₂ with
    ⟨k, hk, hik, hok⟩
  have hmk : m = k := hfRecursiveNat_injective (him.symm.trans hik)
  subst k
  exact hom.trans hok.symm

theorem hfRecursiveNatSuccessorGraph_total (n m : Nat) (hm : m < n) :
    ∃ output,
      HFRecursiveMember (hfRecursiveOrderedPair (hfRecursiveNat m) output)
        (hfRecursiveNatSuccessorGraph n) := by
  refine ⟨hfRecursiveNat (m + 1), ?_⟩
  exact (hfRecursiveNatSuccessorGraph_apply_iff n (hfRecursiveNat m)
    (hfRecursiveNat (m + 1))).mpr ⟨m, hm, rfl, rfl⟩

/- Finite ordinal translation by a fixed natural offset. -/
def hfRecursiveNatShiftGraph (offset : Nat) : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | n + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph (hfRecursiveNat n) (hfRecursiveNat (n + offset)))
      (hfRecursiveNatShiftGraph offset n)

theorem hfRecursiveNatShiftGraph_apply_iff
    (offset n : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatShiftGraph offset n) ↔
        ∃ m, m < n ∧ input = hfRecursiveNat m ∧ output = hfRecursiveNat (m + offset) := by
  induction n with
  | zero =>
    constructor
    · intro h
      exact False.elim (hfRecursiveMember_empty _ h)
    · rintro ⟨m, hm, _, _⟩
      exact False.elim (Nat.not_lt_zero _ hm)
  | succ n ih =>
    rw [hfRecursiveNatShiftGraph, hfRecursiveMember_union_iff,
      hfRecursiveSingletonGraph_apply_iff, ih]
    constructor
    · rintro (⟨hinput, houtput⟩ | ⟨m, hm, hinput, houtput⟩)
      · exact ⟨n, Nat.lt_succ_self n, hinput, houtput⟩
      · exact ⟨m, Nat.lt_trans hm (Nat.lt_succ_self n), hinput, houtput⟩
    · rintro ⟨m, hm, hinput, houtput⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hmn | rfl
      · exact Or.inr ⟨m, hmn, hinput, houtput⟩
      · exact Or.inl ⟨hinput, houtput⟩

theorem hfRecursiveNatShiftGraph_functional (offset n : Nat) :
    HFRecursiveFunctional (hfRecursiveNatShiftGraph offset n) := by
  intro input output₁ output₂ h₁ h₂
  rcases (hfRecursiveNatShiftGraph_apply_iff offset n input output₁).mp h₁ with
    ⟨m, hm, him, hom⟩
  rcases (hfRecursiveNatShiftGraph_apply_iff offset n input output₂).mp h₂ with
    ⟨k, hk, hik, hok⟩
  have hmk : m = k := hfRecursiveNat_injective (him.symm.trans hik)
  subst k
  exact hom.trans hok.symm

theorem hfRecursiveNatShiftGraph_total (offset n m : Nat) (hm : m < n) :
    ∃ output,
      HFRecursiveMember (hfRecursiveOrderedPair (hfRecursiveNat m) output)
        (hfRecursiveNatShiftGraph offset n) := by
  refine ⟨hfRecursiveNat (m + offset), ?_⟩
  exact (hfRecursiveNatShiftGraph_apply_iff offset n (hfRecursiveNat m)
    (hfRecursiveNat (m + offset))).mpr ⟨m, hm, rfl, rfl⟩

/- One row of the bounded internal addition graph: the right summand is
   fixed, while the left summand ranges over the finite ordinal `leftBound`. -/
def hfRecursiveNatAdditionRow (right : Nat) : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | leftBound + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph
        (hfRecursiveOrderedPair (hfRecursiveNat leftBound) (hfRecursiveNat right))
        (hfRecursiveNat (leftBound + right)))
      (hfRecursiveNatAdditionRow right leftBound)

theorem hfRecursiveNatAdditionRow_apply_iff
    (right leftBound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatAdditionRow right leftBound) ↔
      ∃ left, left < leftBound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right) ∧
        output = hfRecursiveNat (left + right) := by
  induction leftBound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨left, less, _, _⟩
        exact False.elim (Nat.not_lt_zero left less)
  | succ leftBound ih =>
      rw [hfRecursiveNatAdditionRow, hfRecursiveMember_union_iff,
        hfRecursiveSingletonGraph_apply_iff, ih]
      constructor
      · rintro (⟨inputEq, outputEq⟩ | ⟨left, less, inputEq, outputEq⟩)
        · exact ⟨leftBound, Nat.lt_succ_self leftBound, inputEq, outputEq⟩
        · exact ⟨left, Nat.lt_trans less (Nat.lt_succ_self leftBound),
            inputEq, outputEq⟩
      · rintro ⟨left, less, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ less) with earlier | rfl
        · exact Or.inr ⟨left, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨inputEq, outputEq⟩

/- Rows for all right summands below `rightBound`. -/
def hfRecursiveNatAdditionRows (leftBound : Nat) : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | rightBound + 1 =>
    hfRecursiveUnion (hfRecursiveNatAdditionRow rightBound leftBound)
      (hfRecursiveNatAdditionRows leftBound rightBound)

theorem hfRecursiveNatAdditionRows_apply_iff
    (leftBound rightBound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatAdditionRows leftBound rightBound) ↔
      ∃ left right, left < leftBound ∧ right < rightBound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right) ∧
        output = hfRecursiveNat (left + right) := by
  induction rightBound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨left, right, _, less, _, _⟩
        exact False.elim (Nat.not_lt_zero right less)
  | succ rightBound ih =>
      rw [hfRecursiveNatAdditionRows, hfRecursiveMember_union_iff,
        hfRecursiveNatAdditionRow_apply_iff, ih]
      constructor
      · rintro (⟨left, leftLess, inputEq, outputEq⟩ |
          ⟨left, right, leftLess, rightLess, inputEq, outputEq⟩)
        · exact ⟨left, rightBound, leftLess, Nat.lt_succ_self rightBound,
            inputEq, outputEq⟩
        · exact ⟨left, right, leftLess,
            Nat.lt_trans rightLess (Nat.lt_succ_self rightBound),
            inputEq, outputEq⟩
      · rintro ⟨left, right, leftLess, rightLess, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ rightLess) with earlier | rfl
        · exact Or.inr ⟨left, right, leftLess, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨left, leftLess, inputEq, outputEq⟩

def hfRecursiveNatAdditionGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveNatAdditionRows bound bound

theorem hfRecursiveNatAdditionGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatAdditionGraph bound) ↔
      ∃ left right, left < bound ∧ right < bound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right) ∧
        output = hfRecursiveNat (left + right) :=
  hfRecursiveNatAdditionRows_apply_iff bound bound input output

theorem hfRecursiveNatAdditionGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveNatAdditionGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveNatAdditionGraph_apply_iff bound input output₁).mp first with
    ⟨left, right, _, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveNatAdditionGraph_apply_iff bound input output₂).mp second with
    ⟨left', right', _, _, inputEq₂, outputEq₂⟩
  have pairEq := inputEq₁.symm.trans inputEq₂
  rcases hfRecursiveOrderedPair_injective pairEq with ⟨leftEq, rightEq⟩
  have leftIndexEq : left = left' := hfRecursiveNat_injective leftEq
  have rightIndexEq : right = right' := hfRecursiveNat_injective rightEq
  subst left'
  subst right'
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveNatAdditionGraph_total
    (bound left right : Nat) (leftLess : left < bound)
    (rightLess : right < bound) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right)) output)
        (hfRecursiveNatAdditionGraph bound) := by
  refine ⟨hfRecursiveNat (left + right), ?_⟩
  exact (hfRecursiveNatAdditionGraph_apply_iff bound _ _).mpr
    ⟨left, right, leftLess, rightLess, rfl, rfl⟩

theorem hfRecursiveNatAdditionGraph_on_nats_iff
    (bound left right : Nat) (leftLess : left < bound)
    (rightLess : right < bound) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right)) output)
        (hfRecursiveNatAdditionGraph bound) ↔
      output = hfRecursiveNat (left + right) := by
  constructor
  · intro applies
    rcases (hfRecursiveNatAdditionGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with
      ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveNat_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveNat_injective rightEq
    subst actualLeft
    subst actualRight
    exact outputEq
  · intro outputEq
    exact (hfRecursiveNatAdditionGraph_apply_iff bound _ _).mpr
      ⟨left, right, leftLess, rightLess, rfl, outputEq⟩

theorem hfRecursiveNatAdditionGraph_zero_right
    (bound left : Nat) (leftLess : left < bound) (zeroLess : 0 < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat 0)) output)
        (hfRecursiveNatAdditionGraph bound) ↔
      output = hfRecursiveNat left := by
  rw [hfRecursiveNatAdditionGraph_on_nats_iff bound left 0 leftLess zeroLess,
    Nat.add_zero]

theorem hfRecursiveNatAdditionGraph_zero_left
    (bound right : Nat) (zeroLess : 0 < bound) (rightLess : right < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat 0) (hfRecursiveNat right)) output)
        (hfRecursiveNatAdditionGraph bound) ↔
      output = hfRecursiveNat right := by
  rw [hfRecursiveNatAdditionGraph_on_nats_iff bound 0 right zeroLess rightLess,
    Nat.zero_add]

theorem hfRecursiveNatAdditionGraph_comm
    (bound left right : Nat) (leftLess : left < bound)
    (rightLess : right < bound) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right)) output)
        (hfRecursiveNatAdditionGraph bound) ↔
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat right) (hfRecursiveNat left)) output)
        (hfRecursiveNatAdditionGraph bound) := by
  constructor
  · intro applies
    rcases (hfRecursiveNatAdditionGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with
      ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveNat_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveNat_injective rightEq
    subst actualLeft
    subst actualRight
    apply (hfRecursiveNatAdditionGraph_apply_iff bound _ _).mpr
    refine ⟨right, left, rightLess, leftLess, rfl, ?_⟩
    simpa [Nat.add_comm] using outputEq
  · intro applies
    rcases (hfRecursiveNatAdditionGraph_apply_iff bound _ _).mp applies with
      ⟨actualRight, actualLeft, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with
      ⟨rightEq, leftEq⟩
    have actualRightEq : right = actualRight := hfRecursiveNat_injective rightEq
    have actualLeftEq : left = actualLeft := hfRecursiveNat_injective leftEq
    subst actualRight
    subst actualLeft
    apply (hfRecursiveNatAdditionGraph_apply_iff bound _ _).mpr
    refine ⟨left, right, leftLess, rightLess, rfl, ?_⟩
    simpa [Nat.add_comm] using outputEq

theorem hfRecursiveNatAdditionGraph_associative
    (bound a b c : Nat) (aLess : a < bound) (bLess : b < bound)
    (cLess : c < bound) (abLess : a + b < bound)
    (bcLess : b + c < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat b))
          (hfRecursiveNat (a + b)))
        (hfRecursiveNatAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (a + b)) (hfRecursiveNat c))
          (hfRecursiveNat ((a + b) + c)))
        (hfRecursiveNatAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat b) (hfRecursiveNat c))
          (hfRecursiveNat (b + c)))
        (hfRecursiveNatAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat (b + c)))
          (hfRecursiveNat (a + (b + c))))
        (hfRecursiveNatAdditionGraph bound) ∧
    hfRecursiveNat ((a + b) + c) = hfRecursiveNat (a + (b + c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound a b aLess bLess _).mpr rfl
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound (a + b) c abLess cLess _).mpr rfl
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound b c bLess cLess _).mpr rfl
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound a (b + c) aLess bcLess _).mpr rfl
  · exact congrArg hfRecursiveNat (Nat.add_assoc a b c)

/- The analogous bounded multiplication table, again represented internally
   as a set of ordered input/output pairs. -/
def hfRecursiveNatMultiplicationRow (right : Nat) : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | leftBound + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph
        (hfRecursiveOrderedPair (hfRecursiveNat leftBound) (hfRecursiveNat right))
        (hfRecursiveNat (leftBound * right)))
      (hfRecursiveNatMultiplicationRow right leftBound)

theorem hfRecursiveNatMultiplicationRow_apply_iff
    (right leftBound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatMultiplicationRow right leftBound) ↔
      ∃ left, left < leftBound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right) ∧
        output = hfRecursiveNat (left * right) := by
  induction leftBound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨left, less, _, _⟩
        exact False.elim (Nat.not_lt_zero left less)
  | succ leftBound ih =>
      rw [hfRecursiveNatMultiplicationRow, hfRecursiveMember_union_iff,
        hfRecursiveSingletonGraph_apply_iff, ih]
      constructor
      · rintro (⟨inputEq, outputEq⟩ | ⟨left, less, inputEq, outputEq⟩)
        · exact ⟨leftBound, Nat.lt_succ_self leftBound, inputEq, outputEq⟩
        · exact ⟨left, Nat.lt_trans less (Nat.lt_succ_self leftBound),
            inputEq, outputEq⟩
      · rintro ⟨left, less, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ less) with earlier | rfl
        · exact Or.inr ⟨left, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨inputEq, outputEq⟩

def hfRecursiveNatMultiplicationRows (leftBound : Nat) : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | rightBound + 1 =>
    hfRecursiveUnion (hfRecursiveNatMultiplicationRow rightBound leftBound)
      (hfRecursiveNatMultiplicationRows leftBound rightBound)

theorem hfRecursiveNatMultiplicationRows_apply_iff
    (leftBound rightBound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatMultiplicationRows leftBound rightBound) ↔
      ∃ left right, left < leftBound ∧ right < rightBound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right) ∧
        output = hfRecursiveNat (left * right) := by
  induction rightBound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨left, right, _, less, _, _⟩
        exact False.elim (Nat.not_lt_zero right less)
  | succ rightBound ih =>
      rw [hfRecursiveNatMultiplicationRows, hfRecursiveMember_union_iff,
        hfRecursiveNatMultiplicationRow_apply_iff, ih]
      constructor
      · rintro (⟨left, leftLess, inputEq, outputEq⟩ |
          ⟨left, right, leftLess, rightLess, inputEq, outputEq⟩)
        · exact ⟨left, rightBound, leftLess, Nat.lt_succ_self rightBound,
            inputEq, outputEq⟩
        · exact ⟨left, right, leftLess,
            Nat.lt_trans rightLess (Nat.lt_succ_self rightBound),
            inputEq, outputEq⟩
      · rintro ⟨left, right, leftLess, rightLess, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ rightLess) with earlier | rfl
        · exact Or.inr ⟨left, right, leftLess, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨left, leftLess, inputEq, outputEq⟩

def hfRecursiveNatMultiplicationGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveNatMultiplicationRows bound bound

theorem hfRecursiveNatMultiplicationGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatMultiplicationGraph bound) ↔
      ∃ left right, left < bound ∧ right < bound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right) ∧
        output = hfRecursiveNat (left * right) :=
  hfRecursiveNatMultiplicationRows_apply_iff bound bound input output

theorem hfRecursiveNatMultiplicationGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveNatMultiplicationGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveNatMultiplicationGraph_apply_iff bound input output₁).mp first with
    ⟨left, right, _, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveNatMultiplicationGraph_apply_iff bound input output₂).mp second with
    ⟨left', right', _, _, inputEq₂, outputEq₂⟩
  have pairEq := inputEq₁.symm.trans inputEq₂
  rcases hfRecursiveOrderedPair_injective pairEq with ⟨leftEq, rightEq⟩
  have leftIndexEq : left = left' := hfRecursiveNat_injective leftEq
  have rightIndexEq : right = right' := hfRecursiveNat_injective rightEq
  subst left'
  subst right'
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveNatMultiplicationGraph_total
    (bound left right : Nat) (leftLess : left < bound)
    (rightLess : right < bound) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right)) output)
        (hfRecursiveNatMultiplicationGraph bound) := by
  refine ⟨hfRecursiveNat (left * right), ?_⟩
  exact (hfRecursiveNatMultiplicationGraph_apply_iff bound _ _).mpr
    ⟨left, right, leftLess, rightLess, rfl, rfl⟩

/- A bounded exponentiation table on internal finite ordinals. -/
def hfRecursiveNatPowerRow (exponent : Nat) : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | baseBound + 1 =>
    hfRecursiveUnion
      (hfRecursiveSingletonGraph
        (hfRecursiveOrderedPair (hfRecursiveNat baseBound) (hfRecursiveNat exponent))
        (hfRecursiveNat (baseBound ^ exponent)))
      (hfRecursiveNatPowerRow exponent baseBound)

theorem hfRecursiveNatPowerRow_apply_iff
    (exponent baseBound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatPowerRow exponent baseBound) ↔
      ∃ base, base < baseBound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat base) (hfRecursiveNat exponent) ∧
        output = hfRecursiveNat (base ^ exponent) := by
  induction baseBound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨base, less, _, _⟩
        exact False.elim (Nat.not_lt_zero base less)
  | succ baseBound ih =>
      rw [hfRecursiveNatPowerRow, hfRecursiveMember_union_iff,
        hfRecursiveSingletonGraph_apply_iff, ih]
      constructor
      · rintro (⟨inputEq, outputEq⟩ | ⟨base, less, inputEq, outputEq⟩)
        · exact ⟨baseBound, Nat.lt_succ_self baseBound, inputEq, outputEq⟩
        · exact ⟨base, Nat.lt_trans less (Nat.lt_succ_self baseBound),
            inputEq, outputEq⟩
      · rintro ⟨base, less, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ less) with earlier | rfl
        · exact Or.inr ⟨base, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨inputEq, outputEq⟩

def hfRecursiveNatPowerRows (baseBound : Nat) : Nat → HFRecursiveSet
  | 0 => hfRecursiveEmpty
  | exponentBound + 1 =>
    hfRecursiveUnion (hfRecursiveNatPowerRow exponentBound baseBound)
      (hfRecursiveNatPowerRows baseBound exponentBound)

theorem hfRecursiveNatPowerRows_apply_iff
    (baseBound exponentBound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatPowerRows baseBound exponentBound) ↔
      ∃ base exponent, base < baseBound ∧ exponent < exponentBound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat base) (hfRecursiveNat exponent) ∧
        output = hfRecursiveNat (base ^ exponent) := by
  induction exponentBound with
  | zero =>
      constructor
      · intro member
        exact False.elim (hfRecursiveMember_empty _ member)
      · rintro ⟨base, exponent, _, less, _, _⟩
        exact False.elim (Nat.not_lt_zero exponent less)
  | succ exponentBound ih =>
      rw [hfRecursiveNatPowerRows, hfRecursiveMember_union_iff,
        hfRecursiveNatPowerRow_apply_iff, ih]
      constructor
      · rintro (⟨base, baseLess, inputEq, outputEq⟩ |
          ⟨base, exponent, baseLess, exponentLess, inputEq, outputEq⟩)
        · exact ⟨base, exponentBound, baseLess,
            Nat.lt_succ_self exponentBound, inputEq, outputEq⟩
        · exact ⟨base, exponent, baseLess,
            Nat.lt_trans exponentLess (Nat.lt_succ_self exponentBound),
            inputEq, outputEq⟩
      · rintro ⟨base, exponent, baseLess, exponentLess, inputEq, outputEq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ exponentLess) with earlier | rfl
        · exact Or.inr ⟨base, exponent, baseLess, earlier, inputEq, outputEq⟩
        · exact Or.inl ⟨base, baseLess, inputEq, outputEq⟩

def hfRecursiveNatPowerGraph (bound : Nat) : HFRecursiveSet :=
  hfRecursiveNatPowerRows bound bound

theorem hfRecursiveNatPowerGraph_apply_iff
    (bound : Nat) (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatPowerGraph bound) ↔
      ∃ base exponent, base < bound ∧ exponent < bound ∧
        input = hfRecursiveOrderedPair (hfRecursiveNat base) (hfRecursiveNat exponent) ∧
        output = hfRecursiveNat (base ^ exponent) :=
  hfRecursiveNatPowerRows_apply_iff bound bound input output

theorem hfRecursiveNatPowerGraph_functional (bound : Nat) :
    HFRecursiveFunctional (hfRecursiveNatPowerGraph bound) := by
  intro input output₁ output₂ first second
  rcases (hfRecursiveNatPowerGraph_apply_iff bound input output₁).mp first with
    ⟨base, exponent, _, _, inputEq₁, outputEq₁⟩
  rcases (hfRecursiveNatPowerGraph_apply_iff bound input output₂).mp second with
    ⟨base', exponent', _, _, inputEq₂, outputEq₂⟩
  have pairEq := inputEq₁.symm.trans inputEq₂
  rcases hfRecursiveOrderedPair_injective pairEq with ⟨baseEq, exponentEq⟩
  have baseIndexEq : base = base' := hfRecursiveNat_injective baseEq
  have exponentIndexEq : exponent = exponent' := hfRecursiveNat_injective exponentEq
  subst base'
  subst exponent'
  exact outputEq₁.trans outputEq₂.symm

theorem hfRecursiveNatPowerGraph_total
    (bound base exponent : Nat) (baseLess : base < bound)
    (exponentLess : exponent < bound) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base) (hfRecursiveNat exponent)) output)
        (hfRecursiveNatPowerGraph bound) := by
  refine ⟨hfRecursiveNat (base ^ exponent), ?_⟩
  exact (hfRecursiveNatPowerGraph_apply_iff bound _ _).mpr
    ⟨base, exponent, baseLess, exponentLess, rfl, rfl⟩

theorem hfRecursiveNatPowerGraph_on_nats_iff
    (bound base exponent : Nat) (baseLess : base < bound)
    (exponentLess : exponent < bound) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base) (hfRecursiveNat exponent)) output)
        (hfRecursiveNatPowerGraph bound) ↔
      output = hfRecursiveNat (base ^ exponent) := by
  constructor
  · intro applies
    rcases (hfRecursiveNatPowerGraph_apply_iff bound _ _).mp applies with
      ⟨actualBase, actualExponent, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with
      ⟨baseEq, exponentEq⟩
    have actualBaseEq : base = actualBase := hfRecursiveNat_injective baseEq
    have actualExponentEq : exponent = actualExponent :=
      hfRecursiveNat_injective exponentEq
    subst actualBase
    subst actualExponent
    exact outputEq
  · intro outputEq
    exact (hfRecursiveNatPowerGraph_apply_iff bound _ _).mpr
      ⟨base, exponent, baseLess, exponentLess, rfl, outputEq⟩

theorem hfRecursiveNatPowerGraph_zero_exponent
    (bound base : Nat) (baseLess : base < bound) (zeroLess : 0 < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base) (hfRecursiveNat 0)) output)
        (hfRecursiveNatPowerGraph bound) ↔
      output = hfRecursiveNat 1 := by
  rw [hfRecursiveNatPowerGraph_on_nats_iff
    bound base 0 baseLess zeroLess, Nat.pow_zero]

theorem hfRecursiveNatPowerGraph_one_exponent
    (bound base : Nat) (baseLess : base < bound) (oneLess : 1 < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base) (hfRecursiveNat 1)) output)
        (hfRecursiveNatPowerGraph bound) ↔
      output = hfRecursiveNat base := by
  rw [hfRecursiveNatPowerGraph_on_nats_iff
    bound base 1 baseLess oneLess, Nat.pow_one]

theorem hfRecursiveNatPowerGraph_one_base
    (bound exponent : Nat) (oneLess : 1 < bound)
    (exponentLess : exponent < bound) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat 1) (hfRecursiveNat exponent)) output)
        (hfRecursiveNatPowerGraph bound) ↔
      output = hfRecursiveNat 1 := by
  rw [hfRecursiveNatPowerGraph_on_nats_iff
    bound 1 exponent oneLess exponentLess, Nat.one_pow]

theorem hfRecursiveNatPowerGraph_zero_base
    (bound exponent : Nat) (zeroLess : 0 < bound)
    (exponentLess : exponent < bound) (exponentPositive : 0 < exponent)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat 0) (hfRecursiveNat exponent)) output)
        (hfRecursiveNatPowerGraph bound) ↔
      output = hfRecursiveNat 0 := by
  rw [hfRecursiveNatPowerGraph_on_nats_iff
    bound 0 exponent zeroLess exponentLess,
    Nat.zero_pow exponentPositive]

theorem hfRecursiveNatMultiplicationGraph_on_nats_iff
    (bound left right : Nat) (leftLess : left < bound)
    (rightLess : right < bound) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right)) output)
        (hfRecursiveNatMultiplicationGraph bound) ↔
      output = hfRecursiveNat (left * right) := by
  constructor
  · intro applies
    rcases (hfRecursiveNatMultiplicationGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with
      ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveNat_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveNat_injective rightEq
    subst actualLeft
    subst actualRight
    exact outputEq
  · intro outputEq
    exact (hfRecursiveNatMultiplicationGraph_apply_iff bound _ _).mpr
      ⟨left, right, leftLess, rightLess, rfl, outputEq⟩

theorem hfRecursiveNatMultiplicationGraph_zero_right
    (bound left : Nat) (leftLess : left < bound) (zeroLess : 0 < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat 0)) output)
        (hfRecursiveNatMultiplicationGraph bound) ↔
      output = hfRecursiveNat 0 := by
  rw [hfRecursiveNatMultiplicationGraph_on_nats_iff bound left 0 leftLess zeroLess,
    Nat.mul_zero]

theorem hfRecursiveNatMultiplicationGraph_zero_left
    (bound right : Nat) (zeroLess : 0 < bound) (rightLess : right < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat 0) (hfRecursiveNat right)) output)
        (hfRecursiveNatMultiplicationGraph bound) ↔
      output = hfRecursiveNat 0 := by
  rw [hfRecursiveNatMultiplicationGraph_on_nats_iff bound 0 right zeroLess rightLess,
    Nat.zero_mul]

theorem hfRecursiveNatMultiplicationGraph_one_right
    (bound left : Nat) (leftLess : left < bound) (oneLess : 1 < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat 1)) output)
        (hfRecursiveNatMultiplicationGraph bound) ↔
      output = hfRecursiveNat left := by
  rw [hfRecursiveNatMultiplicationGraph_on_nats_iff bound left 1 leftLess oneLess,
    Nat.mul_one]

theorem hfRecursiveNatMultiplicationGraph_one_left
    (bound right : Nat) (oneLess : 1 < bound) (rightLess : right < bound)
    (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat 1) (hfRecursiveNat right)) output)
        (hfRecursiveNatMultiplicationGraph bound) ↔
      output = hfRecursiveNat right := by
  rw [hfRecursiveNatMultiplicationGraph_on_nats_iff bound 1 right oneLess rightLess,
    Nat.one_mul]

theorem hfRecursiveNatMultiplicationGraph_comm
    (bound left right : Nat) (leftLess : left < bound)
    (rightLess : right < bound) (output : HFRecursiveSet) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right)) output)
        (hfRecursiveNatMultiplicationGraph bound) ↔
      HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat right) (hfRecursiveNat left)) output)
        (hfRecursiveNatMultiplicationGraph bound) := by
  constructor
  · intro applies
    rcases (hfRecursiveNatMultiplicationGraph_apply_iff bound _ _).mp applies with
      ⟨actualLeft, actualRight, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with
      ⟨leftEq, rightEq⟩
    have actualLeftEq : left = actualLeft := hfRecursiveNat_injective leftEq
    have actualRightEq : right = actualRight := hfRecursiveNat_injective rightEq
    subst actualLeft
    subst actualRight
    apply (hfRecursiveNatMultiplicationGraph_apply_iff bound _ _).mpr
    refine ⟨right, left, rightLess, leftLess, rfl, ?_⟩
    simpa [Nat.mul_comm] using outputEq
  · intro applies
    rcases (hfRecursiveNatMultiplicationGraph_apply_iff bound _ _).mp applies with
      ⟨actualRight, actualLeft, _, _, inputEq, outputEq⟩
    rcases hfRecursiveOrderedPair_injective inputEq with
      ⟨rightEq, leftEq⟩
    have actualRightEq : right = actualRight := hfRecursiveNat_injective rightEq
    have actualLeftEq : left = actualLeft := hfRecursiveNat_injective leftEq
    subst actualRight
    subst actualLeft
    apply (hfRecursiveNatMultiplicationGraph_apply_iff bound _ _).mpr
    refine ⟨left, right, leftLess, rightLess, rfl, ?_⟩
    simpa [Nat.mul_comm] using outputEq

theorem hfRecursiveNatMultiplicationGraph_associative
    (bound a b c : Nat) (aLess : a < bound) (bLess : b < bound)
    (cLess : c < bound) (abLess : a * b < bound)
    (bcLess : b * c < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat b))
          (hfRecursiveNat (a * b)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (a * b)) (hfRecursiveNat c))
          (hfRecursiveNat ((a * b) * c)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat b) (hfRecursiveNat c))
          (hfRecursiveNat (b * c)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat (b * c)))
          (hfRecursiveNat (a * (b * c))))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    hfRecursiveNat ((a * b) * c) = hfRecursiveNat (a * (b * c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound a b aLess bLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound (a * b) c abLess cLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound b c bLess cLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound a (b * c) aLess bcLess _).mpr rfl
  · exact congrArg hfRecursiveNat (Nat.mul_assoc a b c)

theorem hfRecursiveNatMultiplicationGraph_distributes_over_addition
    (bound a b c : Nat) (aLess : a < bound) (bLess : b < bound)
    (cLess : c < bound) (bcLess : b + c < bound)
    (abLess : a * b < bound) (acLess : a * c < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat b) (hfRecursiveNat c))
          (hfRecursiveNat (b + c)))
        (hfRecursiveNatAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat (b + c)))
          (hfRecursiveNat (a * (b + c))))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat b))
          (hfRecursiveNat (a * b)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat c))
          (hfRecursiveNat (a * c)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (a * b)) (hfRecursiveNat (a * c)))
          (hfRecursiveNat (a * b + a * c)))
        (hfRecursiveNatAdditionGraph bound) ∧
    hfRecursiveNat (a * (b + c)) = hfRecursiveNat (a * b + a * c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound b c bLess cLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound a (b + c) aLess bcLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound a b aLess bLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound a c aLess cLess _).mpr rfl
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound (a * b) (a * c) abLess acLess _).mpr rfl
  · exact congrArg hfRecursiveNat (Nat.mul_add a b c)

theorem hfRecursiveNatMultiplicationGraph_right_distributes_over_addition
    (bound a b c : Nat) (aLess : a < bound) (bLess : b < bound)
    (cLess : c < bound) (abLess : a + b < bound)
    (acLess : a * c < bound) (bcLess : b * c < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat b))
          (hfRecursiveNat (a + b)))
        (hfRecursiveNatAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (a + b)) (hfRecursiveNat c))
          (hfRecursiveNat ((a + b) * c)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat a) (hfRecursiveNat c))
          (hfRecursiveNat (a * c)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat b) (hfRecursiveNat c))
          (hfRecursiveNat (b * c)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (a * c)) (hfRecursiveNat (b * c)))
          (hfRecursiveNat (a * c + b * c)))
        (hfRecursiveNatAdditionGraph bound) ∧
    hfRecursiveNat ((a + b) * c) = hfRecursiveNat (a * c + b * c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound a b aLess bLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound (a + b) c abLess cLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound a c aLess cLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff
      bound b c bLess cLess _).mpr rfl
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff
      bound (a * c) (b * c) acLess bcLess _).mpr rfl
  · exact congrArg hfRecursiveNat (Nat.add_mul a b c)

theorem hfRecursiveNatAdditionGraph_right_cancel
    (bound left₁ left₂ right : Nat)
    (left₁Less : left₁ < bound) (left₂Less : left₂ < bound)
    (rightLess : right < bound) (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left₁) (hfRecursiveNat right)) output)
      (hfRecursiveNatAdditionGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left₂) (hfRecursiveNat right)) output)
      (hfRecursiveNatAdditionGraph bound)) :
    left₁ = left₂ := by
  have firstValue := (hfRecursiveNatAdditionGraph_on_nats_iff
    bound left₁ right left₁Less rightLess output).mp first
  have secondValue := (hfRecursiveNatAdditionGraph_on_nats_iff
    bound left₂ right left₂Less rightLess output).mp second
  have sumEq : left₁ + right = left₂ + right :=
    hfRecursiveNat_injective (firstValue.symm.trans secondValue)
  exact Nat.add_right_cancel sumEq

theorem hfRecursiveNatAdditionGraph_left_cancel
    (bound left right₁ right₂ : Nat)
    (leftLess : left < bound) (right₁Less : right₁ < bound)
    (right₂Less : right₂ < bound) (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right₁)) output)
      (hfRecursiveNatAdditionGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right₂)) output)
      (hfRecursiveNatAdditionGraph bound)) :
    right₁ = right₂ := by
  have firstValue := (hfRecursiveNatAdditionGraph_on_nats_iff
    bound left right₁ leftLess right₁Less output).mp first
  have secondValue := (hfRecursiveNatAdditionGraph_on_nats_iff
    bound left right₂ leftLess right₂Less output).mp second
  have sumEq : left + right₁ = left + right₂ :=
    hfRecursiveNat_injective (firstValue.symm.trans secondValue)
  exact Nat.add_left_cancel sumEq

theorem hfRecursiveNatMultiplicationGraph_right_cancel
    (bound left₁ left₂ right : Nat)
    (left₁Less : left₁ < bound) (left₂Less : left₂ < bound)
    (rightLess : right < bound) (rightPositive : 0 < right)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left₁) (hfRecursiveNat right)) output)
      (hfRecursiveNatMultiplicationGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left₂) (hfRecursiveNat right)) output)
      (hfRecursiveNatMultiplicationGraph bound)) :
    left₁ = left₂ := by
  have firstValue := (hfRecursiveNatMultiplicationGraph_on_nats_iff
    bound left₁ right left₁Less rightLess output).mp first
  have secondValue := (hfRecursiveNatMultiplicationGraph_on_nats_iff
    bound left₂ right left₂Less rightLess output).mp second
  have productEq : left₁ * right = left₂ * right :=
    hfRecursiveNat_injective (firstValue.symm.trans secondValue)
  exact Nat.mul_right_cancel rightPositive productEq

theorem hfRecursiveNatMultiplicationGraph_left_cancel
    (bound left right₁ right₂ : Nat)
    (leftLess : left < bound) (leftPositive : 0 < left)
    (right₁Less : right₁ < bound) (right₂Less : right₂ < bound)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right₁)) output)
      (hfRecursiveNatMultiplicationGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right₂)) output)
      (hfRecursiveNatMultiplicationGraph bound)) :
    right₁ = right₂ := by
  have firstValue := (hfRecursiveNatMultiplicationGraph_on_nats_iff
    bound left right₁ leftLess right₁Less output).mp first
  have secondValue := (hfRecursiveNatMultiplicationGraph_on_nats_iff
    bound left right₂ leftLess right₂Less output).mp second
  have productEq : left * right₁ = left * right₂ :=
    hfRecursiveNat_injective (firstValue.symm.trans secondValue)
  exact Nat.mul_left_cancel leftPositive productEq

theorem hfRecursiveNatMultiplicationGraph_eq_zero_iff
    (bound left right : Nat) (leftLess : left < bound)
    (rightLess : right < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat left) (hfRecursiveNat right))
          (hfRecursiveNat 0))
        (hfRecursiveNatMultiplicationGraph bound) ↔
      left = 0 ∨ right = 0 := by
  rw [hfRecursiveNatMultiplicationGraph_on_nats_iff
    bound left right leftLess rightLess]
  constructor
  · intro valueEq
    have indexEq : 0 = left * right := hfRecursiveNat_injective valueEq
    exact (Nat.mul_eq_zero.mp indexEq.symm)
  · intro zeroFactor
    apply congrArg hfRecursiveNat
    exact (Nat.mul_eq_zero.mpr zeroFactor).symm

theorem hfRecursiveNatPowerGraph_add_exponents
    (bound base firstExponent secondExponent : Nat)
    (baseLess : base < bound) (firstLess : firstExponent < bound)
    (secondLess : secondExponent < bound)
    (sumLess : firstExponent + secondExponent < bound)
    (firstPowerLess : base ^ firstExponent < bound)
    (secondPowerLess : base ^ secondExponent < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat firstExponent)
            (hfRecursiveNat secondExponent))
          (hfRecursiveNat (firstExponent + secondExponent)))
        (hfRecursiveNatAdditionGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base)
            (hfRecursiveNat firstExponent))
          (hfRecursiveNat (base ^ firstExponent)))
        (hfRecursiveNatPowerGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base)
            (hfRecursiveNat secondExponent))
          (hfRecursiveNat (base ^ secondExponent)))
        (hfRecursiveNatPowerGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (base ^ firstExponent))
            (hfRecursiveNat (base ^ secondExponent)))
          (hfRecursiveNat (base ^ firstExponent * base ^ secondExponent)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base)
            (hfRecursiveNat (firstExponent + secondExponent)))
          (hfRecursiveNat (base ^ (firstExponent + secondExponent))))
        (hfRecursiveNatPowerGraph bound) ∧
    hfRecursiveNat (base ^ (firstExponent + secondExponent)) =
      hfRecursiveNat (base ^ firstExponent * base ^ secondExponent) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveNatAdditionGraph_on_nats_iff bound
      firstExponent secondExponent firstLess secondLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      base firstExponent baseLess firstLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      base secondExponent baseLess secondLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff bound
      (base ^ firstExponent) (base ^ secondExponent)
      firstPowerLess secondPowerLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      base (firstExponent + secondExponent) baseLess sumLess _).mpr rfl
  · exact congrArg hfRecursiveNat
      (Nat.pow_add base firstExponent secondExponent)

theorem hfRecursiveNatPowerGraph_mul_exponents
    (bound base firstExponent secondExponent : Nat)
    (baseLess : base < bound) (firstLess : firstExponent < bound)
    (secondLess : secondExponent < bound)
    (productLess : firstExponent * secondExponent < bound)
    (firstPowerLess : base ^ firstExponent < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat firstExponent)
            (hfRecursiveNat secondExponent))
          (hfRecursiveNat (firstExponent * secondExponent)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base)
            (hfRecursiveNat firstExponent))
          (hfRecursiveNat (base ^ firstExponent)))
        (hfRecursiveNatPowerGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (base ^ firstExponent))
            (hfRecursiveNat secondExponent))
          (hfRecursiveNat ((base ^ firstExponent) ^ secondExponent)))
        (hfRecursiveNatPowerGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat base)
            (hfRecursiveNat (firstExponent * secondExponent)))
          (hfRecursiveNat (base ^ (firstExponent * secondExponent))))
        (hfRecursiveNatPowerGraph bound) ∧
    hfRecursiveNat (base ^ (firstExponent * secondExponent)) =
      hfRecursiveNat ((base ^ firstExponent) ^ secondExponent) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff bound
      firstExponent secondExponent firstLess secondLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      base firstExponent baseLess firstLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      (base ^ firstExponent) secondExponent firstPowerLess secondLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      base (firstExponent * secondExponent) baseLess productLess _).mpr rfl
  · exact congrArg hfRecursiveNat
      (Nat.pow_mul base firstExponent secondExponent)

theorem hfRecursiveNatPowerGraph_mul_bases
    (bound firstBase secondBase exponent : Nat)
    (firstBaseLess : firstBase < bound) (secondBaseLess : secondBase < bound)
    (exponentLess : exponent < bound)
    (baseProductLess : firstBase * secondBase < bound)
    (firstPowerLess : firstBase ^ exponent < bound)
    (secondPowerLess : secondBase ^ exponent < bound) :
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat firstBase)
            (hfRecursiveNat secondBase))
          (hfRecursiveNat (firstBase * secondBase)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (firstBase * secondBase))
            (hfRecursiveNat exponent))
          (hfRecursiveNat ((firstBase * secondBase) ^ exponent)))
        (hfRecursiveNatPowerGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat firstBase)
            (hfRecursiveNat exponent))
          (hfRecursiveNat (firstBase ^ exponent)))
        (hfRecursiveNatPowerGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat secondBase)
            (hfRecursiveNat exponent))
          (hfRecursiveNat (secondBase ^ exponent)))
        (hfRecursiveNatPowerGraph bound) ∧
    HFRecursiveMember
        (hfRecursiveOrderedPair
          (hfRecursiveOrderedPair (hfRecursiveNat (firstBase ^ exponent))
            (hfRecursiveNat (secondBase ^ exponent)))
          (hfRecursiveNat (firstBase ^ exponent * secondBase ^ exponent)))
        (hfRecursiveNatMultiplicationGraph bound) ∧
    hfRecursiveNat ((firstBase * secondBase) ^ exponent) =
      hfRecursiveNat (firstBase ^ exponent * secondBase ^ exponent) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff bound
      firstBase secondBase firstBaseLess secondBaseLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      (firstBase * secondBase) exponent baseProductLess exponentLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      firstBase exponent firstBaseLess exponentLess _).mpr rfl
  · exact (hfRecursiveNatPowerGraph_on_nats_iff bound
      secondBase exponent secondBaseLess exponentLess _).mpr rfl
  · exact (hfRecursiveNatMultiplicationGraph_on_nats_iff bound
      (firstBase ^ exponent) (secondBase ^ exponent)
      firstPowerLess secondPowerLess _).mpr rfl
  · exact congrArg hfRecursiveNat
      (Nat.mul_pow firstBase secondBase exponent)

theorem hfRecursiveNatPowerGraph_cancel_bases
    (bound firstBase secondBase exponent : Nat)
    (firstBaseLess : firstBase < bound) (secondBaseLess : secondBase < bound)
    (exponentLess : exponent < bound) (exponentPositive : 0 < exponent)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat firstBase)
          (hfRecursiveNat exponent)) output)
      (hfRecursiveNatPowerGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat secondBase)
          (hfRecursiveNat exponent)) output)
      (hfRecursiveNatPowerGraph bound)) :
    firstBase = secondBase := by
  have firstValue := (hfRecursiveNatPowerGraph_on_nats_iff bound
    firstBase exponent firstBaseLess exponentLess output).mp first
  have secondValue := (hfRecursiveNatPowerGraph_on_nats_iff bound
    secondBase exponent secondBaseLess exponentLess output).mp second
  have powerEq : firstBase ^ exponent = secondBase ^ exponent :=
    hfRecursiveNat_injective (firstValue.symm.trans secondValue)
  apply Nat.le_antisymm
  · exact (Nat.pow_le_pow_iff_left (Nat.ne_of_gt exponentPositive)).mp
      (Nat.le_of_eq powerEq)
  · exact (Nat.pow_le_pow_iff_left (Nat.ne_of_gt exponentPositive)).mp
      (Nat.le_of_eq powerEq.symm)

theorem hfRecursiveNatPowerGraph_cancel_exponents
    (bound base firstExponent secondExponent : Nat)
    (baseLess : base < bound) (baseGreaterOne : 1 < base)
    (firstLess : firstExponent < bound) (secondLess : secondExponent < bound)
    (output : HFRecursiveSet)
    (first : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat base)
          (hfRecursiveNat firstExponent)) output)
      (hfRecursiveNatPowerGraph bound))
    (second : HFRecursiveMember
      (hfRecursiveOrderedPair
        (hfRecursiveOrderedPair (hfRecursiveNat base)
          (hfRecursiveNat secondExponent)) output)
      (hfRecursiveNatPowerGraph bound)) :
    firstExponent = secondExponent := by
  have firstValue := (hfRecursiveNatPowerGraph_on_nats_iff bound
    base firstExponent baseLess firstLess output).mp first
  have secondValue := (hfRecursiveNatPowerGraph_on_nats_iff bound
    base secondExponent baseLess secondLess output).mp second
  have powerEq : base ^ firstExponent = base ^ secondExponent :=
    hfRecursiveNat_injective (firstValue.symm.trans secondValue)
  apply Nat.le_antisymm
  · exact (Nat.pow_le_pow_iff_right baseGreaterOne).mp
      (Nat.le_of_eq powerEq)
  · exact (Nat.pow_le_pow_iff_right baseGreaterOne).mp
      (Nat.le_of_eq powerEq.symm)

theorem hfRecursiveNatShiftGraph_zero (n : Nat) :
    hfRecursiveNatShiftGraph 0 n = hfRecursiveNatIdentityGraph n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hfRecursiveNatShiftGraph, hfRecursiveNatIdentityGraph, Nat.add_zero, ih]

theorem hfRecursiveNatShiftGraph_one (n : Nat) :
    hfRecursiveNatShiftGraph 1 n = hfRecursiveNatSuccessorGraph n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hfRecursiveNatShiftGraph, hfRecursiveNatSuccessorGraph, ih]

/- Pointwise composition of finite shift graphs realizes addition of offsets. -/
theorem hfRecursiveNatShiftGraph_compose
    (n m firstOffset secondOffset : Nat) (hm : m < n) :
    HFRecursiveMember
      (hfRecursiveOrderedPair (hfRecursiveNat m) (hfRecursiveNat (m + firstOffset)))
      (hfRecursiveNatShiftGraph firstOffset n) ∧
    HFRecursiveMember
      (hfRecursiveOrderedPair (hfRecursiveNat (m + firstOffset))
        (hfRecursiveNat (m + firstOffset + secondOffset)))
      (hfRecursiveNatShiftGraph secondOffset (n + firstOffset)) ∧
    HFRecursiveMember
      (hfRecursiveOrderedPair (hfRecursiveNat m)
        (hfRecursiveNat (m + (firstOffset + secondOffset))))
      (hfRecursiveNatShiftGraph (firstOffset + secondOffset) n) := by
  constructor
  · exact (hfRecursiveNatShiftGraph_apply_iff firstOffset n
      (hfRecursiveNat m) (hfRecursiveNat (m + firstOffset))).mpr
        ⟨m, hm, rfl, rfl⟩
  constructor
  · exact (hfRecursiveNatShiftGraph_apply_iff secondOffset (n + firstOffset)
      (hfRecursiveNat (m + firstOffset))
      (hfRecursiveNat (m + firstOffset + secondOffset))).mpr
        ⟨m + firstOffset, Nat.add_lt_add_right hm firstOffset, rfl, rfl⟩
  · exact (hfRecursiveNatShiftGraph_apply_iff (firstOffset + secondOffset) n
      (hfRecursiveNat m) (hfRecursiveNat (m + (firstOffset + secondOffset)))).mpr
        ⟨m, hm, rfl, rfl⟩

/- `composite` is the relational composite of `first` followed by `second`.
   Stating this independently of a particular finite presentation makes the
   graph-composition theorem below usable by later relation constructions. -/
def HFRecursiveRelationalComposite
    (first second composite : HFRecursiveSet) : Prop :=
  ∀ input output,
    HFRecursiveMember (hfRecursiveOrderedPair input output) composite ↔
      ∃ middle,
        HFRecursiveMember (hfRecursiveOrderedPair input middle) first ∧
        HFRecursiveMember (hfRecursiveOrderedPair middle output) second

/- Translation graphs compose as genuine internal relations, not merely at a
   selected point.  The middle object is the internally represented ordinal
   `m + firstOffset`. -/
theorem hfRecursiveNatShiftGraph_relationalComposite
    (firstOffset secondOffset n : Nat) :
    HFRecursiveRelationalComposite
      (hfRecursiveNatShiftGraph firstOffset n)
      (hfRecursiveNatShiftGraph secondOffset (n + firstOffset))
      (hfRecursiveNatShiftGraph (firstOffset + secondOffset) n) := by
  intro input output
  constructor
  · intro h
    rcases (hfRecursiveNatShiftGraph_apply_iff
      (firstOffset + secondOffset) n input output).mp h with
      ⟨m, hm, hinput, houtput⟩
    refine ⟨hfRecursiveNat (m + firstOffset), ?_, ?_⟩
    · exact (hfRecursiveNatShiftGraph_apply_iff firstOffset n input
        (hfRecursiveNat (m + firstOffset))).mpr ⟨m, hm, hinput, rfl⟩
    · exact (hfRecursiveNatShiftGraph_apply_iff secondOffset
        (n + firstOffset) (hfRecursiveNat (m + firstOffset)) output).mpr
          ⟨m + firstOffset, Nat.add_lt_add_right hm firstOffset, rfl, by
            simpa [Nat.add_assoc] using houtput⟩
  · rintro ⟨middle, hfirst, hsecond⟩
    rcases (hfRecursiveNatShiftGraph_apply_iff firstOffset n input middle).mp hfirst with
      ⟨m, hm, hinput, hmiddle⟩
    rcases (hfRecursiveNatShiftGraph_apply_iff secondOffset (n + firstOffset)
      middle output).mp hsecond with ⟨k, hk, hmiddle', houtput⟩
    have hmk : m + firstOffset = k :=
      hfRecursiveNat_injective (hmiddle.symm.trans hmiddle')
    subst k
    exact (hfRecursiveNatShiftGraph_apply_iff (firstOffset + secondOffset) n
      input output).mpr ⟨m, hm, hinput, by
        simpa [Nat.add_assoc] using houtput⟩

/- A functional relation is injective when an output determines its input.
   This is the graph-theoretic counterpart of one-to-one finite maps. -/
def HFRecursiveInjective (relation : HFRecursiveSet) : Prop :=
  ∀ input₁ input₂ output,
    HFRecursiveMember (hfRecursiveOrderedPair input₁ output) relation →
      HFRecursiveMember (hfRecursiveOrderedPair input₂ output) relation →
        input₁ = input₂

/- Every finite ordinal shift is an internally represented relation. -/
theorem hfRecursiveNatShiftGraph_relation (offset n : Nat) :
    HFRecursiveRelation (hfRecursiveNatShiftGraph offset n) := by
  induction n with
  | zero =>
    intro element helement
    exact False.elim (hfRecursiveMember_empty element helement)
  | succ n ih =>
    rw [hfRecursiveNatShiftGraph]
    exact hfRecursiveRelation_union
      (hfRecursiveSingletonGraph_relation (hfRecursiveNat n) (hfRecursiveNat (n + offset))) ih

/- Translation by a fixed offset is injective on each finite ordinal. -/
theorem hfRecursiveNatShiftGraph_injective (offset n : Nat) :
    HFRecursiveInjective (hfRecursiveNatShiftGraph offset n) := by
  intro input₁ input₂ output h₁ h₂
  rcases (hfRecursiveNatShiftGraph_apply_iff offset n input₁ output).mp h₁ with
    ⟨m, hm, hinput₁, houtput₁⟩
  rcases (hfRecursiveNatShiftGraph_apply_iff offset n input₂ output).mp h₂ with
    ⟨k, hk, hinput₂, houtput₂⟩
  have hmk : m + offset = k + offset :=
    hfRecursiveNat_injective (houtput₁.symm.trans houtput₂)
  have hmk' : m = k := Nat.add_right_cancel hmk
  subst k
  exact hinput₁.trans hinput₂.symm

/- The inverse of a finite shift is defined exactly on its image.  Supplying
   the output `m + offset` recovers the unique source `m`; this is the
   graph-level inverse law without claiming a total inverse outside the finite
   image. -/
theorem hfRecursiveNatShiftGraph_inverse_on_image_iff
    (offset n m : Nat) (input : HFRecursiveSet) :
    HFRecursiveMember
      (hfRecursiveOrderedPair input (hfRecursiveNat (m + offset)))
      (hfRecursiveNatShiftGraph offset n) ↔
      m < n ∧ input = hfRecursiveNat m := by
  constructor
  · intro h
    rcases (hfRecursiveNatShiftGraph_apply_iff offset n input
        (hfRecursiveNat (m + offset))).mp h with
      ⟨k, hk, hinput, houtput⟩
    have hmk : m = k := Nat.add_right_cancel
      (hfRecursiveNat_injective houtput)
    subst k
    exact ⟨hk, hinput⟩
  · rintro ⟨hm, rfl⟩
    exact (hfRecursiveNatShiftGraph_apply_iff offset n
      (hfRecursiveNat m) (hfRecursiveNat (m + offset))).mpr
      ⟨m, hm, rfl, rfl⟩

/- On every nonempty finite ordinal, the internal translation graph remembers
   its offset.  Thus the graph presentation is a faithful action of natural
   addition, rather than merely a collection of functional relations. -/
theorem hfRecursiveNatShiftGraph_offset_injective
    (n firstOffset secondOffset : Nat) (hn : 0 < n) :
    hfRecursiveNatShiftGraph firstOffset n =
        hfRecursiveNatShiftGraph secondOffset n ↔
      firstOffset = secondOffset := by
  constructor
  · intro hgraphs
    have hfirst :
        HFRecursiveMember
          (hfRecursiveOrderedPair (hfRecursiveNat 0) (hfRecursiveNat (0 + firstOffset)))
          (hfRecursiveNatShiftGraph firstOffset n) :=
      (hfRecursiveNatShiftGraph_apply_iff firstOffset n
        (hfRecursiveNat 0) (hfRecursiveNat (0 + firstOffset))).mpr
        ⟨0, hn, rfl, rfl⟩
    have hsecond :
        HFRecursiveMember
          (hfRecursiveOrderedPair (hfRecursiveNat 0) (hfRecursiveNat (0 + firstOffset)))
          (hfRecursiveNatShiftGraph secondOffset n) := by
      rw [← hgraphs]
      exact hfirst
    rcases (hfRecursiveNatShiftGraph_apply_iff secondOffset n
      (hfRecursiveNat 0) (hfRecursiveNat (0 + firstOffset))).mp hsecond with
      ⟨m, hm, hinput, houtput⟩
    have hmzero : m = 0 := hfRecursiveNat_injective hinput.symm
    subst m
    exact hfRecursiveNat_injective (by simpa using houtput)
  · intro hoffset
    subst secondOffset
    rfl

/- The faithful translation action reflects cancellation of a common left
   offset.  This is stated at graph level so later internal arithmetic can use
   relation equality as its observable equality principle. -/
theorem hfRecursiveNatShiftGraph_add_left_cancel
    (n common firstOffset secondOffset : Nat) (hn : 0 < n)
    (hgraphs :
      hfRecursiveNatShiftGraph (common + firstOffset) n =
        hfRecursiveNatShiftGraph (common + secondOffset) n) :
    firstOffset = secondOffset := by
  have hsums : common + firstOffset = common + secondOffset :=
    (hfRecursiveNatShiftGraph_offset_injective n
      (common + firstOffset) (common + secondOffset) hn).mp hgraphs
  exact Nat.add_left_cancel hsums

theorem hfRecursiveNatIdentityGraph_injective (n : Nat) :
    HFRecursiveInjective (hfRecursiveNatIdentityGraph n) := by
  simpa [hfRecursiveNatShiftGraph_zero] using hfRecursiveNatShiftGraph_injective 0 n

theorem hfRecursiveNatSuccessorGraph_injective (n : Nat) :
    HFRecursiveInjective (hfRecursiveNatSuccessorGraph n) := by
  simpa [hfRecursiveNatShiftGraph_one] using hfRecursiveNatShiftGraph_injective 1 n

/- Functionality is stable under an internally specified relational composite. -/
theorem hfRecursiveRelationalComposite_functional
    {first second composite : HFRecursiveSet}
    (hcomposite : HFRecursiveRelationalComposite first second composite)
    (hfirst : HFRecursiveFunctional first)
    (hsecond : HFRecursiveFunctional second) :
    HFRecursiveFunctional composite := by
  intro input output₁ output₂ h₁ h₂
  rcases (hcomposite input output₁).mp h₁ with ⟨middle₁, hfirst₁, hsecond₁⟩
  rcases (hcomposite input output₂).mp h₂ with ⟨middle₂, hfirst₂, hsecond₂⟩
  have hmiddle : middle₁ = middle₂ := hfirst input middle₁ middle₂ hfirst₁ hfirst₂
  subst middle₂
  exact hsecond middle₁ output₁ output₂ hsecond₁ hsecond₂

/- Hence the composite of two finite shifts is itself functional, with the
   expected summed offset. -/
theorem hfRecursiveNatShiftGraph_composite_functional
    (firstOffset secondOffset n : Nat) :
    HFRecursiveFunctional
      (hfRecursiveNatShiftGraph (firstOffset + secondOffset) n) := by
  apply hfRecursiveRelationalComposite_functional
    (hfRecursiveNatShiftGraph_relationalComposite firstOffset secondOffset n)
    (hfRecursiveNatShiftGraph_functional firstOffset n)
    (hfRecursiveNatShiftGraph_functional secondOffset (n + firstOffset))

/- Injectivity is likewise stable under relational composition.  This gives a
   presentation-independent finite counterpart of the fact that a composite
   of one-to-one maps is one-to-one. -/
theorem hfRecursiveRelationalComposite_injective
    {first second composite : HFRecursiveSet}
    (hcomposite : HFRecursiveRelationalComposite first second composite)
    (hfirst : HFRecursiveInjective first)
    (hsecond : HFRecursiveInjective second) :
    HFRecursiveInjective composite := by
  intro input₁ input₂ output h₁ h₂
  rcases (hcomposite input₁ output).mp h₁ with ⟨middle₁, hfirst₁, hsecond₁⟩
  rcases (hcomposite input₂ output).mp h₂ with ⟨middle₂, hfirst₂, hsecond₂⟩
  have hmiddle : middle₁ = middle₂ := hsecond middle₁ middle₂ output hsecond₁ hsecond₂
  subst middle₂
  exact hfirst input₁ input₂ middle₁ hfirst₁ hfirst₂

/- The internally represented identity graph is a left identity for finite
   ordinal translations. -/
theorem hfRecursiveNatIdentityGraph_left_relationalComposite
    (offset n : Nat) :
    HFRecursiveRelationalComposite
      (hfRecursiveNatIdentityGraph n)
      (hfRecursiveNatShiftGraph offset n)
      (hfRecursiveNatShiftGraph offset n) := by
  simpa [hfRecursiveNatShiftGraph_zero] using
    (hfRecursiveNatShiftGraph_relationalComposite 0 offset n)

/- It is also a right identity, on the translated finite ordinal. -/
theorem hfRecursiveNatIdentityGraph_right_relationalComposite
    (offset n : Nat) :
    HFRecursiveRelationalComposite
      (hfRecursiveNatShiftGraph offset n)
      (hfRecursiveNatIdentityGraph (n + offset))
      (hfRecursiveNatShiftGraph offset n) := by
  simpa [hfRecursiveNatShiftGraph_zero] using
    (hfRecursiveNatShiftGraph_relationalComposite offset 0 n)

/- Therefore the relation-level composite of two finite translations remains
   injective, as well as functional. -/
theorem hfRecursiveNatShiftGraph_composite_injective
    (firstOffset secondOffset n : Nat) :
    HFRecursiveInjective
      (hfRecursiveNatShiftGraph (firstOffset + secondOffset) n) := by
  apply hfRecursiveRelationalComposite_injective
    (hfRecursiveNatShiftGraph_relationalComposite firstOffset secondOffset n)
    (hfRecursiveNatShiftGraph_injective firstOffset n)
    (hfRecursiveNatShiftGraph_injective secondOffset (n + firstOffset))

/- At the application level, the intermediate value in a composite of shifts
   is immaterial: applying the two graph relations succeeds precisely at the
   ordinal obtained by adding both offsets. -/
theorem hfRecursiveNatShiftGraph_composite_application_iff
    (firstOffset secondOffset n m : Nat) (hm : m < n) (output : HFRecursiveSet) :
    (∃ middle,
      HFRecursiveMember
        (hfRecursiveOrderedPair (hfRecursiveNat m) middle)
        (hfRecursiveNatShiftGraph firstOffset n) ∧
      HFRecursiveMember
        (hfRecursiveOrderedPair middle output)
        (hfRecursiveNatShiftGraph secondOffset (n + firstOffset))) ↔
      output = hfRecursiveNat (m + (firstOffset + secondOffset)) := by
  constructor
  · intro h
    have hcomposite :
        HFRecursiveMember
          (hfRecursiveOrderedPair (hfRecursiveNat m) output)
          (hfRecursiveNatShiftGraph (firstOffset + secondOffset) n) :=
      (hfRecursiveNatShiftGraph_relationalComposite firstOffset secondOffset n
        (hfRecursiveNat m) output).mpr h
    rcases (hfRecursiveNatShiftGraph_apply_iff
      (firstOffset + secondOffset) n (hfRecursiveNat m) output).mp hcomposite with
      ⟨k, hk, hinput, houtput⟩
    have hmk : m = k := hfRecursiveNat_injective hinput
    subst k
    exact houtput
  · intro houtput
    apply (hfRecursiveNatShiftGraph_relationalComposite firstOffset secondOffset n
      (hfRecursiveNat m) output).mp
    apply (hfRecursiveNatShiftGraph_apply_iff
      (firstOffset + secondOffset) n (hfRecursiveNat m) output).mpr
    exact ⟨m, hm, rfl, houtput⟩

/- The composite graph is total on its original finite ordinal, with its
   application-level value made explicit. -/
theorem hfRecursiveNatShiftGraph_composite_total
    (firstOffset secondOffset n m : Nat) (hm : m < n) :
    ∃ output,
      HFRecursiveMember
        (hfRecursiveOrderedPair (hfRecursiveNat m) output)
        (hfRecursiveNatShiftGraph (firstOffset + secondOffset) n) ∧
      output = hfRecursiveNat (m + (firstOffset + secondOffset)) := by
  refine ⟨hfRecursiveNat (m + (firstOffset + secondOffset)), ?_, rfl⟩
  exact (hfRecursiveNatShiftGraph_apply_iff
    (firstOffset + secondOffset) n (hfRecursiveNat m)
    (hfRecursiveNat (m + (firstOffset + secondOffset)))).mpr ⟨m, hm, rfl, rfl⟩

/- Associativity is visible before quotienting graph applications: the graph
   for the summed offset is equivalent to choosing both intermediate values.
   This is a genuine three-stage relation calculation, rather than only an
   arithmetic equality of offsets. -/
theorem hfRecursiveNatShiftGraph_associative_application_iff
    (firstOffset secondOffset thirdOffset n : Nat)
    (input output : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveOrderedPair input output)
      (hfRecursiveNatShiftGraph (firstOffset + (secondOffset + thirdOffset)) n) ↔
      ∃ firstMiddle secondMiddle,
        HFRecursiveMember (hfRecursiveOrderedPair input firstMiddle)
          (hfRecursiveNatShiftGraph firstOffset n) ∧
        HFRecursiveMember (hfRecursiveOrderedPair firstMiddle secondMiddle)
          (hfRecursiveNatShiftGraph secondOffset (n + firstOffset)) ∧
        HFRecursiveMember (hfRecursiveOrderedPair secondMiddle output)
          (hfRecursiveNatShiftGraph thirdOffset (n + firstOffset + secondOffset)) := by
  constructor
  · intro h
    rcases (hfRecursiveNatShiftGraph_relationalComposite firstOffset
      (secondOffset + thirdOffset) n input output).mp h with
      ⟨firstMiddle, hfirst, hrest⟩
    rcases (hfRecursiveNatShiftGraph_relationalComposite secondOffset thirdOffset
      (n + firstOffset) firstMiddle output).mp hrest with
      ⟨secondMiddle, hsecond, hthird⟩
    exact ⟨firstMiddle, secondMiddle, hfirst, hsecond, hthird⟩
  · rintro ⟨firstMiddle, secondMiddle, hfirst, hsecond, hthird⟩
    apply (hfRecursiveNatShiftGraph_relationalComposite firstOffset
      (secondOffset + thirdOffset) n input output).mpr
    refine ⟨firstMiddle, hfirst, ?_⟩
    apply (hfRecursiveNatShiftGraph_relationalComposite secondOffset thirdOffset
      (n + firstOffset) firstMiddle output).mpr
    exact ⟨secondMiddle, hsecond, hthird⟩

/- Relational-composite specifications determine a graph extensionally once
   both candidates are known to contain only ordered pairs.  The relation
   hypotheses are essential here: the composite specification itself only
   constrains memberships which are already presented as ordered pairs. -/
theorem hfRecursiveRelationalComposite_unique
    {first second composite₁ composite₂ : HFRecursiveSet}
    (h₁ : HFRecursiveRelationalComposite first second composite₁)
    (h₂ : HFRecursiveRelationalComposite first second composite₂)
    (hr₁ : HFRecursiveRelation composite₁)
    (hr₂ : HFRecursiveRelation composite₂) :
    composite₁ = composite₂ := by
  apply hfRecursiveSet_extensionality
  intro element
  constructor
  · intro hmember
    rcases hr₁ element hmember with ⟨input, output, rfl⟩
    exact (h₂ input output).mpr ((h₁ input output).mp hmember)
  · intro hmember
    rcases hr₂ element hmember with ⟨input, output, rfl⟩
    exact (h₁ input output).mpr ((h₂ input output).mp hmember)

/- Three successive relations, stated without committing to either binary
   parenthesization.  This is the appropriate extensional associativity
   interface for internal graph presentations. -/
def HFRecursiveThreeRelationalComposite
    (first second third composite : HFRecursiveSet) : Prop :=
  ∀ input output,
    HFRecursiveMember (hfRecursiveOrderedPair input output) composite ↔
      ∃ firstMiddle secondMiddle,
        HFRecursiveMember (hfRecursiveOrderedPair input firstMiddle) first ∧
        HFRecursiveMember (hfRecursiveOrderedPair firstMiddle secondMiddle) second ∧
        HFRecursiveMember (hfRecursiveOrderedPair secondMiddle output) third

theorem hfRecursiveThreeRelationalComposite_unique
    {first second third composite₁ composite₂ : HFRecursiveSet}
    (h₁ : HFRecursiveThreeRelationalComposite first second third composite₁)
    (h₂ : HFRecursiveThreeRelationalComposite first second third composite₂)
    (hr₁ : HFRecursiveRelation composite₁)
    (hr₂ : HFRecursiveRelation composite₂) :
    composite₁ = composite₂ := by
  apply hfRecursiveSet_extensionality
  intro element
  constructor
  · intro hmember
    rcases hr₁ element hmember with ⟨input, output, rfl⟩
    exact (h₂ input output).mpr ((h₁ input output).mp hmember)
  · intro hmember
    rcases hr₂ element hmember with ⟨input, output, rfl⟩
    exact (h₁ input output).mpr ((h₂ input output).mp hmember)

/- Translation graphs satisfy the parenthesization-free three-stage
   specification.  Thus their internal graph composite is associative as an
   extensional finite relation, not merely after evaluating an input. -/
theorem hfRecursiveNatShiftGraph_three_relationalComposite
    (firstOffset secondOffset thirdOffset n : Nat) :
    HFRecursiveThreeRelationalComposite
      (hfRecursiveNatShiftGraph firstOffset n)
      (hfRecursiveNatShiftGraph secondOffset (n + firstOffset))
      (hfRecursiveNatShiftGraph thirdOffset (n + firstOffset + secondOffset))
      (hfRecursiveNatShiftGraph (firstOffset + (secondOffset + thirdOffset)) n) := by
  intro input output
  exact hfRecursiveNatShiftGraph_associative_application_iff
    firstOffset secondOffset thirdOffset n input output

/- Both binary parenthesizations are witnessed by the very same extensional
   summed graph.  The conjunction makes the associativity coherence usable by
   clients which work with binary relational-composite certificates. -/
theorem hfRecursiveNatShiftGraph_associative_relationalComposite
    (firstOffset secondOffset thirdOffset n : Nat) :
    HFRecursiveRelationalComposite
      (hfRecursiveNatShiftGraph firstOffset n)
      (hfRecursiveNatShiftGraph (secondOffset + thirdOffset) (n + firstOffset))
      (hfRecursiveNatShiftGraph ((firstOffset + secondOffset) + thirdOffset) n) ∧
    HFRecursiveRelationalComposite
      (hfRecursiveNatShiftGraph (firstOffset + secondOffset) n)
      (hfRecursiveNatShiftGraph thirdOffset (n + (firstOffset + secondOffset)))
      (hfRecursiveNatShiftGraph ((firstOffset + secondOffset) + thirdOffset) n) := by
  constructor
  · simpa [Nat.add_assoc] using
      (hfRecursiveNatShiftGraph_relationalComposite firstOffset
        (secondOffset + thirdOffset) n)
  · exact hfRecursiveNatShiftGraph_relationalComposite
      (firstOffset + secondOffset) thirdOffset n

/- Any relation graph realizing the same three translations is uniquely the
   summed shift graph.  This packages the concrete three-way composition
   calculation as a reusable quotient-level uniqueness theorem. -/
theorem hfRecursiveNatShiftGraph_three_relationalComposite_unique
    {firstOffset secondOffset thirdOffset n : Nat} {composite : HFRecursiveSet}
    (hcomposite : HFRecursiveThreeRelationalComposite
      (hfRecursiveNatShiftGraph firstOffset n)
      (hfRecursiveNatShiftGraph secondOffset (n + firstOffset))
      (hfRecursiveNatShiftGraph thirdOffset (n + firstOffset + secondOffset))
      composite)
    (hrelation : HFRecursiveRelation composite) :
    composite = hfRecursiveNatShiftGraph
      (firstOffset + (secondOffset + thirdOffset)) n := by
  apply hfRecursiveThreeRelationalComposite_unique hcomposite
    (hfRecursiveNatShiftGraph_three_relationalComposite
      firstOffset secondOffset thirdOffset n) hrelation
  exact hfRecursiveNatShiftGraph_relation _ _

def HFRecursiveSubset (s t : HFRecursiveSet) : Prop :=
  ∀ x, HFRecursiveMember x s → HFRecursiveMember x t

/- The quotient subset relation has the expected finite presentation-level
   characterization. -/
theorem hfRecursiveSubset_mk_iff_raw (u s : HFSet) :
    HFRecursiveSubset (Quotient.mk hfRecursiveSetoid u)
      (Quotient.mk hfRecursiveSetoid s) ↔ HFRecursiveSubsetRaw u s := by
  constructor
  · intro h x hx
    have hxu : HFRecursiveMember (Quotient.mk hfRecursiveSetoid x)
        (Quotient.mk hfRecursiveSetoid u) := by
      exact (hfRecursiveMember_mk x u).mpr
        (fun n => ⟨x, hx, hfApprox_refl n x⟩)
    rcases hfRecursiveMemberRaw_iff_exists.mp
        ((hfRecursiveMember_mk x s).mp (h _ hxu)) with ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  · intro h x hx
    revert hx
    refine Quotient.inductionOn x ?_
    intro x hx
    rcases hfRecursiveMemberRaw_iff_exists.mp
        ((hfRecursiveMember_mk x u).mp hx) with ⟨z, hz, hxz⟩
    rcases h z hz with ⟨y, hy, hzy⟩
    exact (hfRecursiveMember_mk x s).mpr
      (hfRecursiveMemberRaw_iff_exists.mpr
        ⟨y, hy, hfRecursiveEq_trans hxz hzy⟩)

/- Quotient-level normalization relative to a fixed finite presentation.
   Any recursively represented subset of `[s]` has a literal syntactic subset
   `v ⊆ s` as a representative.  Thus changing to the normalized witness is
   invisible in the extensional quotient, while its inclusion is decidable at
   the raw finite level. -/
theorem hfRecursiveSubset_normalize_mk
    (u : HFRecursiveSet) (s : HFSet)
    (hsubset : HFRecursiveSubset u (Quotient.mk hfRecursiveSetoid s)) :
    ∃ v, HFSubset v s ∧ u = Quotient.mk hfRecursiveSetoid v := by
  revert hsubset
  refine Quotient.inductionOn u ?_
  intro u hsubset
  rcases hfRecursiveSubsetRaw_refine
      ((hfRecursiveSubset_mk_iff_raw u s).mp hsubset) with
    ⟨v, hvsubset, huv⟩
  exact ⟨v, hvsubset, Quotient.sound huv⟩

/- Membership in the syntactic powerset is precisely internal subsethood of
   the represented sets.  The reverse direction uses finite normalization and
   the already proved extensional completeness of the presentation. -/
theorem hfRecursiveMember_power_mk_iff_subset (x : HFRecursiveSet) (s : HFSet) :
    HFRecursiveMember x (Quotient.mk hfRecursiveSetoid s.power) ↔
      HFRecursiveSubset x (Quotient.mk hfRecursiveSetoid s) := by
  refine Quotient.inductionOn x ?_
  intro x
  constructor
  · intro hx
    apply (hfRecursiveSubset_mk_iff_raw x s).mpr
    rcases hfRecursiveMemberRaw_iff_exists.mp
        ((hfRecursiveMember_mk x s.power).mp hx) with ⟨v, hv, hxv⟩
    intro z hz
    have hzRaw : HFRecursiveMemberRaw z x :=
      fun n => ⟨z, hz, hfApprox_refl n z⟩
    have hzv : HFRecursiveMemberRaw z v :=
      (hfRecursiveMemberRaw_source_congruent hxv).mp hzRaw
    rcases hfRecursiveMemberRaw_iff_exists.mp hzv with ⟨w, hw, hzw⟩
    exact ⟨w, hf_power_member_subset hv w hw, hzw⟩
  · intro hx
    have hraw : HFRecursiveSubsetRaw x s :=
      (hfRecursiveSubset_mk_iff_raw x s).mp hx
    rcases hfRecursiveSubsetRaw_refine hraw with ⟨v, hvs, hxv⟩
    rcases hf_power_complete_extensional hvs with ⟨w, hw, hvw⟩
    exact (hfRecursiveMember_mk x s.power).mpr
      (hfRecursiveMemberRaw_iff_exists.mpr
        ⟨w, hw, hfRecursiveEq_trans hxv (hfExtensionalEq_recursive hvw)⟩)

/- Therefore the finite powerset presentation is invariant under recursive
   extensional equality and can genuinely descend to the quotient. -/
theorem hfRecursive_power_congruent {s t : HFSet}
    (h : HFRecursiveEq s t) : HFRecursiveEq s.power t.power := by
  apply @Quotient.exact HFSet hfRecursiveSetoid s.power t.power
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_power_mk_iff_subset,
    hfRecursiveMember_power_mk_iff_subset]
  have hst : (Quotient.mk hfRecursiveSetoid s : HFRecursiveSet) =
      Quotient.mk hfRecursiveSetoid t := Quotient.sound h
  rw [hst]

/- The quotient-level finite powerset.  It is a powerset operation for the
   finite hereditary-set fragment, not an assertion of a full set-theoretic
   powerset principle. -/
def hfRecursivePower (s : HFRecursiveSet) : HFRecursiveSet :=
  Quotient.liftOn s
    (fun s => Quotient.mk hfRecursiveSetoid s.power)
    (by
      intro s t h
      exact Quotient.sound (hfRecursive_power_congruent h))

theorem hfRecursivePower_mk (s : HFSet) :
    hfRecursivePower (Quotient.mk hfRecursiveSetoid s) =
      Quotient.mk hfRecursiveSetoid s.power := rfl

theorem hfRecursiveMember_power_iff_subset (x s : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursivePower s) ↔ HFRecursiveSubset x s := by
  refine Quotient.inductionOn s ?_
  intro s
  exact hfRecursiveMember_power_mk_iff_subset x s

/- A singleton is included in a set exactly when its unique element is a
   member.  This is the bridge from the powerset specification back to the
   original set, and will make powerset extensionality available internally. -/
theorem hfRecursiveSubset_singleton_iff (x s : HFRecursiveSet) :
    HFRecursiveSubset (hfRecursiveSingleton x) s ↔ HFRecursiveMember x s := by
  constructor
  · intro h
    exact h x ((hfRecursiveMember_singleton_iff x x).mpr rfl)
  · intro hx y hy
    have hyx : y = x := (hfRecursiveMember_singleton_iff y x).mp hy
    rw [hyx]
    exact hx

/- Singleton membership in a finite powerset has the expected Boolean
   interpretation. -/
theorem hfRecursiveMember_singleton_power_iff (x s : HFRecursiveSet) :
    HFRecursiveMember (hfRecursiveSingleton x) (hfRecursivePower s) ↔
      HFRecursiveMember x s := by
  rw [hfRecursiveMember_power_iff_subset, hfRecursiveSubset_singleton_iff]

/- The empty set is a member of every finite powerset. -/
theorem hfRecursiveEmpty_mem_power (s : HFRecursiveSet) :
    HFRecursiveMember hfRecursiveEmpty (hfRecursivePower s) := by
  rw [hfRecursiveMember_power_iff_subset]
  intro x hx
  exact False.elim (hfRecursiveMember_empty x hx)

/- Finite powerset is extensional: its value determines the original
   quotient-level hereditary finite set. -/
theorem hfRecursivePower_injective : ∀ ⦃s t : HFRecursiveSet⦄,
    hfRecursivePower s = hfRecursivePower t → s = t := by
  intro s t hpower
  apply hfRecursiveSet_extensionality
  intro x
  constructor
  · intro hxs
    have hsingleton : HFRecursiveMember (hfRecursiveSingleton x)
        (hfRecursivePower s) :=
      (hfRecursiveMember_singleton_power_iff x s).mpr hxs
    rw [hpower] at hsingleton
    exact (hfRecursiveMember_singleton_power_iff x t).mp hsingleton
  · intro hxt
    have hsingleton : HFRecursiveMember (hfRecursiveSingleton x)
        (hfRecursivePower t) :=
      (hfRecursiveMember_singleton_power_iff x t).mpr hxt
    rw [← hpower] at hsingleton
    exact (hfRecursiveMember_singleton_power_iff x s).mp hsingleton

theorem hfRecursivePower_eq_iff (s t : HFRecursiveSet) :
  hfRecursivePower s = hfRecursivePower t ↔ s = t := by
  constructor
  · exact hfRecursivePower_injective (s := s) (t := t)
  · intro h
    rw [h]

/- The finite powerset of the empty set has exactly its sole subset. -/
theorem hfRecursivePower_empty :
    hfRecursivePower hfRecursiveEmpty = hfRecursiveSingleton hfRecursiveEmpty := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_power_iff_subset, hfRecursiveMember_singleton_iff]
  constructor
  · intro hx
    apply hfRecursiveSet_extensionality
    intro y
    constructor
    · intro hy
      exact False.elim (hfRecursiveMember_empty y (hx y hy))
    · intro hy
      exact False.elim (hfRecursiveMember_empty y hy)
  · intro hx y hy
    rw [hx] at hy
    exact False.elim (hfRecursiveMember_empty y hy)

/- Finite powerset is monotone for the internally defined subset order. -/
theorem hfRecursivePower_monotone {s t : HFRecursiveSet} :
    HFRecursiveSubset s t → HFRecursiveSubset (hfRecursivePower s) (hfRecursivePower t) := by
  intro h x hx
  rw [hfRecursiveMember_power_iff_subset] at hx ⊢
  intro y hy
  exact h y (hx y hy)

/- Powerset is not merely monotone: on the finite hereditary-set quotient it
   reflects the internal inclusion order.  The reverse implication recovers a
   member of the base set through its singleton. -/
theorem hfRecursivePower_subset_iff {s t : HFRecursiveSet} :
    HFRecursiveSubset (hfRecursivePower s) (hfRecursivePower t) ↔
      HFRecursiveSubset s t := by
  constructor
  · intro h x hxs
    have hsingleton : HFRecursiveMember (hfRecursiveSingleton x)
        (hfRecursivePower s) :=
      (hfRecursiveMember_singleton_power_iff x s).mpr hxs
    have hsingleton' : HFRecursiveMember (hfRecursiveSingleton x)
        (hfRecursivePower t) := h _ hsingleton
    exact (hfRecursiveMember_singleton_power_iff x t).mp hsingleton'
  · exact hfRecursivePower_monotone

/- Taking the internal union of all finite subsets reconstructs the original
   finite hereditary set.  This is the quotient-level finite analogue of
   `⋃ 𝒫(s) = s`, and uses singleton subsets for the nontrivial direction. -/
theorem hfRecursiveBigUnion_power (s : HFRecursiveSet) :
    hfRecursiveBigUnion (hfRecursivePower s) = s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_bigUnion_iff]
  constructor
  · rintro ⟨u, huPower, hxu⟩
    exact (hfRecursiveMember_power_iff_subset u s).mp huPower x hxu
  · intro hxs
    refine ⟨hfRecursiveSingleton x,
      (hfRecursiveMember_singleton_power_iff x s).mpr hxs, ?_⟩
    exact (hfRecursiveMember_singleton_iff x x).mpr rfl

structure HFRecursivePowerOrderEmbedding where
  power : HFRecursiveSet → HFRecursiveSet
  retraction : HFRecursiveSet → HFRecursiveSet
  left_inverse : ∀ s, retraction (power s) = s
  order_iff : ∀ {s t},
    HFRecursiveSubset (power s) (power t) ↔ HFRecursiveSubset s t
  injective : ∀ ⦃s t⦄, power s = power t → s = t

def hfRecursivePowerOrderEmbedding : HFRecursivePowerOrderEmbedding where
  power := hfRecursivePower
  retraction := hfRecursiveBigUnion
  left_inverse := hfRecursiveBigUnion_power
  order_iff := hfRecursivePower_subset_iff
  injective := hfRecursivePower_injective

theorem hfRecursiveSubset_refl (s : HFRecursiveSet) : HFRecursiveSubset s s :=
  fun _ h => h

/- Internal von Neumann naturals are linearly ordered by membership. -/
theorem hfRecursiveNat_trichotomy (m n : Nat) :
    HFRecursiveMember (hfRecursiveNat m) (hfRecursiveNat n) ∨
      m = n ∨ HFRecursiveMember (hfRecursiveNat n) (hfRecursiveNat m) := by
  rcases Nat.lt_trichotomy m n with hmn | heq | hnm
  · exact Or.inl ((hfRecursiveNat_member_iff m n).mpr hmn)
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr ((hfRecursiveNat_member_iff n m).mpr hnm))

/- Finite von Neumann ordinals are transitive in the internal membership
   relation: a member of a member is already a member of the ordinal. -/
theorem hfRecursiveNat_transitive (n : Nat) (x : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveNat n) →
      HFRecursiveSubset x (hfRecursiveNat n) := by
  intro hx y hy
  rcases (hfRecursiveMember_nat_iff_exists x n).mp hx with ⟨m, hm, hxm⟩
  rw [hxm] at hy
  rcases (hfRecursiveMember_nat_iff_exists y m).mp hy with ⟨k, hk, hyk⟩
  rw [hyk]
  exact (hfRecursiveNat_member_iff k n).mpr (Nat.lt_trans hk hm)

/- The internally represented successor is constructed from the already
   available pairing and binary-union operations: `n + 1 = n ∪ {n}`. -/
theorem hfRecursiveNat_succ_eq (n : Nat) :
    hfRecursiveNat (n + 1) =
      hfRecursiveUnion (hfRecursiveNat n)
        (hfRecursivePair (hfRecursiveNat n) (hfRecursiveNat n)) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_union_iff, hfRecursiveMember_pair_iff]
  constructor
  · intro hx
    rcases (hfRecursiveMember_nat_iff_exists x (n + 1)).mp hx with
      ⟨m, hm, hxm⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hmn | rfl
    · left
      rw [hxm]
      exact (hfRecursiveNat_member_iff m n).mpr hmn
    · right
      exact Or.inl hxm
  · rintro (hxn | (hxn | hxn))
    · rcases (hfRecursiveMember_nat_iff_exists x n).mp hxn with ⟨m, hm, hxm⟩
      rw [hxm]
      exact (hfRecursiveNat_member_iff m (n + 1)).mpr
        (Nat.lt_trans hm (Nat.lt_succ_self n))
    · rw [hxn]
      exact hfRecursiveNat_succ_member n
    · rw [hxn]
      exact hfRecursiveNat_succ_member n

theorem hfRecursiveNat_zero_ne_succ (n : Nat) :
    hfRecursiveNat 0 ≠ hfRecursiveNat (n + 1) := by
  intro equal
  have indexEqual : 0 = n + 1 := hfRecursiveNat_injective equal
  cases indexEqual

theorem hfRecursiveNat_succ_injective {m n : Nat} :
    hfRecursiveNat (m + 1) = hfRecursiveNat (n + 1) → m = n := by
  intro equal
  have indexEqual : m + 1 = n + 1 := hfRecursiveNat_injective equal
  exact Nat.add_right_cancel indexEqual

theorem hfRecursiveNat_induction (predicate : HFRecursiveSet → Prop)
    (zero : predicate (hfRecursiveNat 0))
    (successor : ∀ n, predicate (hfRecursiveNat n) →
      predicate (hfRecursiveNat (n + 1))) :
    ∀ n, predicate (hfRecursiveNat n) := by
  intro n
  induction n with
  | zero => exact zero
  | succ n ih => exact successor n ih

theorem hfRecursiveNat_recursion_unique {A : Type}
    (f g : HFRecursiveSet → A) (step : A → A)
    (zero : f (hfRecursiveNat 0) = g (hfRecursiveNat 0))
    (fSucc : ∀ n, f (hfRecursiveNat (n + 1)) = step (f (hfRecursiveNat n)))
    (gSucc : ∀ n, g (hfRecursiveNat (n + 1)) = step (g (hfRecursiveNat n))) :
    ∀ n, f (hfRecursiveNat n) = g (hfRecursiveNat n) := by
  intro n
  induction n with
  | zero => exact zero
  | succ n ih =>
      calc
        f (hfRecursiveNat (n + 1)) = step (f (hfRecursiveNat n)) := fSucc n
        _ = step (g (hfRecursiveNat n)) := congrArg step ih
        _ = g (hfRecursiveNat (n + 1)) := (gSucc n).symm

/- Binary union of finite von Neumann ordinals is their ordinal maximum.
   This is an internal, extensional reconstruction of the usual ordinal
   operation, rather than merely an equality of their natural indices. -/
theorem hfRecursiveNat_union_eq_max (m n : Nat) :
    hfRecursiveUnion (hfRecursiveNat m) (hfRecursiveNat n) =
      hfRecursiveNat (Nat.max m n) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_union_iff]
  constructor
  · rintro (hxm | hxn)
    · rcases (hfRecursiveMember_nat_iff_exists x m).mp hxm with ⟨k, hk, rfl⟩
      exact (hfRecursiveNat_member_iff k (Nat.max m n)).mpr
        (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _))
    · rcases (hfRecursiveMember_nat_iff_exists x n).mp hxn with ⟨k, hk, rfl⟩
      exact (hfRecursiveNat_member_iff k (Nat.max m n)).mpr
        (Nat.lt_of_lt_of_le hk (Nat.le_max_right _ _))
  · intro hx
    rcases (hfRecursiveMember_nat_iff_exists x (Nat.max m n)).mp hx with
      ⟨k, hk, rfl⟩
    by_cases hmn : m ≤ n
    · right
      exact (hfRecursiveNat_member_iff k n).mpr
        (by simpa [Nat.max_eq_right hmn] using hk)
    · left
      have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      exact (hfRecursiveNat_member_iff k m).mpr
        (by simpa [Nat.max_eq_left hnm] using hk)

/- The big union of a successor finite ordinal is its predecessor.  Together
   with `hfRecursiveNat_succ_eq`, this gives the familiar successor/union
   laws directly in the internally constructed finite-set universe. -/
theorem hfRecursiveBigUnion_nat_succ (n : Nat) :
    hfRecursiveBigUnion (hfRecursiveNat (n + 1)) = hfRecursiveNat n := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_bigUnion_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfRecursiveMember_nat_iff_exists y (n + 1)).mp hy with
      ⟨m, hm, rfl⟩
    rcases (hfRecursiveMember_nat_iff_exists x m).mp hxy with ⟨k, hk, rfl⟩
    exact (hfRecursiveNat_member_iff k n).mpr (by omega)
  · intro hx
    refine ⟨hfRecursiveNat n, hfRecursiveNat_succ_member n, ?_⟩
    exact hx

theorem hfRecursiveSubset_trans {r s t : HFRecursiveSet} :
    HFRecursiveSubset r s → HFRecursiveSubset s t → HFRecursiveSubset r t := by
  intro hrs hst x hx
  exact hst x (hrs x hx)

theorem hfRecursiveSubset_antisymm {s t : HFRecursiveSet} :
    HFRecursiveSubset s t → HFRecursiveSubset t s → s = t := by
  intro hst hts
  apply hfRecursiveSet_extensionality
  intro x
  exact ⟨fun hx => hst x hx, fun hx => hts x hx⟩

/- The finite von Neumann embedding reflects and preserves the ordinary
   non-strict order as internal inclusion.  Together with
   `hfRecursiveNat_member_iff`, this identifies the full finite ordinal order
   inside the recursive-set quotient. -/
theorem hfRecursiveNat_subset_iff (m n : Nat) :
    HFRecursiveSubset (hfRecursiveNat m) (hfRecursiveNat n) ↔ m ≤ n := by
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro hnm
    exact hfRecursiveMember_irreflexive (hfRecursiveNat n)
      (h _ ((hfRecursiveNat_member_iff n m).mpr hnm))
  · intro hmn x hx
    rcases (hfRecursiveMember_nat_iff_exists x m).mp hx with ⟨k, hk, rfl⟩
    exact (hfRecursiveNat_member_iff k n).mpr (Nat.lt_of_lt_of_le hk hmn)

theorem hfRecursiveNat_add_right_subset_iff (a b c : Nat) :
    HFRecursiveSubset (hfRecursiveNat (a + c)) (hfRecursiveNat (b + c)) ↔
      HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_subset_iff, hfRecursiveNat_subset_iff,
    Nat.add_le_add_iff_right]

theorem hfRecursiveNat_add_left_subset_iff (a b c : Nat) :
    HFRecursiveSubset (hfRecursiveNat (c + a)) (hfRecursiveNat (c + b)) ↔
      HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_subset_iff, hfRecursiveNat_subset_iff,
    Nat.add_le_add_iff_left]

theorem hfRecursiveNat_mul_right_subset_iff
    (a b c : Nat) (positive : 0 < c) :
    HFRecursiveSubset (hfRecursiveNat (a * c)) (hfRecursiveNat (b * c)) ↔
      HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_subset_iff, hfRecursiveNat_subset_iff,
    Nat.mul_le_mul_right_iff positive]

theorem hfRecursiveNat_mul_left_subset_iff
    (a b c : Nat) (positive : 0 < c) :
    HFRecursiveSubset (hfRecursiveNat (c * a)) (hfRecursiveNat (c * b)) ↔
      HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_subset_iff, hfRecursiveNat_subset_iff,
    Nat.mul_le_mul_left_iff positive]

theorem hfRecursiveNat_add_monotone
    {a b c d : Nat}
    (first : HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b))
    (second : HFRecursiveSubset (hfRecursiveNat c) (hfRecursiveNat d)) :
    HFRecursiveSubset (hfRecursiveNat (a + c)) (hfRecursiveNat (b + d)) := by
  apply (hfRecursiveNat_subset_iff (a + c) (b + d)).mpr
  exact Nat.add_le_add
    ((hfRecursiveNat_subset_iff a b).mp first)
    ((hfRecursiveNat_subset_iff c d).mp second)

theorem hfRecursiveNat_mul_monotone
    {a b c d : Nat}
    (first : HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b))
    (second : HFRecursiveSubset (hfRecursiveNat c) (hfRecursiveNat d)) :
    HFRecursiveSubset (hfRecursiveNat (a * c)) (hfRecursiveNat (b * d)) := by
  apply (hfRecursiveNat_subset_iff (a * c) (b * d)).mpr
  exact Nat.mul_le_mul
    ((hfRecursiveNat_subset_iff a b).mp first)
    ((hfRecursiveNat_subset_iff c d).mp second)

theorem hfRecursiveNat_pow_base_monotone
    {a b : Nat} (exponent : Nat)
    (ordered : HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b)) :
    HFRecursiveSubset (hfRecursiveNat (a ^ exponent))
      (hfRecursiveNat (b ^ exponent)) := by
  apply (hfRecursiveNat_subset_iff (a ^ exponent) (b ^ exponent)).mpr
  exact Nat.pow_le_pow_left ((hfRecursiveNat_subset_iff a b).mp ordered) exponent

theorem hfRecursiveNat_pow_base_subset_iff
    (a b exponent : Nat) (positive : 0 < exponent) :
    HFRecursiveSubset (hfRecursiveNat (a ^ exponent))
        (hfRecursiveNat (b ^ exponent)) ↔
      HFRecursiveSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_subset_iff, hfRecursiveNat_subset_iff,
    Nat.pow_le_pow_iff_left (Nat.ne_of_gt positive)]

theorem hfRecursiveNat_pow_exponent_monotone
    (base : Nat) (basePositive : 0 < base) {m n : Nat}
    (ordered : HFRecursiveSubset (hfRecursiveNat m) (hfRecursiveNat n)) :
    HFRecursiveSubset (hfRecursiveNat (base ^ m))
      (hfRecursiveNat (base ^ n)) := by
  apply (hfRecursiveNat_subset_iff (base ^ m) (base ^ n)).mpr
  exact Nat.pow_le_pow_right basePositive ((hfRecursiveNat_subset_iff m n).mp ordered)

theorem hfRecursiveNat_pow_exponent_subset_iff
    (base m n : Nat) (baseGreaterOne : 1 < base) :
    HFRecursiveSubset (hfRecursiveNat (base ^ m))
        (hfRecursiveNat (base ^ n)) ↔
      HFRecursiveSubset (hfRecursiveNat m) (hfRecursiveNat n) := by
  rw [hfRecursiveNat_subset_iff, hfRecursiveNat_subset_iff,
    Nat.pow_le_pow_iff_right baseGreaterOne]

/- Strict inclusion is therefore not an external convention: it is exactly
   the strict natural-number order on the internally reconstructed ordinals. -/
def HFRecursiveProperSubset (s t : HFRecursiveSet) : Prop :=
  HFRecursiveSubset s t ∧ ¬ HFRecursiveSubset t s

theorem hfRecursiveNat_properSubset_iff (m n : Nat) :
    HFRecursiveProperSubset (hfRecursiveNat m) (hfRecursiveNat n) ↔ m < n := by
  constructor
  · rintro ⟨hmn, hnm⟩
    have hle : m ≤ n := (hfRecursiveNat_subset_iff m n).mp hmn
    have hneq : m ≠ n := by
      intro h
      apply hnm
      simpa [h] using hmn
    exact Nat.lt_of_le_of_ne hle hneq
  · intro hmn
    refine ⟨(hfRecursiveNat_subset_iff m n).mpr (Nat.le_of_lt hmn), ?_⟩
    intro hnm
    have hle : n ≤ m := (hfRecursiveNat_subset_iff n m).mp hnm
    exact (Nat.not_le_of_gt hmn) hle

theorem hfRecursiveNat_add_right_properSubset_iff (a b c : Nat) :
    HFRecursiveProperSubset (hfRecursiveNat (a + c)) (hfRecursiveNat (b + c)) ↔
      HFRecursiveProperSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_properSubset_iff, hfRecursiveNat_properSubset_iff,
    Nat.add_lt_add_iff_right]

theorem hfRecursiveNat_add_left_properSubset_iff (a b c : Nat) :
    HFRecursiveProperSubset (hfRecursiveNat (c + a)) (hfRecursiveNat (c + b)) ↔
      HFRecursiveProperSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_properSubset_iff, hfRecursiveNat_properSubset_iff,
    Nat.add_lt_add_iff_left]

theorem hfRecursiveNat_mul_right_properSubset_iff
    (a b c : Nat) (positive : 0 < c) :
    HFRecursiveProperSubset (hfRecursiveNat (a * c)) (hfRecursiveNat (b * c)) ↔
      HFRecursiveProperSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_properSubset_iff, hfRecursiveNat_properSubset_iff,
    Nat.mul_lt_mul_right positive]

theorem hfRecursiveNat_mul_left_properSubset_iff
    (a b c : Nat) (positive : 0 < c) :
    HFRecursiveProperSubset (hfRecursiveNat (c * a)) (hfRecursiveNat (c * b)) ↔
      HFRecursiveProperSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_properSubset_iff, hfRecursiveNat_properSubset_iff,
    Nat.mul_lt_mul_left positive]

theorem hfRecursiveNat_pow_base_properSubset_iff
    (a b exponent : Nat) (positive : 0 < exponent) :
    HFRecursiveProperSubset (hfRecursiveNat (a ^ exponent))
        (hfRecursiveNat (b ^ exponent)) ↔
      HFRecursiveProperSubset (hfRecursiveNat a) (hfRecursiveNat b) := by
  rw [hfRecursiveNat_properSubset_iff, hfRecursiveNat_properSubset_iff,
    Nat.pow_lt_pow_iff_left (Nat.ne_of_gt positive)]

theorem hfRecursiveNat_pow_exponent_properSubset_iff
    (base m n : Nat) (baseGreaterOne : 1 < base) :
    HFRecursiveProperSubset (hfRecursiveNat (base ^ m))
        (hfRecursiveNat (base ^ n)) ↔
      HFRecursiveProperSubset (hfRecursiveNat m) (hfRecursiveNat n) := by
  rw [hfRecursiveNat_properSubset_iff, hfRecursiveNat_properSubset_iff,
    Nat.pow_lt_pow_iff_right baseGreaterOne]

/- Equality of internal finite ordinals is exactly equality of their external
   indices; this is the order-reflecting half of the ordinal embedding. -/
theorem hfRecursiveNat_eq_iff (m n : Nat) :
    hfRecursiveNat m = hfRecursiveNat n ↔ m = n := by
  constructor
  · exact hfRecursiveNat_injective
  · intro h
    rw [h]

/- Hence the three internal alternatives of two finite ordinals are mutually
   exclusive and correspond precisely to `<`, `=`, and `>` on naturals. -/
theorem hfRecursiveNat_trichotomy_iff (m n : Nat) :
    (HFRecursiveMember (hfRecursiveNat m) (hfRecursiveNat n) ∧ m < n) ∨
      (hfRecursiveNat m = hfRecursiveNat n ∧ m = n) ∨
      (HFRecursiveMember (hfRecursiveNat n) (hfRecursiveNat m) ∧ n < m) := by
  rcases Nat.lt_trichotomy m n with hmn | hmn | hnm
  · exact Or.inl ⟨(hfRecursiveNat_member_iff m n).mpr hmn, hmn⟩
  · exact Or.inr (Or.inl ⟨by rw [hmn], hmn⟩)
  · exact Or.inr (Or.inr ⟨(hfRecursiveNat_member_iff n m).mpr hnm, hnm⟩)

/- Binary union therefore transports the semilattice laws of `max` to the
   internally reconstructed ordinals. -/
theorem hfRecursiveNat_union_assoc (l m n : Nat) :
    hfRecursiveUnion (hfRecursiveUnion (hfRecursiveNat l) (hfRecursiveNat m))
      (hfRecursiveNat n) =
      hfRecursiveUnion (hfRecursiveNat l)
        (hfRecursiveUnion (hfRecursiveNat m) (hfRecursiveNat n)) := by
  rw [hfRecursiveNat_union_eq_max, hfRecursiveNat_union_eq_max,
    hfRecursiveNat_union_eq_max, hfRecursiveNat_union_eq_max]
  congr 1
  exact Nat.max_assoc l m n

theorem hfRecursiveNat_union_comm (m n : Nat) :
    hfRecursiveUnion (hfRecursiveNat m) (hfRecursiveNat n) =
      hfRecursiveUnion (hfRecursiveNat n) (hfRecursiveNat m) := by
  rw [hfRecursiveNat_union_eq_max, hfRecursiveNat_union_eq_max]
  congr 1
  exact Nat.max_comm m n

theorem hfRecursiveNat_union_idempotent (n : Nat) :
    hfRecursiveUnion (hfRecursiveNat n) (hfRecursiveNat n) = hfRecursiveNat n := by
  rw [hfRecursiveNat_union_eq_max]
  congr 1
  exact Nat.max_self n

theorem hfRecursiveSubset_union_left (s t : HFRecursiveSet) :
    HFRecursiveSubset s (hfRecursiveUnion s t) := by
  intro x hx
  exact (hfRecursiveMember_union_iff x s t).mpr (Or.inl hx)

theorem hfRecursiveSubset_union_right (s t : HFRecursiveSet) :
    HFRecursiveSubset t (hfRecursiveUnion s t) := by
  intro x hx
  exact (hfRecursiveMember_union_iff x s t).mpr (Or.inr hx)

theorem hfRecursiveUnion_least {s t u : HFRecursiveSet} :
    HFRecursiveSubset s u → HFRecursiveSubset t u →
      HFRecursiveSubset (hfRecursiveUnion s t) u := by
  intro hsu htu x hx
  rcases (hfRecursiveMember_union_iff x s t).mp hx with hxs | hxt
  · exact hsu x hxs
  · exact htu x hxt

theorem hfRecursiveUnion_subset_iff {s t u : HFRecursiveSet} :
    HFRecursiveSubset (hfRecursiveUnion s t) u ↔
      HFRecursiveSubset s u ∧ HFRecursiveSubset t u := by
  constructor
  · intro unionSubset
    constructor
    · intro x hxs
      exact unionSubset x (hfRecursiveSubset_union_left s t x hxs)
    · intro x hxt
      exact unionSubset x (hfRecursiveSubset_union_right s t x hxt)
  · rintro ⟨hsu, htu⟩
    exact hfRecursiveUnion_least hsu htu

theorem hfRecursiveUnion_eq_right_iff_subset (s t : HFRecursiveSet) :
    hfRecursiveUnion s t = t ↔ HFRecursiveSubset s t := by
  constructor
  · intro unionEq x hxs
    have hxUnion : HFRecursiveMember x (hfRecursiveUnion s t) :=
      (hfRecursiveMember_union_iff x s t).mpr (Or.inl hxs)
    simpa only [unionEq] using hxUnion
  · intro subset
    apply hfRecursiveSet_extensionality
    intro x
    rw [hfRecursiveMember_union_iff]
    constructor
    · rintro (hxs | hxt)
      · exact subset x hxs
      · exact hxt
    · intro hxt
      exact Or.inr hxt

theorem hfRecursiveUnion_eq_left_iff_subset (s t : HFRecursiveSet) :
    hfRecursiveUnion s t = s ↔ HFRecursiveSubset t s := by
  rw [hfRecursiveUnion_comm]
  exact hfRecursiveUnion_eq_right_iff_subset t s

/- The quotient Cartesian product has the expected zero laws.  These are
   proved from the quotient membership specification, so they do not depend on
   a chosen syntactic presentation of either factor. -/
theorem hfRecursiveProduct_empty_left (s : HFRecursiveSet) :
    hfRecursiveProduct hfRecursiveEmpty s = hfRecursiveEmpty := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_product_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hxab⟩
    exact False.elim (hfRecursiveMember_empty a ha)
  · intro hx
    exact False.elim (hfRecursiveMember_empty x hx)

theorem hfRecursiveProduct_empty_right (s : HFRecursiveSet) :
    hfRecursiveProduct s hfRecursiveEmpty = hfRecursiveEmpty := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_product_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hxab⟩
    exact False.elim (hfRecursiveMember_empty b hb)
  · intro hx
    exact False.elim (hfRecursiveMember_empty x hx)

/- Cartesian product is monotone in both arguments for the internally
   defined, quotient-safe subset relation. -/
theorem hfRecursiveProduct_mono {left left' right right' : HFRecursiveSet}
    (hleft : HFRecursiveSubset left left')
    (hright : HFRecursiveSubset right right') :
    HFRecursiveSubset (hfRecursiveProduct left right)
      (hfRecursiveProduct left' right') := by
  intro x hx
  rcases (hfRecursiveMember_product_iff x left right).mp hx with
    ⟨a, ha, b, hb, hxab⟩
  exact (hfRecursiveMember_product_iff x left' right').mpr
    ⟨a, hleft a ha, b, hright b hb, hxab⟩

/- Cartesian product has the expected singleton normal form.  This is an
   equality in the recursive quotient, not equality of raw finite-set
   presentations. -/
theorem hfRecursiveProduct_singleton_singleton (a b : HFRecursiveSet) :
    hfRecursiveProduct (hfRecursiveSingleton a) (hfRecursiveSingleton b) =
      hfRecursiveSingleton (hfRecursiveOrderedPair a b) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_product_iff, hfRecursiveMember_singleton_iff]
  constructor
  · rintro ⟨a', ha', b', hb', hpair⟩
    have haa' : a' = a := (hfRecursiveMember_singleton_iff a' a).mp ha'
    have hbb' : b' = b := (hfRecursiveMember_singleton_iff b' b).mp hb'
    simpa [haa', hbb'] using hpair
  · intro hpair
    exact ⟨a, (hfRecursiveMember_singleton_iff a a).mpr rfl,
      b, (hfRecursiveMember_singleton_iff b b).mpr rfl, hpair⟩

/- For nonempty source factors, inclusion of Cartesian products reflects
   inclusion of both factors.  Nonemptiness is essential: a product with an
   empty factor carries no information about the other factor. -/
theorem hfRecursiveProduct_subset_iff {left left' right right' : HFRecursiveSet}
    (hleftNonempty : ∃ a, HFRecursiveMember a left)
    (hrightNonempty : ∃ b, HFRecursiveMember b right) :
    HFRecursiveSubset (hfRecursiveProduct left right)
      (hfRecursiveProduct left' right') ↔
      HFRecursiveSubset left left' ∧ HFRecursiveSubset right right' := by
  constructor
  · intro hproduct
    constructor
    · intro a ha
      rcases hrightNonempty with ⟨b, hb⟩
      have hpair : HFRecursiveMember (hfRecursiveOrderedPair a b)
          (hfRecursiveProduct left right) :=
        (hfRecursiveMember_product_iff _ left right).mpr ⟨a, ha, b, hb, rfl⟩
      rcases (hfRecursiveMember_product_iff _ left' right').mp
          (hproduct _ hpair) with ⟨a', ha', b', hb', heq⟩
      exact (hfRecursiveOrderedPair_injective heq).left ▸ ha'
    · intro b hb
      rcases hleftNonempty with ⟨a, ha⟩
      have hpair : HFRecursiveMember (hfRecursiveOrderedPair a b)
          (hfRecursiveProduct left right) :=
        (hfRecursiveMember_product_iff _ left right).mpr ⟨a, ha, b, hb, rfl⟩
      rcases (hfRecursiveMember_product_iff _ left' right').mp
          (hproduct _ hpair) with ⟨a', ha', b', hb', heq⟩
      exact (hfRecursiveOrderedPair_injective heq).right ▸ hb'
  · rintro ⟨hleft, hright⟩
    exact hfRecursiveProduct_mono hleft hright

/- The singleton embedding of a pair is compatible with both finite
   powersets.  Equivalently, the canonical point
   `⟨{a}, {b}⟩` belongs to `P(left) × P(right)` exactly when its two original
   coordinates belong to the corresponding factors. -/
theorem hfRecursiveMember_product_power_singletons_iff
    (a b left right : HFRecursiveSet) :
    HFRecursiveMember
      (hfRecursiveOrderedPair (hfRecursiveSingleton a) (hfRecursiveSingleton b))
      (hfRecursiveProduct (hfRecursivePower left) (hfRecursivePower right)) ↔
      HFRecursiveMember a left ∧ HFRecursiveMember b right := by
  constructor
  · intro h
    rcases (hfRecursiveMember_product_iff _ (hfRecursivePower left)
        (hfRecursivePower right)).mp h with
      ⟨a', ha', b', hb', hpair⟩
    rcases hfRecursiveOrderedPair_injective hpair with ⟨haa', hbb'⟩
    constructor
    · apply (hfRecursiveMember_singleton_power_iff a left).mp
      rw [haa']
      exact ha'
    · apply (hfRecursiveMember_singleton_power_iff b right).mp
      rw [hbb']
      exact hb'
  · rintro ⟨ha, hb⟩
    exact (hfRecursiveMember_product_iff _ (hfRecursivePower left)
      (hfRecursivePower right)).mpr
      ⟨hfRecursiveSingleton a,
        (hfRecursiveMember_singleton_power_iff a left).mpr ha,
        hfRecursiveSingleton b,
        (hfRecursiveMember_singleton_power_iff b right).mpr hb, rfl⟩

/- Product distributes over finite union in each coordinate.  The witnesses
   in the product membership criterion make the two directions entirely
   extensional. -/
theorem hfRecursiveProduct_union_right (left right third : HFRecursiveSet) :
    hfRecursiveProduct left (hfRecursiveUnion right third) =
      hfRecursiveUnion (hfRecursiveProduct left right)
        (hfRecursiveProduct left third) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_product_iff, hfRecursiveMember_union_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hxab⟩
    rcases (hfRecursiveMember_union_iff b right third).mp hb with hb | hb
    · exact Or.inl ((hfRecursiveMember_product_iff x left right).mpr
        ⟨a, ha, b, hb, hxab⟩)
    · exact Or.inr ((hfRecursiveMember_product_iff x left third).mpr
        ⟨a, ha, b, hb, hxab⟩)
  · rintro (h | h)
    · rcases (hfRecursiveMember_product_iff x left right).mp h with
        ⟨a, ha, b, hb, hxab⟩
      exact ⟨a, ha, b, (hfRecursiveMember_union_iff b right third).mpr
        (Or.inl hb), hxab⟩
    · rcases (hfRecursiveMember_product_iff x left third).mp h with
        ⟨a, ha, b, hb, hxab⟩
      exact ⟨a, ha, b, (hfRecursiveMember_union_iff b right third).mpr
        (Or.inr hb), hxab⟩

theorem hfRecursiveProduct_union_left (left right third : HFRecursiveSet) :
    hfRecursiveProduct (hfRecursiveUnion left right) third =
      hfRecursiveUnion (hfRecursiveProduct left third)
        (hfRecursiveProduct right third) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_product_iff, hfRecursiveMember_union_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hxab⟩
    rcases (hfRecursiveMember_union_iff a left right).mp ha with ha | ha
    · exact Or.inl ((hfRecursiveMember_product_iff x left third).mpr
        ⟨a, ha, b, hb, hxab⟩)
    · exact Or.inr ((hfRecursiveMember_product_iff x right third).mpr
        ⟨a, ha, b, hb, hxab⟩)
  · rintro (h | h)
    · rcases (hfRecursiveMember_product_iff x left third).mp h with
        ⟨a, ha, b, hb, hxab⟩
      exact ⟨a, (hfRecursiveMember_union_iff a left right).mpr
        (Or.inl ha), b, hb, hxab⟩
    · rcases (hfRecursiveMember_product_iff x right third).mp h with
        ⟨a, ha, b, hb, hxab⟩
      exact ⟨a, (hfRecursiveMember_union_iff a left right).mpr
        (Or.inr ha), b, hb, hxab⟩

/- A nonempty Cartesian factor lets equality of products recover the other
   factor.  Both right factors are required: an empty factor would collapse a
   product to the empty set and would make such reflection false. -/
theorem hfRecursiveProduct_eq_reflect_left
    {left left' right right' : HFRecursiveSet}
    (hproduct : hfRecursiveProduct left right = hfRecursiveProduct left' right')
    (hright : ∃ b, HFRecursiveMember b right)
    (hright' : ∃ b, HFRecursiveMember b right') :
    left = left' := by
  apply hfRecursiveSubset_antisymm
  · intro a ha
    rcases hright with ⟨b, hb⟩
    have hp : HFRecursiveMember (hfRecursiveOrderedPair a b)
        (hfRecursiveProduct left right) :=
      (hfRecursiveMember_product_iff _ left right).mpr ⟨a, ha, b, hb, rfl⟩
    rw [hproduct] at hp
    rcases (hfRecursiveMember_product_iff _ left' right').mp hp with
      ⟨a', ha', b', hb', hpair⟩
    exact (hfRecursiveOrderedPair_injective hpair).left ▸ ha'
  · intro a ha
    rcases hright' with ⟨b, hb⟩
    have hp : HFRecursiveMember (hfRecursiveOrderedPair a b)
        (hfRecursiveProduct left' right') :=
      (hfRecursiveMember_product_iff _ left' right').mpr ⟨a, ha, b, hb, rfl⟩
    rw [← hproduct] at hp
    rcases (hfRecursiveMember_product_iff _ left right).mp hp with
      ⟨a', ha', b', hb', hpair⟩
    exact (hfRecursiveOrderedPair_injective hpair).left ▸ ha'

/- Symmetrically, nonempty left factors make product equality reflect the
   right factor. -/
theorem hfRecursiveProduct_eq_reflect_right
    {left left' right right' : HFRecursiveSet}
    (hproduct : hfRecursiveProduct left right = hfRecursiveProduct left' right')
    (hleft : ∃ a, HFRecursiveMember a left)
    (hleft' : ∃ a, HFRecursiveMember a left') :
    right = right' := by
  apply hfRecursiveSubset_antisymm
  · intro b hb
    rcases hleft with ⟨a, ha⟩
    have hp : HFRecursiveMember (hfRecursiveOrderedPair a b)
        (hfRecursiveProduct left right) :=
      (hfRecursiveMember_product_iff _ left right).mpr ⟨a, ha, b, hb, rfl⟩
    rw [hproduct] at hp
    rcases (hfRecursiveMember_product_iff _ left' right').mp hp with
      ⟨a', ha', b', hb', hpair⟩
    exact (hfRecursiveOrderedPair_injective hpair).right ▸ hb'
  · intro b hb
    rcases hleft' with ⟨a, ha⟩
    have hp : HFRecursiveMember (hfRecursiveOrderedPair a b)
        (hfRecursiveProduct left' right') :=
      (hfRecursiveMember_product_iff _ left' right').mpr ⟨a, ha, b, hb, rfl⟩
    rw [← hproduct] at hp
    rcases (hfRecursiveMember_product_iff _ left right).mp hp with
      ⟨a', ha', b', hb', hpair⟩
    exact (hfRecursiveOrderedPair_injective hpair).right ▸ hb'

theorem hfRecursiveProduct_eq_iff_factors_eq
    {left left' right right' : HFRecursiveSet}
    (hleft : ∃ a, HFRecursiveMember a left)
    (hleft' : ∃ a, HFRecursiveMember a left')
    (hright : ∃ b, HFRecursiveMember b right)
    (hright' : ∃ b, HFRecursiveMember b right') :
    hfRecursiveProduct left right = hfRecursiveProduct left' right' ↔
      left = left' ∧ right = right' := by
  constructor
  · intro productEq
    exact ⟨hfRecursiveProduct_eq_reflect_left productEq hright hright',
      hfRecursiveProduct_eq_reflect_right productEq hleft hleft'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/- The union of two finite powersets has the expected universal property:
   it is below a third powerset exactly when both source sets are below that
   third base set.  In particular this records the join operation on the
   order-embedded image of finite powerset. -/
theorem hfRecursiveUnion_power_subset_power_iff
    {s t u : HFRecursiveSet} :
    HFRecursiveSubset
      (hfRecursiveUnion (hfRecursivePower s) (hfRecursivePower t))
      (hfRecursivePower u) ↔
      HFRecursiveSubset s u ∧ HFRecursiveSubset t u := by
  constructor
  · intro h
    constructor
    · exact (hfRecursivePower_subset_iff).mp
        (hfRecursiveSubset_trans
          (hfRecursiveSubset_union_left (hfRecursivePower s) (hfRecursivePower t)) h)
    · exact (hfRecursivePower_subset_iff).mp
        (hfRecursiveSubset_trans
          (hfRecursiveSubset_union_right (hfRecursivePower s) (hfRecursivePower t)) h)
  · rintro ⟨hsu, htu⟩
    apply hfRecursiveUnion_least
    · exact (hfRecursivePower_subset_iff).mpr hsu
    · exact (hfRecursivePower_subset_iff).mpr htu

/- Every subset of either input remains a subset after adjoining the inputs;
   this is the concrete powerset/union inclusion used by the universal law. -/
theorem hfRecursiveUnion_power_subset_power_union (s t : HFRecursiveSet) :
    HFRecursiveSubset
      (hfRecursiveUnion (hfRecursivePower s) (hfRecursivePower t))
      (hfRecursivePower (hfRecursiveUnion s t)) := by
  exact (hfRecursiveUnion_power_subset_power_iff).mpr
    ⟨hfRecursiveSubset_union_left s t, hfRecursiveSubset_union_right s t⟩

theorem hfRecursiveUnion_idempotent (s : HFRecursiveSet) :
    hfRecursiveUnion s s = s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_union_iff]
  constructor
  · rintro (hx | hx) <;> exact hx
  · intro hx
    exact Or.inl hx

theorem hfRecursiveBigUnion_pair (s t : HFRecursiveSet) :
    hfRecursiveBigUnion (hfRecursivePair s t) = hfRecursiveUnion s t := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_bigUnion_iff, hfRecursiveMember_union_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfRecursiveMember_pair_iff y s t).mp hy with rfl | rfl
    · exact Or.inl hxy
    · exact Or.inr hxy
  · rintro (hxs | hxt)
    · exact ⟨s, (hfRecursiveMember_pair_iff s s t).mpr (Or.inl rfl), hxs⟩
    · exact ⟨t, (hfRecursiveMember_pair_iff t s t).mpr (Or.inr rfl), hxt⟩

theorem hfRecursiveFilter_union (p : HFRecursivePredicate)
    (s t : HFRecursiveSet) :
    hfRecursiveFilter p (hfRecursiveUnion s t) =
      hfRecursiveUnion (hfRecursiveFilter p s) (hfRecursiveFilter p t) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_filter_iff, hfRecursiveMember_union_iff,
    hfRecursiveMember_union_iff, hfRecursiveMember_filter_iff,
    hfRecursiveMember_filter_iff]
  constructor
  · rintro ⟨(hxs | hxt), hp⟩
    · exact Or.inl ⟨hxs, hp⟩
    · exact Or.inr ⟨hxt, hp⟩
  · rintro (⟨hxs, hp⟩ | ⟨hxt, hp⟩)
    · exact ⟨Or.inl hxs, hp⟩
    · exact ⟨Or.inr hxt, hp⟩

theorem hfRecursiveBigUnion_empty :
    hfRecursiveBigUnion hfRecursiveEmpty = hfRecursiveEmpty := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_bigUnion_iff]
  constructor
  · rintro ⟨y, hy, _⟩
    exact False.elim (hfRecursiveMember_empty y hy)
  · intro hx
    exact False.elim (hfRecursiveMember_empty x hx)

theorem hfRecursiveBigUnion_union (s t : HFRecursiveSet) :
    hfRecursiveBigUnion (hfRecursiveUnion s t) =
      hfRecursiveUnion (hfRecursiveBigUnion s) (hfRecursiveBigUnion t) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_bigUnion_iff x (hfRecursiveUnion s t)]
  rw [hfRecursiveMember_union_iff x (hfRecursiveBigUnion s) (hfRecursiveBigUnion t)]
  rw [hfRecursiveMember_bigUnion_iff x s, hfRecursiveMember_bigUnion_iff x t]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfRecursiveMember_union_iff y s t).mp hy with hys | hyt
    · exact Or.inl ⟨y, hys, hxy⟩
    · exact Or.inr ⟨y, hyt, hxy⟩
  · rintro (⟨y, hys, hxy⟩ | ⟨y, hyt, hxy⟩)
    · exact ⟨y, (hfRecursiveMember_union_iff y s t).mpr (Or.inl hys), hxy⟩
    · exact ⟨y, (hfRecursiveMember_union_iff y s t).mpr (Or.inr hyt), hxy⟩

def hfRecursiveTruePredicate : HFRecursivePredicate where
  run := fun _ => true
  respectful := by intro n x y h; rfl

def hfRecursiveFalsePredicate : HFRecursivePredicate where
  run := fun _ => false
  respectful := by intro n x y h; rfl

def HFRecursivePredicate.and (p q : HFRecursivePredicate) : HFRecursivePredicate where
  run := fun x => p.run x && q.run x
  respectful := by
    intro n x y h
    change (p.run x && q.run x) = (p.run y && q.run y)
    rw [p.respectful h, q.respectful h]

theorem hfRecursivePredicate_holds_and (p q : HFRecursivePredicate)
    (x : HFRecursiveSet) :
    (p.and q).holds x ↔ p.holds x ∧ q.holds x := by
  refine Quotient.inductionOn x ?_
  intro x
  change ((p.run x && q.run x) = true) ↔
    (p.run x = true ∧ q.run x = true)
  cases p.run x <;> cases q.run x <;> simp

/- The predicates used for separation are closed under Boolean complement.
   This is deliberately a complement of a *decidable extensional predicate*,
   rather than an attempted raw-presentation test for membership in an
   arbitrary quotient set.  The latter would not be invariant under changing
   representatives without an additional normalization theorem. -/
def HFRecursivePredicate.not (p : HFRecursivePredicate) : HFRecursivePredicate where
  run := fun x => Bool.not (p.run x)
  respectful := by
    intro n x y h
    change Bool.not (p.run x) = Bool.not (p.run y)
    rw [p.respectful h]

theorem hfRecursivePredicate_holds_not (p : HFRecursivePredicate)
    (x : HFRecursiveSet) :
    p.not.holds x ↔ ¬ p.holds x := by
  refine Quotient.inductionOn x ?_
  intro x
  change (Bool.not (p.run x) = true) ↔ ¬ p.run x = true
  cases p.run x <;> simp

/- The Boolean operations are defined on respectful raw predicates, hence all
   of the following laws are statements at the quotient level. -/
def HFRecursivePredicate.or (p q : HFRecursivePredicate) : HFRecursivePredicate where
  run := fun x => p.run x || q.run x
  respectful := by
    intro n x y h
    change (p.run x || q.run x) = (p.run y || q.run y)
    rw [p.respectful h, q.respectful h]

theorem hfRecursivePredicate_holds_or (p q : HFRecursivePredicate)
    (x : HFRecursiveSet) :
    (p.or q).holds x ↔ p.holds x ∨ q.holds x := by
  refine Quotient.inductionOn x ?_
  intro x
  change ((p.run x || q.run x) = true) ↔
    (p.run x = true ∨ q.run x = true)
  cases p.run x <;> cases q.run x <;> simp

theorem hfRecursivePredicate_holds_not_not (p : HFRecursivePredicate)
    (x : HFRecursiveSet) :
    p.not.not.holds x ↔ p.holds x := by
  rw [hfRecursivePredicate_holds_not, hfRecursivePredicate_holds_not]
  constructor
  · intro h
    exact Classical.byContradiction h
  · intro hp hnot
    exact hnot hp

theorem hfRecursivePredicate_holds_not_and (p q : HFRecursivePredicate)
    (x : HFRecursiveSet) :
    (p.and q).not.holds x ↔ p.not.holds x ∨ q.not.holds x := by
  rw [hfRecursivePredicate_holds_not, hfRecursivePredicate_holds_and,
    hfRecursivePredicate_holds_not, hfRecursivePredicate_holds_not]
  classical
  constructor
  · intro h
    by_cases hp : p.holds x
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · exact Or.inl hp
  · rintro (hp | hq) ⟨hp' , hq'⟩
    · exact hp hp'
    · exact hq hq'

theorem hfRecursivePredicate_holds_not_or (p q : HFRecursivePredicate)
    (x : HFRecursiveSet) :
    (p.or q).not.holds x ↔ p.not.holds x ∧ q.not.holds x := by
  rw [hfRecursivePredicate_holds_not, hfRecursivePredicate_holds_or,
    hfRecursivePredicate_holds_not, hfRecursivePredicate_holds_not]
  constructor
  · intro h
    exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · rintro ⟨hp, hq⟩ (hp' | hq')
    · exact hp hp'
    · exact hq hq'

/- Relative set difference (or complement in `s`) is separation by the
   complement predicate.  It is a genuine quotient-level operation, because
   `HFRecursivePredicate.not` remains approximation-respectful. -/
def hfRecursiveDifference (p : HFRecursivePredicate) (s : HFRecursiveSet) :
    HFRecursiveSet :=
  hfRecursiveFilter p.not s

theorem hfRecursiveMember_difference_iff (p : HFRecursivePredicate)
    (x s : HFRecursiveSet) :
    HFRecursiveMember x (hfRecursiveDifference p s) ↔
      HFRecursiveMember x s ∧ ¬ p.holds x := by
  rw [hfRecursiveDifference, hfRecursiveMember_filter_iff,
    hfRecursivePredicate_holds_not]

theorem hfRecursiveDifference_eq_filter_not (p : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveDifference p s = hfRecursiveFilter p.not s := rfl

theorem hfRecursiveDifference_not (p : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveDifference p.not s = hfRecursiveFilter p s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_difference_iff, hfRecursiveMember_filter_iff]
  constructor
  · rintro ⟨hxs, hnot⟩
    apply And.intro hxs
    apply Classical.byContradiction
    intro hpnot
    exact hnot ((hfRecursivePredicate_holds_not p x).mpr hpnot)
  · rintro ⟨hxs, hp⟩
    exact ⟨hxs, fun hpnot =>
      (hfRecursivePredicate_holds_not p x).mp hpnot hp⟩

theorem hfRecursiveDifference_difference (p : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveDifference p (hfRecursiveDifference p s) = hfRecursiveDifference p s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_difference_iff, hfRecursiveMember_difference_iff]
  constructor
  · rintro ⟨⟨hxs, hnot⟩, _⟩
    exact ⟨hxs, hnot⟩
  · rintro ⟨hxs, hnot⟩
    exact ⟨⟨hxs, hnot⟩, hnot⟩

/- Separation and its relative complement form a finite partition. -/
theorem hfRecursiveFilter_union_difference (p : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveUnion (hfRecursiveFilter p s) (hfRecursiveDifference p s) = s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_union_iff, hfRecursiveMember_filter_iff,
    hfRecursiveMember_difference_iff]
  constructor
  · rintro (⟨hxs, _⟩ | ⟨hxs, _⟩)
    · exact hxs
    · exact hxs
  · intro hxs
    by_cases hp : p.holds x
    · exact Or.inl ⟨hxs, hp⟩
    · exact Or.inr ⟨hxs, hp⟩

/- The two pieces of that partition are disjoint. -/
theorem hfRecursiveFilter_difference_disjoint (p : HFRecursivePredicate)
    (s x : HFRecursiveSet) :
    ¬ (HFRecursiveMember x (hfRecursiveFilter p s) ∧
      HFRecursiveMember x (hfRecursiveDifference p s)) := by
  rintro ⟨hfilter, hdifference⟩
  have hp : p.holds x := (hfRecursiveMember_filter_iff p x s).mp hfilter |>.right
  have hnot : ¬ p.holds x := (hfRecursiveMember_difference_iff p x s).mp hdifference |>.right
  exact hnot hp

/- Filtering twice is the intersection of two decidable extensional
   subobjects of `s`; order is immaterial. -/
theorem hfRecursiveFilter_intersection_comm (p q : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveFilter p (hfRecursiveFilter q s) =
      hfRecursiveFilter q (hfRecursiveFilter p s) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_filter_iff, hfRecursiveMember_filter_iff,
    hfRecursiveMember_filter_iff, hfRecursiveMember_filter_iff]
  constructor
  · rintro ⟨⟨hxs, hq⟩, hp⟩
    exact ⟨⟨hxs, hp⟩, hq⟩
  · rintro ⟨⟨hxs, hp⟩, hq⟩
    exact ⟨⟨hxs, hq⟩, hp⟩

theorem hfRecursiveTruePredicate_holds (x : HFRecursiveSet) :
    hfRecursiveTruePredicate.holds x := by
  refine Quotient.inductionOn x ?_
  intro x
  rfl

theorem hfRecursiveFalsePredicate_not_holds (x : HFRecursiveSet) :
    ¬ hfRecursiveFalsePredicate.holds x := by
  refine Quotient.inductionOn x ?_
  intro x h
  cases h

theorem hfRecursiveFilter_true (s : HFRecursiveSet) :
    hfRecursiveFilter hfRecursiveTruePredicate s = s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_filter_iff]
  constructor
  · exact fun h => h.left
  · intro hx
    exact ⟨hx, hfRecursiveTruePredicate_holds x⟩

theorem hfRecursiveFilter_false (s : HFRecursiveSet) :
    hfRecursiveFilter hfRecursiveFalsePredicate s = hfRecursiveEmpty := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_filter_iff]
  constructor
  · rintro ⟨hx, hfalse⟩
    exact False.elim (hfRecursiveFalsePredicate_not_holds x hfalse)
  · intro hx
    exact False.elim (hfRecursiveMember_empty x hx)

theorem hfRecursiveFilter_compose (p q : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveFilter p (hfRecursiveFilter q s) =
      hfRecursiveFilter (p.and q) s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_filter_iff, hfRecursiveMember_filter_iff,
    hfRecursiveMember_filter_iff, hfRecursivePredicate_holds_and]
  constructor
  · rintro ⟨⟨hxs, hq⟩, hp⟩
    exact ⟨hxs, hp, hq⟩
  · rintro ⟨hxs, hp, hq⟩
    exact ⟨⟨hxs, hq⟩, hp⟩

theorem hfRecursiveFilter_not_not (p : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveFilter p.not.not s = hfRecursiveFilter p s := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_filter_iff, hfRecursiveMember_filter_iff,
    hfRecursivePredicate_holds_not_not]

/- A filter and its Boolean complement are a disjoint, exhaustive split of
   their ambient finite set. -/
theorem hfRecursiveFilter_union_filter_not (p : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveUnion (hfRecursiveFilter p s) (hfRecursiveFilter p.not s) = s := by
  simpa only [hfRecursiveDifference_eq_filter_not] using
    hfRecursiveFilter_union_difference p s

theorem hfRecursiveFilter_filter_not_disjoint (p : HFRecursivePredicate)
    (s x : HFRecursiveSet) :
    ¬ (HFRecursiveMember x (hfRecursiveFilter p s) ∧
      HFRecursiveMember x (hfRecursiveFilter p.not s)) := by
  simpa only [hfRecursiveDifference_eq_filter_not] using
    hfRecursiveFilter_difference_disjoint p s x

theorem hfRecursiveFilter_deMorgan_or (p q : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveFilter (p.or q).not s =
      hfRecursiveFilter p.not (hfRecursiveFilter q.not s) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_filter_iff, hfRecursiveMember_filter_iff,
    hfRecursiveMember_filter_iff, hfRecursivePredicate_holds_not_or,
    hfRecursivePredicate_holds_not, hfRecursivePredicate_holds_not]
  constructor
  · rintro ⟨hxs, hp, hq⟩
    exact ⟨⟨hxs, hq⟩, hp⟩
  · rintro ⟨⟨hxs, hq⟩, hp⟩
    exact ⟨hxs, hp, hq⟩

theorem hfRecursiveFilter_difference_intersection (p q : HFRecursivePredicate)
    (s : HFRecursiveSet) :
    hfRecursiveDifference p (hfRecursiveFilter q s) =
      hfRecursiveFilter q (hfRecursiveDifference p s) := by
  apply hfRecursiveSet_extensionality
  intro x
  rw [hfRecursiveMember_difference_iff, hfRecursiveMember_filter_iff,
    hfRecursiveMember_filter_iff, hfRecursiveMember_difference_iff]
  constructor
  · rintro ⟨⟨hxs, hq⟩, hnp⟩
    exact ⟨⟨hxs, hnp⟩, hq⟩
  · rintro ⟨⟨hxs, hnp⟩, hq⟩
    exact ⟨⟨hxs, hq⟩, hnp⟩

structure HFRecursiveNatEmbedding where
  encode : Nat → HFRecursiveSet
  injective : ∀ {m n}, encode m = encode n → m = n
  zero_ne_succ : ∀ n, encode 0 ≠ encode (n + 1)
  succ_injective : ∀ {m n}, encode (m + 1) = encode (n + 1) → m = n
  member_iff_lt : ∀ m n, HFRecursiveMember (encode m) (encode n) ↔ m < n
  subset_iff_le : ∀ m n, HFRecursiveSubset (encode m) (encode n) ↔ m ≤ n
  successor_as_union : ∀ n,
    encode (n + 1) =
      hfRecursiveUnion (encode n) (hfRecursivePair (encode n) (encode n))
  trichotomy : ∀ m n,
    HFRecursiveMember (encode m) (encode n) ∨ m = n ∨
      HFRecursiveMember (encode n) (encode m)
  induction : ∀ predicate : HFRecursiveSet → Prop,
    predicate (encode 0) →
    (∀ n, predicate (encode n) → predicate (encode (n + 1))) →
    ∀ n, predicate (encode n)
  recursion_unique : ∀ (A : Type) (f g : HFRecursiveSet → A) (step : A → A),
    f (encode 0) = g (encode 0) →
    (∀ n, f (encode (n + 1)) = step (f (encode n))) →
    (∀ n, g (encode (n + 1)) = step (g (encode n))) →
    ∀ n, f (encode n) = g (encode n)

def hfRecursiveNatEmbedding : HFRecursiveNatEmbedding where
  encode := hfRecursiveNat
  injective := hfRecursiveNat_injective
  zero_ne_succ := hfRecursiveNat_zero_ne_succ
  succ_injective := hfRecursiveNat_succ_injective
  member_iff_lt := hfRecursiveNat_member_iff
  subset_iff_le := hfRecursiveNat_subset_iff
  successor_as_union := hfRecursiveNat_succ_eq
  trichotomy := hfRecursiveNat_trichotomy
  induction := hfRecursiveNat_induction
  recursion_unique := by
    intro A f g step zero fSucc gSucc
    exact hfRecursiveNat_recursion_unique f g step zero fSucc gSucc

/- A bundled witness for the finite set-theoretic fragment actually proved in
   this file.  It deliberately records only the operations and laws checked
   here; it is not a claim of a full ZF model. -/
structure HFRecursiveSetFragmentModel where
  empty : HFRecursiveSet
  pair : HFRecursiveSet → HFRecursiveSet → HFRecursiveSet
  union : HFRecursiveSet → HFRecursiveSet → HFRecursiveSet
  product : HFRecursiveSet → HFRecursiveSet → HFRecursiveSet
  power : HFRecursiveSet → HFRecursiveSet
  filter : HFRecursivePredicate → HFRecursiveSet → HFRecursiveSet
  bigUnion : HFRecursiveSet → HFRecursiveSet
  subset_refl : ∀ s, HFRecursiveSubset s s
  subset_trans : ∀ {r s t},
    HFRecursiveSubset r s → HFRecursiveSubset s t → HFRecursiveSubset r t
  subset_antisymm : ∀ {s t},
    HFRecursiveSubset s t → HFRecursiveSubset t s → s = t
  empty_no_member : ∀ x, ¬ HFRecursiveMember x empty
  pair_left : ∀ s t, HFRecursiveMember s (pair s t)
  pair_right : ∀ s t, HFRecursiveMember t (pair s t)
  pair_spec : ∀ x s t, HFRecursiveMember x (pair s t) ↔ x = s ∨ x = t
  union_spec : ∀ x s t, HFRecursiveMember x (union s t) ↔
    HFRecursiveMember x s ∨ HFRecursiveMember x t
  subset_union_left : ∀ s t, HFRecursiveSubset s (union s t)
  subset_union_right : ∀ s t, HFRecursiveSubset t (union s t)
  union_subset_iff : ∀ {s t u},
    HFRecursiveSubset (union s t) u ↔
      HFRecursiveSubset s u ∧ HFRecursiveSubset t u
  union_eq_right_iff_subset : ∀ s t,
    union s t = t ↔ HFRecursiveSubset s t
  union_eq_left_iff_subset : ∀ s t,
    union s t = s ↔ HFRecursiveSubset t s
  product_spec : ∀ x s t, HFRecursiveMember x (product s t) ↔
    ∃ leftMember, HFRecursiveMember leftMember s ∧
      ∃ rightMember, HFRecursiveMember rightMember t ∧
        x = hfRecursiveOrderedPair leftMember rightMember
  product_empty_left : ∀ s, product empty s = empty
  product_empty_right : ∀ s, product s empty = empty
  product_mono : ∀ {left left' right right'},
    HFRecursiveSubset left left' → HFRecursiveSubset right right' →
      HFRecursiveSubset (product left right) (product left' right')
  product_subset_iff : ∀ {left left' right right'},
    (∃ a, HFRecursiveMember a left) →
    (∃ b, HFRecursiveMember b right) →
    (HFRecursiveSubset (product left right) (product left' right') ↔
      HFRecursiveSubset left left' ∧ HFRecursiveSubset right right')
  product_eq_iff_factors_eq : ∀ {left left' right right'},
    (∃ a, HFRecursiveMember a left) →
    (∃ a, HFRecursiveMember a left') →
    (∃ b, HFRecursiveMember b right) →
    (∃ b, HFRecursiveMember b right') →
    (product left right = product left' right' ↔
      left = left' ∧ right = right')
  product_union_left : ∀ left right third,
    product (union left right) third =
      union (product left third) (product right third)
  product_union_right : ∀ left right third,
    product left (union right third) =
      union (product left right) (product left third)
  power_spec : ∀ x s, HFRecursiveMember x (power s) ↔ HFRecursiveSubset x s
  power_order_iff : ∀ {s t},
    HFRecursiveSubset (power s) (power t) ↔ HFRecursiveSubset s t
  power_injective : ∀ ⦃s t⦄, power s = power t → s = t
  product_power_singletons : ∀ a b left right,
    HFRecursiveMember
      (hfRecursiveOrderedPair (hfRecursiveSingleton a) (hfRecursiveSingleton b))
      (product (power left) (power right)) ↔
        HFRecursiveMember a left ∧ HFRecursiveMember b right
  union_powers_least : ∀ {s t u},
    HFRecursiveSubset (union (power s) (power t)) (power u) ↔
      HFRecursiveSubset s u ∧ HFRecursiveSubset t u
  union_powers_subset_power_union : ∀ s t,
    HFRecursiveSubset (union (power s) (power t)) (power (union s t))
  bigUnion_power : ∀ s, bigUnion (power s) = s
  filter_spec : ∀ p x s,
    HFRecursiveMember x (filter p s) ↔ HFRecursiveMember x s ∧ p.holds x
  bigUnion_intro : ∀ x y s,
    HFRecursiveMember x y → HFRecursiveMember y s →
      HFRecursiveMember x (bigUnion s)
  bigUnion_spec : ∀ x s, HFRecursiveMember x (bigUnion s) ↔
    ∃ y, HFRecursiveMember y s ∧ HFRecursiveMember x y
  extensional : ∀ {s t},
    (∀ x, HFRecursiveMember x s ↔ HFRecursiveMember x t) → s = t
  foundation : ∀ {s}, (∃ x, HFRecursiveMember x s) →
    ∃ y, HFRecursiveMember y s ∧
      ∀ z, ¬ (HFRecursiveMember z s ∧ HFRecursiveMember z y)

def hfRecursiveSetFragmentModel : HFRecursiveSetFragmentModel where
  empty := hfRecursiveEmpty
  pair := hfRecursivePair
  union := hfRecursiveUnion
  product := hfRecursiveProduct
  power := hfRecursivePower
  filter := hfRecursiveFilter
  bigUnion := hfRecursiveBigUnion
  subset_refl := hfRecursiveSubset_refl
  subset_trans := hfRecursiveSubset_trans
  subset_antisymm := hfRecursiveSubset_antisymm
  empty_no_member := hfRecursiveMember_empty
  pair_left := hfRecursiveMember_pair_left
  pair_right := hfRecursiveMember_pair_right
  pair_spec := hfRecursiveMember_pair_iff
  union_spec := hfRecursiveMember_union_iff
  subset_union_left := hfRecursiveSubset_union_left
  subset_union_right := hfRecursiveSubset_union_right
  union_subset_iff := hfRecursiveUnion_subset_iff
  union_eq_right_iff_subset := hfRecursiveUnion_eq_right_iff_subset
  union_eq_left_iff_subset := hfRecursiveUnion_eq_left_iff_subset
  product_spec := hfRecursiveMember_product_iff
  product_empty_left := hfRecursiveProduct_empty_left
  product_empty_right := hfRecursiveProduct_empty_right
  product_mono := hfRecursiveProduct_mono
  product_subset_iff := hfRecursiveProduct_subset_iff
  product_eq_iff_factors_eq := hfRecursiveProduct_eq_iff_factors_eq
  product_union_left := hfRecursiveProduct_union_left
  product_union_right := hfRecursiveProduct_union_right
  power_spec := hfRecursiveMember_power_iff_subset
  power_order_iff := hfRecursivePower_subset_iff
  power_injective := hfRecursivePower_injective
  product_power_singletons := hfRecursiveMember_product_power_singletons_iff
  union_powers_least := hfRecursiveUnion_power_subset_power_iff
  union_powers_subset_power_union := hfRecursiveUnion_power_subset_power_union
  bigUnion_power := hfRecursiveBigUnion_power
  filter_spec := hfRecursiveMember_filter_iff
  bigUnion_intro := by
    intro x y s hxy hys
    exact hfRecursiveMember_bigUnion_intro hys hxy
  bigUnion_spec := hfRecursiveMember_bigUnion_iff
  extensional := by
    intro s t h
    exact hfRecursiveSet_extensionality h
  foundation := hfRecursive_foundation

end IncidenceCore
