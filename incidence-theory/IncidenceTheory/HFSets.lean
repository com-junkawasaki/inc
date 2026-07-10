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

def HFRecursiveSubset (s t : HFRecursiveSet) : Prop :=
  ∀ x, HFRecursiveMember x s → HFRecursiveMember x t

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

/- A bundled witness for the finite set-theoretic fragment actually proved in
   this file.  It deliberately records only the operations and laws checked
   here; it is not a claim of a full ZF model. -/
structure HFRecursiveSetFragmentModel where
  empty : HFRecursiveSet
  pair : HFRecursiveSet → HFRecursiveSet → HFRecursiveSet
  union : HFRecursiveSet → HFRecursiveSet → HFRecursiveSet
  filter : HFRecursivePredicate → HFRecursiveSet → HFRecursiveSet
  bigUnion : HFRecursiveSet → HFRecursiveSet
  empty_no_member : ∀ x, ¬ HFRecursiveMember x empty
  pair_left : ∀ s t, HFRecursiveMember s (pair s t)
  pair_right : ∀ s t, HFRecursiveMember t (pair s t)
  pair_spec : ∀ x s t, HFRecursiveMember x (pair s t) ↔ x = s ∨ x = t
  union_spec : ∀ x s t, HFRecursiveMember x (union s t) ↔
    HFRecursiveMember x s ∨ HFRecursiveMember x t
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
  filter := hfRecursiveFilter
  bigUnion := hfRecursiveBigUnion
  empty_no_member := hfRecursiveMember_empty
  pair_left := hfRecursiveMember_pair_left
  pair_right := hfRecursiveMember_pair_right
  pair_spec := hfRecursiveMember_pair_iff
  union_spec := hfRecursiveMember_union_iff
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
