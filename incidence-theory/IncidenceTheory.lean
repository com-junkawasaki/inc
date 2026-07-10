import IncidenceTheory.Axioms

/-!
  A small, checked core for incidence structures.

  This module deliberately proves only consequences of the data carried by
  `Incidence`; categorical universality and linear completeness require extra
  hypotheses and are not asserted here.
-/

namespace IncidenceCore

universe u v w

/- Observational equality is equality of the observable type and boundary. -/
def approxEq {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i j : I) : Prop :=
  inc.typeFunc i = inc.typeFunc j ∧ inc.boundary i = inc.boundary j

theorem approxEq_refl {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) : approxEq inc i i := by
  exact ⟨rfl, rfl⟩

theorem approxEq_symm {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {i j : I} : approxEq inc i j → approxEq inc j i := by
  rintro ⟨ht, hb⟩
  exact ⟨ht.symm, hb.symm⟩

theorem approxEq_trans {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {i j k : I} :
    approxEq inc i j → approxEq inc j k → approxEq inc i k := by
  rintro ⟨ht₁, hb₁⟩ ⟨ht₂, hb₂⟩
  exact ⟨ht₁.trans ht₂, hb₁.trans hb₂⟩

/- Endpoint compatibility ignores the endpoint identity but retains its label. -/
def boundaryCompatible {I R T : Type u} [DecidableEq I] (_inc : Incidence I R T)
    (e₁ e₂ : Endpoint I R) : Prop :=
  e₁.role = e₂.role ∧ e₁.sign = e₂.sign ∧ e₁.mult = e₂.mult

theorem boundaryCompatible_symm {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {e₁ e₂ : Endpoint I R} :
    boundaryCompatible inc e₁ e₂ → boundaryCompatible inc e₂ e₁ := by
  rintro ⟨hr, hs, hm⟩
  exact ⟨hr.symm, hs.symm, hm.symm⟩

theorem boundaryCompatible_trans {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {e₁ e₂ e₃ : Endpoint I R} :
    boundaryCompatible inc e₁ e₂ → boundaryCompatible inc e₂ e₃ →
      boundaryCompatible inc e₁ e₃ := by
  rintro ⟨hr₁, hs₁, hm₁⟩ ⟨hr₂, hs₂, hm₂⟩
  exact ⟨hr₁.trans hr₂, hs₁.trans hs₂, hm₁.trans hm₂⟩

def boundaryMatched {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (rel : I → I → Prop) (i j : I) : Prop :=
  (∀ e ∈ inc.boundary i, ∃ e' ∈ inc.boundary j,
      boundaryCompatible inc e e' ∧ rel e.i e'.i) ∧
  (∀ e' ∈ inc.boundary j, ∃ e ∈ inc.boundary i,
      boundaryCompatible inc e e' ∧ rel e.i e'.i)

def IsBisimulation {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (rel : I → I → Prop) : Prop :=
  ∀ i j, rel i j → inc.typeFunc i = inc.typeFunc j ∧ boundaryMatched inc rel i j

def approxBisim {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (i j : I) : Prop :=
  ∃ rel, IsBisimulation inc rel ∧ rel i j

/- Exact agreement of observables is a (strict) bisimulation. -/
theorem isBisimulation_approxEq {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : IsBisimulation inc (approxEq inc) := by
  intro i j hij
  refine ⟨hij.left, ?_⟩
  constructor
  · intro e he
    refine ⟨e, ?_, ⟨rfl, rfl, rfl⟩, approxEq_refl inc e.i⟩
    simpa [hij.right] using he
  · intro e he
    refine ⟨e, ?_, ⟨rfl, rfl, rfl⟩, approxEq_refl inc e.i⟩
    simpa [hij.right] using he

theorem approxEq_implies_approxBisim {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {i j : I} :
    approxEq inc i j → approxBisim inc i j := by
  intro hij
  exact ⟨approxEq inc, isBisimulation_approxEq inc, hij⟩

theorem isBisimulation_rfl {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : IsBisimulation inc (fun a b => a = b) := by
  intro i j hij
  subst j
  refine ⟨rfl, ?_⟩
  constructor
  · intro e he
    exact ⟨e, he, ⟨rfl, rfl, rfl⟩, rfl⟩
  · intro e he
    exact ⟨e, he, ⟨rfl, rfl, rfl⟩, rfl⟩

theorem approxBisim_refl {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) : approxBisim inc i i :=
  ⟨(fun a b => a = b), isBisimulation_rfl inc, rfl⟩

theorem isBisimulation_symm {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {rel : I → I → Prop}
    (h : IsBisimulation inc rel) : IsBisimulation inc (fun a b => rel b a) := by
  intro i j hij
  rcases h j i hij with ⟨ht, hm⟩
  refine ⟨ht.symm, ?_⟩
  constructor
  · intro e he
    rcases hm.right e he with ⟨e', he', hc, hr⟩
    exact ⟨e', he', boundaryCompatible_symm hc, hr⟩
  · intro e he
    rcases hm.left e he with ⟨e', he', hc, hr⟩
    exact ⟨e', he', boundaryCompatible_symm hc, hr⟩

theorem approxBisim_symm {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {i j : I} :
    approxBisim inc i j → approxBisim inc j i := by
  rintro ⟨rel, hr, hij⟩
  exact ⟨(fun a b => rel b a), isBisimulation_symm hr, hij⟩

theorem isBisimulation_comp {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {rel₁ rel₂ : I → I → Prop}
    (h₁ : IsBisimulation inc rel₁) (h₂ : IsBisimulation inc rel₂) :
    IsBisimulation inc (fun a c => ∃ b, rel₁ a b ∧ rel₂ b c) := by
  intro i k hik
  rcases hik with ⟨j, hij, hjk⟩
  rcases h₁ i j hij with ⟨ht₁, hm₁⟩
  rcases h₂ j k hjk with ⟨ht₂, hm₂⟩
  refine ⟨ht₁.trans ht₂, ?_⟩
  constructor
  · intro e he
    rcases hm₁.left e he with ⟨e₂, he₂, hc₁, hr₁⟩
    rcases hm₂.left e₂ he₂ with ⟨e₃, he₃, hc₂, hr₂⟩
    exact ⟨e₃, he₃, boundaryCompatible_trans hc₁ hc₂, ⟨e₂.i, hr₁, hr₂⟩⟩
  · intro e he
    rcases hm₂.right e he with ⟨e₂, he₂, hc₂, hr₂⟩
    rcases hm₁.right e₂ he₂ with ⟨e₁, he₁, hc₁, hr₁⟩
    exact ⟨e₁, he₁,
      boundaryCompatible_trans hc₁ hc₂,
      ⟨e₂.i, hr₁, hr₂⟩⟩

theorem approxBisim_trans {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {i j k : I} :
    approxBisim inc i j → approxBisim inc j k → approxBisim inc i k := by
  rintro ⟨rel₁, h₁, hij⟩ ⟨rel₂, h₂, hjk⟩
  exact ⟨(fun a c => ∃ b, rel₁ a b ∧ rel₂ b c),
    isBisimulation_comp h₁ h₂, ⟨j, hij, hjk⟩⟩

/- Bisimilarity can therefore be used as an equivalence relation. -/
theorem approxBisim_equivalence {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : Equivalence (approxBisim inc) where
  refl := approxBisim_refl inc
  symm := by
    intro i j
    exact approxBisim_symm
  trans := by
    intro i j k
    exact approxBisim_trans

def approxBisimSetoid {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : Setoid I where
  r := approxBisim inc
  iseqv := approxBisim_equivalence inc

abbrev IncidenceQuotient {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) := Quotient (approxBisimSetoid inc)

theorem incidence_quotient_sound {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {i j : I} (h : approxBisim inc i j) :
    (Quotient.mk (approxBisimSetoid inc) i : IncidenceQuotient inc) =
      Quotient.mk (approxBisimSetoid inc) j :=
  Quotient.sound h

/- Derived linear data.  It is computation, not an additional assumption. -/
def boundaryMatrix {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (_idx : List I) : Matrix I I Int :=
  fun i j =>
    (inc.boundary i).foldl (fun acc e =>
      if e.i = j then
        acc + match e.sign with
          | Sign.neg => -(Int.ofNat e.mult)
          | Sign.zero => 0
          | Sign.pos => Int.ofNat e.mult
      else acc) 0

def laplacian {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) : Matrix I I Int :=
  let b := boundaryMatrix inc idx
  fun i j => idx.foldl (fun acc k => acc + b k i * b k j) 0

/- Finite integer sums, kept list-based to match the observation lists used
   by `boundaryMatrix` and `laplacian`. -/
def intListSum {α : Type u} (xs : List α) (f : α → Int) : Int :=
  xs.foldl (fun total x => total + f x) 0

theorem intListSum_acc {α : Type u} (xs : List α) (f : α → Int) (acc : Int) :
    xs.foldl (fun total x => total + f x) acc = acc + intListSum xs f := by
  induction xs generalizing acc with
  | nil => simp [intListSum]
  | cons x xs ih =>
    change xs.foldl (fun total y => total + f y) (acc + f x) =
      acc + xs.foldl (fun total y => total + f y) (0 + f x)
    simp only [Int.zero_add]
    rw [ih (acc + f x), ih (f x)]
    exact Int.add_assoc _ _ _

theorem intListSum_cons {α : Type u} (x : α) (xs : List α) (f : α → Int) :
    intListSum (x :: xs) f = f x + intListSum xs f := by
  unfold intListSum
  simpa using intListSum_acc xs f (f x)

theorem intListSum_add {α : Type u} (xs : List α) (f g : α → Int) :
    intListSum xs (fun x => f x + g x) = intListSum xs f + intListSum xs g := by
  induction xs with
  | nil => simp [intListSum]
  | cons x xs ih =>
    rw [intListSum_cons, intListSum_cons, intListSum_cons, ih]
    simp only [Int.add_assoc, Int.add_left_comm]

theorem intListSum_mul_left {α : Type u} (a : Int) (xs : List α) (f : α → Int) :
    intListSum xs (fun x => a * f x) = a * intListSum xs f := by
  induction xs with
  | nil => simp [intListSum]
  | cons x xs ih =>
    rw [intListSum_cons, intListSum_cons, ih, Int.mul_add]

theorem intListSum_zero {α : Type u} (xs : List α) :
    intListSum xs (fun _ : α => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [intListSum_cons, ih]

theorem intListSum_eq_zero_of_mem {α : Type u} (xs : List α) (f : α → Int)
    (hzero : ∀ x ∈ xs, f x = 0) : intListSum xs f = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [intListSum_cons, hzero x (by simp)]
    simp only [Int.zero_add]
    apply ih
    intro y hy
    exact hzero y (by simp [hy])

theorem intListSum_gram_row_swap {I : Type u} (rows cols : List I)
    (b : I → I → Int) (i : I) :
    intListSum cols (fun j => intListSum rows (fun k => b k i * b k j)) =
      intListSum rows (fun k => b k i * intListSum cols (fun j => b k j)) := by
  induction rows with
  | nil =>
    have hzero : intListSum cols (fun _ : I => 0) = 0 := intListSum_zero cols
    simpa [intListSum] using hzero
  | cons k rows ih =>
    have hinner : ∀ j,
        intListSum (k :: rows) (fun r => b r i * b r j) =
          b k i * b k j + intListSum rows (fun r => b r i * b r j) := by
      intro j
      exact intListSum_cons k rows _
    calc
      intListSum cols (fun j => intListSum (k :: rows) (fun r => b r i * b r j)) =
          intListSum cols (fun j =>
            b k i * b k j + intListSum rows (fun r => b r i * b r j)) := by
              apply congrArg (intListSum cols)
              funext j
              exact hinner j
      _ = intListSum cols (fun j => b k i * b k j) +
          intListSum cols (fun j => intListSum rows (fun r => b r i * b r j)) :=
            intListSum_add cols _ _
      _ = b k i * intListSum cols (fun j => b k j) +
          intListSum rows (fun r => b r i * intListSum cols (fun j => b r j)) := by
            rw [intListSum_mul_left, ih]
      _ = intListSum (k :: rows) (fun r =>
          b r i * intListSum cols (fun j => b r j)) :=
            (intListSum_cons k rows
              (fun r => b r i * intListSum cols (fun j => b r j))).symm

/- A boundary row is balanced when the coefficients visible in the chosen
   finite observation list add to zero.  This is an explicit hypothesis: it
   is not implied by the generic incidence axioms. -/
def boundaryRowSum {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (row : I) : Int :=
  intListSum idx (fun column => boundaryMatrix inc idx row column)

def BoundaryRowBalanced {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) : Prop :=
  ∀ row, row ∈ idx → boundaryRowSum inc idx row = 0

def laplacianRowSum {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (row : I) : Int :=
  intListSum idx (fun column => laplacian inc idx row column)

def laplacianColumnSum {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (column : I) : Int :=
  intListSum idx (fun row => laplacian inc idx row column)

theorem laplacian_rowSum_zero_of_boundaryRowBalanced {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (hbalanced : BoundaryRowBalanced inc idx)
    (i : I) : laplacianRowSum inc idx i = 0 := by
  unfold laplacianRowSum laplacian
  let b := boundaryMatrix inc idx
  change intListSum idx (fun j => intListSum idx (fun k => b k i * b k j)) = 0
  rw [intListSum_gram_row_swap]
  apply intListSum_eq_zero_of_mem
  intro k hk
  have hrow : intListSum idx (fun j => b k j) = 0 := by
    exact hbalanced k hk
  rw [hrow]
  simp

/- `BᵀB` is symmetric independently of any extra incidence axioms. -/
theorem laplacian_symmetric {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (i j : I) :
    laplacian inc idx i j = laplacian inc idx j i := by
  let b := boundaryMatrix inc idx
  have fold_symmetric : ∀ (xs : List I) (acc : Int),
      xs.foldl (fun total k => total + b k i * b k j) acc =
        xs.foldl (fun total k => total + b k j * b k i) acc := by
    intro xs acc
    induction xs generalizing acc with
    | nil => rfl
    | cons k xs ih =>
      simp only [List.foldl]
      rw [Int.mul_comm (b k i) (b k j)]
      exact ih _
  exact fold_symmetric idx 0

theorem laplacian_columnSum_zero_of_boundaryRowBalanced {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (hbalanced : BoundaryRowBalanced inc idx)
    (j : I) : laplacianColumnSum inc idx j = 0 := by
  unfold laplacianColumnSum
  have hrewrite : (fun row => laplacian inc idx row j) =
      (fun row => laplacian inc idx j row) := by
    funext row
    exact laplacian_symmetric inc idx row j
  rw [hrewrite]
  exact laplacian_rowSum_zero_of_boundaryRowBalanced inc idx hbalanced j

/- Each diagonal entry of `BᵀB` is a finite sum of integer squares. -/
theorem laplacian_diagonal_nonnegative {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (i : I) :
    0 ≤ laplacian inc idx i i := by
  let b := boundaryMatrix inc idx
  have square_nonnegative : ∀ value : Int, 0 ≤ value * value := by
    intro value
    rcases Int.le_total 0 value with hnonneg | hnonpos
    · exact Int.mul_nonneg hnonneg hnonneg
    · rw [← Int.neg_mul_neg value value]
      exact Int.mul_nonneg
        (Int.neg_nonneg_of_nonpos hnonpos)
        (Int.neg_nonneg_of_nonpos hnonpos)
  have fold_nonnegative : ∀ (xs : List I) (acc : Int), 0 ≤ acc →
      0 ≤ xs.foldl (fun total k => total + b k i * b k i) acc := by
    intro xs acc hacc
    induction xs generalizing acc with
    | nil => simpa using hacc
    | cons k xs ih =>
      simp only [List.foldl]
      apply ih
      exact Int.add_nonneg hacc (square_nonnegative (b k i))
  exact fold_nonnegative idx 0 (Int.le_refl 0)

/- The `BᵀB` sum is additive in the finite list of rows.  This makes the
   derived Laplacian usable incrementally: extending a finite observation
   list adds exactly the contribution of the new rows. -/
theorem laplacian_append {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx extra : List I) (i j : I) :
    laplacian inc (idx ++ extra) i j =
      laplacian inc idx i j + laplacian inc extra i j := by
  simp only [laplacian]
  let b := boundaryMatrix inc idx
  change
    (idx ++ extra).foldl (fun total k => total + b k i * b k j) 0 =
      idx.foldl (fun total k => total + b k i * b k j) 0 +
        extra.foldl (fun total k => total + b k i * b k j) 0
  have fold_add : ∀ (xs : List I) (acc : Int),
      xs.foldl (fun total k => total + b k i * b k j) acc =
        acc + xs.foldl (fun total k => total + b k i * b k j) 0 := by
    intro xs acc
    induction xs generalizing acc with
    | nil => simp
    | cons k xs ih =>
      simp only [List.foldl]
      calc
        xs.foldl (fun total k => total + b k i * b k j)
            (acc + b k i * b k j) =
            (acc + b k i * b k j) +
              xs.foldl (fun total k => total + b k i * b k j) 0 := ih _
        _ = acc + (b k i * b k j +
              xs.foldl (fun total k => total + b k i * b k j) 0) :=
              Int.add_assoc _ _ _
        _ = acc + xs.foldl (fun total k => total + b k i * b k j)
              (0 + b k i * b k j) := by
              rw [Int.zero_add]
              exact congrArg (fun z => acc + z) (ih _).symm
  rw [List.foldl_append, fold_add]

/- A single observed row contributes its outer product to `BᵀB`. -/
theorem laplacian_cons {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (k : I) (idx : List I) (i j : I) :
    laplacian inc (k :: idx) i j =
      boundaryMatrix inc idx k i * boundaryMatrix inc idx k j +
        laplacian inc idx i j := by
  simpa [laplacian] using laplacian_append inc [k] idx i j

theorem laplacian_empty {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i j : I) : laplacian inc [] i j = 0 := by
  rfl

/- Adding observed rows can only increase a diagonal entry.  This is the
   finite positive-semidefinite monotonicity of the derived `BᵀB` data; no
   incidence postulate beyond the definition of the boundary matrix is used. -/
theorem laplacian_diagonal_monotone_append {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx extra : List I) (i : I) :
    laplacian inc idx i i ≤ laplacian inc (idx ++ extra) i i := by
  rw [laplacian_append]
  exact Int.le_add_of_nonneg_right
    (laplacian_diagonal_nonnegative inc extra i)

/- In particular, a single additional row adds a nonnegative square to the
   diagonal. -/
theorem laplacian_diagonal_monotone_cons {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (k : I) (idx : List I) (i : I) :
    laplacian inc idx i i ≤ laplacian inc (k :: idx) i i := by
  rw [laplacian_cons]
  have hrow : 0 ≤ boundaryMatrix inc idx k i * boundaryMatrix inc idx k i := by
    simpa [laplacian] using laplacian_diagonal_nonnegative inc [k] i
  exact Int.le_add_of_nonneg_left hrow

/- If all observed boundary rows vanish, the complete derived Laplacian is
   zero, not merely square-zero. -/
theorem laplacian_of_empty_boundaries {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (hempty : ∀ i, inc.boundary i = [])
    (i j : I) : laplacian inc idx i j = 0 := by
  have hfold : ∀ xs : List I, xs.foldl (fun (acc : Int) _ => acc) 0 = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ xs ih => exact ih
  simpa [laplacian, boundaryMatrix, hempty] using hfold idx

/- The observation list is a row selector for `laplacian`; it does not alter
   the boundary row itself.  Keeping this fact explicit is useful when a
   finite observation is extended or reindexed. -/
theorem boundaryMatrix_index_irrel {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx idx' : List I) (i j : I) :
    boundaryMatrix inc idx i j = boundaryMatrix inc idx' i j := rfl

/- Equal boundary data give equal derived linear data.  This is the precise
   preservation statement available without asking a translation to preserve
   any extra, non-derived matrix structure. -/
theorem boundaryMatrix_congr {I R T : Type u} [DecidableEq I]
    (inc inc' : Incidence I R T) (idx idx' : List I)
    (hboundary : ∀ i, inc.boundary i = inc'.boundary i) (i j : I) :
    boundaryMatrix inc idx i j = boundaryMatrix inc' idx' i j := by
  simp [boundaryMatrix, hboundary i]

theorem laplacian_congr {I R T : Type u} [DecidableEq I]
    (inc inc' : Incidence I R T) (idx : List I)
    (hboundary : ∀ i, inc.boundary i = inc'.boundary i) (i j : I) :
    laplacian inc idx i j = laplacian inc' idx i j := by
  have hmatrix : ∀ k a, boundaryMatrix inc idx k a = boundaryMatrix inc' idx k a :=
    fun k a => boundaryMatrix_congr inc inc' idx idx hboundary k a
  simp only [laplacian]
  have hfold : ∀ (xs : List I) (acc : Int),
      xs.foldl (fun total k => total + boundaryMatrix inc idx k i * boundaryMatrix inc idx k j) acc =
        xs.foldl (fun total k => total + boundaryMatrix inc' idx k i * boundaryMatrix inc' idx k j) acc := by
    intro xs acc
    induction xs generalizing acc with
    | nil => rfl
    | cons k xs ih =>
      simp only [List.foldl]
      rw [hmatrix k i, hmatrix k j]
      exact ih _
  exact hfold idx 0

/- Pointwise preservation of boundary data transports the explicit
   row-balance hypothesis itself.  Consequently the zero row/column sums of
   `BᵀB` are stable under every boundary-faithful translation. -/
theorem boundaryRowBalanced_congr {I R T : Type u} [DecidableEq I]
    (inc inc' : Incidence I R T) (idx : List I)
    (hboundary : ∀ i, inc.boundary i = inc'.boundary i)
    (hbalanced : BoundaryRowBalanced inc idx) :
    BoundaryRowBalanced inc' idx := by
  intro row hrow
  calc
    boundaryRowSum inc' idx row = boundaryRowSum inc idx row := by
      unfold boundaryRowSum
      apply congrArg (intListSum idx)
      funext column
      exact (boundaryMatrix_congr inc inc' idx idx hboundary row column).symm
    _ = 0 := hbalanced row hrow

theorem laplacianRowSum_congr {I R T : Type u} [DecidableEq I]
    (inc inc' : Incidence I R T) (idx : List I)
    (hboundary : ∀ i, inc.boundary i = inc'.boundary i) (row : I) :
    laplacianRowSum inc idx row = laplacianRowSum inc' idx row := by
  unfold laplacianRowSum
  apply congrArg (intListSum idx)
  funext column
  exact laplacian_congr inc inc' idx hboundary row column

theorem laplacianColumnSum_congr {I R T : Type u} [DecidableEq I]
    (inc inc' : Incidence I R T) (idx : List I)
    (hboundary : ∀ i, inc.boundary i = inc'.boundary i) (column : I) :
    laplacianColumnSum inc idx column = laplacianColumnSum inc' idx column := by
  unfold laplacianColumnSum
  apply congrArg (intListSum idx)
  funext row
  exact laplacian_congr inc inc' idx hboundary row column

theorem laplacianRowSum_zero_preserved_of_boundary_congr {I R T : Type u} [DecidableEq I]
    (inc inc' : Incidence I R T) (idx : List I)
    (hboundary : ∀ i, inc.boundary i = inc'.boundary i)
    (hbalanced : BoundaryRowBalanced inc idx) (row : I) :
    laplacianRowSum inc' idx row = 0 :=
  laplacian_rowSum_zero_of_boundaryRowBalanced inc' idx
    (boundaryRowBalanced_congr inc inc' idx hboundary hbalanced) row

theorem laplacianColumnSum_zero_preserved_of_boundary_congr {I R T : Type u} [DecidableEq I]
    (inc inc' : Incidence I R T) (idx : List I)
    (hboundary : ∀ i, inc.boundary i = inc'.boundary i)
    (hbalanced : BoundaryRowBalanced inc idx) (column : I) :
    laplacianColumnSum inc' idx column = 0 :=
  laplacian_columnSum_zero_of_boundaryRowBalanced inc' idx
    (boundaryRowBalanced_congr inc inc' idx hboundary hbalanced) column

/- A positive contribution from new rows gives strict, rather than merely
   weak, diagonal monotonicity. -/
theorem laplacian_diagonal_strict_monotone_append {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx extra : List I) (i : I)
    (hpositive : 0 < laplacian inc extra i i) :
    laplacian inc idx i i < laplacian inc (idx ++ extra) i i := by
  rw [laplacian_append]
  exact Int.lt_add_of_pos_right _ hpositive

/- Equivalently, the increment is exactly the Laplacian of the appended
   observation rows. -/
theorem laplacian_diagonal_increment_append {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx extra : List I) (i : I) :
    laplacian inc (idx ++ extra) i i - laplacian inc idx i i =
      laplacian inc extra i i := by
  rw [laplacian_append]
  calc
    laplacian inc idx i i + laplacian inc extra i i - laplacian inc idx i i =
        laplacian inc extra i i + laplacian inc idx i i - laplacian inc idx i i := by
          rw [Int.add_comm]
    _ = laplacian inc extra i i := Int.add_sub_cancel _ _

def boundarySquareZero {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) : Prop :=
  ∀ i k, i ∈ idx → k ∈ idx →
    idx.foldl (fun acc j => acc + boundaryMatrix inc idx i j * boundaryMatrix inc idx j k) 0 = 0

theorem boundaryMatrix_of_empty_boundary {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) {i j : I}
    (hempty : inc.boundary i = []) : boundaryMatrix inc idx i j = 0 := by
  simp [boundaryMatrix, hempty]

theorem empty_boundaries_square_zero {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (hempty : ∀ i, inc.boundary i = []) :
    boundarySquareZero inc idx := by
  intro i k _ _
  have hfold : ∀ xs : List I, xs.foldl (fun (acc : Int) _ => acc) 0 = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => exact ih
  simpa [boundaryMatrix, hempty] using hfold idx

theorem boundary_functor_soundness {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (h : boundarySquareZero inc idx) :
    boundarySquareZero inc idx := h

def sameLinearObservations {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (i j : I) : Prop :=
  ∀ k, k ∈ idx →
    boundaryMatrix inc idx i k = boundaryMatrix inc idx j k ∧
      laplacian inc idx i k = laplacian inc idx j k

/- Linear data imply observational equivalence only for a model that supplies
   the corresponding separation theorem. -/
structure LinearCompletenessSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) where
  complete : ∀ {i j}, sameLinearObservations inc idx i j → approxBisim inc i j

theorem linear_completeness {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {idx : List I} (spec : LinearCompletenessSpec inc idx)
    {i j : I} (h : sameLinearObservations inc idx i j) : approxBisim inc i j :=
  spec.complete h

/- A gluing specification supplies the additional laws needed for gluing proofs. -/
structure GluingSpec {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  unit_ok : ∀ i, inc.glue i inc.unit = some i ∧ inc.glue inc.unit i = some i
  type_preserve : ∀ {i j k}, inc.guards.allow i j = true →
    inc.glue i j = some k → inc.typeFunc k = inc.typeFunc i
  assoc_when_ok : ∀ {i j k ij ijk jk},
    inc.guards.allow i j = true → inc.glue i j = some ij →
    inc.guards.allow ij k = true → inc.glue ij k = some ijk →
    inc.guards.allow j k = true → inc.glue j k = some jk →
    inc.guards.allow i jk = true → inc.glue i jk = some ijk

def Guards.permissive (I : Type u) : Guards I := { allow := fun _ _ => true }

theorem glue_left_unit {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) : inc.glue inc.unit i = some i :=
  inc.unit_left i

theorem glue_right_unit {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) : inc.glue i inc.unit = some i :=
  inc.unit_right i

theorem glue_preserves_type {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) {i j k : I}
    (hguard : inc.guards.allow i j = true) (hglue : inc.glue i j = some k) :
    inc.typeFunc k = inc.typeFunc i :=
  inc.type_preserve hguard hglue

theorem glue_associative_when_allowed {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : GluingSpec inc) {i j k ij ijk jk : I}
    (hijAllowed : inc.guards.allow i j = true) (hij : inc.glue i j = some ij)
    (hijkAllowed : inc.guards.allow ij k = true) (hijk : inc.glue ij k = some ijk)
    (hjkAllowed : inc.guards.allow j k = true) (hjk : inc.glue j k = some jk)
    (hiJkAllowed : inc.guards.allow i jk = true) : inc.glue i jk = some ijk :=
  spec.assoc_when_ok hijAllowed hij hijkAllowed hijk hjkAllowed hjk hiJkAllowed

/- A gluing operation may preserve a relation only when that is part of its
   specification; it is not a consequence of boundary data alone. -/
def GlueRespects {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (rel : I → I → Prop) : Prop :=
  ∀ {i₁ i₂ j₁ j₂ k₁ k₂ : I}, rel i₁ i₂ → rel j₁ j₂ →
    inc.glue i₁ j₁ = some k₁ → inc.glue i₂ j₂ = some k₂ → rel k₁ k₂

theorem approxBisim_congruent_under_glue {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (hrespect : GlueRespects inc (approxBisim inc))
    {i₁ i₂ j₁ j₂ k₁ k₂ : I} (hi : approxBisim inc i₁ i₂)
    (hj : approxBisim inc j₁ j₂) (hk₁ : inc.glue i₁ j₁ = some k₁)
    (hk₂ : inc.glue i₂ j₂ = some k₂) : approxBisim inc k₁ k₂ :=
  hrespect hi hj hk₁ hk₂

/- A set-level presentation of the universal property needed for T1. -/
structure Cospan (I : Type u) where
  a : I
  b : I
  c : I
  left : I → I
  right : I → I

structure PushoutWitness {I : Type u} (diagram : Cospan I) where
  apex : I
  inl : I → I
  inr : I → I
  commutes : ∀ x, inl (diagram.left x) = inr (diagram.right x)
  lift : ∀ (leftLeg rightLeg : I → I),
    (∀ x, leftLeg (diagram.left x) = rightLeg (diagram.right x)) → I → I
  lift_inl : ∀ leftLeg rightLeg h x, lift leftLeg rightLeg h (inl x) = leftLeg x
  lift_inr : ∀ leftLeg rightLeg h x, lift leftLeg rightLeg h (inr x) = rightLeg x
  lift_unique : ∀ leftLeg rightLeg h (mediator : I → I),
    (∀ x, mediator (inl x) = leftLeg x) →
    (∀ x, mediator (inr x) = rightLeg x) → mediator = lift leftLeg rightLeg h

/- This is the additional data required to connect `glue` to a pushout. -/
structure GluePushoutSpec {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  diagram : I → I → Cospan I
  witness : ∀ {i j k}, inc.glue i j = some k →
    { pushout : PushoutWitness (diagram i j) // pushout.apex = k }

def glue_creates_pushout {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : GluePushoutSpec inc) {i j k : I}
    (hglue : inc.glue i j = some k) :
    { pushout : PushoutWitness (spec.diagram i j) // pushout.apex = k } :=
  spec.witness hglue

/- Minimal category-theoretic data for the translation theorem (T5). -/
structure IncCategory (Obj : Type u) where
  Hom : Obj → Obj → Type u
  id : ∀ a, Hom a a
  comp : ∀ {a b c}, Hom b c → Hom a b → Hom a c
  id_comp : ∀ {a b} (f : Hom a b), comp (id b) f = f
  comp_id : ∀ {a b} (f : Hom a b), comp f (id a) = f
  assoc : ∀ {a b c d} (f : Hom c d) (g : Hom b c) (h : Hom a b),
    comp f (comp g h) = comp (comp f g) h

structure IncFunctor {CObj DObj : Type u}
    (C : IncCategory CObj) (D : IncCategory DObj) where
  obj : CObj → DObj
  map : ∀ {a b}, C.Hom a b → D.Hom (obj a) (obj b)
  map_id : ∀ a, map (C.id a) = D.id (obj a)
  map_comp : ∀ {a b c} (g : C.Hom b c) (f : C.Hom a b),
    map (C.comp g f) = D.comp (map g) (map f)

def IncFunctor.identity {Obj : Type u} (C : IncCategory Obj) : IncFunctor C C where
  obj := id
  map := fun f => f
  map_id := by intro a; rfl
  map_comp := by intro a b c g f; rfl

def IncFunctor.comp {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (G : IncFunctor D E) (F : IncFunctor C D) : IncFunctor C E where
  obj := fun a => G.obj (F.obj a)
  map := fun f => G.map (F.map f)
  map_id := by
    intro a
    rw [F.map_id, G.map_id]
  map_comp := by
    intro a b c g f
    rw [F.map_comp, G.map_comp]

structure MorphismCospan {Obj : Type u} (C : IncCategory Obj) where
  a : Obj
  b : Obj
  c : Obj
  left : C.Hom a b
  right : C.Hom a c

def IncFunctor.mapCospan {CObj DObj : Type u} {C : IncCategory CObj}
    {D : IncCategory DObj} (F : IncFunctor C D) (span : MorphismCospan C) :
    MorphismCospan D where
  a := F.obj span.a
  b := F.obj span.b
  c := F.obj span.c
  left := F.map span.left
  right := F.map span.right

theorem IncFunctor.mapCospan_identity {Obj : Type u} {C : IncCategory Obj}
    (span : MorphismCospan C) :
    (IncFunctor.identity C).mapCospan span = span := rfl

theorem IncFunctor.mapCospan_comp {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (G : IncFunctor D E) (F : IncFunctor C D) (span : MorphismCospan C) :
    (G.comp F).mapCospan span = G.mapCospan (F.mapCospan span) := rfl

structure MorphismPushout {Obj : Type u} {C : IncCategory Obj}
    (span : MorphismCospan C) where
  apex : Obj
  inl : C.Hom span.b apex
  inr : C.Hom span.c apex
  commutes : C.comp inl span.left = C.comp inr span.right
  lift : ∀ (q : Obj) (leftLeg : C.Hom span.b q) (rightLeg : C.Hom span.c q),
    C.comp leftLeg span.left = C.comp rightLeg span.right → C.Hom apex q
  lift_inl : ∀ q leftLeg rightLeg h, C.comp (lift q leftLeg rightLeg h) inl = leftLeg
  lift_inr : ∀ q leftLeg rightLeg h, C.comp (lift q leftLeg rightLeg h) inr = rightLeg
  lift_unique : ∀ q leftLeg rightLeg h (mediator : C.Hom apex q),
    C.comp mediator inl = leftLeg → C.comp mediator inr = rightLeg →
      mediator = lift q leftLeg rightLeg h

/- The small amount of isomorphism data needed to state uniqueness of a
   pushout apex without importing a larger category-theory library. -/
structure MorphismIso {Obj : Type u} (C : IncCategory Obj) (source target : Obj) where
  hom : C.Hom source target
  inv : C.Hom target source
  inv_hom : C.comp inv hom = C.id source
  hom_inv : C.comp hom inv = C.id target

/- The elementary groupoid laws for translation equivalences.  Keeping these
   in the small core lets later incidence translations compose their chosen
   identifications without importing a category-theory library. -/
def MorphismIso.refl {Obj : Type u} {C : IncCategory Obj} (source : Obj) :
    MorphismIso C source source where
  hom := C.id source
  inv := C.id source
  inv_hom := C.id_comp (C.id source)
  hom_inv := C.id_comp (C.id source)

def MorphismIso.symm {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    (iso : MorphismIso C source target) : MorphismIso C target source where
  hom := iso.inv
  inv := iso.hom
  inv_hom := iso.hom_inv
  hom_inv := iso.inv_hom

def MorphismIso.trans {Obj : Type u} {C : IncCategory Obj}
    {source middle target : Obj} (first : MorphismIso C source middle)
    (second : MorphismIso C middle target) : MorphismIso C source target where
  hom := C.comp second.hom first.hom
  inv := C.comp first.inv second.inv
  inv_hom := by
    rw [← C.assoc first.inv second.inv (C.comp second.hom first.hom),
      C.assoc second.inv second.hom first.hom,
      second.inv_hom, C.id_comp, first.inv_hom]
  hom_inv := by
    rw [← C.assoc second.hom first.hom (C.comp first.inv second.inv),
      C.assoc first.hom first.inv second.inv,
      first.hom_inv, C.id_comp, second.hom_inv]

theorem MorphismIso.trans_hom {Obj : Type u} {C : IncCategory Obj}
    {source middle target : Obj} (first : MorphismIso C source middle)
    (second : MorphismIso C middle target) :
    (first.trans second).hom = C.comp second.hom first.hom := rfl

theorem MorphismIso.trans_inv {Obj : Type u} {C : IncCategory Obj}
    {source middle target : Obj} (first : MorphismIso C source middle)
    (second : MorphismIso C middle target) :
    (first.trans second).inv = C.comp first.inv second.inv := rfl

/- These componentwise laws are the coherence API used below.  We state them
   on arrows rather than as equality of bundled isomorphisms, so no extensional
   equality principle for an arbitrary `Hom` family is required. -/
theorem MorphismIso.refl_hom {Obj : Type u} {C : IncCategory Obj} (source : Obj) :
    (MorphismIso.refl (C := C) source).hom = C.id source := rfl

theorem MorphismIso.refl_inv {Obj : Type u} {C : IncCategory Obj} (source : Obj) :
    (MorphismIso.refl (C := C) source).inv = C.id source := rfl

theorem MorphismIso.symm_hom {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    (iso : MorphismIso C source target) : iso.symm.hom = iso.inv := rfl

theorem MorphismIso.symm_inv {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    (iso : MorphismIso C source target) : iso.symm.inv = iso.hom := rfl

theorem MorphismIso.symm_symm_hom {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    iso.symm.symm.hom = iso.hom := rfl

theorem MorphismIso.symm_symm_inv {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    iso.symm.symm.inv = iso.inv := rfl

theorem MorphismIso.trans_assoc_hom {Obj : Type u} {C : IncCategory Obj}
    {a b c d : Obj} (first : MorphismIso C a b) (second : MorphismIso C b c)
    (third : MorphismIso C c d) :
    ((first.trans second).trans third).hom = (first.trans (second.trans third)).hom := by
  exact C.assoc third.hom second.hom first.hom

theorem MorphismIso.trans_assoc_inv {Obj : Type u} {C : IncCategory Obj}
    {a b c d : Obj} (first : MorphismIso C a b) (second : MorphismIso C b c)
    (third : MorphismIso C c d) :
    ((first.trans second).trans third).inv = (first.trans (second.trans third)).inv := by
  exact (C.assoc first.inv second.inv third.inv).symm

theorem MorphismIso.refl_trans_hom {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    ((MorphismIso.refl (C := C) source).trans iso).hom = iso.hom :=
  C.comp_id iso.hom

theorem MorphismIso.trans_refl_hom {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    (iso.trans (MorphismIso.refl (C := C) target)).hom = iso.hom :=
  C.id_comp iso.hom

theorem MorphismIso.refl_trans_inv {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    ((MorphismIso.refl (C := C) source).trans iso).inv = iso.inv :=
  C.id_comp iso.inv

theorem MorphismIso.trans_refl_inv {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    (iso.trans (MorphismIso.refl (C := C) target)).inv = iso.inv :=
  C.comp_id iso.inv

theorem MorphismIso.trans_symm_hom {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    (iso.trans iso.symm).hom = C.id source := iso.inv_hom

theorem MorphismIso.symm_trans_hom {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (iso : MorphismIso C source target) :
    (iso.symm.trans iso).hom = C.id target := iso.hom_inv

def pushoutComparison {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (source target : MorphismPushout span) :
    C.Hom source.apex target.apex :=
  source.lift target.apex target.inl target.inr target.commutes

theorem pushoutComparison_inl {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (source target : MorphismPushout span) :
    C.comp (pushoutComparison source target) source.inl = target.inl :=
  source.lift_inl target.apex target.inl target.inr target.commutes

theorem pushoutComparison_inr {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (source target : MorphismPushout span) :
    C.comp (pushoutComparison source target) source.inr = target.inr :=
  source.lift_inr target.apex target.inl target.inr target.commutes

theorem pushoutComparison_self {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (po : MorphismPushout span) :
    pushoutComparison po po = C.id po.apex := by
  symm
  apply po.lift_unique po.apex po.inl po.inr po.commutes
  · simpa using C.id_comp po.inl
  · simpa using C.id_comp po.inr

theorem pushoutComparison_comp {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (first second third : MorphismPushout span) :
    pushoutComparison first third =
      C.comp (pushoutComparison second third) (pushoutComparison first second) := by
  symm
  apply first.lift_unique third.apex third.inl third.inr third.commutes
  · rw [← C.assoc, pushoutComparison_inl, pushoutComparison_inl]
  · rw [← C.assoc, pushoutComparison_inr, pushoutComparison_inr]

def pushout_unique_up_to_iso {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (source target : MorphismPushout span) :
    MorphismIso C source.apex target.apex where
  hom := pushoutComparison source target
  inv := pushoutComparison target source
  inv_hom := by
    rw [← pushoutComparison_comp, pushoutComparison_self]
  hom_inv := by
    rw [← pushoutComparison_comp, pushoutComparison_self]

/- Comparison isomorphisms are coherent: the direct identification of two
   translated pushout presentations is the composite through any third one. -/
theorem pushout_unique_up_to_iso_trans_hom {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (first second third : MorphismPushout span) :
    ((pushout_unique_up_to_iso first second).trans
      (pushout_unique_up_to_iso second third)).hom =
      (pushout_unique_up_to_iso first third).hom := by
  exact (pushoutComparison_comp first second third).symm

theorem pushout_unique_up_to_iso_symm_hom {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (source target : MorphismPushout span) :
    (pushout_unique_up_to_iso source target).symm.hom =
      (pushout_unique_up_to_iso target source).hom := rfl

theorem pushout_unique_up_to_iso_self_hom {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (po : MorphismPushout span) :
    (pushout_unique_up_to_iso po po).hom = C.id po.apex :=
  pushoutComparison_self po

theorem pushout_unique_up_to_iso_trans_inv {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (first second third : MorphismPushout span) :
    ((pushout_unique_up_to_iso first second).trans
      (pushout_unique_up_to_iso second third)).inv =
      (pushout_unique_up_to_iso first third).inv := by
  exact (pushoutComparison_comp third second first).symm

theorem pushout_unique_up_to_iso_symm_inv {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (source target : MorphismPushout span) :
    (pushout_unique_up_to_iso source target).symm.inv =
      (pushout_unique_up_to_iso target source).inv := rfl

theorem pushout_unique_up_to_iso_self_inv {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (po : MorphismPushout span) :
    (pushout_unique_up_to_iso po po).inv = C.id po.apex :=
  pushoutComparison_self po

/- Four presentations have a path-independent comparison.  The two displayed
   parenthesizations are intentionally retained: later translation towers can
   rewrite either syntactic composite to the direct comparison. -/
theorem pushoutComparison_quad_comp {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C}
    (first second third fourth : MorphismPushout span) :
    pushoutComparison first fourth =
      C.comp (pushoutComparison third fourth)
        (C.comp (pushoutComparison second third) (pushoutComparison first second)) := by
  rw [pushoutComparison_comp first third fourth,
    pushoutComparison_comp first second third]

theorem pushoutComparison_quad_comp_assoc {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C}
    (first second third fourth : MorphismPushout span) :
    pushoutComparison first fourth =
      C.comp (C.comp (pushoutComparison third fourth) (pushoutComparison second third))
        (pushoutComparison first second) := by
  rw [pushoutComparison_quad_comp]
  exact C.assoc _ _ _

theorem pushout_unique_up_to_iso_refl_trans_hom {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (first second : MorphismPushout span) :
    ((pushout_unique_up_to_iso first first).trans
      (pushout_unique_up_to_iso first second)).hom =
      (pushout_unique_up_to_iso first second).hom := by
  change C.comp (pushoutComparison first second) (pushoutComparison first first) =
    pushoutComparison first second
  rw [pushoutComparison_self, C.comp_id]

theorem pushout_unique_up_to_iso_trans_refl_hom {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (first second : MorphismPushout span) :
    ((pushout_unique_up_to_iso first second).trans
      (pushout_unique_up_to_iso second second)).hom =
      (pushout_unique_up_to_iso first second).hom := by
  change C.comp (pushoutComparison second second) (pushoutComparison first second) =
    pushoutComparison first second
  rw [pushoutComparison_self, C.id_comp]

theorem pushout_unique_up_to_iso_roundtrip_hom {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (first second : MorphismPushout span) :
    ((pushout_unique_up_to_iso first second).trans
      (pushout_unique_up_to_iso second first)).hom = C.id first.apex :=
  (pushout_unique_up_to_iso first second).inv_hom

theorem pushout_unique_up_to_iso_roundtrip_inv {Obj : Type u} {C : IncCategory Obj}
    {span : MorphismCospan C} (first second : MorphismPushout span) :
    ((pushout_unique_up_to_iso first second).trans
      (pushout_unique_up_to_iso second first)).inv = C.id first.apex :=
  by
    change C.comp (pushoutComparison second first) (pushoutComparison first second) = C.id first.apex
    exact (pushout_unique_up_to_iso first second).inv_hom

theorem functor_maps_pushout_cocone {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} (F : IncFunctor C D)
    {span : MorphismCospan C} (po : MorphismPushout span) :
    D.comp (F.map po.inl) (F.map span.left) =
      D.comp (F.map po.inr) (F.map span.right) := by
  rw [← F.map_comp, po.commutes, F.map_comp]

/- T5's nontrivial hypothesis: mapping the source universal cocone is again
   universal in the target category. -/
structure PushoutPreserving {CObj DObj : Type u} {C : IncCategory CObj}
    {D : IncCategory DObj} (F : IncFunctor C D) {span : MorphismCospan C}
    (po : MorphismPushout span) where
  mapped_pushout : MorphismPushout (F.mapCospan span)
  apex_is_image : mapped_pushout.apex = F.obj po.apex

def translation_preserves_pushout {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {F : IncFunctor C D}
    {span : MorphismCospan C} (po : MorphismPushout span)
    (hpreserves : PushoutPreserving F po) :
    MorphismPushout (F.mapCospan span) :=
  hpreserves.mapped_pushout

/- Preservation composes: translating through two pushout-preserving stages
   preserves the same source pushout through their composite translation. -/
def PushoutPreserving.comp {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F : IncFunctor C D} {G : IncFunctor D E}
    {span : MorphismCospan C} (po : MorphismPushout span)
    (hF : PushoutPreserving F po)
    (hG : PushoutPreserving G hF.mapped_pushout) :
    PushoutPreserving (G.comp F) po where
  mapped_pushout := hG.mapped_pushout
  apex_is_image := by
    calc
      hG.mapped_pushout.apex = G.obj hF.mapped_pushout.apex := hG.apex_is_image
      _ = G.obj (F.obj po.apex) := congrArg G.obj hF.apex_is_image

end IncidenceCore
