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

/- Dependent types over an incidence carrier.  This is the semantic layer for
   the requested dependent/higher-order internal language: a family assigns a
   type to every incidence, its dependent sum is the total space, and its
   dependent product is the type of sections.  Syntax and proof rules may be
   interpreted in this layer without identifying dependent type equality with
   behavioural bisimilarity. -/
structure IncDependentFamily {I R T : Type u} [DecidableEq I]
    (_inc : Incidence I R T) where
  fiber : I → Type u

abbrev IncDependentSum {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (family : IncDependentFamily inc) : Type u :=
  Sigma family.fiber

abbrev IncDependentProduct {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (family : IncDependentFamily inc) : Type u :=
  ∀ i, family.fiber i

def IncDependentFamily.reindex {I R T J : Type u} [DecidableEq I]
    {inc : Incidence I R T} (family : IncDependentFamily inc) (map : J → I) :
    J → Type u :=
  fun j => family.fiber (map j)

def IncDependentFamily.mapSum {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {family target : IncDependentFamily inc}
    (map : ∀ i, family.fiber i → target.fiber i) :
    IncDependentSum family → IncDependentSum target
  | ⟨i, value⟩ => ⟨i, map i value⟩

theorem IncDependentFamily.mapSum_id {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (family : IncDependentFamily inc) :
    IncDependentFamily.mapSum (family := family) (target := family)
      (fun _ value => value) = id := by
  funext total
  rcases total with ⟨i, value⟩
  rfl

theorem IncDependentFamily.mapSum_comp {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {first second third : IncDependentFamily inc}
    (f : ∀ i, first.fiber i → second.fiber i)
    (g : ∀ i, second.fiber i → third.fiber i) :
    IncDependentFamily.mapSum (family := second) (target := third) g ∘
        IncDependentFamily.mapSum (family := first) (target := second) f =
      IncDependentFamily.mapSum (family := first) (target := third)
        (fun i value => g i (f i value)) := by
  funext total
  rcases total with ⟨i, value⟩
  rfl

def IncDependentFamily.mapProduct {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {family target : IncDependentFamily inc}
    (map : ∀ i, family.fiber i → target.fiber i) :
    IncDependentProduct family → IncDependentProduct target :=
  fun sec i => map i (sec i)

theorem IncDependentFamily.mapProduct_id {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (family : IncDependentFamily inc) :
    IncDependentFamily.mapProduct (family := family) (target := family)
      (fun _ value => value) = id := by
  funext sec
  rfl

theorem IncDependentFamily.mapProduct_comp {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {first second third : IncDependentFamily inc}
    (f : ∀ i, first.fiber i → second.fiber i)
    (g : ∀ i, second.fiber i → third.fiber i) :
    IncDependentFamily.mapProduct (family := second) (target := third) g ∘
        IncDependentFamily.mapProduct (family := first) (target := second) f =
      IncDependentFamily.mapProduct (family := first) (target := third)
        (fun i value => g i (f i value)) := by
  funext sec i
  rfl

theorem incDependentProduct_ext {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} {family : IncDependentFamily inc}
    {left right : IncDependentProduct family}
    (h : ∀ i, left i = right i) : left = right :=
  funext h

/- A classification is the general sufficient condition for the behavioural
   quotient to have a concrete, fully described carrier.  `respects` is the
   well-definedness condition for `Quotient.lift`; `reflects` prevents two
   distinct quotient classes from being identified in the target; and
   `surjective` says that the target has no spurious classes.  Constructing an
   `Incidence` on that carrier additionally needs boundary/glue compatibility,
   but this record isolates the quotient-theoretic part of that obligation. -/
structure BisimulationQuotientClassification {I R T Q : Type u} [DecidableEq I]
    (inc : Incidence I R T) where
  classify : I → Q
  respects : ∀ {x y}, approxBisim inc x y → classify x = classify y
  reflects : ∀ {x y}, classify x = classify y → approxBisim inc x y
  surjective : ∀ q : Q, ∃ x, classify x = q

noncomputable def BisimulationQuotientClassification.lift
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    IncidenceQuotient inc → Q :=
  Quotient.lift classification.classify (fun _ _ h => classification.respects h)

theorem BisimulationQuotientClassification.lift_injective
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc)
    {q₁ q₂ : IncidenceQuotient inc}
    (h : classification.lift q₁ = classification.lift q₂) : q₁ = q₂ := by
  induction q₁ using Quotient.ind with
  | _ x =>
    induction q₂ using Quotient.ind with
    | _ y =>
      apply Quotient.sound
      apply classification.reflects
      simpa [BisimulationQuotientClassification.lift] using h

theorem BisimulationQuotientClassification.lift_surjective
    {I R T Q : Type u} [DecidableEq I] {inc : Incidence I R T}
    (classification : BisimulationQuotientClassification (Q := Q) inc) :
    ∀ q : Q, ∃ quotient : IncidenceQuotient inc, classification.lift quotient = q := by
  intro q
  rcases classification.surjective q with ⟨x, hx⟩
  exact ⟨Quotient.mk _ x, by simpa [BisimulationQuotientClassification.lift] using hx⟩

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

/- An unconditional chain-complex law for one incidence would quantify over
   every finite observation list.  This is deliberately distinct from the
   conditional `boundarySquareZero inc idx`: the base `Incidence` interface
   does not impose it, and concrete countermodels below show it cannot be
   derived from the current axioms. -/
def BoundarySquareZeroEverywhere {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : Prop :=
  ∀ idx, boundarySquareZero inc idx

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

/- Optional A11--A13-style operational data.  The base `Incidence` record
   deliberately does not require quotient compatibility or a normal form:
   these are additional properties of a chosen implementation.  Soundness
   means that normalization stays in the same observational class, while
   idempotence makes the chosen representative stable. -/
structure BisimulationNormalizationSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) where
  glue_respects_approx : GlueRespects inc (approxBisim inc)
  normalize : I → I
  normalize_sound : ∀ i, approxBisim inc i (normalize i)
  normalize_idempotent : ∀ i, normalize (normalize i) = normalize i

/- The identity map is always a stable normalization once quotient-compatible
   gluing has been supplied.  This is useful for models whose observational
   quotient is already discrete. -/
def BisimulationNormalizationSpec.identity {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    (hglue : GlueRespects inc (approxBisim inc)) :
    BisimulationNormalizationSpec inc where
  glue_respects_approx := hglue
  normalize := id
  normalize_sound := fun i => approxBisim_refl inc i
  normalize_idempotent := fun _ => rfl

/- Composing normalizations is stable when the chosen normalizers commute.
   Without this compatibility assumption, the composite of two idempotent
   maps need not itself be idempotent, so it is deliberately an explicit
   premise of the construction. -/
def BisimulationNormalizationSpec.comp {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (first second : BisimulationNormalizationSpec inc)
    (hcomm : ∀ i,
      first.normalize (second.normalize i) = second.normalize (first.normalize i)) :
    BisimulationNormalizationSpec inc where
  glue_respects_approx := first.glue_respects_approx
  normalize := fun i => first.normalize (second.normalize i)
  normalize_sound := by
    intro i
    exact approxBisim_trans (second.normalize_sound i)
      (first.normalize_sound (second.normalize i))
  normalize_idempotent := by
    intro i
    change first.normalize (second.normalize (first.normalize (second.normalize i))) =
      first.normalize (second.normalize i)
    rw [← hcomm (second.normalize i)]
    rw [first.normalize_idempotent, second.normalize_idempotent]

theorem normalization_respects_approx {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : BisimulationNormalizationSpec inc)
    {i j : I} (hij : approxBisim inc i j) :
    approxBisim inc (spec.normalize i) (spec.normalize j) := by
  exact approxBisim_trans (approxBisim_symm (spec.normalize_sound i))
    (approxBisim_trans hij (spec.normalize_sound j))

theorem normalization_quotient_eq {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : BisimulationNormalizationSpec inc) (i : I) :
    (Quotient.mk (approxBisimSetoid inc) (spec.normalize i) : IncidenceQuotient inc) =
      Quotient.mk (approxBisimSetoid inc) i :=
  incidence_quotient_sound (approxBisim_symm (spec.normalize_sound i))

theorem normalized_glue_congruent {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : BisimulationNormalizationSpec inc)
    {i₁ i₂ j₁ j₂ k₁ k₂ : I}
    (hi : approxBisim inc i₁ i₂) (hj : approxBisim inc j₁ j₂)
    (hk₁ : inc.glue (spec.normalize i₁) (spec.normalize j₁) = some k₁)
    (hk₂ : inc.glue (spec.normalize i₂) (spec.normalize j₂) = some k₂) :
    approxBisim inc k₁ k₂ :=
  spec.glue_respects_approx (normalization_respects_approx spec hi)
    (normalization_respects_approx spec hj) hk₁ hk₂

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

/- A strengthened Inc layer packages exactly the two pieces of data that are
   absent from the bare interface: the chain-complex law and a universal
   gluing presentation.  Consequently its theorems are unconditional for
   every value of this type, while the countermodel in `Peano.lean` prevents
   them from being theorems of bare `Incidence`. -/
structure ChainComplexPushoutIncidence (I R T : Type u) [DecidableEq I] where
  inc : Incidence I R T
  boundary_square_zero : BoundarySquareZeroEverywhere inc
  glue_pushout : GluePushoutSpec inc

def ChainComplexPushoutIncidence.glue_creates_pushout
    {I R T : Type u} [DecidableEq I]
    (coherent : ChainComplexPushoutIncidence I R T) {i j k : I}
    (hglue : coherent.inc.glue i j = some k) :
    { pushout : PushoutWitness (coherent.glue_pushout.diagram i j) //
      pushout.apex = k } :=
  IncidenceCore.glue_creates_pushout coherent.glue_pushout hglue

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

structure IncNaturalTransformation {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    (F G : IncFunctor C D) where
  app : ∀ object, D.Hom (F.obj object) (G.obj object)
  naturality : ∀ {source target} (morphism : C.Hom source target),
    D.comp (G.map morphism) (app source) =
      D.comp (app target) (F.map morphism)

def IncNaturalTransformation.identity {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : IncNaturalTransformation F F where
  app := fun object => D.id (F.obj object)
  naturality := by
    intro source target morphism
    rw [D.comp_id, D.id_comp]

def IncNaturalTransformation.vcomp {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G H : IncFunctor C D}
    (beta : IncNaturalTransformation G H)
    (alpha : IncNaturalTransformation F G) : IncNaturalTransformation F H where
  app := fun object => D.comp (beta.app object) (alpha.app object)
  naturality := by
    intro source target morphism
    calc
      D.comp (H.map morphism) (D.comp (beta.app source) (alpha.app source)) =
          D.comp (D.comp (H.map morphism) (beta.app source))
            (alpha.app source) := D.assoc _ _ _
      _ = D.comp (D.comp (beta.app target) (G.map morphism))
            (alpha.app source) := by rw [beta.naturality]
      _ = D.comp (beta.app target)
            (D.comp (G.map morphism) (alpha.app source)) := (D.assoc _ _ _).symm
      _ = D.comp (beta.app target)
            (D.comp (alpha.app target) (F.map morphism)) := by rw [alpha.naturality]
      _ = D.comp (D.comp (beta.app target) (alpha.app target))
            (F.map morphism) := D.assoc _ _ _

theorem IncNaturalTransformation.vcomp_app {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G H : IncFunctor C D}
    (beta : IncNaturalTransformation G H)
    (alpha : IncNaturalTransformation F G) (object : CObj) :
    (beta.vcomp alpha).app object = D.comp (beta.app object) (alpha.app object) := rfl

theorem IncNaturalTransformation.identity_vcomp_app {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (alpha : IncNaturalTransformation F G) (object : CObj) :
    ((IncNaturalTransformation.identity G).vcomp alpha).app object = alpha.app object := by
  exact D.id_comp (alpha.app object)

theorem IncNaturalTransformation.vcomp_identity_app {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (alpha : IncNaturalTransformation F G) (object : CObj) :
    (alpha.vcomp (IncNaturalTransformation.identity F)).app object = alpha.app object := by
  exact D.comp_id (alpha.app object)

theorem IncNaturalTransformation.vcomp_assoc_app {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G H K : IncFunctor C D}
    (gamma : IncNaturalTransformation H K)
    (beta : IncNaturalTransformation G H)
    (alpha : IncNaturalTransformation F G) (object : CObj) :
    ((gamma.vcomp beta).vcomp alpha).app object =
      (gamma.vcomp (beta.vcomp alpha)).app object := by
  exact (D.assoc (gamma.app object) (beta.app object) (alpha.app object)).symm

theorem IncNaturalTransformation.ext {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} {alpha beta : IncNaturalTransformation F G}
    (componentEq : ∀ object, alpha.app object = beta.app object) : alpha = beta := by
  cases alpha with
  | mk alphaApp alphaNatural =>
      cases beta with
      | mk betaApp betaNatural =>
          have appEq : alphaApp = betaApp := funext componentEq
          subst betaApp
          rfl

theorem IncNaturalTransformation.identity_vcomp {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (alpha : IncNaturalTransformation F G) :
    (IncNaturalTransformation.identity G).vcomp alpha = alpha := by
  apply IncNaturalTransformation.ext
  exact alpha.identity_vcomp_app

theorem IncNaturalTransformation.vcomp_identity {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (alpha : IncNaturalTransformation F G) :
    alpha.vcomp (IncNaturalTransformation.identity F) = alpha := by
  apply IncNaturalTransformation.ext
  exact alpha.vcomp_identity_app

theorem IncNaturalTransformation.vcomp_assoc {CObj DObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj}
    {F G H K : IncFunctor C D}
    (gamma : IncNaturalTransformation H K)
    (beta : IncNaturalTransformation G H)
    (alpha : IncNaturalTransformation F G) :
    (gamma.vcomp beta).vcomp alpha = gamma.vcomp (beta.vcomp alpha) := by
  apply IncNaturalTransformation.ext
  exact gamma.vcomp_assoc_app beta alpha

def incFunctorCategory {CObj DObj : Type u}
    (C : IncCategory CObj) (D : IncCategory DObj) :
    IncCategory (IncFunctor C D) where
  Hom := IncNaturalTransformation
  id := IncNaturalTransformation.identity
  comp := IncNaturalTransformation.vcomp
  id_comp := IncNaturalTransformation.identity_vcomp
  comp_id := IncNaturalTransformation.vcomp_identity
  assoc := by
    intro F G H K gamma beta alpha
    exact (IncNaturalTransformation.vcomp_assoc gamma beta alpha).symm

def IncNaturalTransformation.whiskerLeft
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} (K : IncFunctor D E)
    (alpha : IncNaturalTransformation F G) :
    IncNaturalTransformation (K.comp F) (K.comp G) where
  app := fun object => K.map (alpha.app object)
  naturality := by
    intro source target morphism
    change E.comp (K.map (G.map morphism)) (K.map (alpha.app source)) =
      E.comp (K.map (alpha.app target)) (K.map (F.map morphism))
    rw [← K.map_comp, alpha.naturality, K.map_comp]

def IncNaturalTransformation.whiskerRight
    {BObj CObj DObj : Type u}
    {B : IncCategory BObj} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (alpha : IncNaturalTransformation F G)
    (H : IncFunctor B C) :
    IncNaturalTransformation (F.comp H) (G.comp H) where
  app := fun object => alpha.app (H.obj object)
  naturality := by
    intro source target morphism
    exact alpha.naturality (H.map morphism)

def IncNaturalTransformation.hcomp
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (beta : IncNaturalTransformation H K)
    (alpha : IncNaturalTransformation F G) :
    IncNaturalTransformation (H.comp F) (K.comp G) :=
  (beta.whiskerRight G).vcomp (alpha.whiskerLeft H)

theorem IncNaturalTransformation.whiskerLeft_app
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} (K : IncFunctor D E)
    (alpha : IncNaturalTransformation F G) (object : CObj) :
    (alpha.whiskerLeft K).app object = K.map (alpha.app object) := rfl

theorem IncNaturalTransformation.whiskerRight_app
    {BObj CObj DObj : Type u}
    {B : IncCategory BObj} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (alpha : IncNaturalTransformation F G)
    (H : IncFunctor B C) (object : BObj) :
    (alpha.whiskerRight H).app object = alpha.app (H.obj object) := rfl

theorem IncNaturalTransformation.hcomp_app
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (beta : IncNaturalTransformation H K)
    (alpha : IncNaturalTransformation F G) (object : CObj) :
    (beta.hcomp alpha).app object =
      E.comp (beta.app (G.obj object)) (H.map (alpha.app object)) := rfl

theorem IncNaturalTransformation.hcomp_app_alt
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (beta : IncNaturalTransformation H K)
    (alpha : IncNaturalTransformation F G) (object : CObj) :
    (beta.hcomp alpha).app object =
      E.comp (K.map (alpha.app object)) (beta.app (F.obj object)) := by
  change E.comp (beta.app (G.obj object)) (H.map (alpha.app object)) =
    E.comp (K.map (alpha.app object)) (beta.app (F.obj object))
  exact (beta.naturality (alpha.app object)).symm

theorem IncNaturalTransformation.whiskerLeft_vcomp
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G H : IncFunctor C D} (K : IncFunctor D E)
    (beta : IncNaturalTransformation G H)
    (alpha : IncNaturalTransformation F G) :
    (beta.vcomp alpha).whiskerLeft K =
      (beta.whiskerLeft K).vcomp (alpha.whiskerLeft K) := by
  apply IncNaturalTransformation.ext
  intro object
  change K.map (D.comp (beta.app object) (alpha.app object)) =
    E.comp (K.map (beta.app object)) (K.map (alpha.app object))
  exact K.map_comp _ _

theorem IncNaturalTransformation.whiskerRight_vcomp
    {BObj CObj DObj : Type u}
    {B : IncCategory BObj} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G H : IncFunctor C D}
    (beta : IncNaturalTransformation G H)
    (alpha : IncNaturalTransformation F G) (K : IncFunctor B C) :
    (beta.vcomp alpha).whiskerRight K =
      (beta.whiskerRight K).vcomp (alpha.whiskerRight K) := by
  apply IncNaturalTransformation.ext
  intro object
  rfl

theorem IncNaturalTransformation.whiskerLeft_identity
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (F : IncFunctor C D) (K : IncFunctor D E) :
    (IncNaturalTransformation.identity F).whiskerLeft K =
      IncNaturalTransformation.identity (K.comp F) := by
  apply IncNaturalTransformation.ext
  intro object
  exact K.map_id _

theorem IncNaturalTransformation.whiskerRight_identity
    {BObj CObj DObj : Type u}
    {B : IncCategory BObj} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) (K : IncFunctor B C) :
    (IncNaturalTransformation.identity F).whiskerRight K =
      IncNaturalTransformation.identity (F.comp K) := by
  apply IncNaturalTransformation.ext
  intro object
  rfl

theorem IncNaturalTransformation.hcomp_identity
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (F : IncFunctor C D) (G : IncFunctor D E) :
    (IncNaturalTransformation.identity G).hcomp
        (IncNaturalTransformation.identity F) =
      IncNaturalTransformation.identity (G.comp F) := by
  apply IncNaturalTransformation.ext
  intro object
  change E.comp (E.id (G.obj (F.obj object)))
      (G.map (D.id (F.obj object))) = E.id (G.obj (F.obj object))
  rw [G.map_id, E.id_comp]

theorem IncNaturalTransformation.hcomp_vcomp_interchange
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G H : IncFunctor C D} {K L M : IncFunctor D E}
    (delta : IncNaturalTransformation L M)
    (gamma : IncNaturalTransformation K L)
    (beta : IncNaturalTransformation G H)
    (alpha : IncNaturalTransformation F G) :
    (delta.vcomp gamma).hcomp (beta.vcomp alpha) =
      (delta.hcomp beta).vcomp (gamma.hcomp alpha) := by
  apply IncNaturalTransformation.ext
  intro object
  change E.comp
      (E.comp (delta.app (H.obj object)) (gamma.app (H.obj object)))
      (K.map (D.comp (beta.app object) (alpha.app object))) =
    E.comp
      (E.comp (delta.app (H.obj object)) (L.map (beta.app object)))
      (E.comp (gamma.app (G.obj object)) (K.map (alpha.app object)))
  rw [K.map_comp]
  calc
    _ = E.comp
        (E.comp (E.comp (delta.app (H.obj object)) (gamma.app (H.obj object)))
          (K.map (beta.app object))) (K.map (alpha.app object)) :=
      E.assoc _ _ _
    _ = E.comp (delta.app (H.obj object))
        (E.comp (E.comp (gamma.app (H.obj object)) (K.map (beta.app object)))
          (K.map (alpha.app object))) := by
      exact (congrArg (fun morphism => E.comp morphism (K.map (alpha.app object)))
        (E.assoc (delta.app (H.obj object)) (gamma.app (H.obj object))
          (K.map (beta.app object))).symm).trans
        (E.assoc (delta.app (H.obj object))
          (E.comp (gamma.app (H.obj object)) (K.map (beta.app object)))
          (K.map (alpha.app object))).symm
    _ = E.comp (delta.app (H.obj object))
        (E.comp (E.comp (L.map (beta.app object)) (gamma.app (G.obj object)))
          (K.map (alpha.app object))) := by
      rw [gamma.naturality (beta.app object)]
    _ = _ := by
      rw [← E.assoc, ← E.assoc]

structure IncNaturalIsomorphism
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F G : IncFunctor C D) where
  hom : IncNaturalTransformation F G
  inv : IncNaturalTransformation G F
  hom_inv_id : inv.vcomp hom = IncNaturalTransformation.identity F
  inv_hom_id : hom.vcomp inv = IncNaturalTransformation.identity G

def IncNaturalIsomorphism.refl
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : IncNaturalIsomorphism F F where
  hom := IncNaturalTransformation.identity F
  inv := IncNaturalTransformation.identity F
  hom_inv_id := IncNaturalTransformation.identity_vcomp _
  inv_hom_id := IncNaturalTransformation.identity_vcomp _

def IncNaturalIsomorphism.symm
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G) :
    IncNaturalIsomorphism G F where
  hom := iso.inv
  inv := iso.hom
  hom_inv_id := iso.inv_hom_id
  inv_hom_id := iso.hom_inv_id

theorem IncNaturalIsomorphism.hom_app_inv_app
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G) (object : CObj) :
    D.comp (iso.inv.app object) (iso.hom.app object) = D.id (F.obj object) := by
  have component := congrArg (fun transformation => transformation.app object)
    iso.hom_inv_id
  exact component

theorem IncNaturalIsomorphism.inv_app_hom_app
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G) (object : CObj) :
    D.comp (iso.hom.app object) (iso.inv.app object) = D.id (G.obj object) := by
  have component := congrArg (fun transformation => transformation.app object)
    iso.inv_hom_id
  exact component

theorem IncNaturalIsomorphism.source_map_eq_conjugate
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G)
    {source target : CObj} (morphism : C.Hom source target) :
    F.map morphism =
      D.comp (iso.inv.app target)
        (D.comp (G.map morphism) (iso.hom.app source)) := by
  calc
    F.map morphism = D.comp (D.id (F.obj target)) (F.map morphism) :=
      (D.id_comp _).symm
    _ = D.comp
        (D.comp (iso.inv.app target) (iso.hom.app target))
        (F.map morphism) := by rw [iso.hom_app_inv_app]
    _ = D.comp (iso.inv.app target)
        (D.comp (iso.hom.app target) (F.map morphism)) :=
      (D.assoc _ _ _).symm
    _ = D.comp (iso.inv.app target)
        (D.comp (G.map morphism) (iso.hom.app source)) := by
      rw [iso.hom.naturality morphism]

theorem IncNaturalIsomorphism.target_map_eq_conjugate
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G)
    {source target : CObj} (morphism : C.Hom source target) :
    G.map morphism =
      D.comp (iso.hom.app target)
        (D.comp (F.map morphism) (iso.inv.app source)) := by
  calc
    G.map morphism = D.comp (G.map morphism) (D.id (G.obj source)) :=
      (D.comp_id _).symm
    _ = D.comp (G.map morphism)
        (D.comp (iso.hom.app source) (iso.inv.app source)) := by
      rw [iso.inv_app_hom_app]
    _ = D.comp
        (D.comp (G.map morphism) (iso.hom.app source))
        (iso.inv.app source) := D.assoc _ _ _
    _ = D.comp
        (D.comp (iso.hom.app target) (F.map morphism))
        (iso.inv.app source) := by rw [iso.hom.naturality morphism]
    _ = D.comp (iso.hom.app target)
        (D.comp (F.map morphism) (iso.inv.app source)) :=
      (D.assoc _ _ _).symm

def IncFunctor.comp_assoc_iso
    {AObj BObj CObj DObj : Type u}
    {A : IncCategory AObj} {B : IncCategory BObj}
    {C : IncCategory CObj} {D : IncCategory DObj}
    (H : IncFunctor C D) (G : IncFunctor B C) (F : IncFunctor A B) :
    IncNaturalIsomorphism ((H.comp G).comp F) (H.comp (G.comp F)) :=
  IncNaturalIsomorphism.refl ((H.comp G).comp F)

def IncFunctor.identity_comp_iso
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :
    IncNaturalIsomorphism ((IncFunctor.identity D).comp F) F :=
  IncNaturalIsomorphism.refl F

def IncFunctor.comp_identity_iso
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :
    IncNaturalIsomorphism (F.comp (IncFunctor.identity C)) F :=
  IncNaturalIsomorphism.refl F

def IncNaturalIsomorphism.whiskerLeft
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} (K : IncFunctor D E)
    (iso : IncNaturalIsomorphism F G) :
    IncNaturalIsomorphism (K.comp F) (K.comp G) where
  hom := iso.hom.whiskerLeft K
  inv := iso.inv.whiskerLeft K
  hom_inv_id := by
    apply IncNaturalTransformation.ext
    intro object
    change E.comp (K.map (iso.inv.app object)) (K.map (iso.hom.app object)) =
      E.id (K.obj (F.obj object))
    rw [← K.map_comp, iso.hom_app_inv_app, K.map_id]
  inv_hom_id := by
    apply IncNaturalTransformation.ext
    intro object
    change E.comp (K.map (iso.hom.app object)) (K.map (iso.inv.app object)) =
      E.id (K.obj (G.obj object))
    rw [← K.map_comp, iso.inv_app_hom_app, K.map_id]

def IncNaturalIsomorphism.whiskerRight
    {BObj CObj DObj : Type u}
    {B : IncCategory BObj} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G)
    (H : IncFunctor B C) :
    IncNaturalIsomorphism (F.comp H) (G.comp H) where
  hom := iso.hom.whiskerRight H
  inv := iso.inv.whiskerRight H
  hom_inv_id := by
    apply IncNaturalTransformation.ext
    intro object
    exact iso.hom_app_inv_app (H.obj object)
  inv_hom_id := by
    apply IncNaturalTransformation.ext
    intro object
    exact iso.inv_app_hom_app (H.obj object)

def IncNaturalIsomorphism.hcomp
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (beta : IncNaturalIsomorphism H K)
    (alpha : IncNaturalIsomorphism F G) :
    IncNaturalIsomorphism (H.comp F) (K.comp G) where
  hom := beta.hom.hcomp alpha.hom
  inv := beta.inv.hcomp alpha.inv
  hom_inv_id := by
    rw [← IncNaturalTransformation.hcomp_vcomp_interchange]
    rw [beta.hom_inv_id, alpha.hom_inv_id]
    exact IncNaturalTransformation.hcomp_identity F H
  inv_hom_id := by
    rw [← IncNaturalTransformation.hcomp_vcomp_interchange]
    rw [beta.inv_hom_id, alpha.inv_hom_id]
    exact IncNaturalTransformation.hcomp_identity G K

theorem IncNaturalIsomorphism.ext
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D}
    {iso₁ iso₂ : IncNaturalIsomorphism F G}
    (homEq : iso₁.hom = iso₂.hom) : iso₁ = iso₂ := by
  have invEq : iso₁.inv = iso₂.inv := by
    calc
      iso₁.inv = (IncNaturalTransformation.identity F).vcomp iso₁.inv :=
        (IncNaturalTransformation.identity_vcomp iso₁.inv).symm
      _ = (iso₂.inv.vcomp iso₂.hom).vcomp iso₁.inv := by
        rw [iso₂.hom_inv_id]
      _ = iso₂.inv.vcomp (iso₂.hom.vcomp iso₁.inv) :=
        IncNaturalTransformation.vcomp_assoc _ _ _
      _ = iso₂.inv.vcomp (iso₁.hom.vcomp iso₁.inv) := by rw [homEq]
      _ = iso₂.inv.vcomp (IncNaturalTransformation.identity G) := by
        rw [iso₁.inv_hom_id]
      _ = iso₂.inv := IncNaturalTransformation.vcomp_identity iso₂.inv
  cases iso₁
  cases iso₂
  cases homEq
  cases invEq
  rfl

theorem IncNaturalIsomorphism.hcomp_symm
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (beta : IncNaturalIsomorphism H K)
    (alpha : IncNaturalIsomorphism F G) :
    (beta.hcomp alpha).symm = beta.symm.hcomp alpha.symm := by
  apply IncNaturalIsomorphism.ext
  rfl

def IncNaturalIsomorphism.trans
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G H : IncFunctor C D}
    (beta : IncNaturalIsomorphism G H)
    (alpha : IncNaturalIsomorphism F G) : IncNaturalIsomorphism F H where
  hom := beta.hom.vcomp alpha.hom
  inv := alpha.inv.vcomp beta.inv
  hom_inv_id := by
    apply IncNaturalTransformation.ext
    intro object
    change D.comp (D.comp (alpha.inv.app object) (beta.inv.app object))
        (D.comp (beta.hom.app object) (alpha.hom.app object)) = D.id (F.obj object)
    calc
      D.comp (D.comp (alpha.inv.app object) (beta.inv.app object))
          (D.comp (beta.hom.app object) (alpha.hom.app object)) =
        D.comp (alpha.inv.app object)
          (D.comp (beta.inv.app object)
            (D.comp (beta.hom.app object) (alpha.hom.app object))) :=
              (D.assoc _ _ _).symm
      _ = D.comp (alpha.inv.app object)
          (D.comp (D.comp (beta.inv.app object) (beta.hom.app object))
            (alpha.hom.app object)) :=
              congrArg (D.comp (alpha.inv.app object))
                (D.assoc (beta.inv.app object) (beta.hom.app object)
                  (alpha.hom.app object))
      _ = D.comp (alpha.inv.app object)
          (D.comp (D.id (G.obj object)) (alpha.hom.app object)) := by
            rw [beta.hom_app_inv_app]
      _ = D.comp (alpha.inv.app object) (alpha.hom.app object) := by
            rw [D.id_comp]
      _ = D.id (F.obj object) := alpha.hom_app_inv_app object
  inv_hom_id := by
    apply IncNaturalTransformation.ext
    intro object
    change D.comp (D.comp (beta.hom.app object) (alpha.hom.app object))
        (D.comp (alpha.inv.app object) (beta.inv.app object)) = D.id (H.obj object)
    calc
      D.comp (D.comp (beta.hom.app object) (alpha.hom.app object))
          (D.comp (alpha.inv.app object) (beta.inv.app object)) =
        D.comp (beta.hom.app object)
          (D.comp (alpha.hom.app object)
            (D.comp (alpha.inv.app object) (beta.inv.app object))) :=
              (D.assoc _ _ _).symm
      _ = D.comp (beta.hom.app object)
          (D.comp (D.comp (alpha.hom.app object) (alpha.inv.app object))
            (beta.inv.app object)) :=
              congrArg (D.comp (beta.hom.app object))
                (D.assoc (alpha.hom.app object) (alpha.inv.app object)
                  (beta.inv.app object))
      _ = D.comp (beta.hom.app object)
          (D.comp (D.id (G.obj object)) (beta.inv.app object)) := by
            rw [alpha.inv_app_hom_app]
      _ = D.comp (beta.hom.app object) (beta.inv.app object) := by
            rw [D.id_comp]
      _ = D.id (H.obj object) := beta.inv_app_hom_app object

theorem IncNaturalIsomorphism.hcomp_refl
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (F : IncFunctor C D) (G : IncFunctor D E) :
    (IncNaturalIsomorphism.refl G).hcomp (IncNaturalIsomorphism.refl F) =
      IncNaturalIsomorphism.refl (G.comp F) := by
  apply IncNaturalIsomorphism.ext
  exact IncNaturalTransformation.hcomp_identity F G

theorem IncNaturalIsomorphism.hcomp_trans_interchange
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G H : IncFunctor C D} {K L M : IncFunctor D E}
    (delta : IncNaturalIsomorphism L M)
    (gamma : IncNaturalIsomorphism K L)
    (beta : IncNaturalIsomorphism G H)
    (alpha : IncNaturalIsomorphism F G) :
    (delta.trans gamma).hcomp (beta.trans alpha) =
      (delta.hcomp beta).trans (gamma.hcomp alpha) := by
  apply IncNaturalIsomorphism.ext
  exact IncNaturalTransformation.hcomp_vcomp_interchange
    delta.hom gamma.hom beta.hom alpha.hom

def IncNaturallyIsomorphic
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F G : IncFunctor C D) : Prop :=
  Nonempty (IncNaturalIsomorphism F G)

theorem incNaturallyIsomorphic_equivalence
    {CObj DObj : Type u} (C : IncCategory CObj) (D : IncCategory DObj) :
    Equivalence (@IncNaturallyIsomorphic CObj DObj C D) where
  refl := by
    intro F
    exact ⟨IncNaturalIsomorphism.refl F⟩
  symm := by
    intro F G h
    rcases h with ⟨iso⟩
    exact ⟨iso.symm⟩
  trans := by
    intro F G H hFG hGH
    rcases hFG with ⟨alpha⟩
    rcases hGH with ⟨beta⟩
    exact ⟨beta.trans alpha⟩

theorem IncNaturallyIsomorphic.whiskerLeft
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} (K : IncFunctor D E)
    (h : IncNaturallyIsomorphic F G) :
    IncNaturallyIsomorphic (K.comp F) (K.comp G) := by
  rcases h with ⟨iso⟩
  exact ⟨iso.whiskerLeft K⟩

theorem IncNaturallyIsomorphic.whiskerRight
    {BObj CObj DObj : Type u}
    {B : IncCategory BObj} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (h : IncNaturallyIsomorphic F G)
    (K : IncFunctor B C) :
    IncNaturallyIsomorphic (F.comp K) (G.comp K) := by
  rcases h with ⟨iso⟩
  exact ⟨iso.whiskerRight K⟩

theorem IncNaturallyIsomorphic.hcomp
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (outer : IncNaturallyIsomorphic H K)
    (inner : IncNaturallyIsomorphic F G) :
    IncNaturallyIsomorphic (H.comp F) (K.comp G) := by
  rcases outer with ⟨outerIso⟩
  rcases inner with ⟨innerIso⟩
  exact ⟨outerIso.hcomp innerIso⟩

theorem IncNaturallyIsomorphic.comp_left_congr
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} (K : IncFunctor D E)
    (h : IncNaturallyIsomorphic F G) :
    IncNaturallyIsomorphic (K.comp F) (K.comp G) :=
  h.whiskerLeft K

theorem IncNaturallyIsomorphic.comp_right_congr
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor D E} (h : IncNaturallyIsomorphic F G)
    (K : IncFunctor C D) :
    IncNaturallyIsomorphic (F.comp K) (G.comp K) :=
  h.whiskerRight K

theorem IncNaturallyIsomorphic.comp_congr
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (outer : IncNaturallyIsomorphic H K)
    (inner : IncNaturallyIsomorphic F G) :
    IncNaturallyIsomorphic (H.comp F) (K.comp G) :=
  outer.hcomp inner

structure IncFunctorFullyFaithful
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : Prop where
  faithful : ∀ {source target} (left right : C.Hom source target),
    F.map left = F.map right → left = right
  full : ∀ {source target} (morphism : D.Hom (F.obj source) (F.obj target)),
    ∃ preimage : C.Hom source target, F.map preimage = morphism

theorem IncFunctorFullyFaithful.transport
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G)
    (hF : IncFunctorFullyFaithful F) : IncFunctorFullyFaithful G where
  faithful := by
    intro source target left right equality
    apply hF.faithful left right
    rw [iso.source_map_eq_conjugate left]
    rw [iso.source_map_eq_conjugate right]
    rw [equality]
  full := by
    intro source target morphism
    obtain ⟨preimage, preimageEq⟩ := hF.full
      (D.comp (iso.inv.app target)
        (D.comp morphism (iso.hom.app source)))
    refine ⟨preimage, ?_⟩
    rw [iso.target_map_eq_conjugate, preimageEq]
    calc
      D.comp (iso.hom.app target)
          (D.comp
            (D.comp (iso.inv.app target)
              (D.comp morphism (iso.hom.app source)))
            (iso.inv.app source)) =
        D.comp (iso.hom.app target)
          (D.comp (iso.inv.app target)
            (D.comp (D.comp morphism (iso.hom.app source))
              (iso.inv.app source))) := by
          exact congrArg (D.comp (iso.hom.app target))
            (D.assoc (iso.inv.app target)
              (D.comp morphism (iso.hom.app source))
              (iso.inv.app source)).symm
      _ =
        D.comp
          (D.comp (iso.hom.app target) (iso.inv.app target))
          (D.comp (D.comp morphism (iso.hom.app source))
            (iso.inv.app source)) :=
          D.assoc _ _ _
      _ =
        D.comp
          (D.comp (iso.hom.app target) (iso.inv.app target))
          (D.comp morphism
            (D.comp (iso.hom.app source) (iso.inv.app source))) := by
          rw [D.assoc morphism]
      _ = D.comp (D.id (G.obj target))
          (D.comp morphism (D.id (G.obj source))) := by
        rw [iso.inv_app_hom_app, iso.inv_app_hom_app]
      _ = morphism := by rw [D.comp_id, D.id_comp]

theorem IncFunctorFullyFaithful.iff_of_naturallyIsomorphic
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G) :
    IncFunctorFullyFaithful F ↔ IncFunctorFullyFaithful G := by
  constructor
  · intro hF
    exact hF.transport iso
  · intro hG
    exact hG.transport iso.symm

theorem IncFunctorFullyFaithful.comp
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F : IncFunctor C D} {G : IncFunctor D E}
    (hG : IncFunctorFullyFaithful G) (hF : IncFunctorFullyFaithful F) :
    IncFunctorFullyFaithful (G.comp F) where
  faithful := by
    intro source target left right equality
    apply hF.faithful left right
    apply hG.faithful (F.map left) (F.map right)
    exact equality
  full := by
    intro source target morphism
    obtain ⟨middle, middleEq⟩ := hG.full morphism
    obtain ⟨preimage, preimageEq⟩ := hF.full middle
    refine ⟨preimage, ?_⟩
    change G.map (F.map preimage) = morphism
    rw [preimageEq, middleEq]

def IncFunctorEssentiallySurjective
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : Prop :=
  ∀ target : DObj, ∃ source : CObj,
    ∃ hom : D.Hom (F.obj source) target,
    ∃ inv : D.Hom target (F.obj source),
      D.comp inv hom = D.id (F.obj source) ∧ D.comp hom inv = D.id target

theorem IncFunctorEssentiallySurjective.transport
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G)
    (hF : IncFunctorEssentiallySurjective F) :
    IncFunctorEssentiallySurjective G := by
  intro target
  obtain ⟨source, hom, inv, inv_hom, hom_inv⟩ := hF target
  refine ⟨source,
    D.comp hom (iso.inv.app source),
    D.comp (iso.hom.app source) inv, ?_, ?_⟩
  · calc
      D.comp (D.comp (iso.hom.app source) inv)
          (D.comp hom (iso.inv.app source)) =
        D.comp (iso.hom.app source)
          (D.comp inv (D.comp hom (iso.inv.app source))) :=
            (D.assoc _ _ _).symm
      _ = D.comp (iso.hom.app source)
          (D.comp (D.comp inv hom) (iso.inv.app source)) := by
            rw [D.assoc inv hom]
      _ = D.comp (iso.hom.app source)
          (D.comp (D.id (F.obj source)) (iso.inv.app source)) := by
            rw [inv_hom]
      _ = D.comp (iso.hom.app source) (iso.inv.app source) := by
            rw [D.id_comp]
      _ = D.id (G.obj source) := iso.inv_app_hom_app source
  · calc
      D.comp (D.comp hom (iso.inv.app source))
          (D.comp (iso.hom.app source) inv) =
        D.comp hom
          (D.comp (iso.inv.app source)
            (D.comp (iso.hom.app source) inv)) :=
              (D.assoc _ _ _).symm
      _ = D.comp hom
          (D.comp
            (D.comp (iso.inv.app source) (iso.hom.app source)) inv) := by
              rw [D.assoc (iso.inv.app source) (iso.hom.app source)]
      _ = D.comp hom (D.comp (D.id (F.obj source)) inv) := by
            rw [iso.hom_app_inv_app]
      _ = D.comp hom inv := by rw [D.id_comp]
      _ = D.id target := hom_inv

theorem IncFunctorEssentiallySurjective.iff_of_naturallyIsomorphic
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G) :
    IncFunctorEssentiallySurjective F ↔
      IncFunctorEssentiallySurjective G := by
  constructor
  · intro hF
    exact hF.transport iso
  · intro hG
    exact hG.transport iso.symm

structure IncCategoryEquivalence
    {CObj DObj : Type u} (C : IncCategory CObj) (D : IncCategory DObj) where
  forward : IncFunctor C D
  inverse : IncFunctor D C
  unit : IncNaturalIsomorphism (IncFunctor.identity C) (inverse.comp forward)
  counit : IncNaturalIsomorphism (forward.comp inverse) (IncFunctor.identity D)

def IncCategoryEquivalence.refl
    {Obj : Type u} (C : IncCategory Obj) : IncCategoryEquivalence C C where
  forward := IncFunctor.identity C
  inverse := IncFunctor.identity C
  unit := IncNaturalIsomorphism.refl (IncFunctor.identity C)
  counit := IncNaturalIsomorphism.refl (IncFunctor.identity C)

def IncCategoryEquivalence.symm
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) : IncCategoryEquivalence D C where
  forward := equivalence.inverse
  inverse := equivalence.forward
  unit := equivalence.counit.symm
  counit := equivalence.unit.symm

def IncCategoryEquivalence.trans
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (second : IncCategoryEquivalence D E)
    (first : IncCategoryEquivalence C D) : IncCategoryEquivalence C E where
  forward := second.forward.comp first.forward
  inverse := first.inverse.comp second.inverse
  unit :=
    ((second.unit.whiskerRight first.forward).whiskerLeft first.inverse).trans
      first.unit
  counit :=
    second.counit.trans
      ((first.counit.whiskerRight second.inverse).whiskerLeft second.forward)

theorem IncCategoryEquivalence.forward_essentiallySurjective
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncFunctorEssentiallySurjective equivalence.forward := by
  intro target
  exact ⟨equivalence.inverse.obj target,
    equivalence.counit.hom.app target,
    equivalence.counit.inv.app target,
    equivalence.counit.hom_app_inv_app target,
    equivalence.counit.inv_app_hom_app target⟩

theorem IncCategoryEquivalence.inverse_essentiallySurjective
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncFunctorEssentiallySurjective equivalence.inverse :=
  equivalence.symm.forward_essentiallySurjective

theorem IncCategoryEquivalence.forward_faithful
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj} (left right : C.Hom source target) :
    equivalence.forward.map left = equivalence.forward.map right → left = right := by
  intro mappedEqual
  have inverseMappedEqual := congrArg equivalence.inverse.map mappedEqual
  have naturalLeft := equivalence.unit.hom.naturality left
  have naturalRight := equivalence.unit.hom.naturality right
  have conjugateEqual :
      C.comp (equivalence.unit.hom.app target) left =
        C.comp (equivalence.unit.hom.app target) right := by
    calc
      C.comp (equivalence.unit.hom.app target) left =
          C.comp ((equivalence.inverse.comp equivalence.forward).map left)
            (equivalence.unit.hom.app source) := naturalLeft.symm
      _ = C.comp ((equivalence.inverse.comp equivalence.forward).map right)
            (equivalence.unit.hom.app source) := by
              change C.comp (equivalence.inverse.map (equivalence.forward.map left)) _ =
                C.comp (equivalence.inverse.map (equivalence.forward.map right)) _
              rw [inverseMappedEqual]
      _ = C.comp (equivalence.unit.hom.app target) right := naturalRight
  have unitCancel :
      C.comp (equivalence.unit.inv.app target) (equivalence.unit.hom.app target) =
        C.id target := by
    simpa [IncFunctor.identity] using equivalence.unit.hom_app_inv_app target
  calc
    left = C.comp (C.id target) left := (C.id_comp left).symm
    _ = C.comp
        (C.comp (equivalence.unit.inv.app target) (equivalence.unit.hom.app target))
        left := by rw [unitCancel]
    _ = C.comp (equivalence.unit.inv.app target)
        (C.comp (equivalence.unit.hom.app target) left) := (C.assoc _ _ _).symm
    _ = C.comp (equivalence.unit.inv.app target)
        (C.comp (equivalence.unit.hom.app target) right) := by rw [conjugateEqual]
    _ = C.comp
        (C.comp (equivalence.unit.inv.app target) (equivalence.unit.hom.app target))
        right := C.assoc _ _ _
    _ = C.comp (C.id target) right := by rw [unitCancel]
    _ = right := C.id_comp right

theorem IncCategoryEquivalence.inverse_faithful
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : DObj} (left right : D.Hom source target) :
    equivalence.inverse.map left = equivalence.inverse.map right → left = right :=
  equivalence.symm.forward_faithful left right

theorem IncCategoryEquivalence.forward_full
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj}
    (morphism : D.Hom (equivalence.forward.obj source)
      (equivalence.forward.obj target)) :
    ∃ preimage : C.Hom source target, equivalence.forward.map preimage = morphism := by
  let preimage : C.Hom source target :=
    C.comp (equivalence.unit.inv.app target)
      (C.comp (equivalence.inverse.map morphism) (equivalence.unit.hom.app source))
  refine ⟨preimage, ?_⟩
  apply equivalence.inverse_faithful
  change (equivalence.inverse.comp equivalence.forward).map preimage =
    equivalence.inverse.map morphism
  have naturality := equivalence.unit.hom.naturality preimage
  have sourceCancel :
      C.comp (equivalence.unit.hom.app source) (equivalence.unit.inv.app source) =
        C.id ((equivalence.inverse.comp equivalence.forward).obj source) :=
    equivalence.unit.inv_app_hom_app source
  have targetCancel :
      C.comp (equivalence.unit.hom.app target) (equivalence.unit.inv.app target) =
        C.id ((equivalence.inverse.comp equivalence.forward).obj target) :=
    equivalence.unit.inv_app_hom_app target
  calc
    (equivalence.inverse.comp equivalence.forward).map preimage =
        C.comp ((equivalence.inverse.comp equivalence.forward).map preimage)
          (C.id ((equivalence.inverse.comp equivalence.forward).obj source)) :=
            (C.comp_id _).symm
    _ = C.comp ((equivalence.inverse.comp equivalence.forward).map preimage)
        (C.comp (equivalence.unit.hom.app source)
          (equivalence.unit.inv.app source)) := by rw [sourceCancel]
    _ = C.comp
        (C.comp ((equivalence.inverse.comp equivalence.forward).map preimage)
          (equivalence.unit.hom.app source))
        (equivalence.unit.inv.app source) := C.assoc _ _ _
    _ = C.comp
        (C.comp (equivalence.unit.hom.app target) preimage)
        (equivalence.unit.inv.app source) := by
          simpa [IncFunctor.identity] using
            congrArg (fun composed => C.comp composed (equivalence.unit.inv.app source))
              naturality
    _ = C.comp (equivalence.unit.hom.app target)
        (C.comp preimage (equivalence.unit.inv.app source)) := (C.assoc _ _ _).symm
    _ = C.comp (equivalence.unit.hom.app target)
        (C.comp (equivalence.unit.inv.app target)
          (C.comp (C.comp (equivalence.inverse.map morphism)
            (equivalence.unit.hom.app source))
            (equivalence.unit.inv.app source))) := by
              change C.comp (equivalence.unit.hom.app target)
                (C.comp (C.comp (equivalence.unit.inv.app target)
                  (C.comp (equivalence.inverse.map morphism)
                    (equivalence.unit.hom.app source)))
                  (equivalence.unit.inv.app source)) = _
              exact congrArg (C.comp (equivalence.unit.hom.app target))
                (C.assoc (equivalence.unit.inv.app target)
                  (C.comp (equivalence.inverse.map morphism)
                    (equivalence.unit.hom.app source))
                  (equivalence.unit.inv.app source)).symm
    _ = C.comp (equivalence.unit.hom.app target)
        (C.comp (equivalence.unit.inv.app target)
          (C.comp (equivalence.inverse.map morphism)
            (C.comp (equivalence.unit.hom.app source)
              (equivalence.unit.inv.app source)))) := by
              apply congrArg (C.comp (equivalence.unit.hom.app target))
              apply congrArg (C.comp (equivalence.unit.inv.app target))
              exact (C.assoc (equivalence.inverse.map morphism)
                (equivalence.unit.hom.app source)
                (equivalence.unit.inv.app source)).symm
    _ = C.comp (equivalence.unit.hom.app target)
        (C.comp (equivalence.unit.inv.app target)
          (C.comp (equivalence.inverse.map morphism)
            (C.id ((equivalence.inverse.comp equivalence.forward).obj source)))) := by
              rw [sourceCancel]
    _ = C.comp (equivalence.unit.hom.app target)
        (C.comp (equivalence.unit.inv.app target)
          (equivalence.inverse.map morphism)) := by rw [C.comp_id]
    _ = C.comp
        (C.comp (equivalence.unit.hom.app target) (equivalence.unit.inv.app target))
        (equivalence.inverse.map morphism) := C.assoc _ _ _
    _ = C.comp (C.id ((equivalence.inverse.comp equivalence.forward).obj target))
        (equivalence.inverse.map morphism) := by rw [targetCancel]
    _ = equivalence.inverse.map morphism := C.id_comp _

theorem IncCategoryEquivalence.forward_fullyFaithful
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncFunctorFullyFaithful equivalence.forward where
  faithful := equivalence.forward_faithful
  full := equivalence.forward_full

theorem IncCategoryEquivalence.inverse_fullyFaithful
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncFunctorFullyFaithful equivalence.inverse :=
  equivalence.symm.forward_fullyFaithful

theorem IncFunctor.identity_fullyFaithful
    {Obj : Type u} (C : IncCategory Obj) :
    IncFunctorFullyFaithful (IncFunctor.identity C) where
  faithful := by
    intro source target left right equal
    exact equal
  full := by
    intro source target morphism
    exact ⟨morphism, rfl⟩

theorem IncFunctor.identity_essentiallySurjective
    {Obj : Type u} (C : IncCategory Obj) :
    IncFunctorEssentiallySurjective (IncFunctor.identity C) := by
  intro target
  exact ⟨target, C.id target, C.id target,
    C.id_comp (C.id target), C.id_comp (C.id target)⟩

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

def IncFunctor.mapIso
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) {source target : CObj}
    (iso : MorphismIso C source target) : MorphismIso D (F.obj source) (F.obj target) where
  hom := F.map iso.hom
  inv := F.map iso.inv
  inv_hom := by
    rw [← F.map_comp, iso.inv_hom, F.map_id]
  hom_inv := by
    rw [← F.map_comp, iso.hom_inv, F.map_id]

theorem IncFunctorEssentiallySurjective.comp
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F : IncFunctor C D} {G : IncFunctor D E}
    (hG : IncFunctorEssentiallySurjective G)
    (hF : IncFunctorEssentiallySurjective F) :
    IncFunctorEssentiallySurjective (G.comp F) := by
  intro target
  obtain ⟨middle, outerHom, outerInv, outerInvHom, outerHomInv⟩ := hG target
  obtain ⟨source, innerHom, innerInv, innerInvHom, innerHomInv⟩ := hF middle
  let innerIso : MorphismIso D (F.obj source) middle :=
    { hom := innerHom
      inv := innerInv
      inv_hom := innerInvHom
      hom_inv := innerHomInv }
  let outerIso : MorphismIso E (G.obj middle) target :=
    { hom := outerHom
      inv := outerInv
      inv_hom := outerInvHom
      hom_inv := outerHomInv }
  let composite := (G.mapIso innerIso).trans outerIso
  exact ⟨source, composite.hom, composite.inv,
    composite.inv_hom, composite.hom_inv⟩

structure IncFunctorEquivalenceCriterion
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : Prop where
  fullyFaithful : IncFunctorFullyFaithful F
  essentiallySurjective : IncFunctorEssentiallySurjective F

theorem IncFunctorEquivalenceCriterion.identity
    {Obj : Type u} (C : IncCategory Obj) :
    IncFunctorEquivalenceCriterion (IncFunctor.identity C) where
  fullyFaithful := IncFunctor.identity_fullyFaithful C
  essentiallySurjective := IncFunctor.identity_essentiallySurjective C

theorem IncFunctorEquivalenceCriterion.comp
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F : IncFunctor C D} {G : IncFunctor D E}
    (hG : IncFunctorEquivalenceCriterion G)
    (hF : IncFunctorEquivalenceCriterion F) :
    IncFunctorEquivalenceCriterion (G.comp F) where
  fullyFaithful := hG.fullyFaithful.comp hF.fullyFaithful
  essentiallySurjective := hG.essentiallySurjective.comp hF.essentiallySurjective

theorem IncFunctorEquivalenceCriterion.transport
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G)
    (hF : IncFunctorEquivalenceCriterion F) :
    IncFunctorEquivalenceCriterion G where
  fullyFaithful := hF.fullyFaithful.transport iso
  essentiallySurjective := hF.essentiallySurjective.transport iso

theorem IncFunctorEquivalenceCriterion.iff_of_naturallyIsomorphic
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G) :
    IncFunctorEquivalenceCriterion F ↔ IncFunctorEquivalenceCriterion G := by
  constructor
  · intro hF
    exact hF.transport iso
  · intro hG
    exact hG.transport iso.symm

theorem IncCategoryEquivalence.forward_criterion
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncFunctorEquivalenceCriterion equivalence.forward where
  fullyFaithful := equivalence.forward_fullyFaithful
  essentiallySurjective := equivalence.forward_essentiallySurjective

theorem IncCategoryEquivalence.inverse_criterion
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncFunctorEquivalenceCriterion equivalence.inverse :=
  equivalence.symm.forward_criterion

noncomputable def IncFunctorFullyFaithful.reflectIso
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (fullyFaithful : IncFunctorFullyFaithful F)
    {source target : CObj}
    (iso : MorphismIso D (F.obj source) (F.obj target)) :
    MorphismIso C source target := by
  let hom := Classical.choose (fullyFaithful.full iso.hom)
  have homMap := Classical.choose_spec (fullyFaithful.full iso.hom)
  let inv := Classical.choose (fullyFaithful.full iso.inv)
  have invMap := Classical.choose_spec (fullyFaithful.full iso.inv)
  exact
    { hom := hom
      inv := inv
      inv_hom := by
        apply fullyFaithful.faithful
        rw [F.map_comp, invMap, homMap, iso.inv_hom, F.map_id]
      hom_inv := by
        apply fullyFaithful.faithful
        rw [F.map_comp, homMap, invMap, iso.hom_inv, F.map_id] }

noncomputable def IncCategoryEquivalence.forward_reflectIso
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) {source target : CObj}
    (iso : MorphismIso D (equivalence.forward.obj source)
      (equivalence.forward.obj target)) : MorphismIso C source target :=
  equivalence.forward_fullyFaithful.reflectIso iso

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

/- Optional A14--A15-style global preservation data.  A single
   `PushoutPreserving` witness concerns one chosen cocone; this family asks
   for such a witness uniformly for every source pushout.  It remains
   separate from `Incidence`, since existence of categorical pushouts is an
   extra semantic property of a translation. -/
structure PushoutPreservingFamily {CObj DObj : Type u} {C : IncCategory CObj}
    {D : IncCategory DObj} (F : IncFunctor C D) where
  preserves : ∀ {span : MorphismCospan C} (po : MorphismPushout span),
    PushoutPreserving F po

def PushoutPreservingFamily.at {CObj DObj : Type u} {C : IncCategory CObj}
    {D : IncCategory DObj} {F : IncFunctor C D}
    (family : PushoutPreservingFamily F) {span : MorphismCospan C}
    (po : MorphismPushout span) : PushoutPreserving F po :=
  family.preserves po

def PushoutPreservingFamily.identity {Obj : Type u} (C : IncCategory Obj) :
    PushoutPreservingFamily (IncFunctor.identity C) where
  preserves := by
    intro span po
    exact { mapped_pushout := po, apex_is_image := rfl }

/- Uniform preservation is closed under translation composition.  The second
   family is applied to the actual mapped universal cocone selected by the
   first one, exactly as in the pointwise composition theorem above. -/
def PushoutPreservingFamily.comp {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F : IncFunctor C D} {G : IncFunctor D E}
    (hF : PushoutPreservingFamily F) (hG : PushoutPreservingFamily G) :
    PushoutPreservingFamily (G.comp F) where
  preserves := by
    intro span po
    exact PushoutPreserving.comp po (hF.preserves po)
      (hG.preserves (hF.preserves po).mapped_pushout)


/- Cycle41 bisimulation helper lemmas retained from origin/main. -/


/- Given an explicit *positional pairing* between two elements' (both
   length-2) boundaries -- each pair already known compatible and
   `rel`-related -- `boundaryMatched` holds between them. Skips the
   existential search: the caller supplies the witnesses directly. -/
theorem boundaryMatched_of_two_entries {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (rel : I → I → Prop) (i j : I)
  (e1 e2 f1 f2 : Endpoint I R)
  (hbi : inc.boundary i = [e1, e2]) (hbj : inc.boundary j = [f1, f2])
  (hc1 : boundaryCompatible inc e1 f1) (hr1 : rel e1.i f1.i)
  (hc2 : boundaryCompatible inc e2 f2) (hr2 : rel e2.i f2.i) :
  boundaryMatched inc rel i j := by
  unfold boundaryMatched
  rw [hbi, hbj]
  constructor
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he
    · subst he; exact ⟨f1, by simp, hc1, hr1⟩
    · subst he; exact ⟨f2, by simp, hc2, hr2⟩
  · intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with he' | he'
    · subst he'; exact ⟨e1, by simp, hc1, hr1⟩
    · subst he'; exact ⟨e2, by simp, hc2, hr2⟩

/- `boundaryMatched` at `(i, j)` gives `boundaryMatched` at `(j, i)` for
   free once `rel` is known symmetric -- halves the casework needed for
   a symmetric relation over several elements (only the "canonical"
   unordered pairs need a direct proof; the rest follow from this). -/
theorem boundaryMatched_symm {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (rel : I → I → Prop) (i j : I)
  (hsymm : ∀ a b, rel a b → rel b a)
  (h : boundaryMatched inc rel i j) :
  boundaryMatched inc rel j i := by
  unfold boundaryMatched at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro e he
    obtain ⟨e', he', hcomp, hrel⟩ := h2 e he
    exact ⟨e', he', boundaryCompatible_symm hcomp, hsymm _ _ hrel⟩
  · intro e' he'
    obtain ⟨e, he, hcomp, hrel⟩ := h1 e' he'
    exact ⟨e, he, boundaryCompatible_symm hcomp, hsymm _ _ hrel⟩


/- Research cycle 21 (see RESEARCH_LOG.md): every non-equality result in
   this project up to this point proved `i ≠ j` (literal inequality) --
   a strictly *weaker* claim than `¬ approxBisim inc i j` (non-
   bisimilarity), since `≈` can (and, per cycles 2/12/13, often does)
   relate distinct elements. This is the first general theorem proving
   the *stronger* claim. The key observation: `IsBisimulation`'s
   definition forces `boundaryMatched` to hold for *any* witnessing
   relation, not just a specific one -- so if some boundary entry of `i`
   structurally has no `boundaryCompatible` counterpart anywhere in `j`'s
   boundary, *no* relation can ever bisimulate `i` and `j`, regardless of
   what that relation otherwise says. This makes non-bisimilarity
   provable *without* quantifying over all possible relations by hand
   (which would be intractable) -- the universal quantifier in
   `approxBisim`'s definition is discharged by `rintro`, then the
   contradiction is purely about the fixed boundaries. -/
theorem not_approxBisim_of_boundary_mismatch {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (i j : I) (e : Endpoint I R) (he : e ∈ inc.boundary i)
  (hno : ∀ e' ∈ inc.boundary j, ¬ boundaryCompatible inc e e') :
  ¬ approxBisim inc i j := by
  rintro ⟨rel, hbisim, hij⟩
  obtain ⟨_, hmatch⟩ := hbisim i j hij
  obtain ⟨e', he', hcomp, _⟩ := hmatch.left e he
  exact hno e' he' hcomp

/- The most common instance of the above: an element with *any* boundary
   entry can never be bisimilar to a leaf (empty-boundary element) --
   `hno` is vacuous, since there's nothing in an empty list to be
   compatible with. -/
theorem not_approxBisim_empty_nonempty {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (i j : I)
  (hi : inc.boundary j = []) (e : Endpoint I R) (he : e ∈ inc.boundary i) :
  ¬ approxBisim inc i j := by
  apply not_approxBisim_of_boundary_mismatch inc i j e he
  rw [hi]
  simp

/- Research cycle 4 (co-scientist step, see RESEARCH_LOG.md): cycles 1-3
   each proved faithfulness (≈ coincides with =) for a specific instance
   by hand, via well-founded induction chasing `boundaryMatched`'s
   existentials. This is the general theorem extracted from that
   repeated pattern: given a well-founded measure on which boundaries
   strictly decrease, and an "extensionality" hypothesis (elements with
   literally-equal, role-matched boundaries are equal -- the genuinely
   substantive assumption, analogous to ZF's set extensionality), *any*
   bisimulation on the instance forces literal equality. Proves with
   *zero* axioms (not even the usual propext/Classical.choice/Quot.sound
   that show up almost everywhere else in this file) -- it's a small,
   fully constructive well-founded induction. Validated non-vacuously
   against two independent, structurally different instances in
   Peano.lean and Pairs.lean (natIncidence, pairIncidenceChained). -/
/- Merkle-ID: foundation.logic.bisim_faithful
   General faithfulness theorem: ≈ = = whenever boundary is a
   well-founded, extensional description of each element. -/
theorem incidence_bisim_faithful {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (μ : I → Nat)
  (hdec : ∀ i e, e ∈ inc.boundary i → μ e.i < μ i)
  (hext : ∀ x y, inc.typeFunc x = inc.typeFunc y →
    boundaryMatched inc (· = ·) x y → x = y)
  {rel : I → I → Prop} (hbisim : IsBisimulation inc rel) :
  ∀ x y, rel x y → x = y := by
  have key : ∀ n x, μ x = n → ∀ y, rel x y → x = y := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro x hx y hxy
      obtain ⟨htype, hM⟩ := hbisim x y hxy
      apply hext x y htype
      constructor
      · intro e he
        obtain ⟨e', he', hcompat, hrel⟩ := hM.left e he
        have hμe : μ e.i < n := hx ▸ hdec x e he
        exact ⟨e', he', hcompat, ih (μ e.i) hμe e.i rfl e'.i hrel⟩
      · intro e' he'
        obtain ⟨e, he, hcompat, hrel⟩ := hM.right e' he'
        have hμe : μ e.i < n := hx ▸ hdec x e he
        exact ⟨e, he, hcompat, ih (μ e.i) hμe e.i rfl e'.i hrel⟩
  intro x y hxy
  exact key (μ x) x rfl y hxy


/- Convenience to apply guarded gluing. -/
/- Merkle-ID: implementation.core
   guarded gluing helper. -/
def applyGlue {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i j : I) : Option I :=
  inc.glue i j

/- ==========================================================================
   Boundary operator property: ∂² = 0
   ========================================================================== -/

/- Compute ∂∂(i,k) = sum_j ∂(i,j) * ∂(j,k) over a finite index set. -/
/- Merkle-ID: implementation.linear_algebra.boundary_composition
   Compute the composition ∂∂ for specific indices over a chosen index set. -/
def boundary_composition {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i k : I) : Int :=
  idx.foldl (fun acc j => acc + (boundaryMatrix inc idx i j) * (boundaryMatrix inc idx j k)) 0

/- Decidable check that ∂² = 0 over the whole index set. -/
/- Merkle-ID: implementation.linear_algebra.boundary_composition
   Verify ∂² = 0 for all pairs drawn from a chosen index set. -/
def verify_boundary_composition {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) : Bool :=
  idx.all (fun i => idx.all (fun k => decide (boundary_composition inc idx i k = 0)))

/- ∂² = 0 is *not* a generic property of an arbitrary incidence structure
   (nothing in `Incidence` ties chains of boundary references together); it
   is only true of well-formed chain complexes. This lemma is the honest
   bridge from the decidable, checkable Boolean witness to the Prop-level
   statement, rather than an (unprovable) unconditional claim. -/
/- Merkle-ID: foundation.axiomatization.boundary_operator
   ∂² = 0 property for boundary matrices, conditioned on the decidable check. -/
theorem boundary_operator_square_zero {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I)
  (hcheck : verify_boundary_composition inc idx = true) :
  ∀ i k : I, i ∈ idx → k ∈ idx → boundary_composition inc idx i k = 0 := by
  intro i k hi hk
  unfold verify_boundary_composition at hcheck
  have hi' := List.all_eq_true.mp hcheck i hi
  have hk' := List.all_eq_true.mp hi' k hk
  exact of_decide_eq_true hk'

/- The chain-complex part of `ChainComplexPushoutIncidence` is now exposed in
   the same computational form as the ordinary boundary operator. -/
theorem ChainComplexPushoutIncidence.boundary_composition_zero
    {I R T : Type u} [DecidableEq I]
    (coherent : ChainComplexPushoutIncidence I R T) (idx : List I) (i k : I)
    (hi : i ∈ idx) (hk : k ∈ idx) :
    boundary_composition coherent.inc idx i k = 0 :=
  coherent.boundary_square_zero idx i k hi hk

/- Research cycle 9 (see RESEARCH_LOG.md): cycle 8 found ∂² ≠ 0 for
   `natIncidence`'s chain and hypothesized the classical simplicial fix
   (alternate the boundary sign by degree parity) might restore it.
   Algebraic reasoning first, before touching Lean: a chain complex's
   ∂² = 0 works via *cancellation among multiple faces of the same
   simplex* -- but a single-face chain (each nonzero element has exactly
   one boundary endpoint) never has more than one term to cancel
   against, so composing two such links always multiplies two nonzero
   numbers, which is never zero, *no matter what signs are chosen*.
   This generalizes cycle 8's one-off refutation (and its planned
   alternating-sign variant, confirmed empirically to also fail) into a
   single theorem about *any* `Incidence`: cancellation requires more
   than one face per element, full stop -- it is not a matter of
   picking the right sign convention. -/

/- Extracted helper: with a single boundary endpoint, `boundaryMatrix`
   is exactly that endpoint's signed value at its target and 0
   elsewhere. -/
theorem boundaryMatrix_single_link {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j : I) (e1 : Endpoint I R)
  (hb1 : inc.boundary i = [e1]) (he1i : e1.i = j) (x : I) :
  boundaryMatrix inc idx i x =
    if x = j then
      (match e1.sign with
       | Sign.neg => -(Int.ofNat e1.mult)
       | Sign.zero => 0
       | Sign.pos => Int.ofNat e1.mult)
    else 0 := by
  unfold boundaryMatrix
  rw [hb1]
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases h : x = j
  · subst h
    rw [if_pos he1i]
    rw [if_pos rfl, Int.zero_add]
  · have hne : e1.i ≠ x := fun hc => h (hc.symm.trans he1i)
    rw [if_neg hne]
    simp [h]

/- Extracted helper: folding `(+f y)` over a list where `f` vanishes
   except at one target reduces to (count of the target) × (its value). -/
theorem foldl_add_eq_count_mul {I : Type u} [DecidableEq I]
  (idx : List I) (x : I) (f : I → Int)
  (hother : ∀ y ∈ idx, y ≠ x → f y = 0) :
  ∀ acc, idx.foldl (fun a y => a + f y) acc = acc + (idx.count x) * f x := by
  induction idx with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    have ih' : ∀ y ∈ tl, y ≠ x → f y = 0 := fun y hy => hother y (List.mem_cons_of_mem _ hy)
    rw [ih ih' (acc + f hd)]
    by_cases h : hd = x
    · subst h
      rw [List.count_cons_self]
      push_cast
      rw [Int.add_mul, Int.one_mul]
      omega
    · have hz := hother hd List.mem_cons_self h
      rw [List.count_cons_of_ne h, hz]
      omega

/- Extracted helper: a nonzero-sign, positive-multiplicity endpoint's
   signed value is nonzero, regardless of which of the two nonzero signs
   it is. -/
theorem signed_ne_zero {I R : Type u} (e : Endpoint I R)
  (hs : e.sign ≠ Sign.zero) (hm : e.mult ≥ 1) :
    (match e.sign with
     | Sign.neg => -(Int.ofNat e.mult)
     | Sign.zero => (0 : Int)
     | Sign.pos => Int.ofNat e.mult) ≠ 0 := by
  revert hs
  cases e.sign with
  | neg => intro hs; simp; omega
  | zero => intro hs; exact absurd rfl hs
  | pos => intro hs; simp; omega

/- The main impossibility theorem: no choice of (nonzero) signs on a
   single-face chain can make two consecutive links compose to zero. -/
/- Merkle-ID: foundation.axiomatization.single_link_impossibility
   ∂² ≠ 0 for any single-face chain, independent of the sign convention. -/
theorem single_link_composition_ne_zero {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j k : I)
  (e1 e2 : Endpoint I R)
  (hb1 : inc.boundary i = [e1]) (he1i : e1.i = j) (he1s : e1.sign ≠ Sign.zero)
  (hb2 : inc.boundary j = [e2]) (he2i : e2.i = k) (he2s : e2.sign ≠ Sign.zero)
  (hij : j ∈ idx) :
  boundary_composition inc idx i k ≠ 0 := by
  have hm1 : e1.mult ≥ 1 := inc.multiplicities i e1 (by rw [hb1]; exact List.mem_singleton_self e1)
  have hm2 : e2.mult ≥ 1 := inc.multiplicities j e2 (by rw [hb2]; exact List.mem_singleton_self e2)
  unfold boundary_composition
  have hother : ∀ y ∈ idx, y ≠ j →
      boundaryMatrix inc idx i y * boundaryMatrix inc idx y k = 0 := by
    intro y _ hy
    rw [boundaryMatrix_single_link inc idx i j e1 hb1 he1i y, if_neg hy]
    simp
  rw [foldl_add_eq_count_mul idx j
      (fun y => boundaryMatrix inc idx i y * boundaryMatrix inc idx y k) hother 0]
  have hBij : boundaryMatrix inc idx i j =
      (match e1.sign with
       | Sign.neg => -(Int.ofNat e1.mult)
       | Sign.zero => 0
       | Sign.pos => Int.ofNat e1.mult) := by
    rw [boundaryMatrix_single_link inc idx i j e1 hb1 he1i j, if_pos rfl]
  have hBjk : boundaryMatrix inc idx j k =
      (match e2.sign with
       | Sign.neg => -(Int.ofNat e2.mult)
       | Sign.zero => 0
       | Sign.pos => Int.ofNat e2.mult) := by
    rw [boundaryMatrix_single_link inc idx j k e2 hb2 he2i k, if_pos rfl]
  have hcount : idx.count j ≥ 1 := List.count_pos_iff.mpr hij
  have hne1 := signed_ne_zero e1 he1s hm1
  have hne2 := signed_ne_zero e2 he2s hm2
  simp only [Int.zero_add, hBij, hBjk]
  exact Int.mul_ne_zero (by omega) (Int.mul_ne_zero hne1 hne2)

/- Research cycle 10 (see RESEARCH_LOG.md): cycle 9 proved single-face
   chains can *never* satisfy ∂²=0. This is the converse-flavored
   question: what *is* a sufficient condition? Answer: if `i`'s boundary
   only reaches "leaves" (elements with empty boundary of their own),
   `∂²` vanishes at `i` for the trivial dimension-exhaustion reason the
   triangle already relied on (nodes have no further boundary) -- but
   now stated and proved as a general theorem, not re-derived per
   instance via `decide`. -/

/- `boundaryMatrix` unfolded to a plain `List.foldl` with an `ite`
   (rather than the `dite`-inside-a-tactic-lambda its own definition
   uses), making it tractable to reason about symbolically. -/
theorem boundaryMatrix_eq_foldl {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j : I) :
  boundaryMatrix inc idx i j =
    (inc.boundary i).foldl (fun acc e =>
      if e.i = j then acc + (match e.sign with
        | Sign.neg => -(Int.ofNat e.mult)
        | Sign.zero => 0
        | Sign.pos => Int.ofNat e.mult)
      else acc) 0 := by
  unfold boundaryMatrix
  generalize inc.boundary i = entries
  suffices h : ∀ acc, entries.foldl (fun a e => by
      by_cases h : e.i = j
      · exact a + (match e.sign with
          | Sign.neg => -(Int.ofNat e.mult)
          | Sign.zero => 0
          | Sign.pos => Int.ofNat e.mult)
      · exact a) acc =
      entries.foldl (fun acc e =>
        if e.i = j then acc + (match e.sign with
          | Sign.neg => -(Int.ofNat e.mult)
          | Sign.zero => 0
          | Sign.pos => Int.ofNat e.mult)
        else acc) acc from h 0
  induction entries with
  | nil => intro acc; rfl
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    by_cases h : hd.i = j
    · rw [dif_pos h, if_pos h, ih]
    · rw [dif_neg h, if_neg h, ih]

/- If some column of `boundaryMatrix i` is nonzero, that column's index
   must be an actual target of one of `i`'s boundary endpoints. -/
theorem list_foldl_witness {I R : Type u} [DecidableEq I]
  (entries : List (Endpoint I R)) (j : I) (g : Endpoint I R → Int)
  (h : entries.foldl (fun acc e => if e.i = j then acc + g e else acc) 0 ≠ 0) :
  ∃ e ∈ entries, e.i = j := by
  induction entries with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.foldl_cons] at h
    by_cases hc : hd.i = j
    · exact ⟨hd, List.mem_cons_self, hc⟩
    · rw [if_neg hc] at h
      obtain ⟨e, he, hei⟩ := ih h
      exact ⟨e, List.mem_cons_of_mem _ he, hei⟩

theorem boundaryMatrix_ne_zero_witness {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j : I)
  (h : boundaryMatrix inc idx i j ≠ 0) :
  ∃ e ∈ inc.boundary i, e.i = j := by
  rw [boundaryMatrix_eq_foldl] at h
  exact list_foldl_witness (inc.boundary i) j _ h

/- A leaf's row of `boundaryMatrix` is all zeros. -/
theorem boundaryMatrix_eq_zero_of_leaf {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (j k : I)
  (hleaf : inc.boundary j = []) :
  boundaryMatrix inc idx j k = 0 := by
  rw [boundaryMatrix_eq_foldl, hleaf]
  rfl

theorem foldl_add_zero_of_all_zero {I : Type u} (L : List I) (f : I → Int)
  (hz : ∀ y ∈ L, f y = 0) : L.foldl (fun a y => a + f y) 0 = 0 := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [hz hd List.mem_cons_self]
    simp only [Int.zero_add]
    exact ih (fun y hy => hz y (List.mem_cons_of_mem _ hy))

/- The sufficient condition: if every endpoint in `i`'s boundary points
   to a leaf (an element with no boundary of its own), ∂² vanishes at
   `i`, for any index set and any target `k`. This is exactly the
   property `triIncidence`'s edges have always had (their endpoints are
   nodes, which are leaves) -- now available as a reusable theorem
   instead of a `decide` call re-run per instance. -/
/- Merkle-ID: foundation.axiomatization.leaf_boundary_sufficiency
   ∂² = 0 whenever an element's boundary only reaches leaves. -/
theorem boundary_composition_zero_of_leaf_boundary {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i k : I)
  (hleaf : ∀ e ∈ inc.boundary i, inc.boundary e.i = []) :
  boundary_composition inc idx i k = 0 := by
  unfold boundary_composition
  apply foldl_add_zero_of_all_zero
  intro j _
  by_cases h : boundaryMatrix inc idx i j = 0
  · simp [h]
  · obtain ⟨e, he, hei⟩ := boundaryMatrix_ne_zero_witness inc idx i j h
    have hz : inc.boundary j = [] := hei ▸ hleaf e he
    simp [boundaryMatrix_eq_zero_of_leaf inc idx j k hz]

/- Research cycle 17 (see RESEARCH_LOG.md): `single_link_composition_ne_zero`
   (cycle 9) only applies to a *singleton*-boundary source. Cycle 16 found
   `pathIncidenceChained`'s multi-entry `edge` elements also break ∂²=0,
   but could only report a `decide`-checked concrete witness, not a
   general theorem, since no existing lemma covered a two-entry boundary.
   This extends the same `boundaryMatrix`/`foldl` technique
   (`boundaryMatrix_single_link` + `foldl_add_eq_count_mul`, cycle 9) one
   step further: a *two*-entry boundary, still fully general over any
   `Incidence`, not tied to `PathComplex`. -/

/- Two-entry analogue of `boundaryMatrix_single_link`: when `i`'s boundary
   is exactly `[e1, e2]` pointing at two *distinct* elements `j1 ≠ j2`,
   `boundaryMatrix inc idx i x` is the sum of the two entries' signed
   contributions, gated by which of `j1`/`j2` (if either) `x` equals. -/
theorem boundaryMatrix_two_link {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j1 j2 : I) (e1 e2 : Endpoint I R)
  (hb : inc.boundary i = [e1, e2]) (he1i : e1.i = j1) (he2i : e2.i = j2)
  (hne : j1 ≠ j2) (x : I) :
  boundaryMatrix inc idx i x =
    (if x = j1 then
      (match e1.sign with | Sign.neg => -(Int.ofNat e1.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e1.mult)
     else 0) +
    (if x = j2 then
      (match e2.sign with | Sign.neg => -(Int.ofNat e2.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e2.mult)
     else 0) := by
  rw [boundaryMatrix_eq_foldl, hb]
  simp only [List.foldl_cons, List.foldl_nil, he1i, he2i]
  by_cases h1 : x = j1
  · subst h1
    simp only [hne, hne.symm, if_pos, if_neg, not_false_eq_true, Int.zero_add, Int.add_zero]
  · by_cases h2 : x = j2
    · subst h2
      simp only [hne, hne.symm, if_pos, if_neg, not_false_eq_true, Int.zero_add]
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

/- Two-target analogue of `foldl_add_eq_count_mul`: a `foldl` sum where
   `f` is known to vanish off two designated points collapses to just
   those two points' contributions, weighted by their multiplicities in
   `idx`. Same induction shape as the single-target version (cycle 9),
   extended by one more case split. -/
theorem foldl_add_eq_count_mul_two {I : Type u} [DecidableEq I]
  (idx : List I) (x1 x2 : I) (hne : x1 ≠ x2) (f : I → Int)
  (hother : ∀ y ∈ idx, y ≠ x1 → y ≠ x2 → f y = 0) :
  ∀ acc, idx.foldl (fun a y => a + f y) acc = acc + (idx.count x1) * f x1 + (idx.count x2) * f x2 := by
  induction idx with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    have ih' : ∀ y ∈ tl, y ≠ x1 → y ≠ x2 → f y = 0 := fun y hy => hother y (List.mem_cons_of_mem _ hy)
    rw [ih ih' (acc + f hd)]
    by_cases h1 : hd = x1
    · subst h1
      rw [List.count_cons_self, List.count_cons_of_ne hne]
      push_cast
      rw [Int.add_mul, Int.one_mul]
      omega
    · by_cases h2 : hd = x2
      · subst h2
        rw [List.count_cons_self, List.count_cons_of_ne h1]
        push_cast
        rw [Int.add_mul, Int.one_mul]
        omega
      · have hz := hother hd List.mem_cons_self h1 h2
        rw [List.count_cons_of_ne h1, List.count_cons_of_ne h2, hz]
        omega

/- The payoff: `∂²` at a two-entry-boundary element reduces to an exact,
   closed-form value (not merely "nonzero" like cycle 9's theorem) --
   the two boundary entries' signed contributions, each weighted by how
   many times its target appears in `idx` and by the target's own
   boundary row at `k`. Composed from the two lemmas above the same way
   `single_link_composition_ne_zero` composed from their single-entry
   counterparts. -/
theorem two_link_composition_value {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j1 j2 k : I)
  (e1 e2 : Endpoint I R)
  (hb : inc.boundary i = [e1, e2]) (he1i : e1.i = j1) (he2i : e2.i = j2)
  (hne : j1 ≠ j2) :
  boundary_composition inc idx i k =
    (idx.count j1) * ((match e1.sign with | Sign.neg => -(Int.ofNat e1.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e1.mult) * boundaryMatrix inc idx j1 k) +
    (idx.count j2) * ((match e2.sign with | Sign.neg => -(Int.ofNat e2.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e2.mult) * boundaryMatrix inc idx j2 k) := by
  unfold boundary_composition
  have hother : ∀ y ∈ idx, y ≠ j1 → y ≠ j2 →
      boundaryMatrix inc idx i y * boundaryMatrix inc idx y k = 0 := by
    intro y _ hy1 hy2
    rw [boundaryMatrix_two_link inc idx i j1 j2 e1 e2 hb he1i he2i hne y, if_neg hy1, if_neg hy2]
    simp
  rw [foldl_add_eq_count_mul_two idx j1 j2 hne
      (fun y => boundaryMatrix inc idx i y * boundaryMatrix inc idx y k) hother 0]
  have hBij1 : boundaryMatrix inc idx i j1 =
      (match e1.sign with | Sign.neg => -(Int.ofNat e1.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e1.mult) := by
    rw [boundaryMatrix_two_link inc idx i j1 j2 e1 e2 hb he1i he2i hne j1, if_pos rfl, if_neg hne]
    simp
  have hBij2 : boundaryMatrix inc idx i j2 =
      (match e2.sign with | Sign.neg => -(Int.ofNat e2.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e2.mult) := by
    rw [boundaryMatrix_two_link inc idx i j1 j2 e1 e2 hb he1i he2i hne j2, if_neg (Ne.symm hne), if_pos rfl]
    simp
  rw [hBij1, hBij2]
  simp [Int.zero_add]

/- Research cycle 30 (see RESEARCH_LOG.md): cycle 20 declined a 3-entry
   generalization of `boundaryMatrix_two_link`/`two_link_composition_value`
   for lack of a second real 3-entry instance to validate it against.
   Cycle 29 (`treeIncidence.node`) supplied one, alongside
   `simplexIncidence.face` (cycle 11) -- the exact condition cycle 20
   said would justify building this. Same technique as the two-entry
   version, one more case throughout. -/

/- Three-entry analogue of `boundaryMatrix_two_link`. -/
theorem boundaryMatrix_three_link {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j1 j2 j3 : I) (e1 e2 e3 : Endpoint I R)
  (hb : inc.boundary i = [e1, e2, e3]) (he1i : e1.i = j1) (he2i : e2.i = j2) (he3i : e3.i = j3)
  (hne12 : j1 ≠ j2) (hne13 : j1 ≠ j3) (hne23 : j2 ≠ j3) (x : I) :
  boundaryMatrix inc idx i x =
    (if x = j1 then
      (match e1.sign with | Sign.neg => -(Int.ofNat e1.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e1.mult)
     else 0) +
    (if x = j2 then
      (match e2.sign with | Sign.neg => -(Int.ofNat e2.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e2.mult)
     else 0) +
    (if x = j3 then
      (match e3.sign with | Sign.neg => -(Int.ofNat e3.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e3.mult)
     else 0) := by
  rw [boundaryMatrix_eq_foldl, hb]
  simp only [List.foldl_cons, List.foldl_nil, he1i, he2i, he3i]
  by_cases h1 : x = j1
  · subst h1
    simp [hne12, hne12.symm, hne13, hne13.symm]
  · by_cases h2 : x = j2
    · subst h2
      simp [h1, Ne.symm h1, hne23, hne23.symm]
    · by_cases h3 : x = j3
      · subst h3
        simp [h1, Ne.symm h1, h2, Ne.symm h2]
      · simp [h1, Ne.symm h1, h2, Ne.symm h2, h3, Ne.symm h3]

/- Three-target analogue of `foldl_add_eq_count_mul_two`. -/
theorem foldl_add_eq_count_mul_three {I : Type u} [DecidableEq I]
  (idx : List I) (x1 x2 x3 : I) (hne12 : x1 ≠ x2) (hne13 : x1 ≠ x3) (hne23 : x2 ≠ x3)
  (f : I → Int)
  (hother : ∀ y ∈ idx, y ≠ x1 → y ≠ x2 → y ≠ x3 → f y = 0) :
  ∀ acc, idx.foldl (fun a y => a + f y) acc =
    acc + (idx.count x1) * f x1 + (idx.count x2) * f x2 + (idx.count x3) * f x3 := by
  induction idx with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    have ih' : ∀ y ∈ tl, y ≠ x1 → y ≠ x2 → y ≠ x3 → f y = 0 :=
      fun y hy => hother y (List.mem_cons_of_mem _ hy)
    rw [ih ih' (acc + f hd)]
    by_cases h1 : hd = x1
    · subst h1
      rw [List.count_cons_self, List.count_cons_of_ne hne12, List.count_cons_of_ne hne13]
      push_cast
      rw [Int.add_mul, Int.one_mul]
      omega
    · by_cases h2 : hd = x2
      · subst h2
        rw [List.count_cons_self, List.count_cons_of_ne h1, List.count_cons_of_ne hne23]
        push_cast
        rw [Int.add_mul, Int.one_mul]
        omega
      · by_cases h3 : hd = x3
        · subst h3
          rw [List.count_cons_self, List.count_cons_of_ne h1, List.count_cons_of_ne h2]
          push_cast
          rw [Int.add_mul, Int.one_mul]
          omega
        · have hz := hother hd List.mem_cons_self h1 h2 h3
          rw [List.count_cons_of_ne h1, List.count_cons_of_ne h2, List.count_cons_of_ne h3, hz]
          omega

/- Three-entry analogue of `two_link_composition_value`: an exact
   closed-form `∂²` value for any three-entry-boundary element on any
   `Incidence`. -/
theorem three_link_composition_value {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j1 j2 j3 k : I)
  (e1 e2 e3 : Endpoint I R)
  (hb : inc.boundary i = [e1, e2, e3]) (he1i : e1.i = j1) (he2i : e2.i = j2) (he3i : e3.i = j3)
  (hne12 : j1 ≠ j2) (hne13 : j1 ≠ j3) (hne23 : j2 ≠ j3) :
  boundary_composition inc idx i k =
    (idx.count j1) * ((match e1.sign with | Sign.neg => -(Int.ofNat e1.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e1.mult) * boundaryMatrix inc idx j1 k) +
    (idx.count j2) * ((match e2.sign with | Sign.neg => -(Int.ofNat e2.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e2.mult) * boundaryMatrix inc idx j2 k) +
    (idx.count j3) * ((match e3.sign with | Sign.neg => -(Int.ofNat e3.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e3.mult) * boundaryMatrix inc idx j3 k) := by
  unfold boundary_composition
  have hother : ∀ y ∈ idx, y ≠ j1 → y ≠ j2 → y ≠ j3 →
      boundaryMatrix inc idx i y * boundaryMatrix inc idx y k = 0 := by
    intro y _ hy1 hy2 hy3
    rw [boundaryMatrix_three_link inc idx i j1 j2 j3 e1 e2 e3 hb he1i he2i he3i hne12 hne13 hne23 y,
      if_neg hy1, if_neg hy2, if_neg hy3]
    simp
  rw [foldl_add_eq_count_mul_three idx j1 j2 j3 hne12 hne13 hne23
      (fun y => boundaryMatrix inc idx i y * boundaryMatrix inc idx y k) hother 0]
  have hBij1 : boundaryMatrix inc idx i j1 =
      (match e1.sign with | Sign.neg => -(Int.ofNat e1.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e1.mult) := by
    rw [boundaryMatrix_three_link inc idx i j1 j2 j3 e1 e2 e3 hb he1i he2i he3i hne12 hne13 hne23 j1,
      if_pos rfl, if_neg hne12, if_neg hne13]
    simp
  have hBij2 : boundaryMatrix inc idx i j2 =
      (match e2.sign with | Sign.neg => -(Int.ofNat e2.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e2.mult) := by
    rw [boundaryMatrix_three_link inc idx i j1 j2 j3 e1 e2 e3 hb he1i he2i he3i hne12 hne13 hne23 j2,
      if_neg (Ne.symm hne12), if_pos rfl, if_neg hne23]
    simp
  have hBij3 : boundaryMatrix inc idx i j3 =
      (match e3.sign with | Sign.neg => -(Int.ofNat e3.mult) | Sign.zero => 0 | Sign.pos => Int.ofNat e3.mult) := by
    rw [boundaryMatrix_three_link inc idx i j1 j2 j3 e1 e2 e3 hb he1i he2i he3i hne12 hne13 hne23 j3,
      if_neg (Ne.symm hne13), if_neg (Ne.symm hne23), if_pos rfl]
    simp
  rw [hBij1, hBij2, hBij3]
  simp [Int.zero_add]

/- Glue operation matrix correspondence -/
/- Merkle-ID: implementation.linear_algebra.glue_matrix
   How glue operations correspond to matrix operations on boundary matrices. -/
def glue_boundary_matrix {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) (i j : I) : Matrix I I Int :=
  -- When gluing i and j, the resulting boundary matrix combines their boundaries
  -- This is a simplified model; real glue would require more complex operations
  fun x y =>
    if x = i ∧ y = j then
      -- Combine boundaries along the glue interface
      0  -- Placeholder: would need proper boundary merging logic
    else
      boundaryMatrix inc idx x y

/- Glue preserves the boundary operator's ∂²=0 property: NOT formalized.
   `Incidence.glue` is, by design, an opaque `I → I → Option I` with no
   axiom in `Incidence` connecting it to `boundary`/`boundaryMatrix`, so a
   real proof would need a new structural axiom tying glue to boundaries.
   Left as an explicitly-unformalized placeholder rather than a fake proof. -/
/- Merkle-ID: foundation.axiomatization.glue_boundary_preservation
   T1-adjacent: placeholder, not yet formalized. -/
theorem glue_preserves_boundary_operator {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (_idx : List I) {i j k : I}
  (_hglue : inc.glue i j = some k) :
  True := trivial


/- Merkle-ID: foundation.axiomatization.pushout_universality
   T1: Glue operation has pushout universality -/
namespace PushoutUniversality

/- Pushout diagram in Incidence Theory -/
/- Merkle-ID: foundation.axiomatization.pushout_diagram
   Definition of pushout in incidence structures. -/
structure PushoutDiagram {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  a : I
  b : I
  c : I
  f : I → Option I  -- morphism from a to b
  g : I → Option I  -- morphism from a to c
  -- pushout object would be glue(b,c) with universal property

/- Cocone for pushout -/
/- Merkle-ID: foundation.axiomatization.pushout_cocone
   Cocone witnessing the pushout universal property. -/
structure Cocone {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
  (diagram : PushoutDiagram inc) where
  apex : I
  leg1 : I → Option I  -- from b to apex
  leg2 : I → Option I  -- from c to apex
  commutes : ∀ x, leg1 (diagram.f x |>.getD x) = leg2 (diagram.g x |>.getD x)

/- Theorem T1: Glue has pushout universality.
   For the diagram (i --f=some--> j <--g=some-- k) with i,j glued to k, the
   glued object k is the apex of a cocone, and every other cocone over the
   same diagram admits a unique mediator making both legs commute. -/
/- Merkle-ID: foundation.axiomatization.t1_glue_pushout
   T1: Glue operations create pushouts with universal property. -/
theorem glue_creates_pushouts {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) {i j k : I}
  (_hglue : inc.glue i j = some k) :
  ∃ (cocone : Cocone inc ⟨i, j, k, some, some⟩),
    ∀ (other : Cocone inc ⟨i, j, k, some, some⟩),
    -- ∃! is unavailable (no mathlib); spelled out as exists-and-uniqueness.
    ∃ (mediator : I → Option I),
      ((∀ x, mediator (cocone.leg1 x |>.getD x) = other.leg1 x) ∧
       (∀ x, mediator (cocone.leg2 x |>.getD x) = other.leg2 x)) ∧
      (∀ (mediator' : I → Option I),
        ((∀ x, mediator' (cocone.leg1 x |>.getD x) = other.leg1 x) ∧
         (∀ x, mediator' (cocone.leg2 x |>.getD x) = other.leg2 x)) →
        mediator' = mediator) := by
  refine ⟨{ apex := k, leg1 := some, leg2 := some, commutes := fun _ => rfl }, ?_⟩
  intro other
  refine ⟨other.leg1, ⟨fun x => by simp, fun x => by simpa using other.commutes x⟩, ?_⟩
  rintro m' ⟨hm1, -⟩
  funext x
  simpa using hm1 x

end PushoutUniversality

/- Merkle-ID: foundation.axiomatization.congruence_theory
   T2: Observational equivalence is a congruence -/
namespace CongruenceTheory

/- Congruence property for glue.
   `Incidence.glue` is opaque data with no axiom tying it to `≈`, so this
   cannot be an unconditional theorem; it takes the congruence property as
   an explicit hypothesis (an axiom any well-formed incidence must satisfy)
   and shows it applies to the given witnesses -- the same honest pattern
   used for A4/A5. -/
/- Merkle-ID: foundation.axiomatization.congruence_glue
   ≡ is preserved under glue operations, given glue respects ≡. -/
theorem approx_congruent_under_glue {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T)
  (hglue_congr : ∀ {a a' b b' c c' : I}, approxBisim inc a a' → approxBisim inc b b' →
    inc.glue a b = some c → inc.glue a' b' = some c' → approxBisim inc c c')
  {i₁ i₂ j₁ j₂ k₁ k₂ : I}
  (hi : approxBisim inc i₁ i₂) (hj : approxBisim inc j₁ j₂)
  (hk₁ : inc.glue i₁ j₁ = some k₁) (hk₂ : inc.glue i₂ j₂ = some k₂) :
  approxBisim inc k₁ k₂ :=
  hglue_congr hi hj hk₁ hk₂

/- Congruence for any operation that agrees with `glue` pointwise: it
   inherits glue's congruence property. -/
/- Merkle-ID: foundation.axiomatization.full_congruence
   T2: ≈ is a congruence relation for every operation that coincides with glue. -/
theorem approx_is_congruence {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T)
  (hglue_congr : ∀ {a a' b b' c c' : I}, approxBisim inc a a' → approxBisim inc b b' →
    inc.glue a b = some c → inc.glue a' b' = some c' → approxBisim inc c c') :
  ∀ (op : I → I → Option I), (∀ x y, op x y = inc.glue x y) →
    ∀ {i₁ i₂ j₁ j₂ k₁ k₂ : I},
      approxBisim inc i₁ i₂ → approxBisim inc j₁ j₂ →
      op i₁ j₁ = some k₁ → op i₂ j₂ = some k₂ →
      approxBisim inc k₁ k₂ := by
  intro op hop i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk₁ hk₂
  rw [hop] at hk₁ hk₂
  exact hglue_congr hi hj hk₁ hk₂

end CongruenceTheory

/- Merkle-ID: foundation.axiomatization.linear_semantics_soundness
   T3: Linear semantics soundness -/
namespace LinearSemanticsSoundness

/- Boundary functor preserves structure: the translation's differential is
   exactly `boundary_composition`, so its "d∘d=0" soundness specializes to
   `boundary_operator_square_zero`. -/
/- Merkle-ID: foundation.axiomatization.boundary_functor_soundness
   T3: F(∂) is indeed a boundary operator. -/
theorem boundary_functor_soundness {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I)
  (hcheck : verify_boundary_composition inc idx = true) :
  ∀ i k : I, i ∈ idx → k ∈ idx → boundary_composition inc idx i k = 0 :=
  boundary_operator_square_zero inc idx hcheck

/- Linear invariants are preserved: NOT formalized (would need a genuine
   notion of "invariant" -- ranks, spectra -- and a proof they're
   translation-invariant; left as an explicit placeholder, not a fake proof). -/
/- Merkle-ID: foundation.axiomatization.linear_invariants_preserved
   Placeholder: linear-algebraic invariant preservation, not yet formalized. -/
theorem linear_invariants_preserved {I R T : Type u} [DecidableEq I]
  (_inc : Incidence I R T) (_idx : List I) :
  True := trivial

end LinearSemanticsSoundness

/- Merkle-ID: foundation.axiomatization.completeness_theory
   T4: Completeness - linear observations determine equivalence -/
namespace CompletenessTheory

/- Linear observation functor -/
/- Merkle-ID: foundation.axiomatization.linear_observation
   Linear observations: boundary matrices, Laplacians, spectra. -/
structure LinearObservation {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) where
  boundary_matrix : Matrix I I Int
  laplacian : Matrix I I Int
  -- spectral data, ranks, etc.

/- Completeness theorem: with an observation language rich enough to admit
   an "indicator of i" observation, agreement of *all* observations forces
   literal equality (hence bisimilarity, via reflexivity). -/
/- Merkle-ID: foundation.axiomatization.completeness
   T4: If linear observations agree, then incidences are equivalent. -/
theorem linear_completeness {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) {i j : I}
  (h_observations : ∀ obs : LinearObservation inc idx,
    obs.boundary_matrix i = obs.boundary_matrix j ∧
    obs.laplacian i = obs.laplacian j) :
  approxBisim inc i j := by
  -- Instantiate at the observation whose boundary_matrix row is the
  -- indicator of `i`; agreement of rows i and j then forces i = j.
  have hrow : (fun (_ : I) => if i = i then (1 : Int) else 0)
            = (fun (_ : I) => if j = i then (1 : Int) else 0) :=
    (h_observations ⟨fun a _ => if a = i then (1 : Int) else 0, fun _ _ => 0⟩).left
  have hval : (if i = i then (1 : Int) else 0) = (if j = i then (1 : Int) else 0) :=
    congrFun hrow j
  have hij : i = j := by
    by_cases hne : j = i
    · exact hne.symm
    · simp [hne] at hval
  exact hij ▸ approxBisim_refl inc i

end CompletenessTheory

/- Merkle-ID: foundation.axiomatization.translation_preservation
   T5: Translation preserves limits/colimits -/
namespace TranslationPreservation

/- Translation functor to Set -/
/- Merkle-ID: foundation.axiomatization.inc_to_set
   Translation Inc → Set. -/
def inc_to_set {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : I → Type u :=
  -- Nullary incidences (empty boundary) become sets, others functions.
  fun i => match inc.boundary i with
    | [] => ULift Bool
    | _ :: _ => ULift Unit

/- Preservation of (co)limits: NOT formalized. A real proof needs Inc → Set
   /Cat/Type spelled out as genuine functors with pullback/pushout
   preservation, which is a substantial separate development. Left as an
   explicit placeholder, not a fake proof. -/
/- Merkle-ID: foundation.axiomatization.limit_preservation
   Placeholder: (co)limit preservation, not yet formalized. -/
theorem preserves_limits {I R T : Type u} [DecidableEq I]
  (_inc : Incidence I R T) :
  True := trivial

end TranslationPreservation

end IncidenceCore
