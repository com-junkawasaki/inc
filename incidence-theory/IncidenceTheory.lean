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

theorem IncDependentFamily.reindex_id
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) :
    family.reindex id = family.fiber := by
  funext index
  rfl

theorem IncDependentFamily.reindex_comp
    {I R T J K : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) (first : J → I) (second : K → J) :
    family.reindex (first ∘ second) = fun index => family.reindex first (second index) := by
  funext index
  rfl

def IncDependentFamily.reindexProduct
    {I R T J : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) (map : J → I)
    (term : IncDependentProduct family) :
    ∀ index, family.reindex map index :=
  fun index => term (map index)

theorem IncDependentFamily.reindexProduct_id
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc)
    (term : IncDependentProduct family) :
    family.reindexProduct id term = term := by
  funext index
  rfl

theorem IncDependentFamily.reindexProduct_comp
    {I R T J K : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) (first : J → I) (second : K → J)
    (term : IncDependentProduct family) :
    family.reindexProduct (first ∘ second) term =
      fun index => family.reindexProduct first term (second index) := by
  funext index
  rfl

def IncDependentFamily.reindexSum
    {I R T J : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) (map : J → I) :
    Sigma (family.reindex map) → IncDependentSum family
  | ⟨index, value⟩ => ⟨map index, value⟩

theorem IncDependentFamily.reindexSum_id
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) :
    family.reindexSum id = id := by
  funext total
  rcases total with ⟨index, value⟩
  rfl

theorem IncDependentFamily.reindexSum_comp
    {I R T J K : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) (first : J → I) (second : K → J) :
    family.reindexSum (first ∘ second) =
      family.reindexSum first ∘
        (fun total : Sigma (family.reindex (first ∘ second)) =>
          match total with
          | ⟨index, value⟩ =>
              (⟨second index, value⟩ : Sigma (family.reindex first))) := by
  funext total
  rcases total with ⟨index, value⟩
  rfl

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

structure IncDependentFamilyMorphism
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (source target : IncDependentFamily inc) where
  app : ∀ index, source.fiber index → target.fiber index

def IncDependentFamilyMorphism.identity
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) : IncDependentFamilyMorphism family family where
  app := fun _ value => value

def IncDependentFamilyMorphism.comp
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondMap : IncDependentFamilyMorphism second third)
    (firstMap : IncDependentFamilyMorphism first second) :
    IncDependentFamilyMorphism first third where
  app := fun index value => secondMap.app index (firstMap.app index value)

theorem IncDependentFamilyMorphism.ext
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    {first second : IncDependentFamilyMorphism source target}
    (pointwise : ∀ index value, first.app index value = second.app index value) :
    first = second := by
  cases first
  cases second
  congr
  funext index value
  exact pointwise index value

theorem IncDependentFamilyMorphism.identity_comp
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (morphism : IncDependentFamilyMorphism source target) :
    (IncDependentFamilyMorphism.identity target).comp morphism = morphism := by
  apply IncDependentFamilyMorphism.ext
  intro index value
  rfl

theorem IncDependentFamilyMorphism.comp_identity
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (morphism : IncDependentFamilyMorphism source target) :
    morphism.comp (IncDependentFamilyMorphism.identity source) = morphism := by
  apply IncDependentFamilyMorphism.ext
  intro index value
  rfl

theorem IncDependentFamilyMorphism.comp_assoc
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third fourth : IncDependentFamily inc}
    (thirdMap : IncDependentFamilyMorphism third fourth)
    (secondMap : IncDependentFamilyMorphism second third)
    (firstMap : IncDependentFamilyMorphism first second) :
    (thirdMap.comp secondMap).comp firstMap =
      thirdMap.comp (secondMap.comp firstMap) := by
  apply IncDependentFamilyMorphism.ext
  intro index value
  rfl

def IncDependentFamilyMorphism.mapSum
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (morphism : IncDependentFamilyMorphism source target) :
    IncDependentSum source → IncDependentSum target :=
  IncDependentFamily.mapSum morphism.app

def IncDependentFamilyMorphism.mapProduct
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (morphism : IncDependentFamilyMorphism source target) :
    IncDependentProduct source → IncDependentProduct target :=
  IncDependentFamily.mapProduct morphism.app

theorem IncDependentFamilyMorphism.mapSum_comp
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondMap : IncDependentFamilyMorphism second third)
    (firstMap : IncDependentFamilyMorphism first second) :
    (secondMap.comp firstMap).mapSum = secondMap.mapSum ∘ firstMap.mapSum := by
  funext total
  rcases total with ⟨index, value⟩
  rfl

theorem IncDependentFamilyMorphism.mapProduct_comp
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondMap : IncDependentFamilyMorphism second third)
    (firstMap : IncDependentFamilyMorphism first second) :
    (secondMap.comp firstMap).mapProduct =
      secondMap.mapProduct ∘ firstMap.mapProduct := by
  funext value i
  rfl

theorem IncDependentFamilyMorphism.reindexProduct_naturality
    {I R T J : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (morphism : IncDependentFamilyMorphism source target)
    (baseMap : J → I) (term : IncDependentProduct source) :
    target.reindexProduct baseMap (morphism.mapProduct term) =
      fun index => morphism.app (baseMap index)
        (source.reindexProduct baseMap term index) := by
  funext index
  rfl

theorem IncDependentFamilyMorphism.reindexSum_naturality
    {I R T J : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (morphism : IncDependentFamilyMorphism source target)
    (baseMap : J → I) :
    morphism.mapSum ∘ source.reindexSum baseMap =
      target.reindexSum baseMap ∘
        (fun total : Sigma (source.reindex baseMap) =>
          match total with
          | ⟨index, value⟩ =>
              (⟨index, morphism.app (baseMap index) value⟩ :
                Sigma (target.reindex baseMap))) := by
  funext total
  rcases total with ⟨index, value⟩
  rfl

structure IncDependentFamilyIsomorphism
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (source target : IncDependentFamily inc) where
  hom : IncDependentFamilyMorphism source target
  inv : IncDependentFamilyMorphism target source
  inv_hom : ∀ index value, inv.app index (hom.app index value) = value
  hom_inv : ∀ index value, hom.app index (inv.app index value) = value

theorem IncDependentFamilyIsomorphism.ext
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    {first second : IncDependentFamilyIsomorphism source target}
    (homEq : first.hom = second.hom) (invEq : first.inv = second.inv) :
    first = second := by
  cases first
  cases second
  cases homEq
  cases invEq
  rfl

def IncDependentFamilyIsomorphism.refl
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (family : IncDependentFamily inc) :
    IncDependentFamilyIsomorphism family family where
  hom := IncDependentFamilyMorphism.identity family
  inv := IncDependentFamilyMorphism.identity family
  inv_hom := by intro index value; rfl
  hom_inv := by intro index value; rfl

def IncDependentFamilyIsomorphism.symm
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    IncDependentFamilyIsomorphism target source where
  hom := iso.inv
  inv := iso.hom
  inv_hom := iso.hom_inv
  hom_inv := iso.inv_hom

def IncDependentFamilyIsomorphism.trans
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    IncDependentFamilyIsomorphism first third where
  hom := secondIso.hom.comp firstIso.hom
  inv := firstIso.inv.comp secondIso.inv
  inv_hom := by
    intro index value
    change firstIso.inv.app index
      (secondIso.inv.app index
        (secondIso.hom.app index (firstIso.hom.app index value))) = value
    rw [secondIso.inv_hom, firstIso.inv_hom]
  hom_inv := by
    intro index value
    change secondIso.hom.app index
      (firstIso.hom.app index
        (firstIso.inv.app index (secondIso.inv.app index value))) = value
    rw [firstIso.hom_inv, secondIso.hom_inv]

theorem IncDependentFamilyIsomorphism.refl_trans
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.trans (IncDependentFamilyIsomorphism.refl source) = iso := by
  apply IncDependentFamilyIsomorphism.ext
  · exact iso.hom.comp_identity
  · exact iso.inv.identity_comp

theorem IncDependentFamilyIsomorphism.trans_refl
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    (IncDependentFamilyIsomorphism.refl target).trans iso = iso := by
  apply IncDependentFamilyIsomorphism.ext
  · exact iso.hom.identity_comp
  · exact iso.inv.comp_identity

theorem IncDependentFamilyIsomorphism.trans_assoc
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third fourth : IncDependentFamily inc}
    (thirdIso : IncDependentFamilyIsomorphism third fourth)
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    (thirdIso.trans secondIso).trans firstIso =
      thirdIso.trans (secondIso.trans firstIso) := by
  apply IncDependentFamilyIsomorphism.ext
  · exact IncDependentFamilyMorphism.comp_assoc
      thirdIso.hom secondIso.hom firstIso.hom
  · exact (IncDependentFamilyMorphism.comp_assoc
      firstIso.inv secondIso.inv thirdIso.inv).symm

theorem IncDependentFamilyIsomorphism.symm_symm
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.symm.symm = iso := by
  apply IncDependentFamilyIsomorphism.ext <;> rfl

theorem IncDependentFamilyIsomorphism.symm_trans_self
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.symm.trans iso = IncDependentFamilyIsomorphism.refl source := by
  apply IncDependentFamilyIsomorphism.ext
  · apply IncDependentFamilyMorphism.ext
    intro index value
    exact iso.inv_hom index value
  · apply IncDependentFamilyMorphism.ext
    intro index value
    exact iso.inv_hom index value

theorem IncDependentFamilyIsomorphism.trans_symm_self
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.trans iso.symm = IncDependentFamilyIsomorphism.refl target := by
  apply IncDependentFamilyIsomorphism.ext
  · apply IncDependentFamilyMorphism.ext
    intro index value
    exact iso.hom_inv index value
  · apply IncDependentFamilyMorphism.ext
    intro index value
    exact iso.hom_inv index value

theorem IncDependentFamilyIsomorphism.mapSum_inv_hom
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.inv.mapSum ∘ iso.hom.mapSum = id := by
  funext total
  rcases total with ⟨index, value⟩
  change Sigma.mk index (iso.inv.app index (iso.hom.app index value)) =
    Sigma.mk index value
  rw [iso.inv_hom]

theorem IncDependentFamilyIsomorphism.mapSum_hom_inv
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.hom.mapSum ∘ iso.inv.mapSum = id := by
  funext total
  rcases total with ⟨index, value⟩
  change Sigma.mk index (iso.hom.app index (iso.inv.app index value)) =
    Sigma.mk index value
  rw [iso.hom_inv]

theorem IncDependentFamilyIsomorphism.mapProduct_inv_hom
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.inv.mapProduct ∘ iso.hom.mapProduct = id := by
  funext term index
  exact iso.inv_hom index (term index)

theorem IncDependentFamilyIsomorphism.mapProduct_hom_inv
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.hom.mapProduct ∘ iso.inv.mapProduct = id := by
  funext term index
  exact iso.hom_inv index (term index)

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

/- A right-multiplied constant can be pulled out of a finite sum, the
   mirror image of `intListSum_mul_left`. -/
theorem intListSum_mul_right {α : Type u} (xs : List α) (f : α → Int) (a : Int) :
    intListSum xs f * a = intListSum xs (fun x => f x * a) := by
  rw [Int.mul_comm (intListSum xs f) a, ← intListSum_mul_left]
  congr 1
  funext x
  exact Int.mul_comm a (f x)

/- Two nested finite sums over independent index lists commute (finite
   Fubini).  This generalizes `intListSum_gram_row_swap` above (which is the
   special case `f a b := b_ (a) i * b_ (a) b` composed with pulling a
   factor out of the inner sum): here the summand `f` is an arbitrary
   two-argument function, with no multiplicative structure assumed. -/
theorem intListSum_comm {α : Type u} {β : Type v} (xs : List α) (ys : List β)
    (f : α → β → Int) :
    intListSum xs (fun a => intListSum ys (fun b => f a b)) =
      intListSum ys (fun b => intListSum xs (fun a => f a b)) := by
  induction xs with
  | nil =>
    have hzero : (fun b : β => intListSum ([] : List α) (fun a => f a b)) =
        fun _ : β => (0 : Int) := funext (fun _ => rfl)
    calc
      intListSum ([] : List α) (fun a => intListSum ys (fun b => f a b)) = 0 := rfl
      _ = intListSum ys (fun _ : β => (0 : Int)) := (intListSum_zero ys).symm
      _ = intListSum ys (fun b => intListSum ([] : List α) (fun a => f a b)) := by
            rw [hzero]
  | cons a xs ih =>
    rw [intListSum_cons, ih, ← intListSum_add]
    congr 1
    funext b
    exact (intListSum_cons a xs (fun a' => f a' b)).symm

/- Merkle-ID: foundation.axiomatization.matrix_algebra
   General arithmetic for the bare `Matrix m n α := m → n → α` abstraction
   (`Axioms/Basic.lean` L30).  Before this block no arithmetic operation on
   `Matrix` existed anywhere in the project -- `boundaryMatrix`/`laplacian`
   above are concrete, narrow formulas built directly from
   `Incidence.boundary`, not instances of a general `add`/`mul`/`transpose`
   layer.  Multiplication sums over an explicit finite observation list for
   the shared middle index, matching this project's existing
   `idx : List I`-based summation style rather than assuming a
   `Fintype`/`Finset` structure the index types need not have. Entries are
   fixed to `Int`, matching every other numeric development in this project
   (`Integers.lean`, `boundaryMatrix`/`laplacian`); `transpose` is kept
   polymorphic in the entry type since it is purely structural. -/
namespace Matrix

def add {m : Type u} {n : Type v} (A B : Matrix m n Int) : Matrix m n Int :=
  fun i j => A i j + B i j

theorem add_comm {m : Type u} {n : Type v} (A B : Matrix m n Int) :
    add A B = add B A := by
  funext i j
  exact Int.add_comm (A i j) (B i j)

theorem add_assoc {m : Type u} {n : Type v} (A B C : Matrix m n Int) :
    add (add A B) C = add A (add B C) := by
  funext i j
  exact Int.add_assoc (A i j) (B i j) (C i j)

def transpose {m : Type u} {n : Type v} {α : Type w} (A : Matrix m n α) : Matrix n m α :=
  fun j i => A i j

theorem transpose_transpose {m : Type u} {n : Type v} {α : Type w} (A : Matrix m n α) :
    transpose (transpose A) = A := rfl

theorem transpose_add {m : Type u} {n : Type v} (A B : Matrix m n Int) :
    transpose (add A B) = add (transpose A) (transpose B) := rfl

def mul {m : Type u} {n : Type v} {p : Type w} (idx : List n)
    (A : Matrix m n Int) (B : Matrix n p Int) : Matrix m p Int :=
  fun i j => intListSum idx (fun k => A i k * B k j)

theorem mul_add {m : Type u} {n : Type v} {p : Type w} (idx : List n)
    (A : Matrix m n Int) (B C : Matrix n p Int) :
    mul idx A (add B C) = add (mul idx A B) (mul idx A C) := by
  funext i j
  show intListSum idx (fun k => A i k * (B k j + C k j)) =
      intListSum idx (fun k => A i k * B k j) + intListSum idx (fun k => A i k * C k j)
  rw [← intListSum_add]
  congr 1
  funext k
  exact Int.mul_add (A i k) (B k j) (C k j)

theorem add_mul {m : Type u} {n : Type v} {p : Type w} (idx : List n)
    (A B : Matrix m n Int) (C : Matrix n p Int) :
    mul idx (add A B) C = add (mul idx A C) (mul idx B C) := by
  funext i j
  show intListSum idx (fun k => (A i k + B i k) * C k j) =
      intListSum idx (fun k => A i k * C k j) + intListSum idx (fun k => B i k * C k j)
  rw [← intListSum_add]
  congr 1
  funext k
  exact Int.add_mul (A i k) (B i k) (C k j)

theorem transpose_mul {m : Type u} {n : Type v} {p : Type w} (idx : List n)
    (A : Matrix m n Int) (B : Matrix n p Int) :
    transpose (mul idx A B) = mul idx (transpose B) (transpose A) := by
  funext j i
  show intListSum idx (fun k => A i k * B k j) = intListSum idx (fun k => B k j * A i k)
  congr 1
  funext k
  exact Int.mul_comm (A i k) (B k j)

/- Associativity of `mul`: the middle-index sum for `A * B` and the
   shared-index sum for `(A * B) * C`/`A * (B * C)` may range over different
   observation lists (`idxN : List n`, `idxP : List p`), since `n` and `p`
   need not coincide or share a canonical enumeration.  Reuses
   `intListSum_mul_left`/`intListSum_mul_right` to move constants across a
   sum and `intListSum_comm` (finite Fubini, just above) to swap the two
   nested sums -- no finite-sum algebra is re-derived from scratch here. -/
theorem mul_assoc {m : Type u} {n : Type v} {p : Type w} {q : Type u}
    (idxN : List n) (idxP : List p)
    (A : Matrix m n Int) (B : Matrix n p Int) (C : Matrix p q Int) :
    mul idxP (mul idxN A B) C = mul idxN A (mul idxP B C) := by
  funext i j
  show intListSum idxP (fun k => (intListSum idxN (fun l => A i l * B l k)) * C k j) =
      intListSum idxN (fun l => A i l * intListSum idxP (fun k => B l k * C k j))
  have step1 : ∀ k, (intListSum idxN (fun l => A i l * B l k)) * C k j =
      intListSum idxN (fun l => A i l * (B l k * C k j)) := by
    intro k
    rw [intListSum_mul_right]
    congr 1
    funext l
    exact Int.mul_assoc (A i l) (B l k) (C k j)
  calc
    intListSum idxP (fun k => (intListSum idxN (fun l => A i l * B l k)) * C k j)
        = intListSum idxP (fun k => intListSum idxN (fun l => A i l * (B l k * C k j))) := by
          congr 1
          funext k
          exact step1 k
    _ = intListSum idxN (fun l => intListSum idxP (fun k => A i l * (B l k * C k j))) :=
          intListSum_comm idxP idxN (fun k l => A i l * (B l k * C k j))
    _ = intListSum idxN (fun l => A i l * intListSum idxP (fun k => B l k * C k j)) := by
          congr 1
          funext l
          exact intListSum_mul_left (A i l) idxP (fun k => B l k * C k j)

end Matrix

/- The concrete `A17` payoff: `IncidenceTheory/Axioms/A14_A17.lean` L16
   carries the comment "A17: Laplacian (B^T @ B)" next to the
   `IncidenceAlgebraic.laplacian` field, but nothing in the project actually
   states this as a theorem connecting the two abstract fields, let alone
   the concrete `laplacian`/`boundaryMatrix` defined above. This closes that
   gap for the concrete definitions: `laplacian` literally IS `Bᵀ * B` under
   the general `Matrix.mul`/`Matrix.transpose` just defined, for the same
   observation list on both sides. Both sides unfold to the identical
   `idx.foldl`/`intListSum` expression, so the proof is definitional. -/
theorem laplacian_eq_transpose_mul_boundaryMatrix {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    laplacian inc idx =
      Matrix.mul idx (Matrix.transpose (boundaryMatrix inc idx)) (boundaryMatrix inc idx) := by
  funext i j
  rfl

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

/- Resonance is the central relational interaction.  Unlike the compatibility
selector `glue`, it may relate one pair to several emergent modes. -/
structure ResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) where
  symmetric : ∀ {i j k}, inc.resonance i j k → inc.resonance j i k
  unit_left : ∀ i, inc.resonance inc.unit i i
  unit_right : ∀ i, inc.resonance i inc.unit i
  type_compatible : ∀ {i j k}, inc.resonance i j k →
    inc.typeFunc i = inc.typeFunc j ∧ inc.typeFunc k = inc.typeFunc i

/- A functional resonance identifies every relational mode with the mode
selected by the legacy/computational compatibility operation. -/
structure FunctionalResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : Type u extends ResonanceSpec inc where
  selected_complete : ∀ {i j k}, inc.resonance i j k → inc.glue i j = some k

/- Relational associativity compares the complete sets of modes reachable by
the two binary parenthesizations.  It does not choose intermediate modes. -/
structure AssociativeResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) where
  reassociate : ∀ {i j k out},
    (∃ ij, inc.resonance i j ij ∧ inc.resonance ij k out) ↔
    (∃ jk, inc.resonance j k jk ∧ inc.resonance i jk out)

/- A functional associative resonance becomes an additive group when every
mode has a specified inverse resonating with it at the vacuum. -/
structure AdditiveGroupResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    extends FunctionalResonanceSpec inc, AssociativeResonanceSpec inc where
  inverse : I → I
  inverse_mode : ∀ i, inc.resonance i (inverse i) inc.unit

/- A unit-reflecting resonance cannot create the vacuum from two non-vacuum
inputs. This is the exact missing law exposed by the sum associativity
counterexample. -/
structure UnitReflectingResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) where
  reflects : ∀ {i j}, inc.resonance i j inc.unit →
    i = inc.unit ∨ j = inc.unit

/- A second resonance channel can interact distributively with the central
additive resonance. This packages semiring/ring-style algebra without reducing
either interaction to a primitive binary function. -/
structure DistributiveResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) where
  one : I
  multiply : I → I → I → Prop
  symmetric : ∀ {i j k}, multiply i j k → multiply j i k
  unit_left : ∀ i, multiply one i i
  unit_right : ∀ i, multiply i one i
  associative : ∀ {i j k out},
    (∃ ij, multiply i j ij ∧ multiply ij k out) ↔
    (∃ jk, multiply j k jk ∧ multiply i jk out)
  distributes : ∀ {i j k out},
    (∃ jk, inc.resonance j k jk ∧ multiply i jk out) ↔
    (∃ ij ik, multiply i j ij ∧ multiply i k ik ∧
      inc.resonance ij ik out)

/- A field-level relational algebra adds additive inverse modes,
nontriviality, and a multiplicative inverse mode for every non-vacuum input.
No global inverse selector is required: existence belongs to the resonance
relation itself. -/
structure FieldResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) extends DistributiveResonanceSpec inc where
  zero_ne_one : inc.unit ≠ one
  additive_inverse : ∀ i, ∃ inverse, inc.resonance i inverse inc.unit
  multiplicative_inverse : ∀ {i}, i ≠ inc.unit →
    ∃ inverse, multiply i inverse one

/- An ordered field remains relational in both algebraic channels. Order is
required to be total, additive resonance is monotone in either translated
input (by symmetry), and multiplication preserves the nonnegative cone. -/
structure OrderedFieldResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) extends FieldResonanceSpec inc where
  le : I → I → Prop
  le_refl : ∀ i, le i i
  le_antisymm : ∀ {i j}, le i j → le j i → i = j
  le_trans : ∀ {i j k}, le i j → le j k → le i k
  le_total : ∀ i j, le i j ∨ le j i
  add_monotone : ∀ {offset i j outI outJ}, le i j →
    inc.resonance offset i outI → inc.resonance offset j outJ →
    le outI outJ
  multiply_nonnegative : ∀ {i j out}, le inc.unit i → le inc.unit j →
    multiply i j out → le inc.unit out

theorem resonance_reassociate {I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : AssociativeResonanceSpec inc)
    {i j k out : I} :
    (∃ ij, inc.resonance i j ij ∧ inc.resonance ij k out) ↔
    (∃ jk, inc.resonance j k jk ∧ inc.resonance i jk out) :=
  spec.reassociate

theorem resonance_of_selected {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) {i j k : I} (selected : inc.glue i j = some k) :
    inc.resonance i j k :=
  inc.selected_resonates selected

/-- Computable choice of at most one resonance mode.  The relation
`Incidence.resonance` is authoritative; this selector exists for algorithms
and compatibility with the original `glue` API. -/
def Incidence.selectedMode {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i j : I) : Option I :=
  inc.glue i j

theorem selectedMode_resonates {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) {i j k : I}
    (selected : inc.selectedMode i j = some k) : inc.resonance i j k :=
  inc.selected_resonates selected

theorem resonance_left_unit {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) : inc.resonance inc.unit i i :=
  inc.selected_resonates (inc.unit_left i)

theorem resonance_right_unit {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) : inc.resonance i inc.unit i :=
  inc.selected_resonates (inc.unit_right i)

theorem selected_resonance_preserves_type
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    {i j k : I} (allowed : inc.guards.allow i j = true)
    (selected : inc.glue i j = some k) :
    inc.typeFunc k = inc.typeFunc i :=
  inc.type_preserve allowed selected

/- A gluing specification supplies the additional laws needed for the
computable resonance selector.  New relational developments should prefer
`ResonanceSpec`; this structure remains the compatibility API. -/
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

/- Relational congruence for resonance.  This is stronger and more natural
than selector congruence: any mode of related inputs must be matchable by a
related mode, in both directions. -/
def ResonanceRespects {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (rel : I → I → Prop) : Prop :=
  ∀ {i₁ i₂ j₁ j₂ : I}, rel i₁ i₂ → rel j₁ j₂ →
    (∀ {k₁}, inc.resonance i₁ j₁ k₁ →
      ∃ k₂, inc.resonance i₂ j₂ k₂ ∧ rel k₁ k₂) ∧
    (∀ {k₂}, inc.resonance i₂ j₂ k₂ →
      ∃ k₁, inc.resonance i₁ j₁ k₁ ∧ rel k₁ k₂)

structure BisimulationResonanceSpec {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) where
  respects : ResonanceRespects inc (approxBisim inc)

/- Extensionality in all three positions is exactly the condition under which
resonance descends without ambiguity to bisimulation classes. -/
def QuotientResonanceCongruent {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : Prop :=
  ∀ {i₁ i₂ j₁ j₂ k₁ k₂},
    approxBisim inc i₁ i₂ → approxBisim inc j₁ j₂ →
    approxBisim inc k₁ k₂ →
    (inc.resonance i₁ j₁ k₁ ↔ inc.resonance i₂ j₂ k₂)

theorem quotientResonanceCongruent_of_faithful
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (faithful : ∀ x y, approxBisim inc x y ↔ x = y) :
    QuotientResonanceCongruent inc := by
  intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk
  have hiEq := (faithful i₁ i₂).mp hi
  have hjEq := (faithful j₁ j₂).mp hj
  have hkEq := (faithful k₁ k₂).mp hk
  subst i₂
  subst j₂
  subst k₂
  rfl

def quotientResonance {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) :
    IncidenceQuotient inc → IncidenceQuotient inc →
      IncidenceQuotient inc → Prop :=
  fun qi qj qk => ∃ i j k,
    Quotient.mk (approxBisimSetoid inc) i = qi ∧
    Quotient.mk (approxBisimSetoid inc) j = qj ∧
    Quotient.mk (approxBisimSetoid inc) k = qk ∧
    inc.resonance i j k

theorem quotientResonance_of_resonance
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {i j k : I} (resonant : inc.resonance i j k) :
    quotientResonance inc
      (Quotient.mk (approxBisimSetoid inc) i)
      (Quotient.mk (approxBisimSetoid inc) j)
      (Quotient.mk (approxBisimSetoid inc) k) :=
  ⟨i, j, k, rfl, rfl, rfl, resonant⟩

theorem quotientResonance_mk_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (congruent : QuotientResonanceCongruent inc) {i j k : I} :
    quotientResonance inc
      (Quotient.mk (approxBisimSetoid inc) i)
      (Quotient.mk (approxBisimSetoid inc) j)
      (Quotient.mk (approxBisimSetoid inc) k) ↔ inc.resonance i j k := by
  constructor
  · rintro ⟨i', j', k', hi, hj, hk, resonant⟩
    have hi' : approxBisim inc i' i := Quotient.exact hi
    have hj' : approxBisim inc j' j := Quotient.exact hj
    have hk' : approxBisim inc k' k := Quotient.exact hk
    exact (congruent hi' hj' hk').mp resonant
  · exact quotientResonance_of_resonance

structure ResonanceHomomorphism
    {I J R₁ R₂ T₁ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂) where
  toFun : I → J
  preserves : ∀ {i j k}, source.resonance i j k →
    target.resonance (toFun i) (toFun j) (toFun k)

def ResonanceHomomorphism.identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceHomomorphism inc inc where
  toFun := id
  preserves := fun resonant => resonant

def ResonanceHomomorphism.comp
    {I J K R₁ R₂ R₃ T₁ T₂ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (right : ResonanceHomomorphism second third)
    (left : ResonanceHomomorphism first second) :
    ResonanceHomomorphism first third where
  toFun := right.toFun ∘ left.toFun
  preserves := fun resonant => right.preserves (left.preserves resonant)

@[simp] theorem ResonanceHomomorphism.identity_apply
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) :
    (ResonanceHomomorphism.identity inc).toFun i = i := rfl

@[simp] theorem ResonanceHomomorphism.comp_apply
    {I J K R₁ R₂ R₃ T₁ T₂ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (right : ResonanceHomomorphism second third)
    (left : ResonanceHomomorphism first second) (i : I) :
    (right.comp left).toFun i = right.toFun (left.toFun i) := rfl

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

def IncCategory.op {Obj : Type u} (C : IncCategory Obj) : IncCategory Obj where
  Hom := fun source target => C.Hom target source
  id := C.id
  comp := fun first second => C.comp second first
  id_comp := C.comp_id
  comp_id := C.id_comp
  assoc := by
    intro a b c d first second third
    exact (C.assoc third second first).symm

def IncFunctor.op
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : IncFunctor C.op D.op where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := by
    intro a b c first second
    exact F.map_comp second first

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

theorem IncFunctorFullyFaithful.op
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (fullyFaithful : IncFunctorFullyFaithful F) :
    IncFunctorFullyFaithful F.op where
  faithful := by
    intro source target left right equality
    exact fullyFaithful.faithful left right equality
  full := by
    intro source target morphism
    exact fullyFaithful.full morphism

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

theorem IncFunctorEssentiallySurjective.op
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (essentiallySurjective : IncFunctorEssentiallySurjective F) :
    IncFunctorEssentiallySurjective F.op := by
  intro target
  obtain ⟨source, hom, inv, inv_hom, hom_inv⟩ := essentiallySurjective target
  exact ⟨source, inv, hom, inv_hom, hom_inv⟩

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

theorem IncFunctorEquivalenceCriterion.op
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    IncFunctorEquivalenceCriterion F.op where
  fullyFaithful := criterion.fullyFaithful.op
  essentiallySurjective := criterion.essentiallySurjective.op

structure IncEssentialPreimage
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) (target : DObj) where
  source : CObj
  iso : MorphismIso D (F.obj source) target

theorem IncFunctorEssentiallySurjective.nonempty_preimage
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (hF : IncFunctorEssentiallySurjective F)
    (target : DObj) : Nonempty (IncEssentialPreimage F target) := by
  obtain ⟨source, hom, inv, inv_hom, hom_inv⟩ := hF target
  exact ⟨
    { source := source
      iso :=
        { hom := hom
          inv := inv
          inv_hom := inv_hom
          hom_inv := hom_inv } }⟩

noncomputable def IncFunctorEssentiallySurjective.choosePreimage
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (hF : IncFunctorEssentiallySurjective F)
    (target : DObj) : IncEssentialPreimage F target :=
  Classical.choice (hF.nonempty_preimage target)

noncomputable def IncFunctorEquivalenceCriterion.inverseObj
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    DObj → CObj :=
  fun target => (criterion.essentiallySurjective.choosePreimage target).source

noncomputable def IncFunctorEquivalenceCriterion.inverseObj_iso
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (target : DObj) :
    MorphismIso D (F.obj (criterion.inverseObj target)) target :=
  (criterion.essentiallySurjective.choosePreimage target).iso

noncomputable def IncFunctorEquivalenceCriterion.inverseMap
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    {source target : DObj} (morphism : D.Hom source target) :
    C.Hom (criterion.inverseObj source) (criterion.inverseObj target) :=
  Classical.choose (criterion.fullyFaithful.full
    (D.comp (criterion.inverseObj_iso target).inv
      (D.comp morphism (criterion.inverseObj_iso source).hom)))

theorem IncFunctorEquivalenceCriterion.inverseMap_spec
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    {source target : DObj} (morphism : D.Hom source target) :
    F.map (criterion.inverseMap morphism) =
      D.comp (criterion.inverseObj_iso target).inv
        (D.comp morphism (criterion.inverseObj_iso source).hom) :=
  Classical.choose_spec (criterion.fullyFaithful.full
    (D.comp (criterion.inverseObj_iso target).inv
      (D.comp morphism (criterion.inverseObj_iso source).hom)))

theorem IncFunctorEquivalenceCriterion.inverseMap_id
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (object : DObj) :
    criterion.inverseMap (D.id object) =
      C.id (criterion.inverseObj object) := by
  apply criterion.fullyFaithful.faithful
  rw [criterion.inverseMap_spec, F.map_id]
  rw [D.id_comp, (criterion.inverseObj_iso object).inv_hom]

theorem IncFunctorEquivalenceCriterion.inverseMap_comp
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    {source middle target : DObj}
    (second : D.Hom middle target) (first : D.Hom source middle) :
    criterion.inverseMap (D.comp second first) =
      C.comp (criterion.inverseMap second) (criterion.inverseMap first) := by
  apply criterion.fullyFaithful.faithful
  rw [criterion.inverseMap_spec, F.map_comp]
  rw [criterion.inverseMap_spec, criterion.inverseMap_spec]
  let sourceIso := criterion.inverseObj_iso source
  let middleIso := criterion.inverseObj_iso middle
  let targetIso := criterion.inverseObj_iso target
  change D.comp targetIso.inv
      (D.comp (D.comp second first) sourceIso.hom) =
    D.comp
      (D.comp targetIso.inv (D.comp second middleIso.hom))
      (D.comp middleIso.inv (D.comp first sourceIso.hom))
  calc
    D.comp targetIso.inv (D.comp (D.comp second first) sourceIso.hom) =
      D.comp targetIso.inv
        (D.comp second (D.comp first sourceIso.hom)) := by
          rw [D.assoc second first]
    _ = D.comp targetIso.inv
        (D.comp second
          (D.comp (D.id middle) (D.comp first sourceIso.hom))) := by
            rw [D.id_comp]
    _ = D.comp targetIso.inv
        (D.comp second
          (D.comp (D.comp middleIso.hom middleIso.inv)
            (D.comp first sourceIso.hom))) := by
              rw [middleIso.hom_inv]
    _ = D.comp
        (D.comp targetIso.inv (D.comp second middleIso.hom))
        (D.comp middleIso.inv (D.comp first sourceIso.hom)) := by
          rw [← D.assoc, ← D.assoc, ← D.assoc, D.assoc targetIso.inv]

noncomputable def IncFunctorEquivalenceCriterion.inverseFunctor
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    IncFunctor D C where
  obj := criterion.inverseObj
  map := criterion.inverseMap
  map_id := criterion.inverseMap_id
  map_comp := criterion.inverseMap_comp

noncomputable def IncFunctorEquivalenceCriterion.counit
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    IncNaturalIsomorphism (F.comp criterion.inverseFunctor)
      (IncFunctor.identity D) where
  hom :=
    { app := fun object => (criterion.inverseObj_iso object).hom
      naturality := by
        intro source target morphism
        change D.comp morphism (criterion.inverseObj_iso source).hom =
          D.comp (criterion.inverseObj_iso target).hom
            (F.map (criterion.inverseMap morphism))
        rw [criterion.inverseMap_spec]
        symm
        calc
          D.comp (criterion.inverseObj_iso target).hom
              (D.comp (criterion.inverseObj_iso target).inv
                (D.comp morphism (criterion.inverseObj_iso source).hom)) =
            D.comp
              (D.comp (criterion.inverseObj_iso target).hom
                (criterion.inverseObj_iso target).inv)
              (D.comp morphism (criterion.inverseObj_iso source).hom) :=
                D.assoc _ _ _
          _ = D.comp (D.id target)
              (D.comp morphism (criterion.inverseObj_iso source).hom) := by
                rw [(criterion.inverseObj_iso target).hom_inv]
          _ = D.comp morphism (criterion.inverseObj_iso source).hom :=
                D.id_comp _ }
  inv :=
    { app := fun object => (criterion.inverseObj_iso object).inv
      naturality := by
        intro source target morphism
        change D.comp (F.map (criterion.inverseMap morphism))
            (criterion.inverseObj_iso source).inv =
          D.comp (criterion.inverseObj_iso target).inv morphism
        rw [criterion.inverseMap_spec]
        calc
          D.comp
              (D.comp (criterion.inverseObj_iso target).inv
                (D.comp morphism (criterion.inverseObj_iso source).hom))
              (criterion.inverseObj_iso source).inv =
            D.comp (criterion.inverseObj_iso target).inv
              (D.comp morphism
                (D.comp (criterion.inverseObj_iso source).hom
                  (criterion.inverseObj_iso source).inv)) := by
                    rw [← D.assoc, ← D.assoc]
          _ = D.comp (criterion.inverseObj_iso target).inv
              (D.comp morphism (D.id source)) := by
                rw [(criterion.inverseObj_iso source).hom_inv]
          _ = D.comp (criterion.inverseObj_iso target).inv morphism := by
                rw [D.comp_id] }
  hom_inv_id := by
    apply IncNaturalTransformation.ext
    intro object
    exact (criterion.inverseObj_iso object).inv_hom
  inv_hom_id := by
    apply IncNaturalTransformation.ext
    intro object
    exact (criterion.inverseObj_iso object).hom_inv

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

theorem IncFunctorFullyFaithful.map_reflectIso_hom
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (fullyFaithful : IncFunctorFullyFaithful F)
    {source target : CObj}
    (iso : MorphismIso D (F.obj source) (F.obj target)) :
    F.map (fullyFaithful.reflectIso iso).hom = iso.hom := by
  change F.map (Classical.choose (fullyFaithful.full iso.hom)) = iso.hom
  exact Classical.choose_spec (fullyFaithful.full iso.hom)

theorem IncFunctorFullyFaithful.map_reflectIso_inv
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (fullyFaithful : IncFunctorFullyFaithful F)
    {source target : CObj}
    (iso : MorphismIso D (F.obj source) (F.obj target)) :
    F.map (fullyFaithful.reflectIso iso).inv = iso.inv := by
  change F.map (Classical.choose (fullyFaithful.full iso.inv)) = iso.inv
  exact Classical.choose_spec (fullyFaithful.full iso.inv)

noncomputable def IncFunctorEquivalenceCriterion.unitComponent
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (object : CObj) :
    MorphismIso C object (criterion.inverseObj (F.obj object)) :=
  criterion.fullyFaithful.reflectIso
    (criterion.inverseObj_iso (F.obj object)).symm

theorem IncFunctorEquivalenceCriterion.map_unitComponent_hom
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (object : CObj) :
    F.map (criterion.unitComponent object).hom =
      (criterion.inverseObj_iso (F.obj object)).inv :=
  criterion.fullyFaithful.map_reflectIso_hom _

theorem IncFunctorEquivalenceCriterion.map_unitComponent_inv
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (object : CObj) :
    F.map (criterion.unitComponent object).inv =
      (criterion.inverseObj_iso (F.obj object)).hom :=
  criterion.fullyFaithful.map_reflectIso_inv _

noncomputable def IncFunctorEquivalenceCriterion.unit
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    IncNaturalIsomorphism (IncFunctor.identity C)
      (criterion.inverseFunctor.comp F) where
  hom :=
    { app := fun object => (criterion.unitComponent object).hom
      naturality := by
        intro source target morphism
        apply criterion.fullyFaithful.faithful
        rw [F.map_comp, F.map_comp]
        change D.comp
            (F.map (criterion.inverseMap (F.map morphism)))
            (F.map (criterion.unitComponent source).hom) =
          D.comp (F.map (criterion.unitComponent target).hom) (F.map morphism)
        rw [criterion.map_unitComponent_hom,
          criterion.map_unitComponent_hom]
        exact criterion.counit.inv.naturality (F.map morphism) }
  inv :=
    { app := fun object => (criterion.unitComponent object).inv
      naturality := by
        intro source target morphism
        apply criterion.fullyFaithful.faithful
        rw [F.map_comp, F.map_comp]
        change D.comp (F.map morphism)
            (F.map (criterion.unitComponent source).inv) =
          D.comp (F.map (criterion.unitComponent target).inv)
            (F.map (criterion.inverseMap (F.map morphism)))
        rw [criterion.map_unitComponent_inv,
          criterion.map_unitComponent_inv]
        exact criterion.counit.hom.naturality (F.map morphism) }
  hom_inv_id := by
    apply IncNaturalTransformation.ext
    intro object
    exact (criterion.unitComponent object).inv_hom
  inv_hom_id := by
    apply IncNaturalTransformation.ext
    intro object
    exact (criterion.unitComponent object).hom_inv

noncomputable def IncFunctorEquivalenceCriterion.toCategoryEquivalence
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    IncCategoryEquivalence C D where
  forward := F
  inverse := criterion.inverseFunctor
  unit := criterion.unit
  counit := criterion.counit

theorem IncFunctorEquivalenceCriterion.left_triangle
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (object : CObj) :
    D.comp (criterion.counit.hom.app (F.obj object))
        (F.map (criterion.unit.hom.app object)) =
      D.id (F.obj object) := by
  change D.comp (criterion.inverseObj_iso (F.obj object)).hom
      (F.map (criterion.unitComponent object).hom) = D.id (F.obj object)
  rw [criterion.map_unitComponent_hom]
  exact (criterion.inverseObj_iso (F.obj object)).hom_inv

theorem IncFunctorEquivalenceCriterion.right_triangle
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (object : DObj) :
    C.comp
        (criterion.inverseFunctor.map (criterion.counit.hom.app object))
        (criterion.unit.hom.app (criterion.inverseFunctor.obj object)) =
      C.id (criterion.inverseFunctor.obj object) := by
  apply criterion.fullyFaithful.faithful
  rw [F.map_comp, F.map_id (criterion.inverseFunctor.obj object)]
  change D.comp
      (F.map (criterion.inverseMap (criterion.inverseObj_iso object).hom))
      (F.map (criterion.unitComponent (criterion.inverseObj object)).hom) =
    D.id (F.obj (criterion.inverseObj object))
  rw [criterion.inverseMap_spec, criterion.map_unitComponent_hom]
  let objectIso := criterion.inverseObj_iso object
  let liftedIso := criterion.inverseObj_iso (F.obj (criterion.inverseObj object))
  change D.comp
      (D.comp objectIso.inv (D.comp objectIso.hom liftedIso.hom))
      liftedIso.inv = D.id (F.obj (criterion.inverseObj object))
  calc
    D.comp (D.comp objectIso.inv (D.comp objectIso.hom liftedIso.hom))
        liftedIso.inv =
      D.comp objectIso.inv
        (D.comp objectIso.hom (D.comp liftedIso.hom liftedIso.inv)) := by
          rw [← D.assoc, ← D.assoc]
    _ = D.comp objectIso.inv (D.comp objectIso.hom (D.id _)) := by
      rw [liftedIso.hom_inv]
    _ = D.comp objectIso.inv objectIso.hom := by rw [D.comp_id]
    _ = D.id _ := objectIso.inv_hom

structure IncCoherentCategoryEquivalence
    {CObj DObj : Type u} (C : IncCategory CObj) (D : IncCategory DObj) where
  equivalence : IncCategoryEquivalence C D
  left_triangle : ∀ object : CObj,
    D.comp (equivalence.counit.hom.app (equivalence.forward.obj object))
        (equivalence.forward.map (equivalence.unit.hom.app object)) =
      D.id (equivalence.forward.obj object)
  right_triangle : ∀ object : DObj,
    C.comp
        (equivalence.inverse.map (equivalence.counit.hom.app object))
        (equivalence.unit.hom.app (equivalence.inverse.obj object)) =
      C.id (equivalence.inverse.obj object)

theorem IncCoherentCategoryEquivalence.counit_inv_forward_eq_map_unit
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D) (object : CObj) :
    coherent.equivalence.counit.inv.app
        (coherent.equivalence.forward.obj object) =
      coherent.equivalence.forward.map
        (coherent.equivalence.unit.hom.app object) := by
  let equivalence := coherent.equivalence
  calc
    equivalence.counit.inv.app (equivalence.forward.obj object) =
      D.comp (equivalence.counit.inv.app (equivalence.forward.obj object))
        (D.id (equivalence.forward.obj object)) :=
          (D.comp_id _).symm
    _ = D.comp (equivalence.counit.inv.app (equivalence.forward.obj object))
        (D.comp (equivalence.counit.hom.app (equivalence.forward.obj object))
          (equivalence.forward.map (equivalence.unit.hom.app object))) := by
            rw [coherent.left_triangle object]
    _ = D.comp
        (D.comp (equivalence.counit.inv.app (equivalence.forward.obj object))
          (equivalence.counit.hom.app (equivalence.forward.obj object)))
        (equivalence.forward.map (equivalence.unit.hom.app object)) :=
          D.assoc _ _ _
    _ = D.comp
        (D.id ((equivalence.forward.comp equivalence.inverse).obj
          (equivalence.forward.obj object)))
        (equivalence.forward.map (equivalence.unit.hom.app object)) := by
          rw [equivalence.counit.hom_app_inv_app]
    _ = equivalence.forward.map (equivalence.unit.hom.app object) :=
      D.id_comp _

theorem IncCoherentCategoryEquivalence.counit_hom_forward_eq_map_unit_inv
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D) (object : CObj) :
    coherent.equivalence.counit.hom.app
        (coherent.equivalence.forward.obj object) =
      coherent.equivalence.forward.map
        (coherent.equivalence.unit.inv.app object) := by
  let equivalence := coherent.equivalence
  calc
    equivalence.counit.hom.app (equivalence.forward.obj object) =
      D.comp (equivalence.counit.hom.app (equivalence.forward.obj object))
        (D.id ((equivalence.forward.comp equivalence.inverse).obj
          (equivalence.forward.obj object))) :=
            (D.comp_id _).symm
    _ = D.comp (equivalence.counit.hom.app (equivalence.forward.obj object))
        (D.comp
          (equivalence.forward.map (equivalence.unit.hom.app object))
          (equivalence.forward.map (equivalence.unit.inv.app object))) := by
            rw [← equivalence.forward.map_comp,
              equivalence.unit.inv_app_hom_app, equivalence.forward.map_id]
            rfl
    _ = D.comp
        (D.comp (equivalence.counit.hom.app (equivalence.forward.obj object))
          (equivalence.forward.map (equivalence.unit.hom.app object)))
        (equivalence.forward.map (equivalence.unit.inv.app object)) :=
          D.assoc _ _ _
    _ = D.comp
        (D.comp (equivalence.counit.hom.app (equivalence.forward.obj object))
          (equivalence.counit.inv.app (equivalence.forward.obj object)))
        (equivalence.forward.map (equivalence.unit.inv.app object)) := by
          rw [coherent.counit_inv_forward_eq_map_unit]
    _ = D.comp (D.id (equivalence.forward.obj object))
        (equivalence.forward.map (equivalence.unit.inv.app object)) := by
          rw [equivalence.counit.inv_app_hom_app]
          rfl
    _ = equivalence.forward.map (equivalence.unit.inv.app object) :=
      D.id_comp _

theorem IncCoherentCategoryEquivalence.unit_inv_inverse_eq_map_counit
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D) (object : DObj) :
    coherent.equivalence.unit.inv.app
        (coherent.equivalence.inverse.obj object) =
      coherent.equivalence.inverse.map
        (coherent.equivalence.counit.hom.app object) := by
  let equivalence := coherent.equivalence
  calc
    equivalence.unit.inv.app (equivalence.inverse.obj object) =
      C.comp (C.id (equivalence.inverse.obj object))
        (equivalence.unit.inv.app (equivalence.inverse.obj object)) :=
          (C.id_comp _).symm
    _ = C.comp
        (C.comp
          (equivalence.inverse.map (equivalence.counit.hom.app object))
          (equivalence.unit.hom.app (equivalence.inverse.obj object)))
        (equivalence.unit.inv.app (equivalence.inverse.obj object)) := by
          rw [coherent.right_triangle object]
    _ = C.comp
        (equivalence.inverse.map (equivalence.counit.hom.app object))
        (C.comp (equivalence.unit.hom.app (equivalence.inverse.obj object))
          (equivalence.unit.inv.app (equivalence.inverse.obj object))) :=
            (C.assoc _ _ _).symm
    _ = C.comp (equivalence.inverse.map (equivalence.counit.hom.app object))
        (C.id ((equivalence.inverse.comp equivalence.forward).obj
          (equivalence.inverse.obj object))) := by
            rw [equivalence.unit.inv_app_hom_app]
    _ = equivalence.inverse.map (equivalence.counit.hom.app object) :=
      C.comp_id _

noncomputable def IncFunctorEquivalenceCriterion.toCoherentCategoryEquivalence
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    IncCoherentCategoryEquivalence C D where
  equivalence := criterion.toCategoryEquivalence
  left_triangle := criterion.left_triangle
  right_triangle := criterion.right_triangle

theorem IncCoherentCategoryEquivalence.forward_criterion
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCoherentCategoryEquivalence C D) :
    IncFunctorEquivalenceCriterion equivalence.equivalence.forward :=
  equivalence.equivalence.forward_criterion

noncomputable def IncCoherentCategoryEquivalence.refl
    {Obj : Type u} (C : IncCategory Obj) :
    IncCoherentCategoryEquivalence C C :=
  (IncFunctorEquivalenceCriterion.identity C).toCoherentCategoryEquivalence

noncomputable def IncCoherentCategoryEquivalence.symm
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCoherentCategoryEquivalence C D) :
    IncCoherentCategoryEquivalence D C :=
  equivalence.equivalence.inverse_criterion.toCoherentCategoryEquivalence

noncomputable def IncCoherentCategoryEquivalence.trans
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (second : IncCoherentCategoryEquivalence D E)
    (first : IncCoherentCategoryEquivalence C D) :
    IncCoherentCategoryEquivalence C E :=
  IncFunctorEquivalenceCriterion.toCoherentCategoryEquivalence
    (second.forward_criterion.comp first.forward_criterion)

def IncCoherentlyEquivalent
    {CObj DObj : Type u} (C : IncCategory CObj) (D : IncCategory DObj) : Prop :=
  Nonempty (IncCoherentCategoryEquivalence C D)

theorem incCoherentlyEquivalent_refl
    {Obj : Type u} (C : IncCategory Obj) : IncCoherentlyEquivalent C C :=
  ⟨IncCoherentCategoryEquivalence.refl C⟩

theorem incCoherentlyEquivalent_symm
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj} :
    IncCoherentlyEquivalent C D → IncCoherentlyEquivalent D C := by
  rintro ⟨equivalence⟩
  exact ⟨equivalence.symm⟩

theorem incCoherentlyEquivalent_trans
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj} :
    IncCoherentlyEquivalent C D → IncCoherentlyEquivalent D E →
      IncCoherentlyEquivalent C E := by
  rintro ⟨first⟩ ⟨second⟩
  exact ⟨second.trans first⟩

theorem incCoherentlyEquivalent_iff_categoryEquivalent
    {CObj DObj : Type u} (C : IncCategory CObj) (D : IncCategory DObj) :
    IncCoherentlyEquivalent C D ↔ Nonempty (IncCategoryEquivalence C D) := by
  constructor
  · rintro ⟨coherent⟩
    exact ⟨coherent.equivalence⟩
  · rintro ⟨equivalence⟩
    exact ⟨equivalence.forward_criterion.toCoherentCategoryEquivalence⟩

noncomputable def IncCategoryEquivalence.coherentReplacement
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncCoherentCategoryEquivalence C D :=
  equivalence.forward_criterion.toCoherentCategoryEquivalence

theorem IncCategoryEquivalence.coherentReplacement_forward
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    equivalence.coherentReplacement.equivalence.forward =
      equivalence.forward := rfl

theorem IncCategoryEquivalence.has_triangle_coherent_replacement
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    ∃ replacement : IncCoherentCategoryEquivalence C D,
      replacement.equivalence.forward = equivalence.forward :=
  ⟨equivalence.coherentReplacement,
    equivalence.coherentReplacement_forward⟩

theorem incFunctor_equivalenceCriterion_iff_exists_coherentCategoryEquivalence
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :
    IncFunctorEquivalenceCriterion F ↔
      ∃ equivalence : IncCoherentCategoryEquivalence C D,
        equivalence.equivalence.forward = F := by
  constructor
  · intro criterion
    exact ⟨criterion.toCoherentCategoryEquivalence, rfl⟩
  · rintro ⟨equivalence, forwardEq⟩
    subst F
    exact equivalence.forward_criterion

theorem incFunctor_equivalenceCriterion_iff_exists_categoryEquivalence
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :
    IncFunctorEquivalenceCriterion F ↔
      ∃ equivalence : IncCategoryEquivalence C D,
        equivalence.forward = F := by
  constructor
  · intro criterion
    exact ⟨criterion.toCategoryEquivalence, rfl⟩
  · rintro ⟨equivalence, forwardEq⟩
    subst F
    exact equivalence.forward_criterion

noncomputable def IncCategoryEquivalence.forward_reflectIso
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) {source target : CObj}
    (iso : MorphismIso D (equivalence.forward.obj source)
      (equivalence.forward.obj target)) : MorphismIso C source target :=
  equivalence.forward_fullyFaithful.reflectIso iso

def IncObjectsIsomorphic {Obj : Type u} (C : IncCategory Obj)
    (source target : Obj) : Prop :=
  Nonempty (MorphismIso C source target)

theorem incObjectsIsomorphic_equivalence
    {Obj : Type u} (C : IncCategory Obj) :
    Equivalence (IncObjectsIsomorphic C) where
  refl := by
    intro object
    exact ⟨MorphismIso.refl object⟩
  symm := by
    intro source target h
    rcases h with ⟨iso⟩
    exact ⟨iso.symm⟩
  trans := by
    intro source middle target h₁ h₂
    rcases h₁ with ⟨first⟩
    rcases h₂ with ⟨second⟩
    exact ⟨first.trans second⟩

theorem IncFunctor.preservesObjectsIsomorphic
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) {source target : CObj} :
    IncObjectsIsomorphic C source target →
      IncObjectsIsomorphic D (F.obj source) (F.obj target) := by
  rintro ⟨iso⟩
  exact ⟨F.mapIso iso⟩

theorem IncFunctorFullyFaithful.reflectsObjectsIsomorphic
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (fullyFaithful : IncFunctorFullyFaithful F)
    {source target : CObj} :
    IncObjectsIsomorphic D (F.obj source) (F.obj target) →
      IncObjectsIsomorphic C source target := by
  rintro ⟨iso⟩
  exact ⟨fullyFaithful.reflectIso iso⟩

theorem IncFunctorFullyFaithful.objectsIsomorphic_iff
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (fullyFaithful : IncFunctorFullyFaithful F)
    {source target : CObj} :
    IncObjectsIsomorphic C source target ↔
      IncObjectsIsomorphic D (F.obj source) (F.obj target) := by
  constructor
  · exact F.preservesObjectsIsomorphic
  · exact fullyFaithful.reflectsObjectsIsomorphic

theorem IncCategoryEquivalence.forward_objectsIsomorphic_iff
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) {source target : CObj} :
    IncObjectsIsomorphic C source target ↔
      IncObjectsIsomorphic D (equivalence.forward.obj source)
        (equivalence.forward.obj target) :=
  equivalence.forward_fullyFaithful.objectsIsomorphic_iff

theorem incFunctorEssentiallySurjective_iff_isoClassSurjective
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :
    IncFunctorEssentiallySurjective F ↔
      ∀ target : DObj, ∃ source : CObj,
        IncObjectsIsomorphic D (F.obj source) target := by
  constructor
  · intro hF target
    obtain ⟨source, hom, inv, inv_hom, hom_inv⟩ := hF target
    exact ⟨source, ⟨
      { hom := hom
        inv := inv
        inv_hom := inv_hom
        hom_inv := hom_inv }⟩⟩
  · intro hF target
    obtain ⟨source, ⟨iso⟩⟩ := hF target
    exact ⟨source, iso.hom, iso.inv, iso.inv_hom, iso.hom_inv⟩

structure IncFunctorIsoClassBijection
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : Prop where
  reflects : ∀ {source target : CObj},
    IncObjectsIsomorphic D (F.obj source) (F.obj target) →
      IncObjectsIsomorphic C source target
  essentiallySurjective : ∀ target : DObj, ∃ source : CObj,
    IncObjectsIsomorphic D (F.obj source) target

theorem IncFunctorEquivalenceCriterion.isoClassBijection
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    IncFunctorIsoClassBijection F where
  reflects := criterion.fullyFaithful.reflectsObjectsIsomorphic
  essentiallySurjective :=
    (incFunctorEssentiallySurjective_iff_isoClassSurjective F).mp
      criterion.essentiallySurjective

theorem IncCategoryEquivalence.forward_isoClassBijection
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncFunctorIsoClassBijection equivalence.forward :=
  equivalence.forward_criterion.isoClassBijection

def incObjectIsoSetoid {Obj : Type u} (C : IncCategory Obj) : Setoid Obj where
  r := IncObjectsIsomorphic C
  iseqv := incObjectsIsomorphic_equivalence C

def IncObjectIsoClass {Obj : Type u} (C : IncCategory Obj) : Type u :=
  Quotient (incObjectIsoSetoid C)

def IncFunctor.mapObjectIsoClass
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) : IncObjectIsoClass C → IncObjectIsoClass D :=
  Quotient.lift (fun object => Quotient.mk _ (F.obj object)) (by
    intro source target h
    exact Quotient.sound (F.preservesObjectsIsomorphic h))

theorem IncFunctor.mapObjectIsoClass_mk
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) (object : CObj) :
    F.mapObjectIsoClass (Quotient.mk _ object) = Quotient.mk _ (F.obj object) :=
  rfl

theorem IncFunctor.identity_mapObjectIsoClass
    {Obj : Type u} (C : IncCategory Obj) :
    (IncFunctor.identity C).mapObjectIsoClass = id := by
  funext objectClass
  refine Quotient.inductionOn objectClass ?_
  intro object
  rfl

theorem IncFunctor.comp_mapObjectIsoClass
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    (G : IncFunctor D E) (F : IncFunctor C D) :
    (G.comp F).mapObjectIsoClass =
      fun objectClass => G.mapObjectIsoClass (F.mapObjectIsoClass objectClass) := by
  funext objectClass
  refine Quotient.inductionOn objectClass ?_
  intro object
  rfl

theorem IncNaturalIsomorphism.mapObjectIsoClass_eq
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (iso : IncNaturalIsomorphism F G) :
    F.mapObjectIsoClass = G.mapObjectIsoClass := by
  funext objectClass
  refine Quotient.inductionOn objectClass ?_
  intro object
  change Quotient.mk _ (F.obj object) = Quotient.mk _ (G.obj object)
  apply Quotient.sound
  exact ⟨
    { hom := iso.hom.app object
      inv := iso.inv.app object
      inv_hom := iso.hom_app_inv_app object
      hom_inv := iso.inv_app_hom_app object }⟩

theorem IncNaturallyIsomorphic.mapObjectIsoClass_eq
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F G : IncFunctor C D} (h : IncNaturallyIsomorphic F G) :
    F.mapObjectIsoClass = G.mapObjectIsoClass := by
  rcases h with ⟨iso⟩
  exact iso.mapObjectIsoClass_eq

theorem IncNaturallyIsomorphic.comp_mapObjectIsoClass_eq
    {CObj DObj EObj : Type u}
    {C : IncCategory CObj} {D : IncCategory DObj} {E : IncCategory EObj}
    {F G : IncFunctor C D} {H K : IncFunctor D E}
    (outer : IncNaturallyIsomorphic H K)
    (inner : IncNaturallyIsomorphic F G) :
    (H.comp F).mapObjectIsoClass = (K.comp G).mapObjectIsoClass :=
  (outer.hcomp inner).mapObjectIsoClass_eq

theorem IncFunctorFullyFaithful.mapObjectIsoClass_injective
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (fullyFaithful : IncFunctorFullyFaithful F) :
    ∀ left right : IncObjectIsoClass C,
      F.mapObjectIsoClass left = F.mapObjectIsoClass right → left = right := by
  intro left right
  refine Quotient.inductionOn left ?_
  intro source
  refine Quotient.inductionOn right ?_
  intro target equality
  apply Quotient.sound
  apply fullyFaithful.reflectsObjectsIsomorphic
  change Quotient.mk _ (F.obj source) = Quotient.mk _ (F.obj target) at equality
  exact Quotient.exact equality

theorem IncFunctorEssentiallySurjective.mapObjectIsoClass_surjective
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (essentiallySurjective : IncFunctorEssentiallySurjective F) :
    ∀ target : IncObjectIsoClass D,
      ∃ source : IncObjectIsoClass C, F.mapObjectIsoClass source = target := by
  intro target
  refine Quotient.inductionOn target ?_
  intro object
  obtain ⟨source, hom, inv, inv_hom, hom_inv⟩ := essentiallySurjective object
  refine ⟨Quotient.mk _ source, ?_⟩
  change Quotient.mk _ (F.obj source) = Quotient.mk _ object
  apply Quotient.sound
  exact ⟨
    { hom := hom
      inv := inv
      inv_hom := inv_hom
      hom_inv := hom_inv }⟩

theorem IncCategoryEquivalence.forward_mapObjectIsoClass_bijective
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    (∀ left right : IncObjectIsoClass C,
      equivalence.forward.mapObjectIsoClass left =
        equivalence.forward.mapObjectIsoClass right → left = right) ∧
    (∀ target : IncObjectIsoClass D,
      ∃ source : IncObjectIsoClass C,
        equivalence.forward.mapObjectIsoClass source = target) :=
  ⟨equivalence.forward_fullyFaithful.mapObjectIsoClass_injective,
    equivalence.forward_essentiallySurjective.mapObjectIsoClass_surjective⟩

theorem IncCategoryEquivalence.inverse_forward_mapObjectIsoClass
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (objectClass : IncObjectIsoClass C) :
    equivalence.inverse.mapObjectIsoClass
        (equivalence.forward.mapObjectIsoClass objectClass) = objectClass := by
  refine Quotient.inductionOn objectClass ?_
  intro object
  change Quotient.mk _
      (equivalence.inverse.obj (equivalence.forward.obj object)) =
    Quotient.mk _ object
  apply Quotient.sound
  exact ⟨
    { hom := equivalence.unit.inv.app object
      inv := equivalence.unit.hom.app object
      inv_hom := equivalence.unit.inv_app_hom_app object
      hom_inv := equivalence.unit.hom_app_inv_app object }⟩

theorem IncCategoryEquivalence.forward_inverse_mapObjectIsoClass
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (objectClass : IncObjectIsoClass D) :
    equivalence.forward.mapObjectIsoClass
        (equivalence.inverse.mapObjectIsoClass objectClass) = objectClass := by
  refine Quotient.inductionOn objectClass ?_
  intro object
  change Quotient.mk _
      (equivalence.forward.obj (equivalence.inverse.obj object)) =
    Quotient.mk _ object
  apply Quotient.sound
  exact ⟨
    { hom := equivalence.counit.hom.app object
      inv := equivalence.counit.inv.app object
      inv_hom := equivalence.counit.hom_app_inv_app object
      hom_inv := equivalence.counit.inv_app_hom_app object }⟩

structure IncTypeEquivalence (A B : Type u) where
  forward : A → B
  inverse : B → A
  inverse_forward : ∀ value, inverse (forward value) = value
  forward_inverse : ∀ value, forward (inverse value) = value

theorem IncTypeEquivalence.ext {A B : Type u}
    {first second : IncTypeEquivalence A B}
    (forwardEq : first.forward = second.forward)
    (inverseEq : first.inverse = second.inverse) : first = second := by
  cases first
  cases second
  cases forwardEq
  cases inverseEq
  rfl

theorem IncTypeEquivalence.ext_forward {A B : Type u}
    {first second : IncTypeEquivalence A B}
    (forwardEq : first.forward = second.forward) : first = second := by
  apply IncTypeEquivalence.ext forwardEq
  funext value
  have firstAtSecondInverse := first.inverse_forward (second.inverse value)
  rw [forwardEq, second.forward_inverse] at firstAtSecondInverse
  exact firstAtSecondInverse

def IncTypeEquivalence.refl (A : Type u) : IncTypeEquivalence A A where
  forward := id
  inverse := id
  inverse_forward := by intro value; rfl
  forward_inverse := by intro value; rfl

def IncTypeEquivalence.symm {A B : Type u}
    (equivalence : IncTypeEquivalence A B) : IncTypeEquivalence B A where
  forward := equivalence.inverse
  inverse := equivalence.forward
  inverse_forward := equivalence.forward_inverse
  forward_inverse := equivalence.inverse_forward

def IncTypeEquivalence.trans {A B C : Type u}
    (second : IncTypeEquivalence B C) (first : IncTypeEquivalence A B) :
    IncTypeEquivalence A C where
  forward := fun value => second.forward (first.forward value)
  inverse := fun value => first.inverse (second.inverse value)
  inverse_forward := by
    intro value
    rw [second.inverse_forward, first.inverse_forward]
  forward_inverse := by
    intro value
    rw [first.forward_inverse, second.forward_inverse]

theorem IncTypeEquivalence.refl_trans {A B : Type u}
    (equivalence : IncTypeEquivalence A B) :
    equivalence.trans (IncTypeEquivalence.refl A) = equivalence := by
  apply IncTypeEquivalence.ext <;> rfl

theorem IncTypeEquivalence.trans_refl {A B : Type u}
    (equivalence : IncTypeEquivalence A B) :
    (IncTypeEquivalence.refl B).trans equivalence = equivalence := by
  apply IncTypeEquivalence.ext <;> rfl

theorem IncTypeEquivalence.trans_assoc {A B C D : Type u}
    (third : IncTypeEquivalence C D) (second : IncTypeEquivalence B C)
    (first : IncTypeEquivalence A B) :
    (third.trans second).trans first = third.trans (second.trans first) := by
  apply IncTypeEquivalence.ext <;> rfl

theorem IncTypeEquivalence.symm_symm {A B : Type u}
    (equivalence : IncTypeEquivalence A B) :
    equivalence.symm.symm = equivalence := by
  apply IncTypeEquivalence.ext <;> rfl

theorem IncTypeEquivalence.symm_trans_self {A B : Type u}
    (equivalence : IncTypeEquivalence A B) :
    equivalence.symm.trans equivalence = IncTypeEquivalence.refl A := by
  apply IncTypeEquivalence.ext
  · funext value
    exact equivalence.inverse_forward value
  · funext value
    exact equivalence.inverse_forward value

theorem IncTypeEquivalence.trans_symm_self {A B : Type u}
    (equivalence : IncTypeEquivalence A B) :
    equivalence.trans equivalence.symm = IncTypeEquivalence.refl B := by
  apply IncTypeEquivalence.ext
  · funext value
    exact equivalence.forward_inverse value
  · funext value
    exact equivalence.forward_inverse value

def IncDependentFamilyIsomorphism.sumEquivalence
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    IncTypeEquivalence (IncDependentSum source) (IncDependentSum target) where
  forward := iso.hom.mapSum
  inverse := iso.inv.mapSum
  inverse_forward := by
    intro value
    exact congrFun iso.mapSum_inv_hom value
  forward_inverse := by
    intro value
    exact congrFun iso.mapSum_hom_inv value

def IncDependentFamilyIsomorphism.productEquivalence
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    IncTypeEquivalence (IncDependentProduct source) (IncDependentProduct target) where
  forward := iso.hom.mapProduct
  inverse := iso.inv.mapProduct
  inverse_forward := by
    intro value
    exact congrFun iso.mapProduct_inv_hom value
  forward_inverse := by
    intro value
    exact congrFun iso.mapProduct_hom_inv value

def IncDependentFamilyIsomorphism.fiberEquivalence
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) (index : I) :
    IncTypeEquivalence (source.fiber index) (target.fiber index) where
  forward := iso.hom.app index
  inverse := iso.inv.app index
  inverse_forward := iso.inv_hom index
  forward_inverse := iso.hom_inv index

theorem IncDependentFamilyIsomorphism.sumEquivalence_preserves_index
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target)
    (value : IncDependentSum source) :
    (iso.sumEquivalence.forward value).fst = value.fst := by
  rcases value with ⟨index, value⟩
  rfl

theorem IncDependentFamilyIsomorphism.sumEquivalence_on_fiber
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target)
    (index : I) (value : source.fiber index) :
    iso.sumEquivalence.forward ⟨index, value⟩ =
      ⟨index, (iso.fiberEquivalence index).forward value⟩ := by
  rfl

theorem IncDependentFamilyIsomorphism.productEquivalence_evaluate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target)
    (term : IncDependentProduct source) (index : I) :
    iso.productEquivalence.forward term index =
      (iso.fiberEquivalence index).forward (term index) := by
  rfl

theorem IncDependentFamilyIsomorphism.productEquivalence_reindex
    {I R T J : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target)
    (baseMap : J → I) (term : IncDependentProduct source) :
    target.reindexProduct baseMap (iso.productEquivalence.forward term) =
      fun index => (iso.fiberEquivalence (baseMap index)).forward
        (source.reindexProduct baseMap term index) := by
  funext index
  rfl

theorem IncDependentFamilyIsomorphism.sumEquivalence_trans_forward
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    ((secondIso.trans firstIso).sumEquivalence.forward) =
      secondIso.sumEquivalence.forward ∘ firstIso.sumEquivalence.forward := by
  exact IncDependentFamilyMorphism.mapSum_comp secondIso.hom firstIso.hom

theorem IncDependentFamilyIsomorphism.sumEquivalence_trans_inverse
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    ((secondIso.trans firstIso).sumEquivalence.inverse) =
      firstIso.sumEquivalence.inverse ∘ secondIso.sumEquivalence.inverse := by
  exact IncDependentFamilyMorphism.mapSum_comp firstIso.inv secondIso.inv

theorem IncDependentFamilyIsomorphism.productEquivalence_trans_forward
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    ((secondIso.trans firstIso).productEquivalence.forward) =
      secondIso.productEquivalence.forward ∘
        firstIso.productEquivalence.forward := by
  exact IncDependentFamilyMorphism.mapProduct_comp secondIso.hom firstIso.hom

theorem IncDependentFamilyIsomorphism.productEquivalence_trans_inverse
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    ((secondIso.trans firstIso).productEquivalence.inverse) =
      firstIso.productEquivalence.inverse ∘
        secondIso.productEquivalence.inverse := by
  exact IncDependentFamilyMorphism.mapProduct_comp firstIso.inv secondIso.inv

theorem IncDependentFamilyIsomorphism.fiberEquivalence_trans_forward
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) (index : I) :
    ((secondIso.trans firstIso).fiberEquivalence index).forward =
      (secondIso.fiberEquivalence index).forward ∘
        (firstIso.fiberEquivalence index).forward := by
  rfl

theorem IncDependentFamilyIsomorphism.sumEquivalence_trans
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    (secondIso.trans firstIso).sumEquivalence =
      secondIso.sumEquivalence.trans firstIso.sumEquivalence := by
  apply IncTypeEquivalence.ext
  · exact secondIso.sumEquivalence_trans_forward firstIso
  · exact secondIso.sumEquivalence_trans_inverse firstIso

theorem IncDependentFamilyIsomorphism.productEquivalence_trans
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) :
    (secondIso.trans firstIso).productEquivalence =
      secondIso.productEquivalence.trans firstIso.productEquivalence := by
  apply IncTypeEquivalence.ext
  · exact secondIso.productEquivalence_trans_forward firstIso
  · exact secondIso.productEquivalence_trans_inverse firstIso

theorem IncDependentFamilyIsomorphism.fiberEquivalence_trans
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {first second third : IncDependentFamily inc}
    (secondIso : IncDependentFamilyIsomorphism second third)
    (firstIso : IncDependentFamilyIsomorphism first second) (index : I) :
    (secondIso.trans firstIso).fiberEquivalence index =
      (secondIso.fiberEquivalence index).trans
        (firstIso.fiberEquivalence index) := by
  apply IncTypeEquivalence.ext <;> rfl

theorem IncDependentFamilyIsomorphism.sumEquivalence_symm
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.symm.sumEquivalence = iso.sumEquivalence.symm := by
  apply IncTypeEquivalence.ext <;> rfl

theorem IncDependentFamilyIsomorphism.productEquivalence_symm
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) :
    iso.symm.productEquivalence = iso.productEquivalence.symm := by
  apply IncTypeEquivalence.ext <;> rfl

theorem IncDependentFamilyIsomorphism.fiberEquivalence_symm
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {source target : IncDependentFamily inc}
    (iso : IncDependentFamilyIsomorphism source target) (index : I) :
    iso.symm.fiberEquivalence index = (iso.fiberEquivalence index).symm := by
  apply IncTypeEquivalence.ext <;> rfl

def IncCategoryEquivalence.objectIsoClassEquivalence
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    IncTypeEquivalence (IncObjectIsoClass C) (IncObjectIsoClass D) where
  forward := equivalence.forward.mapObjectIsoClass
  inverse := equivalence.inverse.mapObjectIsoClass
  inverse_forward := equivalence.inverse_forward_mapObjectIsoClass
  forward_inverse := equivalence.forward_inverse_mapObjectIsoClass

theorem IncCategoryEquivalence.objectIsoClassEquivalence_forward
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    equivalence.objectIsoClassEquivalence.forward =
      equivalence.forward.mapObjectIsoClass := rfl

theorem IncCategoryEquivalence.objectIsoClassEquivalence_inverse
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    equivalence.objectIsoClassEquivalence.inverse =
      equivalence.inverse.mapObjectIsoClass := rfl

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

structure StrongPushoutPreserving {CObj DObj : Type u} {C : IncCategory CObj}
    {D : IncCategory DObj} (F : IncFunctor C D) {span : MorphismCospan C}
    (po : MorphismPushout span) where
  mapped_pushout : MorphismPushout (F.mapCospan span)
  apex_is_image : mapped_pushout.apex = F.obj po.apex
  inl_is_map :
    Eq.ndrec mapped_pushout.inl apex_is_image = F.map po.inl
  inr_is_map :
    Eq.ndrec mapped_pushout.inr apex_is_image = F.map po.inr

def StrongPushoutPreserving.toPushoutPreserving
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} {span : MorphismCospan C} {po : MorphismPushout span}
    (strong : StrongPushoutPreserving F po) : PushoutPreserving F po where
  mapped_pushout := strong.mapped_pushout
  apex_is_image := strong.apex_is_image

theorem StrongPushoutPreserving.mapped_inl_is_functor_map
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} {span : MorphismCospan C} {po : MorphismPushout span}
    (strong : StrongPushoutPreserving F po) :
    Eq.ndrec strong.mapped_pushout.inl strong.apex_is_image = F.map po.inl :=
  strong.inl_is_map

theorem StrongPushoutPreserving.mapped_inr_is_functor_map
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} {span : MorphismCospan C} {po : MorphismPushout span}
    (strong : StrongPushoutPreserving F po) :
    Eq.ndrec strong.mapped_pushout.inr strong.apex_is_image = F.map po.inr :=
  strong.inr_is_map

def StrongPushoutPreserving.identity
    {Obj : Type u} {C : IncCategory Obj} {span : MorphismCospan C}
    (po : MorphismPushout span) :
    StrongPushoutPreserving (IncFunctor.identity C) po where
  mapped_pushout := po
  apex_is_image := rfl
  inl_is_map := rfl
  inr_is_map := rfl

structure StrongPushoutPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) where
  preserves : ∀ {span : MorphismCospan C} (po : MorphismPushout span),
    StrongPushoutPreserving F po

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

def StrongPushoutPreservingFamily.toPushoutPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (strong : StrongPushoutPreservingFamily F) :
    PushoutPreservingFamily F where
  preserves := fun po => (strong.preserves po).toPushoutPreserving

def StrongPushoutPreservingFamily.identity
    {Obj : Type u} (C : IncCategory Obj) :
    StrongPushoutPreservingFamily (IncFunctor.identity C) where
  preserves := StrongPushoutPreserving.identity

theorem IncCoherentCategoryEquivalence.pulledPushoutCocone_commutes
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} {q : DObj}
    (leftLeg : D.Hom (coherent.equivalence.forward.obj span.b) q)
    (rightLeg : D.Hom (coherent.equivalence.forward.obj span.c) q)
    (commutes :
      D.comp leftLeg (coherent.equivalence.forward.map span.left) =
        D.comp rightLeg (coherent.equivalence.forward.map span.right)) :
    C.comp
        (C.comp (coherent.equivalence.inverse.map leftLeg)
          (coherent.equivalence.unit.hom.app span.b))
        span.left =
      C.comp
        (C.comp (coherent.equivalence.inverse.map rightLeg)
          (coherent.equivalence.unit.hom.app span.c))
        span.right := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  have unitLeft :
      C.comp ((G.comp F).map span.left) (unit.hom.app span.a) =
        C.comp (unit.hom.app span.b) span.left := by
    simpa [IncFunctor.identity] using unit.hom.naturality span.left
  have unitRight :
      C.comp ((G.comp F).map span.right) (unit.hom.app span.a) =
        C.comp (unit.hom.app span.c) span.right := by
    simpa [IncFunctor.identity] using unit.hom.naturality span.right
  calc
    C.comp (C.comp (G.map leftLeg) (unit.hom.app span.b)) span.left =
      C.comp (G.map leftLeg)
        (C.comp (unit.hom.app span.b) span.left) :=
          (C.assoc _ _ _).symm
    _ = C.comp (G.map leftLeg)
        (C.comp ((G.comp F).map span.left) (unit.hom.app span.a)) := by
          rw [unitLeft]
    _ = C.comp
        (C.comp (G.map leftLeg) ((G.comp F).map span.left))
        (unit.hom.app span.a) := C.assoc _ _ _
    _ = C.comp
        (G.map (D.comp leftLeg (F.map span.left)))
        (unit.hom.app span.a) := by
          simp only [IncFunctor.comp]
          rw [G.map_comp]
    _ = C.comp
        (G.map (D.comp rightLeg (F.map span.right)))
        (unit.hom.app span.a) := by rw [commutes]
    _ = C.comp
        (C.comp (G.map rightLeg) ((G.comp F).map span.right))
        (unit.hom.app span.a) := by
          simp only [IncFunctor.comp]
          rw [G.map_comp]
    _ = C.comp (G.map rightLeg)
        (C.comp ((G.comp F).map span.right) (unit.hom.app span.a)) :=
          (C.assoc _ _ _).symm
    _ = C.comp (G.map rightLeg)
        (C.comp (unit.hom.app span.c) span.right) := by
          rw [unitRight]
    _ = C.comp (C.comp (G.map rightLeg) (unit.hom.app span.c))
        span.right := C.assoc _ _ _

def IncCoherentCategoryEquivalence.mappedPushoutLift
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} (po : MorphismPushout span)
    (q : DObj)
    (leftLeg : D.Hom (coherent.equivalence.forward.obj span.b) q)
    (rightLeg : D.Hom (coherent.equivalence.forward.obj span.c) q)
    (commutes :
      D.comp leftLeg (coherent.equivalence.forward.map span.left) =
        D.comp rightLeg (coherent.equivalence.forward.map span.right)) :
    D.Hom (coherent.equivalence.forward.obj po.apex) q :=
  D.comp (coherent.equivalence.counit.hom.app q)
    (coherent.equivalence.forward.map
      (po.lift (coherent.equivalence.inverse.obj q)
        (C.comp (coherent.equivalence.inverse.map leftLeg)
          (coherent.equivalence.unit.hom.app span.b))
        (C.comp (coherent.equivalence.inverse.map rightLeg)
          (coherent.equivalence.unit.hom.app span.c))
        (coherent.pulledPushoutCocone_commutes leftLeg rightLeg commutes)))

theorem IncCoherentCategoryEquivalence.mappedPushoutLift_inl
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} (po : MorphismPushout span)
    (q : DObj)
    (leftLeg : D.Hom (coherent.equivalence.forward.obj span.b) q)
    (rightLeg : D.Hom (coherent.equivalence.forward.obj span.c) q)
    (commutes :
      D.comp leftLeg (coherent.equivalence.forward.map span.left) =
        D.comp rightLeg (coherent.equivalence.forward.map span.right)) :
    D.comp (coherent.mappedPushoutLift po q leftLeg rightLeg commutes)
        (coherent.equivalence.forward.map po.inl) = leftLeg := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  let counit := coherent.equivalence.counit
  let pulledCommutes :=
    coherent.pulledPushoutCocone_commutes leftLeg rightLeg commutes
  let sourceLift := po.lift (G.obj q)
    (C.comp (G.map leftLeg) (unit.hom.app span.b))
    (C.comp (G.map rightLeg) (unit.hom.app span.c)) pulledCommutes
  have sourceLiftInl :
      C.comp sourceLift po.inl =
        C.comp (G.map leftLeg) (unit.hom.app span.b) :=
    po.lift_inl _ _ _ _
  have counitNaturality := counit.hom.naturality leftLeg
  have counitNaturality' :
      D.comp leftLeg (counit.hom.app (F.obj span.b)) =
        D.comp (counit.hom.app q) ((F.comp G).map leftLeg) := by
    simpa [IncFunctor.identity] using counitNaturality
  change D.comp (D.comp (counit.hom.app q) (F.map sourceLift))
      (F.map po.inl) = leftLeg
  calc
    D.comp (D.comp (counit.hom.app q) (F.map sourceLift))
        (F.map po.inl) =
      D.comp (counit.hom.app q)
        (D.comp (F.map sourceLift) (F.map po.inl)) :=
          (D.assoc _ _ _).symm
    _ = D.comp (counit.hom.app q)
        (F.map (C.comp sourceLift po.inl)) := by rw [F.map_comp]
    _ = D.comp (counit.hom.app q)
        (F.map (C.comp (G.map leftLeg) (unit.hom.app span.b))) := by
          rw [sourceLiftInl]
    _ = D.comp (counit.hom.app q)
        (D.comp (F.map (G.map leftLeg))
          (F.map (unit.hom.app span.b))) := by rw [F.map_comp]
    _ = D.comp (counit.hom.app q)
        (D.comp ((F.comp G).map leftLeg)
          (counit.inv.app (F.obj span.b))) := by
            simp only [IncFunctor.comp]
            rw [coherent.counit_inv_forward_eq_map_unit]
    _ = D.comp
        (D.comp (counit.hom.app q) ((F.comp G).map leftLeg))
        (counit.inv.app (F.obj span.b)) := D.assoc _ _ _
    _ = D.comp
        (D.comp leftLeg (counit.hom.app (F.obj span.b)))
        (counit.inv.app (F.obj span.b)) := by
          rw [counitNaturality']
    _ = D.comp leftLeg
        (D.comp (counit.hom.app (F.obj span.b))
          (counit.inv.app (F.obj span.b))) := (D.assoc _ _ _).symm
    _ = D.comp leftLeg (D.id (F.obj span.b)) := by
      simpa [IncFunctor.identity] using congrArg (D.comp leftLeg)
        (counit.inv_app_hom_app (F.obj span.b))
    _ = leftLeg := D.comp_id _

theorem IncCoherentCategoryEquivalence.mappedPushoutLift_inr
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} (po : MorphismPushout span)
    (q : DObj)
    (leftLeg : D.Hom (coherent.equivalence.forward.obj span.b) q)
    (rightLeg : D.Hom (coherent.equivalence.forward.obj span.c) q)
    (commutes :
      D.comp leftLeg (coherent.equivalence.forward.map span.left) =
        D.comp rightLeg (coherent.equivalence.forward.map span.right)) :
    D.comp (coherent.mappedPushoutLift po q leftLeg rightLeg commutes)
        (coherent.equivalence.forward.map po.inr) = rightLeg := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  let counit := coherent.equivalence.counit
  let pulledCommutes :=
    coherent.pulledPushoutCocone_commutes leftLeg rightLeg commutes
  let sourceLift := po.lift (G.obj q)
    (C.comp (G.map leftLeg) (unit.hom.app span.b))
    (C.comp (G.map rightLeg) (unit.hom.app span.c)) pulledCommutes
  have sourceLiftInr :
      C.comp sourceLift po.inr =
        C.comp (G.map rightLeg) (unit.hom.app span.c) :=
    po.lift_inr _ _ _ _
  have counitNaturality' :
      D.comp rightLeg (counit.hom.app (F.obj span.c)) =
        D.comp (counit.hom.app q) ((F.comp G).map rightLeg) := by
    simpa [IncFunctor.identity] using counit.hom.naturality rightLeg
  change D.comp (D.comp (counit.hom.app q) (F.map sourceLift))
      (F.map po.inr) = rightLeg
  calc
    D.comp (D.comp (counit.hom.app q) (F.map sourceLift))
        (F.map po.inr) =
      D.comp (counit.hom.app q)
        (D.comp (F.map sourceLift) (F.map po.inr)) :=
          (D.assoc _ _ _).symm
    _ = D.comp (counit.hom.app q)
        (F.map (C.comp sourceLift po.inr)) := by rw [F.map_comp]
    _ = D.comp (counit.hom.app q)
        (F.map (C.comp (G.map rightLeg) (unit.hom.app span.c))) := by
          rw [sourceLiftInr]
    _ = D.comp (counit.hom.app q)
        (D.comp (F.map (G.map rightLeg))
          (F.map (unit.hom.app span.c))) := by rw [F.map_comp]
    _ = D.comp (counit.hom.app q)
        (D.comp ((F.comp G).map rightLeg)
          (counit.inv.app (F.obj span.c))) := by
            simp only [IncFunctor.comp]
            rw [coherent.counit_inv_forward_eq_map_unit]
    _ = D.comp
        (D.comp (counit.hom.app q) ((F.comp G).map rightLeg))
        (counit.inv.app (F.obj span.c)) := D.assoc _ _ _
    _ = D.comp
        (D.comp rightLeg (counit.hom.app (F.obj span.c)))
        (counit.inv.app (F.obj span.c)) := by
          rw [counitNaturality']
    _ = D.comp rightLeg
        (D.comp (counit.hom.app (F.obj span.c))
          (counit.inv.app (F.obj span.c))) := (D.assoc _ _ _).symm
    _ = D.comp rightLeg (D.id (F.obj span.c)) := by
      simpa [IncFunctor.identity] using congrArg (D.comp rightLeg)
        (counit.inv_app_hom_app (F.obj span.c))
    _ = rightLeg := D.comp_id _

theorem IncCoherentCategoryEquivalence.pulledMediator_eq_sourceLift
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} (po : MorphismPushout span)
    (q : DObj)
    (leftLeg : D.Hom (coherent.equivalence.forward.obj span.b) q)
    (rightLeg : D.Hom (coherent.equivalence.forward.obj span.c) q)
    (commutes :
      D.comp leftLeg (coherent.equivalence.forward.map span.left) =
        D.comp rightLeg (coherent.equivalence.forward.map span.right))
    (mediator : D.Hom (coherent.equivalence.forward.obj po.apex) q)
    (mediator_inl :
      D.comp mediator (coherent.equivalence.forward.map po.inl) = leftLeg)
    (mediator_inr :
      D.comp mediator (coherent.equivalence.forward.map po.inr) = rightLeg) :
    C.comp (coherent.equivalence.inverse.map mediator)
        (coherent.equivalence.unit.hom.app po.apex) =
      po.lift (coherent.equivalence.inverse.obj q)
        (C.comp (coherent.equivalence.inverse.map leftLeg)
          (coherent.equivalence.unit.hom.app span.b))
        (C.comp (coherent.equivalence.inverse.map rightLeg)
          (coherent.equivalence.unit.hom.app span.c))
        (coherent.pulledPushoutCocone_commutes leftLeg rightLeg commutes) := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  apply po.lift_unique
  · calc
      C.comp (C.comp (G.map mediator) (unit.hom.app po.apex)) po.inl =
        C.comp (G.map mediator)
          (C.comp (unit.hom.app po.apex) po.inl) :=
            (C.assoc _ _ _).symm
      _ = C.comp (G.map mediator)
          (C.comp ((G.comp F).map po.inl) (unit.hom.app span.b)) := by
            have naturality := unit.hom.naturality po.inl
            simpa [IncFunctor.identity] using congrArg (C.comp (G.map mediator))
              naturality.symm
      _ = C.comp
          (C.comp (G.map mediator) ((G.comp F).map po.inl))
          (unit.hom.app span.b) := C.assoc _ _ _
      _ = C.comp (G.map (D.comp mediator (F.map po.inl)))
          (unit.hom.app span.b) := by
            simp only [IncFunctor.comp]
            rw [G.map_comp]
      _ = C.comp (G.map leftLeg) (unit.hom.app span.b) := by
            rw [mediator_inl]
  · calc
      C.comp (C.comp (G.map mediator) (unit.hom.app po.apex)) po.inr =
        C.comp (G.map mediator)
          (C.comp (unit.hom.app po.apex) po.inr) :=
            (C.assoc _ _ _).symm
      _ = C.comp (G.map mediator)
          (C.comp ((G.comp F).map po.inr) (unit.hom.app span.c)) := by
            have naturality := unit.hom.naturality po.inr
            simpa [IncFunctor.identity] using congrArg (C.comp (G.map mediator))
              naturality.symm
      _ = C.comp
          (C.comp (G.map mediator) ((G.comp F).map po.inr))
          (unit.hom.app span.c) := C.assoc _ _ _
      _ = C.comp (G.map (D.comp mediator (F.map po.inr)))
          (unit.hom.app span.c) := by
            simp only [IncFunctor.comp]
            rw [G.map_comp]
      _ = C.comp (G.map rightLeg) (unit.hom.app span.c) := by
            rw [mediator_inr]

theorem IncCoherentCategoryEquivalence.mappedPushoutLift_unique
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} (po : MorphismPushout span)
    (q : DObj)
    (leftLeg : D.Hom (coherent.equivalence.forward.obj span.b) q)
    (rightLeg : D.Hom (coherent.equivalence.forward.obj span.c) q)
    (commutes :
      D.comp leftLeg (coherent.equivalence.forward.map span.left) =
        D.comp rightLeg (coherent.equivalence.forward.map span.right))
    (mediator : D.Hom (coherent.equivalence.forward.obj po.apex) q)
    (mediator_inl :
      D.comp mediator (coherent.equivalence.forward.map po.inl) = leftLeg)
    (mediator_inr :
      D.comp mediator (coherent.equivalence.forward.map po.inr) = rightLeg) :
    mediator = coherent.mappedPushoutLift po q leftLeg rightLeg commutes := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  let counit := coherent.equivalence.counit
  let pulledCommutes :=
    coherent.pulledPushoutCocone_commutes leftLeg rightLeg commutes
  let sourceLift := po.lift (G.obj q)
    (C.comp (G.map leftLeg) (unit.hom.app span.b))
    (C.comp (G.map rightLeg) (unit.hom.app span.c)) pulledCommutes
  have pulledMediatorEq :
      C.comp (G.map mediator) (unit.hom.app po.apex) = sourceLift :=
    coherent.pulledMediator_eq_sourceLift po q leftLeg rightLeg commutes
      mediator mediator_inl mediator_inr
  have counitInvNaturality :
      D.comp ((F.comp G).map mediator) (counit.inv.app (F.obj po.apex)) =
        D.comp (counit.inv.app q) mediator := by
    simpa [IncFunctor.identity] using counit.inv.naturality mediator
  change mediator = D.comp (counit.hom.app q) (F.map sourceLift)
  calc
    mediator = D.comp (D.id q) mediator := (D.id_comp mediator).symm
    _ = D.comp
        (D.comp (counit.hom.app q) (counit.inv.app q)) mediator := by
          simpa [IncFunctor.identity] using
            congrArg (fun arrow => D.comp arrow mediator)
              (counit.inv_app_hom_app q).symm
    _ = D.comp (counit.hom.app q)
        (D.comp (counit.inv.app q) mediator) := (D.assoc _ _ _).symm
    _ = D.comp (counit.hom.app q)
        (D.comp ((F.comp G).map mediator)
          (counit.inv.app (F.obj po.apex))) := by
            rw [counitInvNaturality]
    _ = D.comp (counit.hom.app q)
        (D.comp ((F.comp G).map mediator)
          (F.map (unit.hom.app po.apex))) := by
            rw [coherent.counit_inv_forward_eq_map_unit]
    _ = D.comp (counit.hom.app q)
        (D.comp (F.map (G.map mediator))
          (F.map (unit.hom.app po.apex))) := by
            rfl
    _ = D.comp (counit.hom.app q)
        (F.map (C.comp (G.map mediator) (unit.hom.app po.apex))) := by
          rw [F.map_comp]
    _ = D.comp (counit.hom.app q) (F.map sourceLift) := by
          rw [pulledMediatorEq]

def IncCoherentCategoryEquivalence.mapPushout
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} (po : MorphismPushout span) :
    MorphismPushout (coherent.equivalence.forward.mapCospan span) where
  apex := coherent.equivalence.forward.obj po.apex
  inl := coherent.equivalence.forward.map po.inl
  inr := coherent.equivalence.forward.map po.inr
  commutes := functor_maps_pushout_cocone coherent.equivalence.forward po
  lift := coherent.mappedPushoutLift po
  lift_inl := coherent.mappedPushoutLift_inl po
  lift_inr := coherent.mappedPushoutLift_inr po
  lift_unique := by
    intro q leftLeg rightLeg commutes mediator mediator_inl mediator_inr
    exact coherent.mappedPushoutLift_unique po q leftLeg rightLeg commutes
      mediator mediator_inl mediator_inr

def IncCoherentCategoryEquivalence.stronglyPreservesPushout
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {span : MorphismCospan C} (po : MorphismPushout span) :
    StrongPushoutPreserving coherent.equivalence.forward po where
  mapped_pushout := coherent.mapPushout po
  apex_is_image := rfl
  inl_is_map := rfl
  inr_is_map := rfl

def IncCoherentCategoryEquivalence.strongPushoutPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D) :
    StrongPushoutPreservingFamily coherent.equivalence.forward where
  preserves := coherent.stronglyPreservesPushout

def IncCoherentCategoryEquivalence.pushoutPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D) :
    PushoutPreservingFamily coherent.equivalence.forward :=
  coherent.strongPushoutPreservingFamily.toPushoutPreservingFamily

noncomputable def IncCategoryEquivalence.strongPushoutPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongPushoutPreservingFamily equivalence.forward := by
  let coherent := equivalence.coherentReplacement
  have forwardEq : coherent.equivalence.forward = equivalence.forward :=
    equivalence.coherentReplacement_forward
  exact Eq.ndrec coherent.strongPushoutPreservingFamily forwardEq

noncomputable def IncCategoryEquivalence.pushoutPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    PushoutPreservingFamily equivalence.forward :=
  equivalence.strongPushoutPreservingFamily.toPushoutPreservingFamily

abbrev MorphismSpan {Obj : Type u} (C : IncCategory Obj) :=
  MorphismCospan C.op

abbrev MorphismPullback {Obj : Type u} {C : IncCategory Obj}
    (span : MorphismSpan C) :=
  MorphismPushout span

def IncFunctor.mapSpan
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) (span : MorphismSpan C) : MorphismSpan D :=
  F.op.mapCospan span

abbrev StrongPullbackPreserving
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) {span : MorphismSpan C}
    (pullback : MorphismPullback span) :=
  StrongPushoutPreserving F.op pullback

abbrev PullbackPreserving
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) {span : MorphismSpan C}
    (pullback : MorphismPullback span) :=
  PushoutPreserving F.op pullback

abbrev StrongPullbackPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :=
  StrongPushoutPreservingFamily F.op

abbrev PullbackPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :=
  PushoutPreservingFamily F.op

noncomputable def IncFunctorEquivalenceCriterion.strongPullbackPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    StrongPullbackPreservingFamily F :=
  criterion.op.toCoherentCategoryEquivalence.strongPushoutPreservingFamily

noncomputable def IncFunctorEquivalenceCriterion.pullbackPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    PullbackPreservingFamily F :=
  criterion.strongPullbackPreservingFamily.toPushoutPreservingFamily

noncomputable def IncCategoryEquivalence.strongPullbackPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongPullbackPreservingFamily equivalence.forward :=
  equivalence.forward_criterion.strongPullbackPreservingFamily

noncomputable def IncCategoryEquivalence.pullbackPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    PullbackPreservingFamily equivalence.forward :=
  equivalence.forward_criterion.pullbackPreservingFamily

structure StrongBicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) where
  pushouts : StrongPushoutPreservingFamily F
  pullbacks : StrongPullbackPreservingFamily F

structure BicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) where
  pushouts : PushoutPreservingFamily F
  pullbacks : PullbackPreservingFamily F

structure IncInitialObject {Obj : Type u} (C : IncCategory Obj) where
  object : Obj
  to : ∀ target : Obj, C.Hom object target
  unique : ∀ (target : Obj) (morphism : C.Hom object target),
    morphism = to target

abbrev IncTerminalObject {Obj : Type u} (C : IncCategory Obj) :=
  IncInitialObject C.op

def initialObjects_unique_up_to_iso
    {Obj : Type u} {C : IncCategory Obj}
    (first second : IncInitialObject C) :
    MorphismIso C first.object second.object where
  hom := first.to second.object
  inv := second.to first.object
  inv_hom := by
    exact (first.unique first.object _).trans
      (first.unique first.object (C.id first.object)).symm
  hom_inv := by
    exact (second.unique second.object _).trans
      (second.unique second.object (C.id second.object)).symm

def terminalObjects_unique_up_to_iso
    {Obj : Type u} {C : IncCategory Obj}
    (first second : IncTerminalObject C) :
    MorphismIso C first.object second.object := by
  let oppositeIso := initialObjects_unique_up_to_iso (C := C.op) first second
  exact
    { hom := oppositeIso.inv
      inv := oppositeIso.hom
      inv_hom := oppositeIso.inv_hom
      hom_inv := oppositeIso.hom_inv }

def IncCoherentCategoryEquivalence.mapInitialObject
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    (initial : IncInitialObject C) : IncInitialObject D where
  object := coherent.equivalence.forward.obj initial.object
  to := fun target =>
    D.comp (coherent.equivalence.counit.hom.app target)
      (coherent.equivalence.forward.map
        (initial.to (coherent.equivalence.inverse.obj target)))
  unique := by
    intro target morphism
    let F := coherent.equivalence.forward
    let G := coherent.equivalence.inverse
    let unit := coherent.equivalence.unit
    let counit := coherent.equivalence.counit
    have sourceUnique :
        C.comp (G.map morphism) (unit.hom.app initial.object) =
          initial.to (G.obj target) :=
      initial.unique _ _
    have counitInvNaturality :
        D.comp ((F.comp G).map morphism)
            (counit.inv.app (F.obj initial.object)) =
          D.comp (counit.inv.app target) morphism := by
      simpa [IncFunctor.identity] using counit.inv.naturality morphism
    calc
      morphism = D.comp (D.id target) morphism := (D.id_comp morphism).symm
      _ = D.comp (D.comp (counit.hom.app target) (counit.inv.app target))
          morphism := by
            simpa [IncFunctor.identity] using
              congrArg (fun arrow => D.comp arrow morphism)
                (counit.inv_app_hom_app target).symm
      _ = D.comp (counit.hom.app target)
          (D.comp (counit.inv.app target) morphism) :=
            (D.assoc _ _ _).symm
      _ = D.comp (counit.hom.app target)
          (D.comp ((F.comp G).map morphism)
            (counit.inv.app (F.obj initial.object))) := by
              rw [counitInvNaturality]
      _ = D.comp (counit.hom.app target)
          (D.comp ((F.comp G).map morphism)
            (F.map (unit.hom.app initial.object))) := by
              rw [coherent.counit_inv_forward_eq_map_unit]
      _ = D.comp (counit.hom.app target)
          (D.comp (F.map (G.map morphism))
            (F.map (unit.hom.app initial.object))) := by rfl
      _ = D.comp (counit.hom.app target)
          (F.map (C.comp (G.map morphism)
            (unit.hom.app initial.object))) := by rw [F.map_comp]
      _ = D.comp (counit.hom.app target)
          (F.map (initial.to (G.obj target))) := by rw [sourceUnique]

noncomputable def IncFunctorEquivalenceCriterion.mapInitialObject
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (initial : IncInitialObject C) : IncInitialObject D :=
  criterion.toCoherentCategoryEquivalence.mapInitialObject initial

noncomputable def IncFunctorEquivalenceCriterion.mapTerminalObject
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F)
    (terminal : IncTerminalObject C) : IncTerminalObject D :=
  criterion.op.toCoherentCategoryEquivalence.mapInitialObject terminal

noncomputable def IncCategoryEquivalence.mapInitialObject
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (initial : IncInitialObject C) : IncInitialObject D :=
  equivalence.forward_criterion.mapInitialObject initial

noncomputable def IncCategoryEquivalence.mapTerminalObject
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (terminal : IncTerminalObject C) : IncTerminalObject D :=
  equivalence.forward_criterion.mapTerminalObject terminal

theorem IncCategoryEquivalence.mapInitialObject_to_image
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (initial : IncInitialObject C) (target : CObj) :
    (equivalence.mapInitialObject initial).to
        (equivalence.forward.obj target) =
      equivalence.forward.map (initial.to target) := by
  symm
  exact (equivalence.mapInitialObject initial).unique _ _

theorem IncCategoryEquivalence.mapTerminalObject_to_image
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (terminal : IncTerminalObject C) (source : CObj) :
    (equivalence.mapTerminalObject terminal).to
        (equivalence.forward.obj source) =
      equivalence.forward.map (terminal.to source) := by
  symm
  exact (equivalence.mapTerminalObject terminal).unique _ _

theorem IncCategoryEquivalence.initialObject_exists_iff
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    Nonempty (IncInitialObject C) ↔ Nonempty (IncInitialObject D) := by
  constructor
  · rintro ⟨initial⟩
    exact ⟨equivalence.mapInitialObject initial⟩
  · rintro ⟨initial⟩
    exact ⟨equivalence.symm.mapInitialObject initial⟩

theorem IncCategoryEquivalence.terminalObject_exists_iff
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    Nonempty (IncTerminalObject C) ↔ Nonempty (IncTerminalObject D) := by
  constructor
  · rintro ⟨terminal⟩
    exact ⟨equivalence.mapTerminalObject terminal⟩
  · rintro ⟨terminal⟩
    exact ⟨equivalence.symm.mapTerminalObject terminal⟩

structure StrongFiniteBicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) extends StrongBicartesianPreservingFamily F where
  initial : IncInitialObject C → IncInitialObject D
  terminal : IncTerminalObject C → IncTerminalObject D
  initial_object_is_map : ∀ object,
    (initial object).object = F.obj object.object
  terminal_object_is_map : ∀ object,
    (terminal object).object = F.obj object.object

noncomputable def IncFunctorEquivalenceCriterion.strongFiniteBicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    StrongFiniteBicartesianPreservingFamily F where
  pushouts := IncCoherentCategoryEquivalence.strongPushoutPreservingFamily
    criterion.toCoherentCategoryEquivalence
  pullbacks := criterion.strongPullbackPreservingFamily
  initial := criterion.mapInitialObject
  terminal := criterion.mapTerminalObject
  initial_object_is_map := by intro object; rfl
  terminal_object_is_map := by intro object; rfl

noncomputable def IncCategoryEquivalence.strongFiniteBicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongFiniteBicartesianPreservingFamily equivalence.forward :=
  equivalence.forward_criterion.strongFiniteBicartesianPreservingFamily

def binaryProductSpan {Obj : Type u} {C : IncCategory Obj}
    (terminal : IncTerminalObject C) (left right : Obj) : MorphismSpan C where
  a := terminal.object
  b := left
  c := right
  left := terminal.to left
  right := terminal.to right

abbrev IncBinaryProduct {Obj : Type u} {C : IncCategory Obj}
    (terminal : IncTerminalObject C) (left right : Obj) :=
  MorphismPullback (binaryProductSpan terminal left right)

def IncBinaryProduct.pair
    {Obj : Type u} {C : IncCategory Obj}
    {terminal : IncTerminalObject C} {left right : Obj}
    (product : IncBinaryProduct terminal left right)
    (source : Obj) (first : C.Hom source left) (second : C.Hom source right) :
    C.Hom source product.apex :=
  product.lift source first second (by
    exact terminal.unique source _ |>.trans (terminal.unique source _).symm)

theorem IncBinaryProduct.pair_fst
    {Obj : Type u} {C : IncCategory Obj}
    {terminal : IncTerminalObject C} {left right source : Obj}
    (product : IncBinaryProduct terminal left right)
    (first : C.Hom source left) (second : C.Hom source right) :
    C.comp product.inl (product.pair source first second) = first := by
  exact product.lift_inl _ _ _ _

theorem IncBinaryProduct.pair_snd
    {Obj : Type u} {C : IncCategory Obj}
    {terminal : IncTerminalObject C} {left right source : Obj}
    (product : IncBinaryProduct terminal left right)
    (first : C.Hom source left) (second : C.Hom source right) :
    C.comp product.inr (product.pair source first second) = second := by
  exact product.lift_inr _ _ _ _

theorem IncBinaryProduct.pair_unique
    {Obj : Type u} {C : IncCategory Obj}
    {terminal : IncTerminalObject C} {left right source : Obj}
    (product : IncBinaryProduct terminal left right)
    (first : C.Hom source left) (second : C.Hom source right)
    (mediator : C.Hom source product.apex)
    (hfirst : C.comp product.inl mediator = first)
    (hsecond : C.comp product.inr mediator = second) :
    mediator = product.pair source first second := by
  exact product.lift_unique _ _ _ _ mediator hfirst hsecond

def binaryCoproductCospan {Obj : Type u} {C : IncCategory Obj}
    (initial : IncInitialObject C) (left right : Obj) : MorphismCospan C where
  a := initial.object
  b := left
  c := right
  left := initial.to left
  right := initial.to right

abbrev IncBinaryCoproduct {Obj : Type u} {C : IncCategory Obj}
    (initial : IncInitialObject C) (left right : Obj) :=
  MorphismPushout (binaryCoproductCospan initial left right)

def IncBinaryCoproduct.copair
    {Obj : Type u} {C : IncCategory Obj}
    {initial : IncInitialObject C} {left right : Obj}
    (coproduct : IncBinaryCoproduct initial left right)
    (target : Obj) (first : C.Hom left target) (second : C.Hom right target) :
    C.Hom coproduct.apex target :=
  coproduct.lift target first second (by
    exact initial.unique target _ |>.trans (initial.unique target _).symm)

theorem IncBinaryCoproduct.inl_copair
    {Obj : Type u} {C : IncCategory Obj}
    {initial : IncInitialObject C} {left right target : Obj}
    (coproduct : IncBinaryCoproduct initial left right)
    (first : C.Hom left target) (second : C.Hom right target) :
    C.comp (coproduct.copair target first second) coproduct.inl = first :=
  coproduct.lift_inl _ _ _ _

theorem IncBinaryCoproduct.inr_copair
    {Obj : Type u} {C : IncCategory Obj}
    {initial : IncInitialObject C} {left right target : Obj}
    (coproduct : IncBinaryCoproduct initial left right)
    (first : C.Hom left target) (second : C.Hom right target) :
    C.comp (coproduct.copair target first second) coproduct.inr = second :=
  coproduct.lift_inr _ _ _ _

theorem IncBinaryCoproduct.copair_unique
    {Obj : Type u} {C : IncCategory Obj}
    {initial : IncInitialObject C} {left right target : Obj}
    (coproduct : IncBinaryCoproduct initial left right)
    (first : C.Hom left target) (second : C.Hom right target)
    (mediator : C.Hom coproduct.apex target)
    (hfirst : C.comp mediator coproduct.inl = first)
    (hsecond : C.comp mediator coproduct.inr = second) :
    mediator = coproduct.copair target first second :=
  coproduct.lift_unique _ _ _ _ mediator hfirst hsecond

def binaryCoproducts_unique_up_to_iso
    {Obj : Type u} {C : IncCategory Obj}
    {initial : IncInitialObject C} {left right : Obj}
    (first second : IncBinaryCoproduct initial left right) :
    MorphismIso C first.apex second.apex :=
  pushout_unique_up_to_iso first second

def binaryProducts_unique_up_to_iso
    {Obj : Type u} {C : IncCategory Obj}
    {terminal : IncTerminalObject C} {left right : Obj}
    (first second : IncBinaryProduct terminal left right) :
    MorphismIso C first.apex second.apex := by
  let oppositeIso := pushout_unique_up_to_iso (C := C.op) first second
  exact
    { hom := oppositeIso.inv
      inv := oppositeIso.hom
      inv_hom := oppositeIso.inv_hom
      hom_inv := oppositeIso.hom_inv }

theorem binaryCoproductComparison_inl
    {Obj : Type u} {C : IncCategory Obj}
    {initial : IncInitialObject C} {left right : Obj}
    (first second : IncBinaryCoproduct initial left right) :
    C.comp (binaryCoproducts_unique_up_to_iso first second).hom first.inl =
      second.inl :=
  pushoutComparison_inl first second

theorem binaryCoproductComparison_inr
    {Obj : Type u} {C : IncCategory Obj}
    {initial : IncInitialObject C} {left right : Obj}
    (first second : IncBinaryCoproduct initial left right) :
    C.comp (binaryCoproducts_unique_up_to_iso first second).hom first.inr =
      second.inr :=
  pushoutComparison_inr first second

theorem binaryProductComparison_fst
    {Obj : Type u} {C : IncCategory Obj}
    {terminal : IncTerminalObject C} {left right : Obj}
    (first second : IncBinaryProduct terminal left right) :
    C.comp second.inl (binaryProducts_unique_up_to_iso first second).hom =
      first.inl :=
  pushoutComparison_inl second first

theorem binaryProductComparison_snd
    {Obj : Type u} {C : IncCategory Obj}
    {terminal : IncTerminalObject C} {left right : Obj}
    (first second : IncBinaryProduct terminal left right) :
    C.comp second.inr (binaryProducts_unique_up_to_iso first second).hom =
      first.inr :=
  pushoutComparison_inr second first

structure IncEqualizer {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (first second : C.Hom source target) where
  object : Obj
  inclusion : C.Hom object source
  equalizes : C.comp first inclusion = C.comp second inclusion
  lift : ∀ (candidate : Obj) (arrow : C.Hom candidate source),
    C.comp first arrow = C.comp second arrow → C.Hom candidate object
  lift_inclusion : ∀ candidate arrow equality,
    C.comp inclusion (lift candidate arrow equality) = arrow
  lift_unique : ∀ candidate arrow equality (mediator : C.Hom candidate object),
    C.comp inclusion mediator = arrow → mediator = lift candidate arrow equality

abbrev IncCoequalizer {Obj : Type u} {C : IncCategory Obj}
    {source target : Obj} (first second : C.Hom source target) :=
  @IncEqualizer Obj C.op target source first second

def equalizerComparison
    {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    {first second : C.Hom source target}
    (sourceEq targetEq : IncEqualizer first second) :
    C.Hom sourceEq.object targetEq.object :=
  targetEq.lift sourceEq.object sourceEq.inclusion sourceEq.equalizes

theorem equalizerComparison_inclusion
    {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    {first second : C.Hom source target}
    (sourceEq targetEq : IncEqualizer first second) :
    C.comp targetEq.inclusion (equalizerComparison sourceEq targetEq) =
      sourceEq.inclusion :=
  targetEq.lift_inclusion _ _ _

theorem equalizerComparison_self
    {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    {first second : C.Hom source target}
    (equalizer : IncEqualizer first second) :
    equalizerComparison equalizer equalizer = C.id equalizer.object := by
  symm
  apply equalizer.lift_unique
  exact C.comp_id equalizer.inclusion

theorem equalizerComparison_comp
    {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    {first second : C.Hom source target}
    (firstEq secondEq thirdEq : IncEqualizer first second) :
    equalizerComparison firstEq thirdEq =
      C.comp (equalizerComparison secondEq thirdEq)
        (equalizerComparison firstEq secondEq) := by
  symm
  apply thirdEq.lift_unique
  rw [C.assoc, equalizerComparison_inclusion,
    equalizerComparison_inclusion]

def equalizer_unique_up_to_iso
    {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    {first second : C.Hom source target}
    (left right : IncEqualizer first second) :
    MorphismIso C left.object right.object where
  hom := equalizerComparison left right
  inv := equalizerComparison right left
  inv_hom := by
    rw [← equalizerComparison_comp, equalizerComparison_self]
  hom_inv := by
    rw [← equalizerComparison_comp, equalizerComparison_self]

def coequalizer_unique_up_to_iso
    {Obj : Type u} {C : IncCategory Obj} {source target : Obj}
    {first second : C.Hom source target}
    (left right : IncCoequalizer first second) :
    MorphismIso C left.object right.object := by
  let oppositeIso :=
    equalizer_unique_up_to_iso (C := C.op) left right
  exact
    { hom := oppositeIso.inv
      inv := oppositeIso.hom
      inv_hom := oppositeIso.inv_hom
      hom_inv := oppositeIso.hom_inv }

theorem IncCoherentCategoryEquivalence.pulledEqualizerArrow_equalizes
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} (first second : C.Hom source target)
    {candidate : DObj}
    (arrow : D.Hom candidate (coherent.equivalence.forward.obj source))
    (equalizes :
      D.comp (coherent.equivalence.forward.map first) arrow =
        D.comp (coherent.equivalence.forward.map second) arrow) :
    C.comp first
        (C.comp (coherent.equivalence.unit.inv.app source)
          (coherent.equivalence.inverse.map arrow)) =
      C.comp second
        (C.comp (coherent.equivalence.unit.inv.app source)
          (coherent.equivalence.inverse.map arrow)) := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  have firstNaturality :
      C.comp first (unit.inv.app source) =
        C.comp (unit.inv.app target) ((G.comp F).map first) := by
    simpa [IncFunctor.identity] using unit.inv.naturality first
  have secondNaturality :
      C.comp second (unit.inv.app source) =
        C.comp (unit.inv.app target) ((G.comp F).map second) := by
    simpa [IncFunctor.identity] using unit.inv.naturality second
  calc
    C.comp first (C.comp (unit.inv.app source) (G.map arrow)) =
      C.comp (C.comp first (unit.inv.app source)) (G.map arrow) :=
        C.assoc _ _ _
    _ = C.comp
        (C.comp (unit.inv.app target) ((G.comp F).map first))
        (G.map arrow) := by rw [firstNaturality]
    _ = C.comp (unit.inv.app target)
        (C.comp ((G.comp F).map first) (G.map arrow)) :=
          (C.assoc _ _ _).symm
    _ = C.comp (unit.inv.app target)
        (G.map (D.comp (F.map first) arrow)) := by
          simp only [IncFunctor.comp]
          rw [G.map_comp]
    _ = C.comp (unit.inv.app target)
        (G.map (D.comp (F.map second) arrow)) := by rw [equalizes]
    _ = C.comp (unit.inv.app target)
        (C.comp ((G.comp F).map second) (G.map arrow)) := by
          simp only [IncFunctor.comp]
          rw [G.map_comp]
    _ = C.comp
        (C.comp (unit.inv.app target) ((G.comp F).map second))
        (G.map arrow) := C.assoc _ _ _
    _ = C.comp (C.comp second (unit.inv.app source)) (G.map arrow) := by
          rw [secondNaturality]
    _ = C.comp second
        (C.comp (unit.inv.app source) (G.map arrow)) :=
          (C.assoc _ _ _).symm

def IncCoherentCategoryEquivalence.mappedEqualizerLift
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second)
    (candidate : DObj)
    (arrow : D.Hom candidate (coherent.equivalence.forward.obj source))
    (equalizes :
      D.comp (coherent.equivalence.forward.map first) arrow =
        D.comp (coherent.equivalence.forward.map second) arrow) :
    D.Hom candidate (coherent.equivalence.forward.obj equalizer.object) :=
  D.comp
    (coherent.equivalence.forward.map
      (equalizer.lift (coherent.equivalence.inverse.obj candidate)
        (C.comp (coherent.equivalence.unit.inv.app source)
          (coherent.equivalence.inverse.map arrow))
        (coherent.pulledEqualizerArrow_equalizes first second arrow equalizes)))
    (coherent.equivalence.counit.inv.app candidate)

theorem IncCoherentCategoryEquivalence.mappedEqualizerLift_inclusion
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second)
    (candidate : DObj)
    (arrow : D.Hom candidate (coherent.equivalence.forward.obj source))
    (equalizes :
      D.comp (coherent.equivalence.forward.map first) arrow =
        D.comp (coherent.equivalence.forward.map second) arrow) :
    D.comp (coherent.equivalence.forward.map equalizer.inclusion)
        (coherent.mappedEqualizerLift equalizer candidate arrow equalizes) =
      arrow := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  let counit := coherent.equivalence.counit
  let pulledEqualizes :=
    coherent.pulledEqualizerArrow_equalizes first second arrow equalizes
  let sourceLift := equalizer.lift (G.obj candidate)
    (C.comp (unit.inv.app source) (G.map arrow)) pulledEqualizes
  have sourceLiftInclusion :
      C.comp equalizer.inclusion sourceLift =
        C.comp (unit.inv.app source) (G.map arrow) :=
    equalizer.lift_inclusion _ _ _
  have counitNaturality :
      D.comp arrow (counit.hom.app candidate) =
        D.comp (counit.hom.app (F.obj source)) ((F.comp G).map arrow) := by
    simpa [IncFunctor.identity] using counit.hom.naturality arrow
  change D.comp (F.map equalizer.inclusion)
      (D.comp (F.map sourceLift) (counit.inv.app candidate)) = arrow
  calc
    D.comp (F.map equalizer.inclusion)
        (D.comp (F.map sourceLift) (counit.inv.app candidate)) =
      D.comp
        (D.comp (F.map equalizer.inclusion) (F.map sourceLift))
        (counit.inv.app candidate) := D.assoc _ _ _
    _ = D.comp (F.map (C.comp equalizer.inclusion sourceLift))
        (counit.inv.app candidate) := by rw [F.map_comp]
    _ = D.comp (F.map (C.comp (unit.inv.app source) (G.map arrow)))
        (counit.inv.app candidate) := by rw [sourceLiftInclusion]
    _ = D.comp
        (D.comp (F.map (unit.inv.app source)) (F.map (G.map arrow)))
        (counit.inv.app candidate) := by rw [F.map_comp]
    _ = D.comp
        (D.comp (counit.hom.app (F.obj source)) ((F.comp G).map arrow))
        (counit.inv.app candidate) := by
          simp only [IncFunctor.comp]
          rw [coherent.counit_hom_forward_eq_map_unit_inv]
    _ = D.comp
        (D.comp arrow (counit.hom.app candidate))
        (counit.inv.app candidate) := by rw [counitNaturality]
    _ = D.comp arrow
        (D.comp (counit.hom.app candidate) (counit.inv.app candidate)) :=
          (D.assoc _ _ _).symm
    _ = D.comp arrow (D.id candidate) := by
      simpa [IncFunctor.identity] using congrArg (D.comp arrow)
        (counit.inv_app_hom_app candidate)
    _ = arrow := D.comp_id _

theorem IncCoherentCategoryEquivalence.pulledEqualizerMediator_eq_sourceLift
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second)
    (candidate : DObj)
    (arrow : D.Hom candidate (coherent.equivalence.forward.obj source))
    (equalizes :
      D.comp (coherent.equivalence.forward.map first) arrow =
        D.comp (coherent.equivalence.forward.map second) arrow)
    (mediator : D.Hom candidate
      (coherent.equivalence.forward.obj equalizer.object))
    (mediator_inclusion :
      D.comp (coherent.equivalence.forward.map equalizer.inclusion) mediator =
        arrow) :
    C.comp (coherent.equivalence.unit.inv.app equalizer.object)
        (coherent.equivalence.inverse.map mediator) =
      equalizer.lift (coherent.equivalence.inverse.obj candidate)
        (C.comp (coherent.equivalence.unit.inv.app source)
          (coherent.equivalence.inverse.map arrow))
        (coherent.pulledEqualizerArrow_equalizes first second arrow equalizes) := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  apply equalizer.lift_unique
  have inclusionNaturality :
      C.comp equalizer.inclusion (unit.inv.app equalizer.object) =
        C.comp (unit.inv.app source) ((G.comp F).map equalizer.inclusion) := by
    simpa [IncFunctor.identity] using unit.inv.naturality equalizer.inclusion
  calc
    C.comp equalizer.inclusion
        (C.comp (unit.inv.app equalizer.object) (G.map mediator)) =
      C.comp (C.comp equalizer.inclusion (unit.inv.app equalizer.object))
        (G.map mediator) := C.assoc _ _ _
    _ = C.comp
        (C.comp (unit.inv.app source) ((G.comp F).map equalizer.inclusion))
        (G.map mediator) := by rw [inclusionNaturality]
    _ = C.comp (unit.inv.app source)
        (C.comp ((G.comp F).map equalizer.inclusion) (G.map mediator)) :=
          (C.assoc _ _ _).symm
    _ = C.comp (unit.inv.app source)
        (G.map (D.comp (F.map equalizer.inclusion) mediator)) := by
          simp only [IncFunctor.comp]
          rw [G.map_comp]
    _ = C.comp (unit.inv.app source) (G.map arrow) := by
          rw [mediator_inclusion]

theorem IncCoherentCategoryEquivalence.mappedEqualizerLift_unique
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second)
    (candidate : DObj)
    (arrow : D.Hom candidate (coherent.equivalence.forward.obj source))
    (equalizes :
      D.comp (coherent.equivalence.forward.map first) arrow =
        D.comp (coherent.equivalence.forward.map second) arrow)
    (mediator : D.Hom candidate
      (coherent.equivalence.forward.obj equalizer.object))
    (mediator_inclusion :
      D.comp (coherent.equivalence.forward.map equalizer.inclusion) mediator =
        arrow) :
    mediator = coherent.mappedEqualizerLift equalizer candidate arrow equalizes := by
  let F := coherent.equivalence.forward
  let G := coherent.equivalence.inverse
  let unit := coherent.equivalence.unit
  let counit := coherent.equivalence.counit
  let pulledEqualizes :=
    coherent.pulledEqualizerArrow_equalizes first second arrow equalizes
  let sourceLift := equalizer.lift (G.obj candidate)
    (C.comp (unit.inv.app source) (G.map arrow)) pulledEqualizes
  have sourceEq :
      C.comp (unit.inv.app equalizer.object) (G.map mediator) = sourceLift :=
    coherent.pulledEqualizerMediator_eq_sourceLift equalizer candidate arrow
      equalizes mediator mediator_inclusion
  have counitNaturality :
      D.comp mediator (counit.hom.app candidate) =
        D.comp (counit.hom.app (F.obj equalizer.object))
          ((F.comp G).map mediator) := by
    simpa [IncFunctor.identity] using counit.hom.naturality mediator
  change mediator = D.comp (F.map sourceLift) (counit.inv.app candidate)
  calc
    mediator = D.comp mediator (D.id candidate) := (D.comp_id mediator).symm
    _ = D.comp mediator
        (D.comp (counit.hom.app candidate) (counit.inv.app candidate)) := by
          simpa [IncFunctor.identity] using congrArg (D.comp mediator)
            (counit.inv_app_hom_app candidate).symm
    _ = D.comp (D.comp mediator (counit.hom.app candidate))
        (counit.inv.app candidate) := D.assoc _ _ _
    _ = D.comp
        (D.comp (counit.hom.app (F.obj equalizer.object))
          ((F.comp G).map mediator))
        (counit.inv.app candidate) := by rw [counitNaturality]
    _ = D.comp
        (D.comp (F.map (unit.inv.app equalizer.object))
          (F.map (G.map mediator)))
        (counit.inv.app candidate) := by
          simp only [IncFunctor.comp]
          rw [coherent.counit_hom_forward_eq_map_unit_inv]
    _ = D.comp
        (F.map (C.comp (unit.inv.app equalizer.object) (G.map mediator)))
        (counit.inv.app candidate) := by rw [F.map_comp]
    _ = D.comp (F.map sourceLift) (counit.inv.app candidate) := by
          rw [sourceEq]

def IncCoherentCategoryEquivalence.mapEqualizer
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second) :
    IncEqualizer (coherent.equivalence.forward.map first)
      (coherent.equivalence.forward.map second) where
  object := coherent.equivalence.forward.obj equalizer.object
  inclusion := coherent.equivalence.forward.map equalizer.inclusion
  equalizes := by
    rw [← coherent.equivalence.forward.map_comp,
      equalizer.equalizes, coherent.equivalence.forward.map_comp]
  lift := coherent.mappedEqualizerLift equalizer
  lift_inclusion := coherent.mappedEqualizerLift_inclusion equalizer
  lift_unique := by
    intro candidate arrow equalizes mediator mediator_inclusion
    exact coherent.mappedEqualizerLift_unique equalizer candidate arrow equalizes
      mediator mediator_inclusion

theorem IncCoherentCategoryEquivalence.mapEqualizer_object
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second) :
    (coherent.mapEqualizer equalizer).object =
      coherent.equivalence.forward.obj equalizer.object := rfl

theorem IncCoherentCategoryEquivalence.mapEqualizer_inclusion
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (coherent : IncCoherentCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second) :
    (coherent.mapEqualizer equalizer).inclusion =
      coherent.equivalence.forward.map equalizer.inclusion := rfl

structure StrongEqualizerPreserving
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) {source target : CObj}
    {first second : C.Hom source target} (equalizer : IncEqualizer first second) where
  mapped : IncEqualizer (F.map first) (F.map second)
  object_is_image : mapped.object = F.obj equalizer.object
  inclusion_is_map : HEq mapped.inclusion (F.map equalizer.inclusion)

structure StrongEqualizerPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) where
  preserves : ∀ {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second), StrongEqualizerPreserving F equalizer

abbrev StrongCoequalizerPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) :=
  StrongEqualizerPreservingFamily F.op

noncomputable def IncFunctorEquivalenceCriterion.strongEqualizerPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    StrongEqualizerPreservingFamily F where
  preserves := by
    intro source target first second equalizer
    let coherent := criterion.toCoherentCategoryEquivalence
    have forwardEq : coherent.equivalence.forward = F := rfl
    cases forwardEq
    exact
      { mapped := coherent.mapEqualizer equalizer
        object_is_image := rfl
        inclusion_is_map := by
          exact HEq.refl _ }

noncomputable def IncFunctorEquivalenceCriterion.strongCoequalizerPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    StrongCoequalizerPreservingFamily F :=
  criterion.op.strongEqualizerPreservingFamily

noncomputable def IncCategoryEquivalence.strongEqualizerPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongEqualizerPreservingFamily equivalence.forward :=
  equivalence.forward_criterion.strongEqualizerPreservingFamily

noncomputable def IncCategoryEquivalence.strongCoequalizerPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongCoequalizerPreservingFamily equivalence.forward :=
  equivalence.forward_criterion.strongCoequalizerPreservingFamily

noncomputable def IncCategoryEquivalence.mapEqualizer
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second) :
    IncEqualizer (equivalence.forward.map first)
      (equivalence.forward.map second) :=
  (equivalence.strongEqualizerPreservingFamily.preserves equalizer).mapped

theorem IncCategoryEquivalence.mapEqualizer_object
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second) :
    (equivalence.mapEqualizer equalizer).object =
      equivalence.forward.obj equalizer.object :=
  StrongEqualizerPreserving.object_is_image
    (equivalence.strongEqualizerPreservingFamily.preserves equalizer)

theorem IncCategoryEquivalence.mapEqualizer_inclusion
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (equalizer : IncEqualizer first second) :
    HEq (equivalence.mapEqualizer equalizer).inclusion
      (equivalence.forward.map equalizer.inclusion) :=
  StrongEqualizerPreserving.inclusion_is_map
    (equivalence.strongEqualizerPreservingFamily.preserves equalizer)

noncomputable def IncCategoryEquivalence.mapCoequalizer
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (coequalizer : IncCoequalizer first second) :
    IncCoequalizer (equivalence.forward.map first)
      (equivalence.forward.map second) :=
  (equivalence.strongCoequalizerPreservingFamily.preserves coequalizer).mapped

theorem IncCategoryEquivalence.mapCoequalizer_object
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (coequalizer : IncCoequalizer first second) :
    (equivalence.mapCoequalizer coequalizer).object =
      equivalence.forward.obj coequalizer.object :=
  StrongEqualizerPreserving.object_is_image
    (equivalence.strongCoequalizerPreservingFamily.preserves coequalizer)

theorem IncCategoryEquivalence.mapCoequalizer_projection
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    {source target : CObj} {first second : C.Hom source target}
    (coequalizer : IncCoequalizer first second) :
    HEq (equivalence.mapCoequalizer coequalizer).inclusion
      (equivalence.forward.map coequalizer.inclusion) :=
  StrongEqualizerPreserving.inclusion_is_map
    (equivalence.strongCoequalizerPreservingFamily.preserves coequalizer)

structure StrongFiniteLimitColimitPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (F : IncFunctor C D) extends StrongFiniteBicartesianPreservingFamily F where
  equalizers : StrongEqualizerPreservingFamily F
  coequalizers : StrongCoequalizerPreservingFamily F

noncomputable def IncFunctorEquivalenceCriterion.strongFiniteLimitColimitPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    StrongFiniteLimitColimitPreservingFamily F where
  pushouts := IncCoherentCategoryEquivalence.strongPushoutPreservingFamily
    criterion.toCoherentCategoryEquivalence
  pullbacks := criterion.strongPullbackPreservingFamily
  initial := criterion.mapInitialObject
  terminal := criterion.mapTerminalObject
  initial_object_is_map := by intro object; rfl
  terminal_object_is_map := by intro object; rfl
  equalizers := criterion.strongEqualizerPreservingFamily
  coequalizers := criterion.strongCoequalizerPreservingFamily

noncomputable def IncCategoryEquivalence.strongFiniteLimitColimitPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongFiniteLimitColimitPreservingFamily equivalence.forward :=
  equivalence.forward_criterion.strongFiniteLimitColimitPreservingFamily

noncomputable def IncCategoryEquivalence.stronglyPreservesBinaryProduct
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (terminal : IncTerminalObject C) (left right : CObj)
    (product : IncBinaryProduct terminal left right) :
    StrongPullbackPreserving equivalence.forward product :=
  equivalence.strongPullbackPreservingFamily.preserves product

noncomputable def IncCategoryEquivalence.stronglyPreservesBinaryCoproduct
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D)
    (initial : IncInitialObject C) (left right : CObj)
    (coproduct : IncBinaryCoproduct initial left right) :
    StrongPushoutPreserving equivalence.forward coproduct :=
  equivalence.strongPushoutPreservingFamily.preserves coproduct

def StrongBicartesianPreservingFamily.toBicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (strong : StrongBicartesianPreservingFamily F) :
    BicartesianPreservingFamily F where
  pushouts := strong.pushouts.toPushoutPreservingFamily
  pullbacks := strong.pullbacks.toPushoutPreservingFamily

noncomputable def IncFunctorEquivalenceCriterion.strongBicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    {F : IncFunctor C D} (criterion : IncFunctorEquivalenceCriterion F) :
    StrongBicartesianPreservingFamily F where
  pushouts := IncCoherentCategoryEquivalence.strongPushoutPreservingFamily
    criterion.toCoherentCategoryEquivalence
  pullbacks := criterion.strongPullbackPreservingFamily

noncomputable def IncCategoryEquivalence.strongBicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongBicartesianPreservingFamily equivalence.forward :=
  equivalence.forward_criterion.strongBicartesianPreservingFamily

noncomputable def IncCategoryEquivalence.bicartesianPreservingFamily
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    BicartesianPreservingFamily equivalence.forward :=
  StrongBicartesianPreservingFamily.toBicartesianPreservingFamily
    equivalence.strongBicartesianPreservingFamily

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

/- Research cycle 52 (see RESEARCH_LOG.md): the natural 3-entry
   generalization of `boundaryMatched_of_two_entries` above, needed for
   `treeIncidence`'s (and its quotient `treeShapeIncidence`'s) genuinely
   ternary boundaries -- both have exactly 3 role-tagged entries per
   non-leaf element, unlike `pathIncidence`/`simplexIncidence.edgeShape`'s
   2-entry boundaries. Same "caller supplies the witnesses directly"
   shape, one more conjunct. -/
theorem boundaryMatched_of_three_entries {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (rel : I → I → Prop) (i j : I)
  (e1 e2 e3 f1 f2 f3 : Endpoint I R)
  (hbi : inc.boundary i = [e1, e2, e3]) (hbj : inc.boundary j = [f1, f2, f3])
  (hc1 : boundaryCompatible inc e1 f1) (hr1 : rel e1.i f1.i)
  (hc2 : boundaryCompatible inc e2 f2) (hr2 : rel e2.i f2.i)
  (hc3 : boundaryCompatible inc e3 f3) (hr3 : rel e3.i f3.i) :
  boundaryMatched inc rel i j := by
  unfold boundaryMatched
  rw [hbi, hbj]
  constructor
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he
    · subst he; exact ⟨f1, by simp, hc1, hr1⟩
    · subst he; exact ⟨f2, by simp, hc2, hr2⟩
    · subst he; exact ⟨f3, by simp, hc3, hr3⟩
  · intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with he' | he' | he'
    · subst he'; exact ⟨e1, by simp, hc1, hr1⟩
    · subst he'; exact ⟨e2, by simp, hc2, hr2⟩
    · subst he'; exact ⟨e3, by simp, hc3, hr3⟩

/- Research cycle 56 (see RESEARCH_LOG.md): the natural 1-entry
   generalization of `boundaryMatched_of_two_entries`/`_of_three_entries`
   above -- neither prior helper covers a SINGLE-entry boundary (every
   instance built so far with single-entry boundaries, `natIncidence`/
   `cycleIncidence`/`pathIncidence`'s edges, proved `boundaryMatched`
   directly by hand instead). Needed for `mirrorIncidence`'s minimal
   2-element mutual-reference pair, where both sides have exactly one
   entry. Same "caller supplies the witnesses directly" shape. -/
theorem boundaryMatched_of_one_entry {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (rel : I → I → Prop) (i j : I)
  (e f : Endpoint I R)
  (hbi : inc.boundary i = [e]) (hbj : inc.boundary j = [f])
  (hc : boundaryCompatible inc e f) (hr : rel e.i f.i) :
  boundaryMatched inc rel i j := by
  unfold boundaryMatched
  rw [hbi, hbj]
  constructor
  · intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    subst he'; exact ⟨f, by simp, hc, hr⟩
  · intro f' hf'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    subst hf'; exact ⟨e, by simp, hc, hr⟩

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

/- Glue operation matrix correspondence.  Since the minimal `Incidence`
   signature does not prescribe an algebraic formula combining the two input
   rows, the canonical semantics of a successful glue is the actual boundary
   matrix row of its result.  Any stronger merge formula must be supplied as
   an additional compatibility law and proved equal to this semantics. -/
/- Merkle-ID: implementation.linear_algebra.glue_matrix
   The matrix semantics of a successful glue operation. -/
def glue_boundary_matrix {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) {i j k : I}
    (_hglue : inc.glue i j = some k) : I → Int :=
  boundaryMatrix inc idx k

theorem glue_boundary_matrix_represents_result
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) {i j k : I}
    (hglue : inc.glue i j = some k) :
    glue_boundary_matrix inc idx hglue = boundaryMatrix inc idx k := rfl

theorem glue_boundary_matrix_witness_independent
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) {i j k : I}
    (first second : inc.glue i j = some k) :
    glue_boundary_matrix inc idx first = glue_boundary_matrix inc idx second :=
  rfl

/- The exact compatibility condition needed to make glue preserve the chain
   condition.  It is deliberately separate from `Incidence`: the minimal
   incidence signature permits models whose opaque glue operation has no
   relation to boundary data, while chain-compatible models can supply this
   additional law. -/
def GlueBoundaryCompatible {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : Prop :=
  ∀ (idx : List I) {i j k : I}, inc.glue i j = some k →
    (∀ x, boundary_composition inc idx i x = 0) →
    (∀ x, boundary_composition inc idx j x = 0) →
    ∀ x, boundary_composition inc idx k x = 0

/- Merkle-ID: foundation.axiomatization.glue_boundary_preservation
   T1-adjacent: compatible glue preserves the chain condition. -/
theorem glue_preserves_boundary_operator {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (compatible : GlueBoundaryCompatible inc)
    (idx : List I) {i j k : I} (hglue : inc.glue i j = some k)
    (leftSquareZero : ∀ x, boundary_composition inc idx i x = 0)
    (rightSquareZero : ∀ x, boundary_composition inc idx j x = 0) :
    ∀ x, boundary_composition inc idx k x = 0 :=
  compatible idx hglue leftSquareZero rightSquareZero


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

/- A linear invariant is any observation computed solely from a boundary
   matrix.  This abstraction includes rank, determinant, homology summaries,
   and spectral data once their algorithms are supplied; preservation does
   not depend on the particular codomain of the observation. -/
abbrev LinearInvariant (I : Type u) (A : Type v) := Matrix I I Int → A

/- Merkle-ID: foundation.axiomatization.linear_invariants_preserved
   Every matrix-derived invariant is preserved by a translation that
   preserves the boundary matrix pointwise. -/
theorem linear_invariants_preserved
    {I R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] {A : Type v}
    (source : Incidence I R₁ T₁) (target : Incidence I R₂ T₂)
    (idx : List I) (invariant : LinearInvariant I A)
    (preservesBoundary : ∀ i j,
      boundaryMatrix source idx i j = boundaryMatrix target idx i j) :
    invariant (boundaryMatrix source idx) =
      invariant (boundaryMatrix target idx) := by
  apply congrArg invariant
  funext i j
  exact preservesBoundary i j

theorem all_linear_invariants_preserved
    {I R₁ T₁ R₂ T₂ : Type u} [DecidableEq I]
    (source : Incidence I R₁ T₁) (target : Incidence I R₂ T₂)
    (idx : List I)
    (preservesBoundary : ∀ i j,
      boundaryMatrix source idx i j = boundaryMatrix target idx i j) :
    ∀ {A : Type v} (invariant : LinearInvariant I A),
      invariant (boundaryMatrix source idx) =
        invariant (boundaryMatrix target idx) := by
  intro A invariant
  exact linear_invariants_preserved source target idx invariant preservesBoundary

end LinearSemanticsSoundness

/- Merkle-ID: foundation.axiomatization.completeness_theory
   T4: Completeness - linear observations determine equivalence -/
namespace CompletenessTheory

def BisimulationFaithful {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) : Prop :=
  ∀ {i j}, approxBisim inc i j → i = j

/- Linear observation functor -/
/- Merkle-ID: foundation.axiomatization.linear_observation
   Linear observations: boundary matrices, Laplacians, spectra. -/
structure LinearObservation {I R T : Type u} [DecidableEq I]
  (inc : Incidence I R T) (idx : List I) where
  boundary_matrix : Matrix I I Int
  laplacian : Matrix I I Int
  -- spectral data, ranks, etc.

abbrev LinearObservationLanguage
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :=
  LinearObservation inc idx → Prop

def indicatorLinearObservation
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (pivot : I) :
    LinearObservation inc idx :=
  ⟨fun row _ => if row = pivot then (1 : Int) else 0, fun _ _ => 0⟩

def ContainsLinearIndicators
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx) : Prop :=
  ∀ pivot, language (indicatorLinearObservation inc idx pivot)

def indicatorObservationLanguage
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    LinearObservationLanguage inc idx :=
  fun observation => ∃ pivot,
    observation = indicatorLinearObservation inc idx pivot

theorem indicatorObservationLanguage_containsIndicators
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    ContainsLinearIndicators inc idx (indicatorObservationLanguage inc idx) := by
  intro pivot
  exact ⟨pivot, rfl⟩

theorem containsLinearIndicators_iff_indicatorLanguage_included
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx) :
    ContainsLinearIndicators inc idx language ↔
      ∀ observation, indicatorObservationLanguage inc idx observation →
        language observation := by
  constructor
  · intro contains observation indicatorGenerated
    rcases indicatorGenerated with ⟨pivot, rfl⟩
    exact contains pivot
  · intro included pivot
    exact included (indicatorLinearObservation inc idx pivot) ⟨pivot, rfl⟩

theorem indicatorObservationLanguage_least
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (contains : ContainsLinearIndicators inc idx language) :
    ∀ observation, indicatorObservationLanguage inc idx observation →
      language observation :=
  (containsLinearIndicators_iff_indicatorLanguage_included inc idx language).mp
    contains

theorem containsLinearIndicators_mono
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    {smaller larger : LinearObservationLanguage inc idx}
    (included : ∀ observation, smaller observation → larger observation)
    (contains : ContainsLinearIndicators inc idx smaller) :
    ContainsLinearIndicators inc idx larger := by
  intro pivot
  exact included (indicatorLinearObservation inc idx pivot) (contains pivot)

def AgreeOnLinearObservationLanguage
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx) (i j : I) : Prop :=
  ∀ obs, language obs →
    obs.boundary_matrix i = obs.boundary_matrix j ∧
    obs.laplacian i = obs.laplacian j

theorem language_agreement_antitone
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    {smaller larger : LinearObservationLanguage inc idx}
    (included : ∀ observation, smaller observation → larger observation)
    {i j : I}
    (agreesOnLarger : AgreeOnLinearObservationLanguage inc idx larger i j) :
    AgreeOnLinearObservationLanguage inc idx smaller i j := by
  intro observation allowed
  exact agreesOnLarger observation (included observation allowed)

theorem indicator_complete_language_agreement_iff_eq
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (containsIndicators : ContainsLinearIndicators inc idx language)
    (i j : I) :
    AgreeOnLinearObservationLanguage inc idx language i j ↔ i = j := by
  constructor
  · intro agrees
    have rowsEqual :=
      (agrees (indicatorLinearObservation inc idx i) (containsIndicators i)).left
    have atColumn := congrFun rowsEqual j
    by_cases equal : j = i
    · exact equal.symm
    · simp [indicatorLinearObservation, equal] at atColumn
  · intro equal obs allowed
    cases equal
    exact ⟨rfl, rfl⟩

theorem indicator_complete_language_separates_points
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (containsIndicators : ContainsLinearIndicators inc idx language)
    {i j : I} (different : i ≠ j) :
    ∃ obs, language obs ∧
      (obs.boundary_matrix i ≠ obs.boundary_matrix j ∨
       obs.laplacian i ≠ obs.laplacian j) := by
  refine ⟨indicatorLinearObservation inc idx i, containsIndicators i,
    Or.inl ?_⟩
  intro rowsEqual
  have atColumn := congrFun rowsEqual i
  simp [indicatorLinearObservation, Ne.symm different] at atColumn

def languageObservationalSetoid
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (containsIndicators : ContainsLinearIndicators inc idx language) : Setoid I where
  r := AgreeOnLinearObservationLanguage inc idx language
  iseqv := {
    refl := fun i =>
      (indicator_complete_language_agreement_iff_eq inc idx language
        containsIndicators i i).mpr rfl
    symm := fun {i j} related =>
      (indicator_complete_language_agreement_iff_eq inc idx language
        containsIndicators j i).mpr
          ((indicator_complete_language_agreement_iff_eq inc idx language
            containsIndicators i j).mp related).symm
    trans := fun {i j k} first second => by
      apply (indicator_complete_language_agreement_iff_eq inc idx language
        containsIndicators i k).mpr
      exact ((indicator_complete_language_agreement_iff_eq inc idx language
        containsIndicators i j).mp first).trans
          ((indicator_complete_language_agreement_iff_eq inc idx language
            containsIndicators j k).mp second) }

abbrev LanguageObservationQuotient
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (containsIndicators : ContainsLinearIndicators inc idx language) :=
  Quotient (languageObservationalSetoid inc idx language containsIndicators)

def indicatorCompleteLanguageQuotientEquivalence
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (containsIndicators : ContainsLinearIndicators inc idx language) :
    IncTypeEquivalence I
      (LanguageObservationQuotient inc idx language containsIndicators) where
  forward := Quotient.mk
    (languageObservationalSetoid inc idx language containsIndicators)
  inverse := Quotient.lift id (by
    intro i j related
    exact (indicator_complete_language_agreement_iff_eq inc idx language
      containsIndicators i j).mp related)
  inverse_forward := by
    intro value
    rfl
  forward_inverse := by
    intro value
    refine Quotient.inductionOn value ?_
    intro representative
    rfl

theorem indicator_complete_language_bisimulation_completeness
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (containsIndicators : ContainsLinearIndicators inc idx language)
    {i j : I}
    (agrees : AgreeOnLinearObservationLanguage inc idx language i j) :
    approxBisim inc i j := by
  have equal := (indicator_complete_language_agreement_iff_eq inc idx language
    containsIndicators i j).mp agrees
  cases equal
  exact approxBisim_refl inc i

def CompleteLanguageBisimulationSound
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx) : Prop :=
  ∀ {i j}, approxBisim inc i j →
    AgreeOnLinearObservationLanguage inc idx language i j

theorem complete_language_bisimulation_sound_iff_faithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (complete : ContainsLinearIndicators inc idx language) :
    CompleteLanguageBisimulationSound inc idx language ↔
      BisimulationFaithful inc := by
  constructor
  · intro sound i j bisimilar
    exact (indicator_complete_language_agreement_iff_eq inc idx language
      complete i j).mp (sound bisimilar)
  · intro faithful i j bisimilar
    exact (indicator_complete_language_agreement_iff_eq inc idx language
      complete i j).mpr (faithful bisimilar)

theorem complete_language_observational_iff_bisimulation_of_faithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (complete : ContainsLinearIndicators inc idx language)
    (faithful : BisimulationFaithful inc) (i j : I) :
    AgreeOnLinearObservationLanguage inc idx language i j ↔
      approxBisim inc i j := by
  constructor
  · exact indicator_complete_language_bisimulation_completeness
      inc idx language complete
  · exact (complete_language_bisimulation_sound_iff_faithful
      inc idx language complete).mpr faithful

theorem indicator_language_agreement_iff_eq
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (i j : I) :
    AgreeOnLinearObservationLanguage inc idx
      (indicatorObservationLanguage inc idx) i j ↔ i = j :=
  indicator_complete_language_agreement_iff_eq inc idx
    (indicatorObservationLanguage inc idx)
    (indicatorObservationLanguage_containsIndicators inc idx) i j

def indicatorLanguageQuotientEquivalence
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    IncTypeEquivalence I
      (LanguageObservationQuotient inc idx
        (indicatorObservationLanguage inc idx)
        (indicatorObservationLanguage_containsIndicators inc idx)) :=
  indicatorCompleteLanguageQuotientEquivalence inc idx
    (indicatorObservationLanguage inc idx)
    (indicatorObservationLanguage_containsIndicators inc idx)

def completeLanguageQuotientsEquivalent
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (firstIdx secondIdx : List I)
    (firstLanguage : LinearObservationLanguage inc firstIdx)
    (secondLanguage : LinearObservationLanguage inc secondIdx)
    (firstComplete : ContainsLinearIndicators inc firstIdx firstLanguage)
    (secondComplete : ContainsLinearIndicators inc secondIdx secondLanguage) :
    IncTypeEquivalence
      (LanguageObservationQuotient inc firstIdx firstLanguage firstComplete)
      (LanguageObservationQuotient inc secondIdx secondLanguage
        secondComplete) :=
  (indicatorCompleteLanguageQuotientEquivalence inc secondIdx secondLanguage
    secondComplete).trans
      (indicatorCompleteLanguageQuotientEquivalence inc firstIdx firstLanguage
        firstComplete).symm

def indicatorLanguageQuotientsIndexInvariant
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (firstIdx secondIdx : List I) :
    IncTypeEquivalence
      (LanguageObservationQuotient inc firstIdx
        (indicatorObservationLanguage inc firstIdx)
        (indicatorObservationLanguage_containsIndicators inc firstIdx))
      (LanguageObservationQuotient inc secondIdx
        (indicatorObservationLanguage inc secondIdx)
        (indicatorObservationLanguage_containsIndicators inc secondIdx)) :=
  completeLanguageQuotientsEquivalent inc firstIdx secondIdx
    (indicatorObservationLanguage inc firstIdx)
    (indicatorObservationLanguage inc secondIdx)
    (indicatorObservationLanguage_containsIndicators inc firstIdx)
    (indicatorObservationLanguage_containsIndicators inc secondIdx)

theorem language_extension_preserves_completeness
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    {smaller larger : LinearObservationLanguage inc idx}
    (included : ∀ observation, smaller observation → larger observation)
    (smallerContainsIndicators : ContainsLinearIndicators inc idx smaller)
    (i j : I) :
    AgreeOnLinearObservationLanguage inc idx larger i j ↔ i = j :=
  indicator_complete_language_agreement_iff_eq inc idx larger
    (containsLinearIndicators_mono inc idx included smallerContainsIndicators) i j

theorem all_linear_observations_agree_iff_eq
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (i j : I) :
    (∀ obs : LinearObservation inc idx,
      obs.boundary_matrix i = obs.boundary_matrix j ∧
      obs.laplacian i = obs.laplacian j) ↔ i = j := by
  constructor
  · intro observations
    have rowEquality :
        (fun (_ : I) => if i = i then (1 : Int) else 0) =
          (fun (_ : I) => if j = i then (1 : Int) else 0) :=
      (observations
        ⟨fun a _ => if a = i then (1 : Int) else 0, fun _ _ => 0⟩).left
    have valueEquality :
        (if i = i then (1 : Int) else 0) =
          (if j = i then (1 : Int) else 0) :=
      congrFun rowEquality j
    by_cases equal : j = i
    · exact equal.symm
    · simp [equal] at valueEquality
  · intro equal obs
    cases equal
    exact ⟨rfl, rfl⟩

theorem linear_observations_separate_points
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) {i j : I} (different : i ≠ j) :
    ∃ obs : LinearObservation inc idx,
      obs.boundary_matrix i ≠ obs.boundary_matrix j ∨
      obs.laplacian i ≠ obs.laplacian j := by
  let indicator : LinearObservation inc idx :=
    ⟨fun a _ => if a = i then (1 : Int) else 0, fun _ _ => 0⟩
  refine ⟨indicator, Or.inl ?_⟩
  intro rowsEqual
  have atColumn := congrFun rowsEqual i
  simp [indicator, Ne.symm different] at atColumn

def LinearObservationallyEquivalent
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (i j : I) : Prop :=
  ∀ obs : LinearObservation inc idx,
    obs.boundary_matrix i = obs.boundary_matrix j ∧
    obs.laplacian i = obs.laplacian j

theorem linearObservationallyEquivalent_iff_eq
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (i j : I) :
    LinearObservationallyEquivalent inc idx i j ↔ i = j :=
  all_linear_observations_agree_iff_eq inc idx i j

def linearObservationalSetoid
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) : Setoid I where
  r := LinearObservationallyEquivalent inc idx
  iseqv := {
    refl := fun i =>
      (linearObservationallyEquivalent_iff_eq inc idx i i).mpr rfl
    symm := fun {i j} related =>
      (linearObservationallyEquivalent_iff_eq inc idx j i).mpr
        ((linearObservationallyEquivalent_iff_eq inc idx i j).mp related).symm
    trans := fun {i j k} first second => by
      have firstEq : i = j :=
        (linearObservationallyEquivalent_iff_eq inc idx i j).mp first
      have secondEq : j = k :=
        (linearObservationallyEquivalent_iff_eq inc idx j k).mp second
      exact (linearObservationallyEquivalent_iff_eq inc idx i k).mpr
        (firstEq.trans secondEq) }

abbrev LinearObservationQuotient
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :=
  Quotient (linearObservationalSetoid inc idx)

def linearObservationQuotientEquivalence
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    IncTypeEquivalence I (LinearObservationQuotient inc idx) where
  forward := Quotient.mk (linearObservationalSetoid inc idx)
  inverse := Quotient.lift id (by
    intro i j related
    exact (linearObservationallyEquivalent_iff_eq inc idx i j).mp related)
  inverse_forward := by
    intro value
    rfl
  forward_inverse := by
    intro value
    refine Quotient.inductionOn value ?_
    intro representative
    rfl

def observationQuotientToBisimulationQuotient
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    LinearObservationQuotient inc idx → IncidenceQuotient inc :=
  Quotient.lift (Quotient.mk (approxBisimSetoid inc)) (by
    intro i j observationallyEqual
    apply Quotient.sound
    have equal : i = j :=
      (linearObservationallyEquivalent_iff_eq inc idx i j).mp
        observationallyEqual
    cases equal
    exact approxBisim_refl inc i)

theorem observationQuotientToBisimulationQuotient_surjective
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    ∀ target : IncidenceQuotient inc,
      ∃ source : LinearObservationQuotient inc idx,
        observationQuotientToBisimulationQuotient inc idx source = target := by
  intro target
  refine Quotient.inductionOn target ?_
  intro representative
  exact ⟨Quotient.mk (linearObservationalSetoid inc idx) representative, rfl⟩

theorem bisimulationFaithful_of_wellFounded_extensional
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (measure : I → Nat)
    (decreases : ∀ i e, e ∈ inc.boundary i → measure e.i < measure i)
    (extensional : ∀ x y, inc.typeFunc x = inc.typeFunc y →
      boundaryMatched inc (· = ·) x y → x = y) :
    BisimulationFaithful inc := by
  intro i j bisimilar
  rcases bisimilar with ⟨relation, isBisimulation, related⟩
  exact incidence_bisim_faithful inc measure decreases extensional
    isBisimulation i j related

theorem complete_language_soundness_of_wellFounded_extensional
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (complete : ContainsLinearIndicators inc idx language)
    (measure : I → Nat)
    (decreases : ∀ i e, e ∈ inc.boundary i → measure e.i < measure i)
    (extensional : ∀ x y, inc.typeFunc x = inc.typeFunc y →
      boundaryMatched inc (· = ·) x y → x = y) :
    CompleteLanguageBisimulationSound inc idx language :=
  (complete_language_bisimulation_sound_iff_faithful
    inc idx language complete).mpr
      (bisimulationFaithful_of_wellFounded_extensional inc measure
        decreases extensional)

def observationBisimulationQuotientEquivalence
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (faithful : BisimulationFaithful inc) :
    IncTypeEquivalence (LinearObservationQuotient inc idx)
      (IncidenceQuotient inc) where
  forward := observationQuotientToBisimulationQuotient inc idx
  inverse := Quotient.lift
    (Quotient.mk (linearObservationalSetoid inc idx)) (by
      intro i j bisimilar
      apply Quotient.sound
      exact (linearObservationallyEquivalent_iff_eq inc idx i j).mpr
        (faithful bisimilar))
  inverse_forward := by
    intro value
    refine Quotient.inductionOn value ?_
    intro representative
    rfl
  forward_inverse := by
    intro value
    refine Quotient.inductionOn value ?_
    intro representative
    rfl

theorem observationQuotientToBisimulationQuotient_injective_iff_faithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    (∀ {left right : LinearObservationQuotient inc idx},
      observationQuotientToBisimulationQuotient inc idx left =
        observationQuotientToBisimulationQuotient inc idx right →
      left = right) ↔ BisimulationFaithful inc := by
  constructor
  · intro injective i j bisimilar
    have imagesEqual :
        observationQuotientToBisimulationQuotient inc idx
            (Quotient.mk (linearObservationalSetoid inc idx) i) =
          observationQuotientToBisimulationQuotient inc idx
            (Quotient.mk (linearObservationalSetoid inc idx) j) :=
      Quotient.sound bisimilar
    have observationClassesEqual := injective imagesEqual
    exact (linearObservationallyEquivalent_iff_eq inc idx i j).mp
      (Quotient.exact observationClassesEqual)
  · intro faithful left right imagesEqual
    let equivalence := observationBisimulationQuotientEquivalence inc idx faithful
    have inverseImagesEqual :
        equivalence.inverse (equivalence.forward left) =
          equivalence.inverse (equivalence.forward right) :=
      congrArg equivalence.inverse imagesEqual
    rw [equivalence.inverse_forward, equivalence.inverse_forward]
      at inverseImagesEqual
    exact inverseImagesEqual

theorem observationQuotientToBisimulationQuotient_bijective_iff_faithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    ((∀ {left right : LinearObservationQuotient inc idx},
        observationQuotientToBisimulationQuotient inc idx left =
          observationQuotientToBisimulationQuotient inc idx right →
        left = right) ∧
      (∀ target : IncidenceQuotient inc,
        ∃ source : LinearObservationQuotient inc idx,
          observationQuotientToBisimulationQuotient inc idx source = target)) ↔
      BisimulationFaithful inc := by
  constructor
  · intro bijective
    exact (observationQuotientToBisimulationQuotient_injective_iff_faithful
      inc idx).mp bijective.left
  · intro faithful
    exact ⟨
      (observationQuotientToBisimulationQuotient_injective_iff_faithful
        inc idx).mpr faithful,
      observationQuotientToBisimulationQuotient_surjective inc idx⟩

theorem observationQuotientToBisimulationQuotient_kernel
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (left right : LinearObservationQuotient inc idx) :
    observationQuotientToBisimulationQuotient inc idx left =
        observationQuotientToBisimulationQuotient inc idx right ↔
      approxBisim inc
        ((linearObservationQuotientEquivalence inc idx).inverse left)
        ((linearObservationQuotientEquivalence inc idx).inverse right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftRepresentative rightRepresentative
  change (Quotient.mk (approxBisimSetoid inc) leftRepresentative =
      Quotient.mk (approxBisimSetoid inc) rightRepresentative) ↔
    approxBisim inc leftRepresentative rightRepresentative
  constructor
  · exact Quotient.exact
  · intro bisimilar
    exact @Quotient.sound I (approxBisimSetoid inc)
      leftRepresentative rightRepresentative bisimilar

theorem distinct_bisimilar_points_witness_observation_map_noninjective
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) {i j : I}
    (different : i ≠ j) (bisimilar : approxBisim inc i j) :
    ∃ left right : LinearObservationQuotient inc idx,
      left ≠ right ∧
      observationQuotientToBisimulationQuotient inc idx left =
        observationQuotientToBisimulationQuotient inc idx right := by
  let left := Quotient.mk (linearObservationalSetoid inc idx) i
  let right := Quotient.mk (linearObservationalSetoid inc idx) j
  refine ⟨left, right, ?_, ?_⟩
  · intro equal
    apply different
    exact (linearObservationallyEquivalent_iff_eq inc idx i j).mp
      (Quotient.exact equal)
  · exact @Quotient.sound I (approxBisimSetoid inc) i j bisimilar

def ObservationMapCollapses
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) : Prop :=
  ∃ left right : LinearObservationQuotient inc idx,
    left ≠ right ∧
    observationQuotientToBisimulationQuotient inc idx left =
      observationQuotientToBisimulationQuotient inc idx right

theorem observationMapCollapses_iff_exists_distinct_bisimilar
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    ObservationMapCollapses inc idx ↔
      ∃ i j : I, i ≠ j ∧ approxBisim inc i j := by
  constructor
  · rintro ⟨left, right, classesDifferent, imagesEqual⟩
    let carrierEquivalence := linearObservationQuotientEquivalence inc idx
    let i := carrierEquivalence.inverse left
    let j := carrierEquivalence.inverse right
    refine ⟨i, j, ?_, ?_⟩
    · intro equal
      apply classesDifferent
      have forwardEqual : carrierEquivalence.forward i =
          carrierEquivalence.forward j := congrArg carrierEquivalence.forward equal
      rw [carrierEquivalence.forward_inverse,
        carrierEquivalence.forward_inverse] at forwardEqual
      exact forwardEqual
    · exact (observationQuotientToBisimulationQuotient_kernel
        inc idx left right).mp imagesEqual
  · rintro ⟨i, j, different, bisimilar⟩
    exact distinct_bisimilar_points_witness_observation_map_noninjective
      inc idx different bisimilar

theorem observationMapCollapses_implies_not_faithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (collapses : ObservationMapCollapses inc idx) :
    ¬ BisimulationFaithful inc := by
  intro faithful
  obtain ⟨i, j, different, bisimilar⟩ :=
    (observationMapCollapses_iff_exists_distinct_bisimilar inc idx).mp collapses
  exact different (faithful bisimilar)

theorem observationMapCollapses_iff_not_faithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    ObservationMapCollapses inc idx ↔ ¬ BisimulationFaithful inc := by
  constructor
  · exact observationMapCollapses_implies_not_faithful inc idx
  · intro notFaithful
    classical
    exact Classical.byContradiction (fun noCollapse => by
      apply notFaithful
      apply (observationQuotientToBisimulationQuotient_injective_iff_faithful
        inc idx).mp
      intro left right imagesEqual
      exact Classical.byContradiction (fun classesDifferent =>
        noCollapse ⟨left, right, classesDifferent, imagesEqual⟩))

theorem observationMapDoesNotCollapse_iff_faithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) :
    (¬ ObservationMapCollapses inc idx) ↔ BisimulationFaithful inc := by
  classical
  constructor
  · intro noCollapse
    apply (observationQuotientToBisimulationQuotient_injective_iff_faithful
      inc idx).mp
    intro left right imagesEqual
    by_cases equal : left = right
    · exact equal
    · exact False.elim (noCollapse ⟨left, right, equal, imagesEqual⟩)
  · intro faithful
    intro collapses
    exact (observationMapCollapses_implies_not_faithful inc idx collapses)
      faithful

theorem nonfaithful_has_bisimilar_observational_counterexample
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (complete : ContainsLinearIndicators inc idx language)
    (notFaithful : ¬ BisimulationFaithful inc) :
    ∃ i j : I, approxBisim inc i j ∧
      ∃ observation, language observation ∧
        (observation.boundary_matrix i ≠ observation.boundary_matrix j ∨
         observation.laplacian i ≠ observation.laplacian j) := by
  have collapses : ObservationMapCollapses inc idx :=
    (observationMapCollapses_iff_not_faithful inc idx).mpr notFaithful
  obtain ⟨i, j, different, bisimilar⟩ :=
    (observationMapCollapses_iff_exists_distinct_bisimilar inc idx).mp collapses
  obtain ⟨observation, allowed, distinguishes⟩ :=
    indicator_complete_language_separates_points inc idx language complete
      different
  exact ⟨i, j, bisimilar, observation, allowed, distinguishes⟩

theorem complete_language_unsound_of_nonfaithful
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (complete : ContainsLinearIndicators inc idx language)
    (notFaithful : ¬ BisimulationFaithful inc) :
    ¬ CompleteLanguageBisimulationSound inc idx language := by
  intro sound
  exact notFaithful
    ((complete_language_bisimulation_sound_iff_faithful
      inc idx language complete).mp sound)

def observationBisimulationQuotientEquivalence_of_wellFounded_extensional
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I) (measure : I → Nat)
    (decreases : ∀ i e, e ∈ inc.boundary i → measure e.i < measure i)
    (extensional : ∀ x y, inc.typeFunc x = inc.typeFunc y →
      boundaryMatched inc (· = ·) x y → x = y) :
    IncTypeEquivalence (LinearObservationQuotient inc idx)
      (IncidenceQuotient inc) :=
  observationBisimulationQuotientEquivalence inc idx
    (bisimulationFaithful_of_wellFounded_extensional inc measure
      decreases extensional)

def carrierBisimulationQuotientEquivalence
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (faithful : BisimulationFaithful inc) :
    IncTypeEquivalence I (IncidenceQuotient inc) :=
  (observationBisimulationQuotientEquivalence inc idx faithful).trans
    (linearObservationQuotientEquivalence inc idx)

def completeLanguageBisimulationQuotientEquivalence
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (complete : ContainsLinearIndicators inc idx language)
    (faithful : BisimulationFaithful inc) :
    IncTypeEquivalence
      (LanguageObservationQuotient inc idx language complete)
      (IncidenceQuotient inc) :=
  (carrierBisimulationQuotientEquivalence inc idx faithful).trans
    (indicatorCompleteLanguageQuotientEquivalence inc idx language complete).symm

def completeLanguageBisimulationQuotientEquivalence_of_wellFounded_extensional
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (idx : List I)
    (language : LinearObservationLanguage inc idx)
    (complete : ContainsLinearIndicators inc idx language)
    (measure : I → Nat)
    (decreases : ∀ i e, e ∈ inc.boundary i → measure e.i < measure i)
    (extensional : ∀ x y, inc.typeFunc x = inc.typeFunc y →
      boundaryMatched inc (· = ·) x y → x = y) :
    IncTypeEquivalence
      (LanguageObservationQuotient inc idx language complete)
      (IncidenceQuotient inc) :=
  completeLanguageBisimulationQuotientEquivalence inc idx language complete
    (bisimulationFaithful_of_wellFounded_extensional inc measure
      decreases extensional)

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
  have hij : i = j :=
    (all_linear_observations_agree_iff_eq inc idx i j).mp h_observations
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

structure IncLiftedObject (Obj : Type u) : Type (u + 1) where
  down : Obj

structure IncDiscreteHom {Obj : Type u}
    (source target : IncLiftedObject Obj) : Type (u + 1) where
  equality : source = target

structure IncLiftedFunction (source target : Type u) : Type (u + 1) where
  function : source → target

theorem IncLiftedFunction.ext {source target : Type u}
    {first second : IncLiftedFunction source target}
    (functionEq : first.function = second.function) : first = second := by
  cases first
  cases second
  cases functionEq
  rfl

def incDiscreteCategory (Obj : Type u) : IncCategory (IncLiftedObject Obj) where
  Hom := IncDiscreteHom
  id := fun _ => ⟨rfl⟩
  comp := fun second first => ⟨first.equality.trans second.equality⟩
  id_comp := by
    intro source target morphism
    rcases morphism with ⟨morphism⟩
    cases morphism
    rfl
  comp_id := by
    intro source target morphism
    rcases morphism with ⟨morphism⟩
    cases morphism
    rfl
  assoc := by
    intro a b c d first second third
    rcases third with ⟨third⟩
    rcases second with ⟨second⟩
    rcases first with ⟨first⟩
    cases third
    cases second
    cases first
    rfl

def incTypeCategory : IncCategory (Type u) where
  Hom := IncLiftedFunction
  id := fun _ => ⟨id⟩
  comp := fun second first => ⟨second.function ∘ first.function⟩
  id_comp := by intro source target morphism; cases morphism; rfl
  comp_id := by intro source target morphism; cases morphism; rfl
  assoc := by intro a b c d first second third; cases first; cases second; cases third; rfl

def incToSetFunctor {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) :
    IncFunctor (incDiscreteCategory I) incTypeCategory where
  obj := fun i => inc_to_set inc i.down
  map := by
    intro source target equal
    rcases equal with ⟨equal⟩
    cases equal
    exact ⟨id⟩
  map_id := by
    intro object
    rfl
  map_comp := by
    intro source middle target second first
    rcases first with ⟨firstEqual⟩
    rcases second with ⟨secondEqual⟩
    cases firstEqual
    cases secondEqual
    rfl

theorem incToSetFunctor_obj {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) :
    (incToSetFunctor inc).obj ⟨i⟩ = inc_to_set inc i := rfl

theorem incToSetFunctor_faithful {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) :
    ∀ {source target} (left right :
      (incDiscreteCategory I).Hom source target),
      (incToSetFunctor inc).map left = (incToSetFunctor inc).map right →
        left = right := by
  intro source target left right _
  cases left
  cases right
  rfl

def incToSetDefault {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) : inc_to_set inc i := by
  unfold inc_to_set
  cases inc.boundary i with
  | nil => exact ⟨false⟩
  | cons head tail => exact ⟨()⟩

theorem incToSetFunctor_not_full_of_distinct
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) {i j : I} (different : i ≠ j) :
    ¬ (∀ (morphism : incTypeCategory.Hom
        ((incToSetFunctor inc).obj ⟨i⟩) ((incToSetFunctor inc).obj ⟨j⟩)),
      ∃ preimage : (incDiscreteCategory I).Hom ⟨i⟩ ⟨j⟩,
        (incToSetFunctor inc).map preimage = morphism) := by
  intro full
  let constant : incTypeCategory.Hom
      ((incToSetFunctor inc).obj ⟨i⟩) ((incToSetFunctor inc).obj ⟨j⟩) :=
    ⟨fun _ => incToSetDefault inc j⟩
  obtain ⟨preimage, _⟩ := full constant
  apply different
  exact congrArg IncLiftedObject.down preimage.equality

theorem incToSetFunctor_full_implies_subsingleton
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    (full : ∀ {source target}
      (morphism : incTypeCategory.Hom
        ((incToSetFunctor inc).obj source) ((incToSetFunctor inc).obj target)),
      ∃ preimage : (incDiscreteCategory I).Hom source target,
        (incToSetFunctor inc).map preimage = morphism) :
    ∀ i j : I, i = j := by
  intro i j
  let constant : incTypeCategory.Hom
      ((incToSetFunctor inc).obj ⟨i⟩) ((incToSetFunctor inc).obj ⟨j⟩) :=
    ⟨fun _ => incToSetDefault inc j⟩
  obtain ⟨preimage, _⟩ := full constant
  exact congrArg IncLiftedObject.down preimage.equality

theorem incToSetFunctor_fullyFaithful_implies_subsingleton
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    (fullyFaithful : IncFunctorFullyFaithful (incToSetFunctor inc)) :
    ∀ i j : I, i = j :=
  incToSetFunctor_full_implies_subsingleton inc fullyFaithful.full

theorem incToSetFunctor_map_endomorphism_eq_identity
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I)
    (morphism : (incDiscreteCategory I).Hom ⟨i⟩ ⟨i⟩) :
    (incToSetFunctor inc).map morphism =
      incTypeCategory.id ((incToSetFunctor inc).obj ⟨i⟩) := by
  rcases morphism with ⟨equal⟩
  have equalRfl : equal = rfl := Subsingleton.elim _ _
  cases equalRfl
  rfl

theorem incToSetFunctor_full_implies_fiber_subsingleton
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    (full : ∀ {source target}
      (morphism : incTypeCategory.Hom
        ((incToSetFunctor inc).obj source) ((incToSetFunctor inc).obj target)),
      ∃ preimage : (incDiscreteCategory I).Hom source target,
        (incToSetFunctor inc).map preimage = morphism) :
    ∀ i (left right : inc_to_set inc i), left = right := by
  intro i left right
  let constant : incTypeCategory.Hom
      ((incToSetFunctor inc).obj ⟨i⟩) ((incToSetFunctor inc).obj ⟨i⟩) :=
    ⟨fun _ => right⟩
  obtain ⟨preimage, imageEqual⟩ := full constant
  have identityEqualConstant :
      incTypeCategory.id ((incToSetFunctor inc).obj ⟨i⟩) = constant :=
    (incToSetFunctor_map_endomorphism_eq_identity inc i preimage).symm.trans
      imageEqual
  have functionEqual := congrArg IncLiftedFunction.function identityEqualConstant
  exact congrFun functionEqual left

theorem incToSet_nullary_not_subsingleton
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) (nullary : inc.boundary i = []) :
    ¬ (∀ left right : inc_to_set inc i, left = right) := by
  unfold inc_to_set
  rw [nullary]
  intro subsingleton
  have impossible := subsingleton (ULift.up true) (ULift.up false)
  have : (true : Bool) = false := congrArg ULift.down impossible
  contradiction

theorem incToSetFunctor_full_implies_all_nonNullary
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    (full : ∀ {source target}
      (morphism : incTypeCategory.Hom
        ((incToSetFunctor inc).obj source) ((incToSetFunctor inc).obj target)),
      ∃ preimage : (incDiscreteCategory I).Hom source target,
        (incToSetFunctor inc).map preimage = morphism) :
    ∀ i, inc.boundary i ≠ [] := by
  intro i nullary
  exact incToSet_nullary_not_subsingleton inc i nullary
    (incToSetFunctor_full_implies_fiber_subsingleton inc full i)

theorem incToSetFunctor_not_fullyFaithful_of_distinct
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) {i j : I} (different : i ≠ j) :
    ¬ IncFunctorFullyFaithful (incToSetFunctor inc) := by
  intro fullyFaithful
  exact incToSetFunctor_not_full_of_distinct inc different
    fullyFaithful.full

theorem incToSet_nonNullary_subsingleton
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (i : I) (nonNullary : inc.boundary i ≠ []) :
    ∀ left right : inc_to_set inc i, left = right := by
  unfold inc_to_set
  cases boundaryEq : inc.boundary i with
  | nil => exact False.elim (nonNullary boundaryEq)
  | cons head tail =>
      intro left right
      rcases left with ⟨left⟩
      rcases right with ⟨right⟩
      cases left
      cases right
      rfl

theorem incToSetFunctor_fullyFaithful_of_subsingleton_all_nonNullary
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    (subsingleton : ∀ i j : I, i = j)
    (allNonNullary : ∀ i, inc.boundary i ≠ []) :
    IncFunctorFullyFaithful (incToSetFunctor inc) where
  faithful := incToSetFunctor_faithful inc
  full := by
    intro source target morphism
    have objectEqual : source = target := by
      cases source with
      | mk source =>
          cases target with
          | mk target =>
              cases subsingleton source target
              rfl
    cases objectEqual
    refine ⟨⟨rfl⟩, ?_⟩
    apply IncLiftedFunction.ext
    funext value
    exact incToSet_nonNullary_subsingleton inc source.down
      (allNonNullary source.down) _ _

theorem incToSetFunctor_fullyFaithful_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    IncFunctorFullyFaithful (incToSetFunctor inc) ↔
      ((∀ i j : I, i = j) ∧ ∀ i, inc.boundary i ≠ []) := by
  constructor
  · intro fullyFaithful
    exact ⟨incToSetFunctor_fullyFaithful_implies_subsingleton inc fullyFaithful,
      incToSetFunctor_full_implies_all_nonNullary inc fullyFaithful.full⟩
  · rintro ⟨subsingleton, allNonNullary⟩
    exact incToSetFunctor_fullyFaithful_of_subsingleton_all_nonNullary inc
      subsingleton allNonNullary

theorem incidence_subsingleton_has_nullary_unit
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T) (subsingleton : ∀ i j : I, i = j) :
    inc.boundary inc.unit = [] := by
  cases boundaryEq : inc.boundary inc.unit with
  | nil => rfl
  | cons endpoint rest =>
      exfalso
      apply inc.well_founded inc.unit
      exact ⟨endpoint, by rw [boundaryEq]; simp,
        subsingleton endpoint.i inc.unit⟩

theorem incToSetFunctor_never_fullyFaithful
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ¬ IncFunctorFullyFaithful (incToSetFunctor inc) := by
  intro fullyFaithful
  obtain ⟨subsingleton, allNonNullary⟩ :=
    (incToSetFunctor_fullyFaithful_iff inc).mp fullyFaithful
  exact allNonNullary inc.unit
    (incidence_subsingleton_has_nullary_unit inc subsingleton)

theorem incToSetFunctor_never_full
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ¬ (∀ {source target}
      (morphism : incTypeCategory.Hom
        ((incToSetFunctor inc).obj source) ((incToSetFunctor inc).obj target)),
      ∃ preimage : (incDiscreteCategory I).Hom source target,
        (incToSetFunctor inc).map preimage = morphism) := by
  intro full
  apply incToSetFunctor_never_fullyFaithful inc
  exact {
    faithful := incToSetFunctor_faithful inc
    full := full }

theorem incToSetFunctor_faithful_but_not_full
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (∀ {source target} (left right :
      (incDiscreteCategory I).Hom source target),
      (incToSetFunctor inc).map left = (incToSetFunctor inc).map right →
        left = right) ∧
    ¬ (∀ {source target}
      (morphism : incTypeCategory.Hom
        ((incToSetFunctor inc).obj source) ((incToSetFunctor inc).obj target)),
      ∃ preimage : (incDiscreteCategory I).Hom source target,
        (incToSetFunctor inc).map preimage = morphism) :=
  ⟨incToSetFunctor_faithful inc, incToSetFunctor_never_full inc⟩

theorem incToSetFunctor_has_morphism_outside_image
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ∃ source target,
      ∃
      (morphism : incTypeCategory.Hom
        ((incToSetFunctor inc).obj source) ((incToSetFunctor inc).obj target)),
      ∀ preimage : (incDiscreteCategory I).Hom source target,
        (incToSetFunctor inc).map preimage ≠ morphism := by
  classical
  exact Classical.byContradiction (fun noWitness => by
    apply incToSetFunctor_never_full inc
    intro source target morphism
    exact Classical.byContradiction (fun noPreimage => by
      apply noWitness
      refine ⟨source, target, morphism, ?_⟩
      intro preimage imageEqual
      exact noPreimage ⟨preimage, imageEqual⟩))

theorem incToSetFunctor_not_essentiallySurjective
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ¬ IncFunctorEssentiallySurjective (incToSetFunctor inc) := by
  intro essentiallySurjective
  obtain ⟨source, hom, inv, inverseHom, homInverse⟩ :=
    essentiallySurjective (ULift Empty)
  have impossible : ULift Empty :=
    hom.function (incToSetDefault inc source.down)
  exact Empty.elim impossible.down

theorem incToSetFunctor_empty_not_in_essential_image
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ∀ source : IncLiftedObject I,
      ¬ (∃ hom : incTypeCategory.Hom
          ((incToSetFunctor inc).obj source) (ULift Empty),
        ∃ inv : incTypeCategory.Hom
          (ULift Empty) ((incToSetFunctor inc).obj source),
          incTypeCategory.comp inv hom =
              incTypeCategory.id ((incToSetFunctor inc).obj source) ∧
            incTypeCategory.comp hom inv =
              incTypeCategory.id (ULift Empty)) := by
  intro source essentialImageWitness
  obtain ⟨hom, inv, inverseHom, homInverse⟩ := essentialImageWitness
  have impossible : ULift Empty :=
    hom.function (incToSetDefault inc source.down)
  exact Empty.elim impossible.down

theorem incToSetFunctor_has_object_outside_essential_image
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ∃ target : Type u, ∀ source : IncLiftedObject I,
      ¬ (∃ hom : incTypeCategory.Hom
          ((incToSetFunctor inc).obj source) target,
        ∃ inv : incTypeCategory.Hom
          target ((incToSetFunctor inc).obj source),
          incTypeCategory.comp inv hom =
              incTypeCategory.id ((incToSetFunctor inc).obj source) ∧
            incTypeCategory.comp hom inv = incTypeCategory.id target) :=
  ⟨ULift Empty, incToSetFunctor_empty_not_in_essential_image inc⟩

theorem incToSetFunctor_has_no_equivalenceCriterion
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ¬ IncFunctorEquivalenceCriterion (incToSetFunctor inc) := by
  intro criterion
  exact incToSetFunctor_not_essentiallySurjective inc
    criterion.essentiallySurjective

theorem incToSetFunctor_is_not_categoryEquivalence_forward
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ¬ (∃ equivalence : IncCategoryEquivalence
        (incDiscreteCategory I) incTypeCategory,
      equivalence.forward = incToSetFunctor inc) := by
  rintro ⟨equivalence, forwardEq⟩
  have criterion := equivalence.forward_criterion
  rw [forwardEq] at criterion
  exact incToSetFunctor_has_no_equivalenceCriterion inc criterion

def inc_to_set_preserves_boundary_shape
    {I R₁ T₁ R₂ T₂ : Type u} [DecidableEq I]
    (source : Incidence I R₁ T₁) (target : Incidence I R₂ T₂)
    (preservesNullary : ∀ i,
      source.boundary i = [] ↔ target.boundary i = []) :
    ∀ i, IncTypeEquivalence (inc_to_set source i) (inc_to_set target i) := by
  intro i
  unfold inc_to_set
  cases sourceBoundary : source.boundary i with
  | nil =>
      have targetNullary : target.boundary i = [] :=
        (preservesNullary i).mp sourceBoundary
      rw [targetNullary]
      exact IncTypeEquivalence.refl (ULift Bool)
  | cons sourceHead sourceTail =>
      cases targetBoundary : target.boundary i with
      | nil =>
          have sourceNullary : source.boundary i = [] :=
            (preservesNullary i).mpr targetBoundary
          rw [sourceBoundary] at sourceNullary
          contradiction
      | cons targetHead targetTail =>
          exact IncTypeEquivalence.refl (ULift Unit)

theorem inc_to_set_fiber_classification
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) :
    (inc.boundary i = [] ∧
      Nonempty (IncTypeEquivalence (inc_to_set inc i) (ULift Bool))) ∨
    (inc.boundary i ≠ [] ∧
      Nonempty (IncTypeEquivalence (inc_to_set inc i) (ULift Unit))) := by
  cases boundaryEq : inc.boundary i with
  | nil =>
      left
      refine ⟨rfl, ?_⟩
      exact ⟨by simpa [inc_to_set, boundaryEq] using
        IncTypeEquivalence.refl (ULift Bool)⟩
  | cons head tail =>
      right
      refine ⟨?_, ?_⟩
      · intro nullary
        cases nullary
      · exact ⟨by simpa [inc_to_set, boundaryEq] using
          IncTypeEquivalence.refl (ULift Unit)⟩

theorem uliftBool_equivalent_uliftUnit_false
    (equivalence : IncTypeEquivalence (ULift Bool) (ULift Unit)) : False := by
  have forwardEqual : equivalence.forward ⟨true⟩ =
      equivalence.forward ⟨false⟩ := by
    rcases valueTrue : equivalence.forward ⟨true⟩ with ⟨valueTrue⟩
    rcases valueFalse : equivalence.forward ⟨false⟩ with ⟨valueFalse⟩
    cases valueTrue
    cases valueFalse
    rfl
  have inverseEqual := congrArg equivalence.inverse forwardEqual
  rw [equivalence.inverse_forward, equivalence.inverse_forward] at inverseEqual
  contradiction

theorem inc_to_set_equivalent_bool_iff_nullary
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) :
    Nonempty (IncTypeEquivalence (inc_to_set inc i) (ULift Bool)) ↔
      inc.boundary i = [] := by
  constructor
  · rintro ⟨equivalence⟩
    cases boundaryEq : inc.boundary i with
    | nil => rfl
    | cons head tail =>
        exfalso
        apply uliftBool_equivalent_uliftUnit_false
        have reversed := equivalence.symm
        simpa [inc_to_set, boundaryEq] using reversed
  · intro nullary
    exact ⟨by simpa [inc_to_set, nullary] using
      IncTypeEquivalence.refl (ULift Bool)⟩

theorem inc_to_set_equivalent_unit_iff_nonNullary
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) :
    Nonempty (IncTypeEquivalence (inc_to_set inc i) (ULift Unit)) ↔
      inc.boundary i ≠ [] := by
  constructor
  · rintro ⟨equivalence⟩ nullary
    apply uliftBool_equivalent_uliftUnit_false
    simpa [inc_to_set, nullary] using equivalence
  · intro nonNullary
    cases boundaryEq : inc.boundary i with
    | nil => exact False.elim (nonNullary boundaryEq)
    | cons head tail =>
        exact ⟨by simpa [inc_to_set, boundaryEq] using
          IncTypeEquivalence.refl (ULift Unit)⟩

theorem inc_to_set_equivalent_reflects_boundary_shape
    {I R₁ T₁ R₂ T₂ : Type u} [DecidableEq I]
    (source : Incidence I R₁ T₁) (target : Incidence I R₂ T₂)
    (i : I)
    (equivalent : IncTypeEquivalence (inc_to_set source i)
      (inc_to_set target i)) :
    source.boundary i = [] ↔ target.boundary i = [] := by
  cases sourceBoundary : source.boundary i with
  | nil =>
      constructor
      · intro _
        cases targetBoundary : target.boundary i with
        | nil => rfl
        | cons head tail =>
            exfalso
            apply uliftBool_equivalent_uliftUnit_false
            simpa [inc_to_set, sourceBoundary, targetBoundary] using equivalent
      · intro _
        rfl
  | cons sourceHead sourceTail =>
      constructor
      · intro impossible
        contradiction
      · intro targetNullary
        exfalso
        apply uliftBool_equivalent_uliftUnit_false
        have reversed := equivalent.symm
        simpa [inc_to_set, sourceBoundary, targetNullary] using reversed

theorem inc_to_set_equivalent_iff_boundary_shape
    {I R₁ T₁ R₂ T₂ : Type u} [DecidableEq I]
    (source : Incidence I R₁ T₁) (target : Incidence I R₂ T₂) :
    (∀ i, Nonempty (IncTypeEquivalence (inc_to_set source i)
      (inc_to_set target i))) ↔
      (∀ i, source.boundary i = [] ↔ target.boundary i = []) := by
  constructor
  · intro equivalences i
    rcases equivalences i with ⟨equivalence⟩
    exact inc_to_set_equivalent_reflects_boundary_shape source target i
      equivalence
  · intro preservesShape i
    exact ⟨inc_to_set_preserves_boundary_shape source target preservesShape i⟩

structure BoundaryShapeTranslation
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂) where
  map : I → J
  preservesReflectsNullary : ∀ i,
    source.boundary i = [] ↔ target.boundary (map i) = []

def boundaryShapeCode
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) : Bool :=
  match inc.boundary i with
  | [] => true
  | _ :: _ => false

theorem boundaryShapeCode_eq_true_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) (i : I) :
    boundaryShapeCode inc i = true ↔ inc.boundary i = [] := by
  cases boundaryEq : inc.boundary i with
  | nil => simp [boundaryShapeCode, boundaryEq]
  | cons head tail => simp [boundaryShapeCode, boundaryEq]

theorem boundaryShapeCode_eq_iff_nullary_iff
    {I R₁ T₁ R₂ T₂ : Type u} [DecidableEq I]
    (source : Incidence I R₁ T₁) (target : Incidence I R₂ T₂) (i : I) :
    boundaryShapeCode source i = boundaryShapeCode target i ↔
      (source.boundary i = [] ↔ target.boundary i = []) := by
  cases sourceBoundary : source.boundary i with
  | nil =>
      cases targetBoundary : target.boundary i with
      | nil => simp [boundaryShapeCode, sourceBoundary, targetBoundary]
      | cons head tail => simp [boundaryShapeCode, sourceBoundary, targetBoundary]
  | cons sourceHead sourceTail =>
      cases targetBoundary : target.boundary i with
      | nil => simp [boundaryShapeCode, sourceBoundary, targetBoundary]
      | cons targetHead targetTail =>
          simp [boundaryShapeCode, sourceBoundary, targetBoundary]

theorem inc_to_set_pointwise_equivalent_iff_boundaryShapeCode_eq
    {I R₁ T₁ R₂ T₂ : Type u} [DecidableEq I]
    (source : Incidence I R₁ T₁) (target : Incidence I R₂ T₂) :
    (∀ i, Nonempty (IncTypeEquivalence (inc_to_set source i)
      (inc_to_set target i))) ↔
      ∀ i, boundaryShapeCode source i = boundaryShapeCode target i := by
  rw [inc_to_set_equivalent_iff_boundary_shape source target]
  constructor
  · intro sameShape i
    exact (boundaryShapeCode_eq_iff_nullary_iff source target i).mpr
      (sameShape i)
  · intro sameCode i
    exact (boundaryShapeCode_eq_iff_nullary_iff source target i).mp
      (sameCode i)

theorem BoundaryShapeTranslation.preservesCode
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target) (i : I) :
    boundaryShapeCode source i = boundaryShapeCode target (translation.map i) := by
  cases sourceBoundary : source.boundary i with
  | nil =>
      have targetNullary :=
        (translation.preservesReflectsNullary i).mp sourceBoundary
      simp [boundaryShapeCode, sourceBoundary, targetNullary]
  | cons sourceHead sourceTail =>
      cases targetBoundary : target.boundary (translation.map i) with
      | nil =>
          have sourceNullary :=
            (translation.preservesReflectsNullary i).mpr targetBoundary
          rw [sourceBoundary] at sourceNullary
          contradiction
      | cons targetHead targetTail =>
          simp [boundaryShapeCode, sourceBoundary, targetBoundary]

def boundaryShapeTranslationOfCodePreserving
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (map : I → J)
    (preservesCode : ∀ i,
      boundaryShapeCode source i = boundaryShapeCode target (map i)) :
    BoundaryShapeTranslation source target where
  map := map
  preservesReflectsNullary := by
    intro i
    rw [← boundaryShapeCode_eq_true_iff source i,
      ← boundaryShapeCode_eq_true_iff target (map i)]
    exact ⟨fun equal => preservesCode i ▸ equal,
      fun equal => (preservesCode i).symm ▸ equal⟩

theorem boundaryShapeTranslation_exists_iff_code_preserving
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    (map : I → J) :
    (∃ translation : BoundaryShapeTranslation source target,
      translation.map = map) ↔
      ∀ i, boundaryShapeCode source i = boundaryShapeCode target (map i) := by
  constructor
  · rintro ⟨translation, rfl⟩
    exact translation.preservesCode
  · intro preservesCode
    exact ⟨boundaryShapeTranslationOfCodePreserving map preservesCode, rfl⟩

def BoundaryShapeTranslation.identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BoundaryShapeTranslation inc inc where
  map := id
  preservesReflectsNullary := by
    intro i
    rfl

def BoundaryShapeTranslation.comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondMap : BoundaryShapeTranslation second third)
    (firstMap : BoundaryShapeTranslation first second) :
    BoundaryShapeTranslation first third where
  map := secondMap.map ∘ firstMap.map
  preservesReflectsNullary := by
    intro i
    exact (firstMap.preservesReflectsNullary i).trans
      (secondMap.preservesReflectsNullary (firstMap.map i))

theorem BoundaryShapeTranslation.ext
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {first second : BoundaryShapeTranslation source target}
    (mapEq : first.map = second.map) : first = second := by
  cases first
  cases second
  cases mapEq
  rfl

theorem BoundaryShapeTranslation.identity_comp
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target) :
    (BoundaryShapeTranslation.identity target).comp translation = translation := by
  apply BoundaryShapeTranslation.ext
  rfl

theorem BoundaryShapeTranslation.comp_identity
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target) :
    translation.comp (BoundaryShapeTranslation.identity source) = translation := by
  apply BoundaryShapeTranslation.ext
  rfl

theorem BoundaryShapeTranslation.comp_assoc
    {I J K L R₁ T₁ R₂ T₂ R₃ T₃ R₄ T₄ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃} {fourth : Incidence L R₄ T₄}
    (thirdMap : BoundaryShapeTranslation third fourth)
    (secondMap : BoundaryShapeTranslation second third)
    (firstMap : BoundaryShapeTranslation first second) :
    (thirdMap.comp secondMap).comp firstMap =
      thirdMap.comp (secondMap.comp firstMap) := by
  apply BoundaryShapeTranslation.ext
  rfl

def BoundaryShapeTranslation.incToSetEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target) (i : I) :
    IncTypeEquivalence (inc_to_set source i)
      (inc_to_set target (translation.map i)) := by
  unfold inc_to_set
  cases sourceBoundary : source.boundary i with
  | nil =>
      have targetNullary : target.boundary (translation.map i) = [] :=
        (translation.preservesReflectsNullary i).mp sourceBoundary
      rw [targetNullary]
      exact IncTypeEquivalence.refl (ULift Bool)
  | cons sourceHead sourceTail =>
      cases targetBoundary : target.boundary (translation.map i) with
      | nil =>
          have sourceNullary : source.boundary i = [] :=
            (translation.preservesReflectsNullary i).mpr targetBoundary
          rw [sourceBoundary] at sourceNullary
          contradiction
      | cons targetHead targetTail =>
          exact IncTypeEquivalence.refl (ULift Unit)

theorem inc_to_set_equivalent_along_map_reflects_boundary_shape
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    (map : I → J) (i : I)
    (equivalent : IncTypeEquivalence (inc_to_set source i)
      (inc_to_set target (map i))) :
    source.boundary i = [] ↔ target.boundary (map i) = [] := by
  cases sourceBoundary : source.boundary i with
  | nil =>
      constructor
      · intro _
        cases targetBoundary : target.boundary (map i) with
        | nil => rfl
        | cons head tail =>
            exfalso
            apply uliftBool_equivalent_uliftUnit_false
            simpa [inc_to_set, sourceBoundary, targetBoundary] using equivalent
      · intro _
        rfl
  | cons sourceHead sourceTail =>
      constructor
      · intro impossible
        contradiction
      · intro targetNullary
        exfalso
        apply uliftBool_equivalent_uliftUnit_false
        have reversed := equivalent.symm
        simpa [inc_to_set, sourceBoundary, targetNullary] using reversed

theorem boundaryShapeTranslation_exists_iff_inc_to_set_equivalent_along_map
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    (map : I → J) :
    (∃ translation : BoundaryShapeTranslation source target,
      translation.map = map) ↔
      ∀ i, Nonempty (IncTypeEquivalence (inc_to_set source i)
        (inc_to_set target (map i))) := by
  constructor
  · rintro ⟨translation, rfl⟩ i
    exact ⟨translation.incToSetEquivalence i⟩
  · intro equivalences
    let translation : BoundaryShapeTranslation source target := {
      map := map
      preservesReflectsNullary := by
        intro i
        rcases equivalences i with ⟨equivalent⟩
        exact inc_to_set_equivalent_along_map_reflects_boundary_shape
          source target map i equivalent }
    exact ⟨translation, rfl⟩

def incDiscreteMapFunctor
    {I J : Type u} (map : I → J) :
    IncFunctor (incDiscreteCategory I) (incDiscreteCategory J) where
  obj := fun i => ⟨map i.down⟩
  map := by
    intro first second morphism
    exact ⟨by
      cases morphism.equality
      rfl⟩
  map_id := by
    intro object
    rfl
  map_comp := by
    intro first second third secondMap firstMap
    rcases firstMap with ⟨firstEqual⟩
    rcases secondMap with ⟨secondEqual⟩
    cases firstEqual
    cases secondEqual
    rfl

def BoundaryShapeTranslation.discreteFunctor
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target) :
    IncFunctor (incDiscreteCategory I) (incDiscreteCategory J) :=
  incDiscreteMapFunctor translation.map

def BoundaryShapeTranslation.incToSetNaturalTransformation
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target) :
    IncNaturalTransformation (incToSetFunctor source)
      ((incToSetFunctor target).comp translation.discreteFunctor) where
  app := fun i => ⟨(translation.incToSetEquivalence i.down).forward⟩
  naturality := by
    intro first second morphism
    rcases morphism with ⟨equal⟩
    cases equal
    rfl

def BoundaryShapeTranslation.incToSetNaturalIsomorphism
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target) :
    IncNaturalIsomorphism (incToSetFunctor source)
      ((incToSetFunctor target).comp translation.discreteFunctor) where
  hom := translation.incToSetNaturalTransformation
  inv := {
    app := fun i => ⟨(translation.incToSetEquivalence i.down).inverse⟩
    naturality := by
      intro first second morphism
      rcases morphism with ⟨equal⟩
      cases equal
      rfl }
  hom_inv_id := by
    apply IncNaturalTransformation.ext
    intro i
    apply IncLiftedFunction.ext
    funext value
    exact (translation.incToSetEquivalence i.down).inverse_forward value
  inv_hom_id := by
    apply IncNaturalTransformation.ext
    intro i
    apply IncLiftedFunction.ext
    funext value
    exact (translation.incToSetEquivalence i.down).forward_inverse value

theorem boundaryShapeTranslation_exists_iff_incToSet_naturallyIsomorphic
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    (map : I → J) :
    (∃ translation : BoundaryShapeTranslation source target,
      translation.map = map) ↔
      IncNaturallyIsomorphic (incToSetFunctor source)
        ((incToSetFunctor target).comp (incDiscreteMapFunctor map)) := by
  constructor
  · rintro ⟨translation, rfl⟩
    exact ⟨translation.incToSetNaturalIsomorphism⟩
  · rintro ⟨iso⟩
    apply (boundaryShapeTranslation_exists_iff_inc_to_set_equivalent_along_map
      source target map).mpr
    intro i
    refine ⟨{
      forward := (iso.hom.app ⟨i⟩).function
      inverse := (iso.inv.app ⟨i⟩).function
      inverse_forward := ?_
      forward_inverse := ?_ }⟩
    · intro value
      have component := iso.hom_app_inv_app (⟨i⟩ : IncLiftedObject I)
      exact congrFun (congrArg IncLiftedFunction.function component) value
    · intro value
      have component := iso.inv_app_hom_app (⟨i⟩ : IncLiftedObject I)
      exact congrFun (congrArg IncLiftedFunction.function component) value

theorem incToSet_naturallyIsomorphic_iff_boundaryShapeCode_preserved
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    (map : I → J) :
    IncNaturallyIsomorphic (incToSetFunctor source)
        ((incToSetFunctor target).comp (incDiscreteMapFunctor map)) ↔
      ∀ i, boundaryShapeCode source i = boundaryShapeCode target (map i) := by
  rw [← boundaryShapeTranslation_exists_iff_incToSet_naturallyIsomorphic
      source target map]
  exact boundaryShapeTranslation_exists_iff_code_preserving source target map

theorem incToSet_naturallyIsomorphic_iff_fibers_equivalent
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    (map : I → J) :
    IncNaturallyIsomorphic (incToSetFunctor source)
        ((incToSetFunctor target).comp (incDiscreteMapFunctor map)) ↔
      ∀ i, Nonempty (IncTypeEquivalence (inc_to_set source i)
        (inc_to_set target (map i))) := by
  rw [← boundaryShapeTranslation_exists_iff_incToSet_naturallyIsomorphic
      source target map]
  exact boundaryShapeTranslation_exists_iff_inc_to_set_equivalent_along_map
    source target map

theorem BoundaryShapeTranslation.discreteFunctor_obj
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BoundaryShapeTranslation source target)
    (i : IncLiftedObject I) :
    translation.discreteFunctor.obj i = ⟨translation.map i.down⟩ := rfl

theorem BoundaryShapeTranslation.discreteFunctor_comp_obj
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondMap : BoundaryShapeTranslation second third)
    (firstMap : BoundaryShapeTranslation first second)
    (i : IncLiftedObject I) :
    (secondMap.comp firstMap).discreteFunctor.obj i =
      secondMap.discreteFunctor.obj (firstMap.discreteFunctor.obj i) := rfl

structure BoundaryShapeEmbedding
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    extends BoundaryShapeTranslation source target where
  injective : ∀ {i j}, map i = map j → i = j

structure BehavioralBoundaryShapeTranslation
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    extends BoundaryShapeTranslation source target where
  preservesBisimulation : ∀ {i j}, approxBisim source i j →
    approxBisim target (map i) (map j)

def BehavioralBoundaryShapeTranslation.identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BehavioralBoundaryShapeTranslation inc inc where
  toBoundaryShapeTranslation := BoundaryShapeTranslation.identity inc
  preservesBisimulation := fun bisimilar => bisimilar

def BehavioralBoundaryShapeTranslation.comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondMap : BehavioralBoundaryShapeTranslation second third)
    (firstMap : BehavioralBoundaryShapeTranslation first second) :
    BehavioralBoundaryShapeTranslation first third where
  toBoundaryShapeTranslation :=
    secondMap.toBoundaryShapeTranslation.comp
      firstMap.toBoundaryShapeTranslation
  preservesBisimulation := fun bisimilar =>
    secondMap.preservesBisimulation
      (firstMap.preservesBisimulation bisimilar)

theorem BehavioralBoundaryShapeTranslation.ext
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {first second : BehavioralBoundaryShapeTranslation source target}
    (mapEq : first.map = second.map) : first = second := by
  have baseEq : first.toBoundaryShapeTranslation =
      second.toBoundaryShapeTranslation :=
    BoundaryShapeTranslation.ext mapEq
  cases first
  cases second
  cases baseEq
  rfl

theorem BehavioralBoundaryShapeTranslation.identity_comp
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target) :
    (BehavioralBoundaryShapeTranslation.identity target).comp translation =
      translation := by
  apply BehavioralBoundaryShapeTranslation.ext
  rfl

theorem BehavioralBoundaryShapeTranslation.comp_identity
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target) :
    translation.comp (BehavioralBoundaryShapeTranslation.identity source) =
      translation := by
  apply BehavioralBoundaryShapeTranslation.ext
  rfl

theorem BehavioralBoundaryShapeTranslation.comp_assoc
    {I J K L R₁ T₁ R₂ T₂ R₃ T₃ R₄ T₄ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃} {fourth : Incidence L R₄ T₄}
    (thirdMap : BehavioralBoundaryShapeTranslation third fourth)
    (secondMap : BehavioralBoundaryShapeTranslation second third)
    (firstMap : BehavioralBoundaryShapeTranslation first second) :
    (thirdMap.comp secondMap).comp firstMap =
      thirdMap.comp (secondMap.comp firstMap) := by
  apply BehavioralBoundaryShapeTranslation.ext
  rfl

/- A translation of the interaction theory must preserve the whole ternary
resonance relation, not merely the deterministic selected mode. -/
structure ResonantBehavioralTranslation
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    extends BehavioralBoundaryShapeTranslation source target where
  preservesResonance : ∀ {i j k}, source.resonance i j k →
    target.resonance (map i) (map j) (map k)

def ResonantBehavioralTranslation.toResonanceHomomorphism
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : ResonantBehavioralTranslation source target) :
    ResonanceHomomorphism source target where
  toFun := translation.map
  preserves := translation.preservesResonance

def ResonantBehavioralTranslation.identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonantBehavioralTranslation inc inc where
  toBehavioralBoundaryShapeTranslation :=
    BehavioralBoundaryShapeTranslation.identity inc
  preservesResonance := fun resonant => resonant

def ResonantBehavioralTranslation.comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondMap : ResonantBehavioralTranslation second third)
    (firstMap : ResonantBehavioralTranslation first second) :
    ResonantBehavioralTranslation first third where
  toBehavioralBoundaryShapeTranslation :=
    secondMap.toBehavioralBoundaryShapeTranslation.comp
      firstMap.toBehavioralBoundaryShapeTranslation
  preservesResonance := fun resonant =>
    secondMap.preservesResonance (firstMap.preservesResonance resonant)

theorem ResonantBehavioralTranslation.ext
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {first second : ResonantBehavioralTranslation source target}
    (mapEq : first.map = second.map) : first = second := by
  have baseEq : first.toBehavioralBoundaryShapeTranslation =
      second.toBehavioralBoundaryShapeTranslation :=
    BehavioralBoundaryShapeTranslation.ext mapEq
  cases first
  cases second
  cases baseEq
  rfl

theorem ResonantBehavioralTranslation.identity_comp
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : ResonantBehavioralTranslation source target) :
    (ResonantBehavioralTranslation.identity target).comp translation =
      translation := by
  apply ResonantBehavioralTranslation.ext
  rfl

theorem ResonantBehavioralTranslation.comp_identity
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : ResonantBehavioralTranslation source target) :
    translation.comp (ResonantBehavioralTranslation.identity source) =
      translation := by
  apply ResonantBehavioralTranslation.ext
  rfl

theorem ResonantBehavioralTranslation.comp_assoc
    {I J K L R₁ T₁ R₂ T₂ R₃ T₃ R₄ T₄ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃} {fourth : Incidence L R₄ T₄}
    (thirdMap : ResonantBehavioralTranslation third fourth)
    (secondMap : ResonantBehavioralTranslation second third)
    (firstMap : ResonantBehavioralTranslation first second) :
    (thirdMap.comp secondMap).comp firstMap =
      thirdMap.comp (secondMap.comp firstMap) := by
  apply ResonantBehavioralTranslation.ext
  rfl

structure ResonantBehavioralEmbedding
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    extends ResonantBehavioralTranslation source target where
  reflectsResonance : ∀ {i j k},
    target.resonance (map i) (map j) (map k) → source.resonance i j k

def BehavioralBoundaryShapeTranslation.mapBisimulationQuotient
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target) :
    IncidenceQuotient source → IncidenceQuotient target :=
  Quotient.lift
    (fun i => Quotient.mk (approxBisimSetoid target) (translation.map i))
    (by
      intro i j bisimilar
      exact Quotient.sound (translation.preservesBisimulation bisimilar))

theorem BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (BehavioralBoundaryShapeTranslation.identity inc).mapBisimulationQuotient =
      id := by
  funext value
  refine Quotient.inductionOn value ?_
  intro representative
  rfl

theorem BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondMap : BehavioralBoundaryShapeTranslation second third)
    (firstMap : BehavioralBoundaryShapeTranslation first second) :
    (secondMap.comp firstMap).mapBisimulationQuotient =
      secondMap.mapBisimulationQuotient ∘ firstMap.mapBisimulationQuotient := by
  funext value
  refine Quotient.inductionOn value ?_
  intro representative
  rfl

structure BehavioralBoundaryShapeEmbedding
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂)
    extends BehavioralBoundaryShapeTranslation source target where
  reflectsBisimulation : ∀ {i j}, approxBisim target (map i) (map j) →
    approxBisim source i j

def BehavioralBoundaryShapeEmbedding.identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BehavioralBoundaryShapeEmbedding inc inc where
  toBehavioralBoundaryShapeTranslation :=
    BehavioralBoundaryShapeTranslation.identity inc
  reflectsBisimulation := fun bisimilar => bisimilar

def BehavioralBoundaryShapeEmbedding.comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondMap : BehavioralBoundaryShapeEmbedding second third)
    (firstMap : BehavioralBoundaryShapeEmbedding first second) :
    BehavioralBoundaryShapeEmbedding first third where
  toBehavioralBoundaryShapeTranslation :=
    secondMap.toBehavioralBoundaryShapeTranslation.comp
      firstMap.toBehavioralBoundaryShapeTranslation
  reflectsBisimulation := fun bisimilar =>
    firstMap.reflectsBisimulation
      (secondMap.reflectsBisimulation bisimilar)

theorem BehavioralBoundaryShapeEmbedding.mapBisimulationQuotient_injective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (embedding : BehavioralBoundaryShapeEmbedding source target) :
    ∀ {left right : IncidenceQuotient source},
      embedding.toBehavioralBoundaryShapeTranslation.mapBisimulationQuotient left =
        embedding.toBehavioralBoundaryShapeTranslation.mapBisimulationQuotient right →
      left = right := by
  intro left right imagesEqual
  refine Quotient.inductionOn₂ left right ?_ imagesEqual
  intro i j representativesEqual
  apply Quotient.sound
  apply embedding.reflectsBisimulation
  exact Quotient.exact representativesEqual

def BehaviorallyEssentiallySurjective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target) : Prop :=
  ∀ j, ∃ i, approxBisim target (translation.map i) j

theorem BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_surjective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target)
    (essentiallySurjective : BehaviorallyEssentiallySurjective translation) :
    ∀ targetClass : IncidenceQuotient target,
      ∃ sourceClass : IncidenceQuotient source,
        translation.mapBisimulationQuotient sourceClass = targetClass := by
  intro targetClass
  refine Quotient.inductionOn targetClass ?_
  intro j
  obtain ⟨i, bisimilar⟩ := essentiallySurjective j
  exact ⟨Quotient.mk (approxBisimSetoid source) i, Quotient.sound bisimilar⟩

structure BehavioralQuotientEquivalenceCriterion
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂) where
  embedding : BehavioralBoundaryShapeEmbedding source target
  essentiallySurjective : BehaviorallyEssentiallySurjective
    embedding.toBehavioralBoundaryShapeTranslation

def BehavioralQuotientEquivalenceCriterion.identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BehavioralQuotientEquivalenceCriterion inc inc where
  embedding := BehavioralBoundaryShapeEmbedding.identity inc
  essentiallySurjective := by
    intro i
    exact ⟨i, approxBisim_refl inc i⟩

def BehavioralQuotientEquivalenceCriterion.comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondCriterion : BehavioralQuotientEquivalenceCriterion second third)
    (firstCriterion : BehavioralQuotientEquivalenceCriterion first second) :
    BehavioralQuotientEquivalenceCriterion first third where
  embedding := secondCriterion.embedding.comp firstCriterion.embedding
  essentiallySurjective := by
    intro k
    obtain ⟨j, secondBisimilar⟩ := secondCriterion.essentiallySurjective k
    obtain ⟨i, firstBisimilar⟩ := firstCriterion.essentiallySurjective j
    refine ⟨i, approxBisim_trans ?_ secondBisimilar⟩
    exact secondCriterion.embedding.preservesBisimulation firstBisimilar

theorem BehavioralQuotientEquivalenceCriterion.quotientMap_bijective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (criterion : BehavioralQuotientEquivalenceCriterion source target) :
    (∀ {left right : IncidenceQuotient source},
      BehavioralBoundaryShapeTranslation.mapBisimulationQuotient
          criterion.embedding.toBehavioralBoundaryShapeTranslation left =
        BehavioralBoundaryShapeTranslation.mapBisimulationQuotient
          criterion.embedding.toBehavioralBoundaryShapeTranslation right →
      left = right) ∧
    (∀ targetClass : IncidenceQuotient target,
      ∃ sourceClass : IncidenceQuotient source,
        BehavioralBoundaryShapeTranslation.mapBisimulationQuotient
          criterion.embedding.toBehavioralBoundaryShapeTranslation sourceClass =
            targetClass) :=
  ⟨criterion.embedding.mapBisimulationQuotient_injective,
    BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_surjective
      criterion.embedding.toBehavioralBoundaryShapeTranslation
        criterion.essentiallySurjective⟩

noncomputable def BehavioralQuotientEquivalenceCriterion.quotientEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (criterion : BehavioralQuotientEquivalenceCriterion source target) :
    IncTypeEquivalence (IncidenceQuotient source) (IncidenceQuotient target) := by
  let forward :=
    BehavioralBoundaryShapeTranslation.mapBisimulationQuotient
      criterion.embedding.toBehavioralBoundaryShapeTranslation
  have surjective : ∀ targetClass : IncidenceQuotient target,
      ∃ sourceClass : IncidenceQuotient source, forward sourceClass = targetClass :=
    BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_surjective
      criterion.embedding.toBehavioralBoundaryShapeTranslation
        criterion.essentiallySurjective
  let inverse : IncidenceQuotient target → IncidenceQuotient source :=
    fun targetClass => Classical.choose (surjective targetClass)
  exact {
    forward := forward
    inverse := inverse
    inverse_forward := by
      intro sourceClass
      apply criterion.embedding.mapBisimulationQuotient_injective
      change forward (inverse (forward sourceClass)) = forward sourceClass
      exact Classical.choose_spec (surjective (forward sourceClass))
    forward_inverse := by
      intro targetClass
      exact Classical.choose_spec (surjective targetClass) }

noncomputable def behavioralQuotientCriterionOfBijectiveMap
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target)
    (injective : ∀ {left right : IncidenceQuotient source},
      translation.mapBisimulationQuotient left =
        translation.mapBisimulationQuotient right → left = right)
    (surjective : ∀ targetClass : IncidenceQuotient target,
      ∃ sourceClass : IncidenceQuotient source,
        translation.mapBisimulationQuotient sourceClass = targetClass) :
    BehavioralQuotientEquivalenceCriterion source target where
  embedding := {
    toBehavioralBoundaryShapeTranslation := translation
    reflectsBisimulation := by
      intro i j targetBisimilar
      exact @Quotient.exact I (approxBisimSetoid source) i j
        (injective (@Quotient.sound J (approxBisimSetoid target)
          (translation.map i) (translation.map j) targetBisimilar)) }
  essentiallySurjective := by
    intro j
    obtain ⟨sourceClass, imageEqual⟩ :=
      surjective (Quotient.mk (approxBisimSetoid target) j)
    obtain ⟨i, representativeEqual⟩ := Quotient.exists_rep sourceClass
    refine ⟨i, ?_⟩
    apply @Quotient.exact J (approxBisimSetoid target)
      (translation.map i) j
    have mappedRepresentativeEqual :=
      congrArg translation.mapBisimulationQuotient representativeEqual
    exact mappedRepresentativeEqual.trans imageEqual

theorem behavioralQuotientCriterion_iff_quotientMap_bijective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target) :
    (∃ criterion : BehavioralQuotientEquivalenceCriterion source target,
      criterion.embedding.toBehavioralBoundaryShapeTranslation = translation) ↔
    ((∀ {left right : IncidenceQuotient source},
        translation.mapBisimulationQuotient left =
          translation.mapBisimulationQuotient right → left = right) ∧
      (∀ targetClass : IncidenceQuotient target,
        ∃ sourceClass : IncidenceQuotient source,
          translation.mapBisimulationQuotient sourceClass = targetClass)) := by
  constructor
  · rintro ⟨criterion, underlyingEq⟩
    cases underlyingEq
    exact criterion.quotientMap_bijective
  · rintro ⟨injective, surjective⟩
    exact ⟨behavioralQuotientCriterionOfBijectiveMap translation
      injective surjective, rfl⟩

theorem behavioralQuotientCriterion_iff_quotientEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (translation : BehavioralBoundaryShapeTranslation source target) :
    (∃ criterion : BehavioralQuotientEquivalenceCriterion source target,
      criterion.embedding.toBehavioralBoundaryShapeTranslation = translation) ↔
    (∃ equivalence : IncTypeEquivalence
        (IncidenceQuotient source) (IncidenceQuotient target),
      equivalence.forward = translation.mapBisimulationQuotient) := by
  constructor
  · rintro ⟨criterion, underlyingEq⟩
    cases underlyingEq
    exact ⟨criterion.quotientEquivalence, rfl⟩
  · rintro ⟨equivalence, forwardEq⟩
    have injective : ∀ {left right : IncidenceQuotient source},
        translation.mapBisimulationQuotient left =
          translation.mapBisimulationQuotient right → left = right := by
      intro left right imagesEqual
      have inverseImagesEqual := congrArg equivalence.inverse imagesEqual
      rw [← forwardEq, equivalence.inverse_forward,
        equivalence.inverse_forward] at inverseImagesEqual
      exact inverseImagesEqual
    have surjective : ∀ targetClass : IncidenceQuotient target,
        ∃ sourceClass : IncidenceQuotient source,
          translation.mapBisimulationQuotient sourceClass = targetClass := by
      intro targetClass
      refine ⟨equivalence.inverse targetClass, ?_⟩
      rw [← forwardEq]
      exact equivalence.forward_inverse targetClass
    exact ⟨behavioralQuotientCriterionOfBijectiveMap translation
      injective surjective, rfl⟩

theorem BehavioralQuotientEquivalenceCriterion.quotientEquivalence_forward
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (criterion : BehavioralQuotientEquivalenceCriterion source target) :
    criterion.quotientEquivalence.forward =
      BehavioralBoundaryShapeTranslation.mapBisimulationQuotient
        criterion.embedding.toBehavioralBoundaryShapeTranslation := rfl

theorem BehavioralQuotientEquivalenceCriterion.quotientEquivalence_identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    (BehavioralQuotientEquivalenceCriterion.identity inc).quotientEquivalence =
      IncTypeEquivalence.refl (IncidenceQuotient inc) := by
  apply IncTypeEquivalence.ext_forward
  exact BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_identity inc

theorem BehavioralQuotientEquivalenceCriterion.quotientEquivalence_comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondCriterion : BehavioralQuotientEquivalenceCriterion second third)
    (firstCriterion : BehavioralQuotientEquivalenceCriterion first second) :
    (secondCriterion.comp firstCriterion).quotientEquivalence =
      secondCriterion.quotientEquivalence.trans
        firstCriterion.quotientEquivalence := by
  apply IncTypeEquivalence.ext_forward
  exact BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_comp
    secondCriterion.embedding.toBehavioralBoundaryShapeTranslation
    firstCriterion.embedding.toBehavioralBoundaryShapeTranslation

structure BehavioralBoundaryShapeEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂) where
  hom : BehavioralBoundaryShapeTranslation source target
  inv : BehavioralBoundaryShapeTranslation target source
  inv_hom : ∀ i, inv.map (hom.map i) = i
  hom_inv : ∀ j, hom.map (inv.map j) = j

theorem BehavioralBoundaryShapeEquivalence.ext
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {first second : BehavioralBoundaryShapeEquivalence source target}
    (homEq : first.hom = second.hom) (invEq : first.inv = second.inv) :
    first = second := by
  cases first
  cases second
  cases homEq
  cases invEq
  rfl

def BehavioralBoundaryShapeEquivalence.refl
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BehavioralBoundaryShapeEquivalence inc inc where
  hom := BehavioralBoundaryShapeTranslation.identity inc
  inv := BehavioralBoundaryShapeTranslation.identity inc
  inv_hom := by intro i; rfl
  hom_inv := by intro i; rfl

def BehavioralBoundaryShapeEquivalence.symm
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    BehavioralBoundaryShapeEquivalence target source where
  hom := equivalence.inv
  inv := equivalence.hom
  inv_hom := equivalence.hom_inv
  hom_inv := equivalence.inv_hom

def BehavioralBoundaryShapeEquivalence.trans
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondEquivalence : BehavioralBoundaryShapeEquivalence second third)
    (firstEquivalence : BehavioralBoundaryShapeEquivalence first second) :
    BehavioralBoundaryShapeEquivalence first third where
  hom := secondEquivalence.hom.comp firstEquivalence.hom
  inv := firstEquivalence.inv.comp secondEquivalence.inv
  inv_hom := by
    intro i
    change firstEquivalence.inv.map
      (secondEquivalence.inv.map
        (secondEquivalence.hom.map (firstEquivalence.hom.map i))) = i
    rw [secondEquivalence.inv_hom, firstEquivalence.inv_hom]
  hom_inv := by
    intro k
    change secondEquivalence.hom.map
      (firstEquivalence.hom.map
        (firstEquivalence.inv.map (secondEquivalence.inv.map k))) = k
    rw [firstEquivalence.hom_inv, secondEquivalence.hom_inv]

theorem BehavioralBoundaryShapeEquivalence.refl_trans
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    equivalence.trans (BehavioralBoundaryShapeEquivalence.refl source) =
      equivalence := by
  apply BehavioralBoundaryShapeEquivalence.ext
  · exact BehavioralBoundaryShapeTranslation.comp_identity equivalence.hom
  · exact BehavioralBoundaryShapeTranslation.identity_comp equivalence.inv

theorem BehavioralBoundaryShapeEquivalence.trans_refl
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    (BehavioralBoundaryShapeEquivalence.refl target).trans equivalence =
      equivalence := by
  apply BehavioralBoundaryShapeEquivalence.ext
  · exact BehavioralBoundaryShapeTranslation.identity_comp equivalence.hom
  · exact BehavioralBoundaryShapeTranslation.comp_identity equivalence.inv

theorem BehavioralBoundaryShapeEquivalence.trans_assoc
    {I J K L R₁ T₁ R₂ T₂ R₃ T₃ R₄ T₄ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃} {fourth : Incidence L R₄ T₄}
    (thirdEquivalence : BehavioralBoundaryShapeEquivalence third fourth)
    (secondEquivalence : BehavioralBoundaryShapeEquivalence second third)
    (firstEquivalence : BehavioralBoundaryShapeEquivalence first second) :
    (thirdEquivalence.trans secondEquivalence).trans firstEquivalence =
      thirdEquivalence.trans (secondEquivalence.trans firstEquivalence) := by
  apply BehavioralBoundaryShapeEquivalence.ext
  · exact BehavioralBoundaryShapeTranslation.comp_assoc
      thirdEquivalence.hom secondEquivalence.hom firstEquivalence.hom
  · exact (BehavioralBoundaryShapeTranslation.comp_assoc
      firstEquivalence.inv secondEquivalence.inv thirdEquivalence.inv).symm

theorem BehavioralBoundaryShapeEquivalence.symm_symm
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    equivalence.symm.symm = equivalence := by
  apply BehavioralBoundaryShapeEquivalence.ext <;> rfl

theorem BehavioralBoundaryShapeEquivalence.symm_trans_self
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    equivalence.symm.trans equivalence =
      BehavioralBoundaryShapeEquivalence.refl source := by
  apply BehavioralBoundaryShapeEquivalence.ext <;>
    apply BehavioralBoundaryShapeTranslation.ext <;> funext value
  · exact equivalence.inv_hom value
  · exact equivalence.inv_hom value

theorem BehavioralBoundaryShapeEquivalence.trans_symm_self
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    equivalence.trans equivalence.symm =
      BehavioralBoundaryShapeEquivalence.refl target := by
  apply BehavioralBoundaryShapeEquivalence.ext <;>
    apply BehavioralBoundaryShapeTranslation.ext <;> funext value
  · exact equivalence.hom_inv value
  · exact equivalence.hom_inv value

def BehavioralBoundaryShapeEquivalence.quotientEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    IncTypeEquivalence (IncidenceQuotient source) (IncidenceQuotient target) where
  forward := equivalence.hom.mapBisimulationQuotient
  inverse := equivalence.inv.mapBisimulationQuotient
  inverse_forward := by
    intro value
    refine Quotient.inductionOn value ?_
    intro representative
    change Quotient.mk (approxBisimSetoid source)
      (equivalence.inv.map (equivalence.hom.map representative)) =
        Quotient.mk (approxBisimSetoid source) representative
    rw [equivalence.inv_hom]
  forward_inverse := by
    intro value
    refine Quotient.inductionOn value ?_
    intro representative
    change Quotient.mk (approxBisimSetoid target)
      (equivalence.hom.map (equivalence.inv.map representative)) =
        Quotient.mk (approxBisimSetoid target) representative
    rw [equivalence.hom_inv]

def BehavioralBoundaryShapeEquivalence.toEmbedding
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    BehavioralBoundaryShapeEmbedding source target where
  toBehavioralBoundaryShapeTranslation := equivalence.hom
  reflectsBisimulation := by
    intro i j bisimilar
    have reflected := equivalence.inv.preservesBisimulation bisimilar
    simpa [equivalence.inv_hom] using reflected

theorem BehavioralBoundaryShapeEquivalence.essentiallySurjective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    BehaviorallyEssentiallySurjective equivalence.hom := by
  intro j
  refine ⟨equivalence.inv.map j, ?_⟩
  rw [equivalence.hom_inv]
  exact approxBisim_refl target j

def BehavioralBoundaryShapeEquivalence.toQuotientCriterion
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    BehavioralQuotientEquivalenceCriterion source target where
  embedding := equivalence.toEmbedding
  essentiallySurjective := equivalence.essentiallySurjective

theorem BehavioralBoundaryShapeEquivalence.quotient_forward_injective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    ∀ {left right : IncidenceQuotient source},
      equivalence.quotientEquivalence.forward left =
        equivalence.quotientEquivalence.forward right → left = right :=
  equivalence.toEmbedding.mapBisimulationQuotient_injective

theorem BehavioralBoundaryShapeEquivalence.quotientEquivalence_trans
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondEquivalence : BehavioralBoundaryShapeEquivalence second third)
    (firstEquivalence : BehavioralBoundaryShapeEquivalence first second) :
    (secondEquivalence.trans firstEquivalence).quotientEquivalence =
      secondEquivalence.quotientEquivalence.trans
        firstEquivalence.quotientEquivalence := by
  apply IncTypeEquivalence.ext
  · exact BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_comp
      secondEquivalence.hom firstEquivalence.hom
  · exact BehavioralBoundaryShapeTranslation.mapBisimulationQuotient_comp
      firstEquivalence.inv secondEquivalence.inv

theorem BehavioralBoundaryShapeEquivalence.quotientEquivalence_symm
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    equivalence.symm.quotientEquivalence =
      equivalence.quotientEquivalence.symm := by
  apply IncTypeEquivalence.ext <;> rfl

def BoundaryShapeEmbedding.identity
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BoundaryShapeEmbedding inc inc where
  toBoundaryShapeTranslation := BoundaryShapeTranslation.identity inc
  injective := by
    intro i j equal
    exact equal

def BoundaryShapeEmbedding.comp
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondMap : BoundaryShapeEmbedding second third)
    (firstMap : BoundaryShapeEmbedding first second) :
    BoundaryShapeEmbedding first third where
  toBoundaryShapeTranslation :=
    secondMap.toBoundaryShapeTranslation.comp
      firstMap.toBoundaryShapeTranslation
  injective := by
    intro i j equal
    apply firstMap.injective
    apply secondMap.injective
    exact equal

structure BoundaryShapeEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂) where
  hom : BoundaryShapeTranslation source target
  inv : BoundaryShapeTranslation target source
  inv_hom : ∀ i, inv.map (hom.map i) = i
  hom_inv : ∀ j, hom.map (inv.map j) = j

theorem BoundaryShapeEquivalence.ext
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {first second : BoundaryShapeEquivalence source target}
    (homEq : first.hom = second.hom) (invEq : first.inv = second.inv) :
    first = second := by
  cases first
  cases second
  cases homEq
  cases invEq
  rfl

def BoundaryShapeEquivalence.refl
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BoundaryShapeEquivalence inc inc where
  hom := BoundaryShapeTranslation.identity inc
  inv := BoundaryShapeTranslation.identity inc
  inv_hom := by intro i; rfl
  hom_inv := by intro i; rfl

def BoundaryShapeEquivalence.symm
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    BoundaryShapeEquivalence target source where
  hom := equivalence.inv
  inv := equivalence.hom
  inv_hom := equivalence.hom_inv
  hom_inv := equivalence.inv_hom

def BoundaryShapeEquivalence.trans
    {I J K R₁ T₁ R₂ T₂ R₃ T₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃}
    (secondEquivalence : BoundaryShapeEquivalence second third)
    (firstEquivalence : BoundaryShapeEquivalence first second) :
    BoundaryShapeEquivalence first third where
  hom := secondEquivalence.hom.comp firstEquivalence.hom
  inv := firstEquivalence.inv.comp secondEquivalence.inv
  inv_hom := by
    intro i
    change firstEquivalence.inv.map
      (secondEquivalence.inv.map
        (secondEquivalence.hom.map (firstEquivalence.hom.map i))) = i
    rw [secondEquivalence.inv_hom, firstEquivalence.inv_hom]
  hom_inv := by
    intro k
    change secondEquivalence.hom.map
      (firstEquivalence.hom.map
        (firstEquivalence.inv.map (secondEquivalence.inv.map k))) = k
    rw [firstEquivalence.hom_inv, secondEquivalence.hom_inv]

def boundaryShapeEquivalenceOfCodeEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (carrier : IncTypeEquivalence I J)
    (preservesCode : ∀ i,
      boundaryShapeCode source i = boundaryShapeCode target (carrier.forward i)) :
    BoundaryShapeEquivalence source target where
  hom := boundaryShapeTranslationOfCodePreserving carrier.forward preservesCode
  inv := boundaryShapeTranslationOfCodePreserving carrier.inverse (by
    intro j
    have atInverse := preservesCode (carrier.inverse j)
    rw [carrier.forward_inverse] at atInverse
    exact atInverse.symm)
  inv_hom := carrier.inverse_forward
  hom_inv := carrier.forward_inverse

theorem boundaryShapeEquivalence_exists_iff_code_equivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂) :
    Nonempty (BoundaryShapeEquivalence source target) ↔
      ∃ carrier : IncTypeEquivalence I J, ∀ i,
        boundaryShapeCode source i =
          boundaryShapeCode target (carrier.forward i) := by
  constructor
  · rintro ⟨equivalence⟩
    let carrier : IncTypeEquivalence I J :=
      { forward := equivalence.hom.map
        inverse := equivalence.inv.map
        inverse_forward := equivalence.inv_hom
        forward_inverse := equivalence.hom_inv }
    exact ⟨carrier, equivalence.hom.preservesCode⟩
  · rintro ⟨carrier, preservesCode⟩
    exact ⟨boundaryShapeEquivalenceOfCodeEquivalence carrier preservesCode⟩

theorem BoundaryShapeEquivalence.refl_trans
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    equivalence.trans (BoundaryShapeEquivalence.refl source) = equivalence := by
  apply BoundaryShapeEquivalence.ext
  · exact BoundaryShapeTranslation.comp_identity equivalence.hom
  · exact BoundaryShapeTranslation.identity_comp equivalence.inv

theorem BoundaryShapeEquivalence.trans_refl
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    (BoundaryShapeEquivalence.refl target).trans equivalence = equivalence := by
  apply BoundaryShapeEquivalence.ext
  · exact BoundaryShapeTranslation.identity_comp equivalence.hom
  · exact BoundaryShapeTranslation.comp_identity equivalence.inv

theorem BoundaryShapeEquivalence.trans_assoc
    {I J K L R₁ T₁ R₂ T₂ R₃ T₃ R₄ T₄ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    {first : Incidence I R₁ T₁} {second : Incidence J R₂ T₂}
    {third : Incidence K R₃ T₃} {fourth : Incidence L R₄ T₄}
    (thirdEquivalence : BoundaryShapeEquivalence third fourth)
    (secondEquivalence : BoundaryShapeEquivalence second third)
    (firstEquivalence : BoundaryShapeEquivalence first second) :
    (thirdEquivalence.trans secondEquivalence).trans firstEquivalence =
      thirdEquivalence.trans (secondEquivalence.trans firstEquivalence) := by
  apply BoundaryShapeEquivalence.ext
  · exact BoundaryShapeTranslation.comp_assoc
      thirdEquivalence.hom secondEquivalence.hom firstEquivalence.hom
  · exact (BoundaryShapeTranslation.comp_assoc
      firstEquivalence.inv secondEquivalence.inv thirdEquivalence.inv).symm

theorem BoundaryShapeEquivalence.symm_symm
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    equivalence.symm.symm = equivalence := by
  apply BoundaryShapeEquivalence.ext <;> rfl

theorem BoundaryShapeEquivalence.symm_trans_self
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    equivalence.symm.trans equivalence = BoundaryShapeEquivalence.refl source := by
  apply BoundaryShapeEquivalence.ext <;>
    apply BoundaryShapeTranslation.ext <;> funext value
  · exact equivalence.inv_hom value
  · exact equivalence.inv_hom value

theorem BoundaryShapeEquivalence.trans_symm_self
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    equivalence.trans equivalence.symm = BoundaryShapeEquivalence.refl target := by
  apply BoundaryShapeEquivalence.ext <;>
    apply BoundaryShapeTranslation.ext <;> funext value
  · exact equivalence.hom_inv value
  · exact equivalence.hom_inv value

def BehavioralBoundaryShapeEquivalence.toBoundaryShapeEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BehavioralBoundaryShapeEquivalence source target) :
    BoundaryShapeEquivalence source target where
  hom := equivalence.hom.toBoundaryShapeTranslation
  inv := equivalence.inv.toBoundaryShapeTranslation
  inv_hom := equivalence.inv_hom
  hom_inv := equivalence.hom_inv

def BoundaryShapeEquivalence.incToSetNaturalIsomorphism
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncNaturalIsomorphism (incToSetFunctor source)
      ((incToSetFunctor target).comp equivalence.hom.discreteFunctor) :=
  equivalence.hom.incToSetNaturalIsomorphism

def BoundaryShapeEquivalence.toEmbedding
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    BoundaryShapeEmbedding source target where
  toBoundaryShapeTranslation := equivalence.hom
  injective := by
    intro i j equal
    have := congrArg equivalence.inv.map equal
    rw [equivalence.inv_hom, equivalence.inv_hom] at this
    exact this

theorem BoundaryShapeEmbedding.discreteFunctor_fullyFaithful
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (embedding : BoundaryShapeEmbedding source target) :
    IncFunctorFullyFaithful
      embedding.toBoundaryShapeTranslation.discreteFunctor where
  faithful := by
    intro first second left right _
    cases left
    cases right
    rfl
  full := by
    intro first second morphism
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    have mappedEqual : embedding.map first = embedding.map second :=
      congrArg IncLiftedObject.down morphism.equality
    have sourceEqual : first = second := embedding.injective mappedEqual
    cases sourceEqual
    refine ⟨⟨rfl⟩, ?_⟩
    cases morphism
    rfl

theorem BoundaryShapeEquivalence.discreteFunctor_essentiallySurjective
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncFunctorEssentiallySurjective equivalence.hom.discreteFunctor := by
  intro targetObject
  have objectEqual : equivalence.hom.discreteFunctor.obj
      ⟨equivalence.inv.map targetObject.down⟩ = targetObject := by
    cases targetObject with
    | mk target =>
        change IncLiftedObject.mk
          (equivalence.hom.map (equivalence.inv.map target)) =
            IncLiftedObject.mk target
        rw [equivalence.hom_inv]
  refine ⟨⟨equivalence.inv.map targetObject.down⟩,
    ⟨objectEqual⟩, ⟨objectEqual.symm⟩, ?_, ?_⟩
  · cases targetObject
    simp only at *
    rfl
  · cases targetObject
    simp only at *
    rfl

def BoundaryShapeEquivalence.discreteFunctorCriterion
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncFunctorEquivalenceCriterion equivalence.hom.discreteFunctor where
  fullyFaithful := equivalence.toEmbedding.discreteFunctor_fullyFaithful
  essentiallySurjective := equivalence.discreteFunctor_essentiallySurjective

noncomputable def BoundaryShapeEquivalence.discreteCategoryEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncCategoryEquivalence (incDiscreteCategory I) (incDiscreteCategory J) :=
  equivalence.discreteFunctorCriterion.toCategoryEquivalence

theorem BoundaryShapeEquivalence.discreteCategoryEquivalence_forward
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    equivalence.discreteCategoryEquivalence.forward =
      equivalence.hom.discreteFunctor := rfl

noncomputable def BoundaryShapeEquivalence.discreteFunctorPreservesFiniteLimitsColimits
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    StrongFiniteLimitColimitPreservingFamily equivalence.hom.discreteFunctor :=
  IncCategoryEquivalence.strongFiniteLimitColimitPreservingFamily
    equivalence.discreteCategoryEquivalence

noncomputable def BoundaryShapeEquivalence.discreteFunctorPreservesPushouts
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    StrongPushoutPreservingFamily equivalence.hom.discreteFunctor :=
  equivalence.discreteCategoryEquivalence.strongPushoutPreservingFamily

noncomputable def BoundaryShapeEquivalence.discreteFunctorPreservesPullbacks
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    StrongPullbackPreservingFamily equivalence.hom.discreteFunctor :=
  equivalence.discreteCategoryEquivalence.strongPullbackPreservingFamily

def BoundaryShapeEquivalence.carrierEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncTypeEquivalence I J where
  forward := equivalence.hom.map
  inverse := equivalence.inv.map
  inverse_forward := equivalence.inv_hom
  forward_inverse := equivalence.hom_inv

abbrev NullaryIncidences
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :=
  { i : I // inc.boundary i = [] }

abbrev NonNullaryIncidences
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :=
  { i : I // inc.boundary i ≠ [] }

noncomputable def boundaryStrataEquivalence
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    IncTypeEquivalence I
      (Sum (NullaryIncidences inc) (NonNullaryIncidences inc)) := by
  classical
  exact {
    forward := fun i =>
      if nullary : inc.boundary i = [] then Sum.inl ⟨i, nullary⟩
      else Sum.inr ⟨i, nullary⟩
    inverse := fun value =>
      match value with
      | Sum.inl nullary => nullary.val
      | Sum.inr nonNullary => nonNullary.val
    inverse_forward := by
      intro i
      by_cases nullary : inc.boundary i = []
      · simp [nullary]
      · simp [nullary]
    forward_inverse := by
      intro value
      cases value with
      | inl nullary => simp [nullary.property]
      | inr nonNullary => simp [nonNullary.property] }

def BoundaryShapeEquivalence.nullaryEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncTypeEquivalence (NullaryIncidences source) (NullaryIncidences target) where
  forward := fun value =>
    ⟨equivalence.hom.map value.val,
      (equivalence.hom.preservesReflectsNullary value.val).mp value.property⟩
  inverse := fun value =>
    ⟨equivalence.inv.map value.val,
      (equivalence.inv.preservesReflectsNullary value.val).mp value.property⟩
  inverse_forward := by
    intro value
    apply Subtype.eq
    exact equivalence.inv_hom value.val
  forward_inverse := by
    intro value
    apply Subtype.eq
    exact equivalence.hom_inv value.val

def BoundaryShapeEquivalence.nonNullaryEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncTypeEquivalence (NonNullaryIncidences source)
      (NonNullaryIncidences target) where
  forward := fun value =>
    ⟨equivalence.hom.map value.val, fun targetNullary =>
      value.property
        ((equivalence.hom.preservesReflectsNullary value.val).mpr targetNullary)⟩
  inverse := fun value =>
    ⟨equivalence.inv.map value.val, fun sourceNullary =>
      value.property
        ((equivalence.inv.preservesReflectsNullary value.val).mpr sourceNullary)⟩
  inverse_forward := by
    intro value
    apply Subtype.eq
    exact equivalence.inv_hom value.val
  forward_inverse := by
    intro value
    apply Subtype.eq
    exact equivalence.hom_inv value.val

def BoundaryShapeEquivalence.strataEquivalence
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    IncTypeEquivalence
      (Sum (NullaryIncidences source) (NonNullaryIncidences source))
      (Sum (NullaryIncidences target) (NonNullaryIncidences target)) where
  forward := fun value =>
    match value with
    | Sum.inl nullary => Sum.inl (equivalence.nullaryEquivalence.forward nullary)
    | Sum.inr nonNullary =>
        Sum.inr (equivalence.nonNullaryEquivalence.forward nonNullary)
  inverse := fun value =>
    match value with
    | Sum.inl nullary => Sum.inl (equivalence.nullaryEquivalence.inverse nullary)
    | Sum.inr nonNullary =>
        Sum.inr (equivalence.nonNullaryEquivalence.inverse nonNullary)
  inverse_forward := by
    intro value
    cases value with
    | inl nullary =>
        change Sum.inl
          (equivalence.nullaryEquivalence.inverse
            (equivalence.nullaryEquivalence.forward nullary)) = Sum.inl nullary
        rw [equivalence.nullaryEquivalence.inverse_forward]
    | inr nonNullary =>
        change Sum.inr
          (equivalence.nonNullaryEquivalence.inverse
            (equivalence.nonNullaryEquivalence.forward nonNullary)) =
          Sum.inr nonNullary
        rw [equivalence.nonNullaryEquivalence.inverse_forward]
  forward_inverse := by
    intro value
    cases value with
    | inl nullary =>
        change Sum.inl
          (equivalence.nullaryEquivalence.forward
            (equivalence.nullaryEquivalence.inverse nullary)) = Sum.inl nullary
        rw [equivalence.nullaryEquivalence.forward_inverse]
    | inr nonNullary =>
        change Sum.inr
          (equivalence.nonNullaryEquivalence.forward
            (equivalence.nonNullaryEquivalence.inverse nonNullary)) =
          Sum.inr nonNullary
        rw [equivalence.nonNullaryEquivalence.forward_inverse]

theorem BoundaryShapeEquivalence.nullary_exists_iff
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    (∃ i, source.boundary i = []) ↔ ∃ j, target.boundary j = [] := by
  constructor
  · rintro ⟨i, nullary⟩
    exact ⟨equivalence.hom.map i,
      (equivalence.hom.preservesReflectsNullary i).mp nullary⟩
  · rintro ⟨j, nullary⟩
    exact ⟨equivalence.inv.map j,
      (equivalence.inv.preservesReflectsNullary j).mp nullary⟩

theorem BoundaryShapeEquivalence.nonNullary_exists_iff
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    (∃ i, source.boundary i ≠ []) ↔ ∃ j, target.boundary j ≠ [] := by
  constructor
  · rintro ⟨i, nonNullary⟩
    exact ⟨equivalence.hom.map i, fun targetNullary =>
      nonNullary ((equivalence.hom.preservesReflectsNullary i).mpr targetNullary)⟩
  · rintro ⟨j, nonNullary⟩
    exact ⟨equivalence.inv.map j, fun sourceNullary =>
      nonNullary ((equivalence.inv.preservesReflectsNullary j).mpr sourceNullary)⟩

theorem BoundaryShapeEquivalence.all_nullary_iff
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    (∀ i, source.boundary i = []) ↔ ∀ j, target.boundary j = [] := by
  constructor
  · intro sourceNullary j
    have atInverse := sourceNullary (equivalence.inv.map j)
    have mapped :=
      (equivalence.hom.preservesReflectsNullary
        (equivalence.inv.map j)).mp atInverse
    rw [equivalence.hom_inv] at mapped
    exact mapped
  · intro targetNullary i
    have atForward := targetNullary (equivalence.hom.map i)
    exact (equivalence.hom.preservesReflectsNullary i).mpr atForward

theorem BoundaryShapeEquivalence.all_nonNullary_iff
    {I J R₁ T₁ R₂ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    (equivalence : BoundaryShapeEquivalence source target) :
    (∀ i, source.boundary i ≠ []) ↔ ∀ j, target.boundary j ≠ [] := by
  constructor
  · intro sourceNonNullary j targetNullary
    have sourceNullary : source.boundary (equivalence.inv.map j) = [] :=
      (equivalence.inv.preservesReflectsNullary j).mp targetNullary
    exact sourceNonNullary (equivalence.inv.map j) sourceNullary
  · intro targetNonNullary i sourceNullary
    have targetNullary : target.boundary (equivalence.hom.map i) = [] :=
      (equivalence.hom.preservesReflectsNullary i).mp sourceNullary
    exact targetNonNullary (equivalence.hom.map i) targetNullary

/- `incToSetFunctor` packages the assignment over the discrete carrier
   category.  It therefore proves functoriality under object equality; a
   category whose objects are whole incidence structures and whose morphisms
   preserve boundary/glue would be a strictly richer construction.  The
   general preservation theorem below applies whenever such a translation is
   presented as a category equivalence. -/
noncomputable def category_equivalence_strongly_preserves_pushouts
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongPushoutPreservingFamily equivalence.forward :=
  equivalence.strongPushoutPreservingFamily

noncomputable def category_equivalence_preserves_pushouts
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    PushoutPreservingFamily equivalence.forward :=
  equivalence.pushoutPreservingFamily

noncomputable def category_equivalence_strongly_preserves_pullbacks
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongPullbackPreservingFamily equivalence.forward :=
  equivalence.strongPullbackPreservingFamily

noncomputable def category_equivalence_preserves_pullbacks
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    PullbackPreservingFamily equivalence.forward :=
  equivalence.pullbackPreservingFamily

noncomputable def category_equivalence_strongly_preserves_bicartesian_shapes
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongBicartesianPreservingFamily equivalence.forward :=
  equivalence.strongBicartesianPreservingFamily

noncomputable def category_equivalence_preserves_bicartesian_shapes
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    BicartesianPreservingFamily equivalence.forward :=
  equivalence.bicartesianPreservingFamily

noncomputable def category_equivalence_strongly_preserves_finite_bicartesian_shapes
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongFiniteBicartesianPreservingFamily equivalence.forward :=
  equivalence.strongFiniteBicartesianPreservingFamily

noncomputable def category_equivalence_strongly_preserves_finite_limits_colimits
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongFiniteLimitColimitPreservingFamily equivalence.forward :=
  equivalence.strongFiniteLimitColimitPreservingFamily

/- Merkle-ID: foundation.axiomatization.limit_preservation
   A translation presented as a category equivalence preserves the complete
   finite-limit/colimit fragment formalized here: terminal/initial objects,
   binary products/coproducts, pullbacks/pushouts, and
   equalizers/coequalizers. -/
noncomputable def preserves_limits
    {CObj DObj : Type u} {C : IncCategory CObj} {D : IncCategory DObj}
    (equivalence : IncCategoryEquivalence C D) :
    StrongFiniteLimitColimitPreservingFamily equivalence.forward :=
  equivalence.strongFiniteLimitColimitPreservingFamily

end TranslationPreservation

end IncidenceCore
