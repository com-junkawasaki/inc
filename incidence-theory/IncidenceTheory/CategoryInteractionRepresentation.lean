import IncidenceTheory.TernaryInteractionRepresentation

namespace IncidenceCore

open CategoryTheory

universe u

/-! A small category is represented by the ternary relation consisting of its
composable pairs and their composites.  This retains object endpoints in the
carrier, so composition is represented without choosing a coding of objects. -/

structure SmallCategoryArrow (C : Type u) [Category.{u} C] where
  source : C
  target : C
  hom : source ⟶ target

def SmallCategoryArrow.compose
    {C : Type u} [Category.{u} C]
    (first second : SmallCategoryArrow C)
    (compatible : first.target = second.source) : SmallCategoryArrow C :=
  ⟨first.source, second.target,
    first.hom ≫ eqToHom compatible ≫ second.hom⟩

def categoryCompositionRelation
    {C : Type u} [Category.{u} C]
    (first second output : SmallCategoryArrow C) : Prop :=
  ∃ compatible : first.target = second.source,
    output = first.compose second compatible

def categoryCompositionSystem
    (C : Type u) [Category.{u} C] : TernaryResonanceSystem where
  Carrier := SmallCategoryArrow C
  resonance := categoryCompositionRelation

def SmallCategoryArrow.ofHom
    {C : Type u} [Category.{u} C] {X Y : C} (hom : X ⟶ Y) :
    SmallCategoryArrow C := ⟨X, Y, hom⟩

@[simp] theorem categoryCompositionRelation_ofHom_iff
    {C : Type u} [Category.{u} C] {X Y Z : C}
    (first : X ⟶ Y) (second : Y ⟶ Z) (output : SmallCategoryArrow C) :
    categoryCompositionRelation (SmallCategoryArrow.ofHom first)
        (SmallCategoryArrow.ofHom second) output ↔
      output = SmallCategoryArrow.ofHom (first ≫ second) := by
  constructor
  · rintro ⟨compatible, rfl⟩
    cases compatible
    simp [SmallCategoryArrow.compose, SmallCategoryArrow.ofHom]
  · intro equal
    refine ⟨rfl, ?_⟩
    simpa [SmallCategoryArrow.compose, SmallCategoryArrow.ofHom] using equal

theorem categoryCompositionRelation_functional
    {C : Type u} [Category.{u} C]
    {first second output₁ output₂ : SmallCategoryArrow C}
    (firstComposite : categoryCompositionRelation first second output₁)
    (secondComposite : categoryCompositionRelation first second output₂) :
    output₁ = output₂ := by
  rcases firstComposite with ⟨firstCompatible, rfl⟩
  rcases secondComposite with ⟨secondCompatible, rfl⟩
  have : firstCompatible = secondCompatible := Subsingleton.elim _ _
  subst this
  rfl

def CategoryCompositionAssociative
    (C : Type u) [Category.{u} C] : Prop :=
  ∀ first second third output : SmallCategoryArrow C,
    (∃ middle,
      categoryCompositionRelation first second middle ∧
      categoryCompositionRelation middle third output) ↔
    (∃ middle,
      categoryCompositionRelation second third middle ∧
      categoryCompositionRelation first middle output)

theorem categoryComposition_associative
    (C : Type u) [Category.{u} C] : CategoryCompositionAssociative C := by
  intro first second third output
  constructor
  · rintro ⟨middle, ⟨firstCompatible, rfl⟩,
      ⟨secondCompatible, rfl⟩⟩
    refine ⟨second.compose third secondCompatible,
      ⟨secondCompatible, rfl⟩, ⟨firstCompatible, ?_⟩⟩
    cases first
    cases second
    cases third
    cases firstCompatible
    cases secondCompatible
    simp [SmallCategoryArrow.compose, Category.assoc]
  · rintro ⟨middle, ⟨secondCompatible, rfl⟩,
      ⟨firstCompatible, rfl⟩⟩
    refine ⟨first.compose second firstCompatible,
      ⟨firstCompatible, rfl⟩, ⟨secondCompatible, ?_⟩⟩
    cases first
    cases second
    cases third
    cases firstCompatible
    cases secondCompatible
    simp [SmallCategoryArrow.compose, Category.assoc]

def SmallCategoryArrow.map
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (functor : C ⥤ D) (arrow : SmallCategoryArrow C) :
    SmallCategoryArrow D :=
  ⟨functor.obj arrow.source, functor.obj arrow.target,
    functor.map arrow.hom⟩

def categoryCompositionMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (functor : C ⥤ D) :
    categoryCompositionSystem C ⟶ categoryCompositionSystem D where
  toFun := SmallCategoryArrow.map functor
  preserves := by
    intro first second output resonant
    rcases resonant with ⟨compatible, rfl⟩
    refine ⟨congrArg functor.obj compatible, ?_⟩
    cases first
    cases second
    cases compatible
    simp [SmallCategoryArrow.map, SmallCategoryArrow.compose]

@[simp] theorem categoryCompositionMap_id
    (C : Type u) [Category.{u} C] :
    categoryCompositionMap (𝟭 C) =
      TernaryResonanceHom.id (categoryCompositionSystem C) := by
  apply TernaryResonanceHom.ext
  funext arrow
  cases arrow
  simp [categoryCompositionMap, SmallCategoryArrow.map,
    TernaryResonanceHom.id]

@[simp] theorem categoryCompositionMap_comp
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    (first : C ⥤ D) (second : D ⥤ E) :
    categoryCompositionMap (first ⋙ second) =
      (categoryCompositionMap second).comp (categoryCompositionMap first) := by
  apply TernaryResonanceHom.ext
  funext arrow
  cases arrow
  simp [categoryCompositionMap, SmallCategoryArrow.map,
    TernaryResonanceHom.comp]

noncomputable def categoryInteractionIncidence
    (C : Type u) [Category.{u} C] :=
  ternaryInteractionIncidence (categoryCompositionSystem C)

@[simp] theorem categoryInteractionIncidence_composition_iff
    {C : Type u} [Category.{u} C] {X Y Z : C}
    (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : SmallCategoryArrow C) :
    (categoryInteractionIncidence C).resonance
        (some (SmallCategoryArrow.ofHom first))
        (some (SmallCategoryArrow.ofHom second)) (some output) ↔
      output = SmallCategoryArrow.ofHom (first ≫ second) := by
  unfold categoryInteractionIncidence
  rw [ternaryInteractionIncidence_resonance_some_iff]
  exact categoryCompositionRelation_ofHom_iff first second output

theorem categoryInteractionRepresentation_recoverable
    (C : Type u) [Category.{u} C] :
    Nonempty (categoryCompositionSystem C ≅
      nonunitResonanceSystem
        (ternaryInteractionObject (categoryCompositionSystem C))) :=
  ⟨ternaryInteractionRepresentationIso (categoryCompositionSystem C)⟩

structure CategoryInteractionRepresentationTheorem
    (C : Type u) [Category.{u} C] : Prop where
  exact_composition : ∀ {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z)
    (output : SmallCategoryArrow C),
    (categoryInteractionIncidence C).resonance
        (some (SmallCategoryArrow.ofHom first))
        (some (SmallCategoryArrow.ofHom second)) (some output) ↔
      output = SmallCategoryArrow.ofHom (first ≫ second)
  functional : ∀ {first second output₁ output₂ : SmallCategoryArrow C},
    categoryCompositionRelation first second output₁ →
    categoryCompositionRelation first second output₂ → output₁ = output₂
  associative : CategoryCompositionAssociative C
  recoverable : Nonempty (categoryCompositionSystem C ≅
    nonunitResonanceSystem
      (ternaryInteractionObject (categoryCompositionSystem C)))

theorem categoryInteractionRepresentationTheorem
    (C : Type u) [Category.{u} C] :
    CategoryInteractionRepresentationTheorem C where
  exact_composition := categoryInteractionIncidence_composition_iff
  functional := categoryCompositionRelation_functional
  associative := categoryComposition_associative C
  recoverable := categoryInteractionRepresentation_recoverable C

end IncidenceCore
