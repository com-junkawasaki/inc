import IncidenceTheory.RelationalCategoryRoundTrip

namespace IncidenceCore

open CategoryTheory

universe u

structure RecognizedTernaryCategory where
  system : TernaryResonanceSystem.{u}
  axioms : RelationalCategoryAxioms system

structure RecognizedTernaryHom
    (source target : RecognizedTernaryCategory.{u}) where
  toFun : source.system.Carrier → target.system.Carrier
  preserves : ∀ {first second output},
    source.system.resonance first second output →
      target.system.resonance (toFun first) (toFun second) (toFun output)
  maps_pure : ∀ {identity}, TernaryPureIdentity source.system identity →
    TernaryPureIdentity target.system (toFun identity)

instance RecognizedTernaryHom.coeFun
    {source target : RecognizedTernaryCategory.{u}} :
    CoeFun (RecognizedTernaryHom source target)
      (fun _ => source.system.Carrier → target.system.Carrier) :=
  ⟨RecognizedTernaryHom.toFun⟩

@[ext] theorem RecognizedTernaryHom.ext
    {source target : RecognizedTernaryCategory.{u}}
    {first second : RecognizedTernaryHom source target}
    (equal : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  cases equal
  rfl

def RecognizedTernaryHom.id (object : RecognizedTernaryCategory.{u}) :
    RecognizedTernaryHom object object where
  toFun := fun value => value
  preserves := fun resonant => resonant
  maps_pure := fun pure => pure

def RecognizedTernaryHom.comp
    {first second third : RecognizedTernaryCategory.{u}}
    (later : RecognizedTernaryHom second third)
    (earlier : RecognizedTernaryHom first second) :
    RecognizedTernaryHom first third where
  toFun := later.toFun ∘ earlier.toFun
  preserves := fun resonant => later.preserves (earlier.preserves resonant)
  maps_pure := fun pure => later.maps_pure (earlier.maps_pure pure)

instance recognizedTernaryCategoryStruct :
    CategoryStruct.{u} (RecognizedTernaryCategory.{u}) where
  Hom := RecognizedTernaryHom
  id := RecognizedTernaryHom.id
  comp first second := RecognizedTernaryHom.comp second first

instance recognizedTernaryCategory :
    Category.{u} (RecognizedTernaryCategory.{u}) where
  id_comp hom := by
    apply RecognizedTernaryHom.ext
    funext value
    rfl
  comp_id hom := by
    apply RecognizedTernaryHom.ext
    funext value
    rfl
  assoc first second third := by
    apply RecognizedTernaryHom.ext
    funext value
    rfl

theorem RecognizedTernaryHom.preserves_source
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target)
    {arrow identity : source.system.Carrier}
    (property : TernarySourceIdentity source.system arrow identity) :
    TernarySourceIdentity target.system (hom arrow) (hom identity) :=
  ⟨hom.maps_pure property.1, hom.preserves property.2⟩

theorem RecognizedTernaryHom.preserves_target
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target)
    {arrow identity : source.system.Carrier}
    (property : TernaryTargetIdentity source.system arrow identity) :
    TernaryTargetIdentity target.system (hom arrow) (hom identity) :=
  ⟨hom.maps_pure property.1, hom.preserves property.2⟩

def RecognizedTernaryHom.mapObject
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target)
    (object : RelationalCategoryObject source.system) :
    RelationalCategoryObject target.system :=
  ⟨hom object.val, hom.maps_pure object.property⟩

def RecognizedTernaryHom.mapHom
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target)
    {X Y : RelationalCategoryObject source.system}
    (arrow : RelationalCategoryHom source.system X Y) :
    RelationalCategoryHom target.system (hom.mapObject X) (hom.mapObject Y) :=
  ⟨hom arrow.val, hom.preserves_source arrow.property.1,
    hom.preserves_target arrow.property.2⟩

noncomputable def RecognizedTernaryHom.reconstructFunctor
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target) :
    @Functor (RelationalCategoryObject source.system)
      source.axioms.toCategory (RelationalCategoryObject target.system)
      target.axioms.toCategory := by
  letI := source.axioms.toCategory
  letI := target.axioms.toCategory
  exact
    { obj := hom.mapObject
      map := hom.mapHom
      map_id := by
        intro object
        rfl
      map_comp := by
        intro X Y Z first second
        apply Subtype.ext
        apply target.axioms.functional
        · exact hom.preserves (source.axioms.composite_resonant first second)
        · exact target.axioms.composite_resonant (hom.mapHom first)
            (hom.mapHom second) }

@[simp] theorem reconstructFunctor_id
    (object : RecognizedTernaryCategory.{u}) :
    (RecognizedTernaryHom.id object).reconstructFunctor =
      @Functor.id (RelationalCategoryObject object.system)
        object.axioms.toCategory := by
  letI := object.axioms.toCategory
  apply CategoryTheory.Functor.ext (fun X => rfl)
    (fun X Y arrow => by simp)

@[simp] theorem reconstructFunctor_comp
    {first second third : RecognizedTernaryCategory.{u}}
    (earlier : RecognizedTernaryHom first second)
    (later : RecognizedTernaryHom second third) :
    (RecognizedTernaryHom.comp later earlier).reconstructFunctor =
      @Functor.comp (RelationalCategoryObject first.system)
        first.axioms.toCategory (RelationalCategoryObject second.system)
        second.axioms.toCategory (RelationalCategoryObject third.system)
        third.axioms.toCategory earlier.reconstructFunctor
        later.reconstructFunctor := by
  letI := first.axioms.toCategory
  letI := second.axioms.toCategory
  letI := third.axioms.toCategory
  apply CategoryTheory.Functor.ext (fun X => rfl)
    (fun X Y arrow => by simp)

noncomputable def RecognizedTernaryHom.mapRecognizedArrow
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target)
    (arrow : RecognizedCategoryArrow source.system source.axioms) :
    RecognizedCategoryArrow target.system target.axioms :=
  @SmallCategoryArrow.map
    (RelationalCategoryObject source.system)
    (RelationalCategoryObject target.system)
    source.axioms.toCategory target.axioms.toCategory
    hom.reconstructFunctor arrow

theorem RecognizedTernaryHom.encodeArrow_natural
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target)
    (arrow : source.system.Carrier) :
    target.axioms.encodeArrow (hom arrow) =
      hom.mapRecognizedArrow (source.axioms.encodeArrow arrow) := by
  have sourceEqual :
      target.axioms.sourceObject (hom arrow) =
        hom.mapObject (source.axioms.sourceObject arrow) := by
    apply Subtype.ext
    exact target.axioms.sourceIdentity_eq
      (hom.preserves_source (source.axioms.sourceIdentity_spec arrow))
  have targetEqual :
      target.axioms.targetObject (hom arrow) =
        hom.mapObject (source.axioms.targetObject arrow) := by
    apply Subtype.ext
    exact target.axioms.targetIdentity_eq
      (hom.preserves_target (source.axioms.targetIdentity_spec arrow))
  apply recognizedCategoryArrow_ext sourceEqual targetEqual
  apply (Subtype.heq_iff_coe_eq (fun candidate => by
    simp only [RelationalCategoryAxioms.encodeArrow,
      RecognizedTernaryHom.mapRecognizedArrow, SmallCategoryArrow.map,
      RecognizedTernaryHom.reconstructFunctor,
      RecognizedTernaryHom.mapHom]
    rw [sourceEqual, targetEqual])).mpr
  rfl

theorem RecognizedTernaryHom.decode_mapRecognizedArrow
    {source target : RecognizedTernaryCategory.{u}}
    (hom : RecognizedTernaryHom source target)
    (arrow : RecognizedCategoryArrow source.system source.axioms) :
    target.axioms.decodeArrow (hom.mapRecognizedArrow arrow) =
      hom (source.axioms.decodeArrow arrow) := by
  rw [← source.axioms.encode_decodeArrow arrow]
  rw [← hom.encodeArrow_natural]
  exact target.axioms.decode_encodeArrow
    (hom (source.axioms.decodeArrow arrow))

structure RelationalCategoryFunctorialityTheorem : Prop where
  morphism_category : Nonempty
    (Category.{u} (RecognizedTernaryCategory.{u}))
  reconstructed_functor : ∀ {source target : RecognizedTernaryCategory.{u}},
    RecognizedTernaryHom source target → Nonempty
      (@Functor (RelationalCategoryObject source.system)
        source.axioms.toCategory (RelationalCategoryObject target.system)
        target.axioms.toCategory)
  identity_exact : ∀ object : RecognizedTernaryCategory.{u},
    (RecognizedTernaryHom.id object).reconstructFunctor =
      @Functor.id (RelationalCategoryObject object.system)
        object.axioms.toCategory
  composition_exact : ∀
      {first second third : RecognizedTernaryCategory.{u}}
      (earlier : RecognizedTernaryHom first second)
    (later : RecognizedTernaryHom second third),
    (RecognizedTernaryHom.comp later earlier).reconstructFunctor =
      @Functor.comp (RelationalCategoryObject first.system)
        first.axioms.toCategory (RelationalCategoryObject second.system)
        second.axioms.toCategory (RelationalCategoryObject third.system)
        third.axioms.toCategory earlier.reconstructFunctor
        later.reconstructFunctor
  encoding_natural : ∀
      {source target : RecognizedTernaryCategory.{u}}
      (hom : RecognizedTernaryHom source target)
      (arrow : source.system.Carrier),
    target.axioms.encodeArrow (hom arrow) =
      hom.mapRecognizedArrow (source.axioms.encodeArrow arrow)
  decoding_natural : ∀
      {source target : RecognizedTernaryCategory.{u}}
      (hom : RecognizedTernaryHom source target)
      (arrow : RecognizedCategoryArrow source.system source.axioms),
    target.axioms.decodeArrow (hom.mapRecognizedArrow arrow) =
      hom (source.axioms.decodeArrow arrow)

theorem relationalCategoryFunctorialityTheorem :
    RelationalCategoryFunctorialityTheorem where
  morphism_category := ⟨recognizedTernaryCategory⟩
  reconstructed_functor := fun hom => ⟨hom.reconstructFunctor⟩
  identity_exact := reconstructFunctor_id
  composition_exact := reconstructFunctor_comp
  encoding_natural := RecognizedTernaryHom.encodeArrow_natural
  decoding_natural := RecognizedTernaryHom.decode_mapRecognizedArrow

end IncidenceCore
