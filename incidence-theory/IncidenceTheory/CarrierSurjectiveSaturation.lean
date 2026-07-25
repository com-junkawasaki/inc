import IncidenceTheory.BoundarySurjectiveSaturation

namespace IncidenceCore

open CategoryTheory

universe u

structure CarrierSurjectiveResonanceObject where
  val : BoundarySurjectiveResonanceObject.{u}

structure CarrierSurjectiveResonanceHom
    (source target : CarrierSurjectiveResonanceObject.{u}) where
  boundaryHom : BoundarySurjectiveResonanceHom source.val target.val
  carrier_surjective : Function.Surjective boundaryHom.exactHom.toFun

@[ext] theorem CarrierSurjectiveResonanceHom.ext
    {source target : CarrierSurjectiveResonanceObject.{u}}
    {first second : CarrierSurjectiveResonanceHom source target}
    (cellEqual : first.boundaryHom.exactHom.toFun =
      second.boundaryHom.exactHom.toFun)
    (roleEqual : first.boundaryHom.exactHom.roleMap =
      second.boundaryHom.exactHom.roleMap)
    (typeEqual : first.boundaryHom.exactHom.typeMap =
      second.boundaryHom.exactHom.typeMap) : first = second := by
  cases first
  cases second
  simp_all [BoundarySurjectiveResonanceHom.ext_iff]

def CarrierSurjectiveResonanceHom.id
    (object : CarrierSurjectiveResonanceObject.{u}) :
    CarrierSurjectiveResonanceHom object object where
  boundaryHom := BoundarySurjectiveResonanceHom.id object.val
  carrier_surjective := Function.surjective_id

def CarrierSurjectiveResonanceHom.comp
    {first second third : CarrierSurjectiveResonanceObject.{u}}
    (after : CarrierSurjectiveResonanceHom second third)
    (before : CarrierSurjectiveResonanceHom first second) :
    CarrierSurjectiveResonanceHom first third where
  boundaryHom := after.boundaryHom.comp before.boundaryHom
  carrier_surjective := after.carrier_surjective.comp before.carrier_surjective

instance carrierSurjectiveResonanceObjectCategory :
    Category CarrierSurjectiveResonanceObject.{u} where
  Hom := CarrierSurjectiveResonanceHom
  id := CarrierSurjectiveResonanceHom.id
  comp before after := after.comp before
  id_comp := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  comp_id := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  assoc := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl

def carrierSurjectiveForgetful :
    CarrierSurjectiveResonanceObject.{u} ⥤
      BoundarySurjectiveResonanceObject.{u} where
  obj object := object.val
  map hom := hom.boundaryHom
  map_id := by intros; rfl
  map_comp := by intros; rfl

def carrierSurjectiveSaturateObject
    (object : CarrierSurjectiveResonanceObject.{u}) :
    CarrierSurjectiveResonanceObject where
  val := boundarySurjectiveSaturateObject object.val

def carrierSurjectiveSaturateMap
    {source target : CarrierSurjectiveResonanceObject.{u}}
    (hom : source ⟶ target) :
    carrierSurjectiveSaturateObject source ⟶
      carrierSurjectiveSaturateObject target where
  boundaryHom := boundarySurjectiveSaturateMap hom.boundaryHom
  carrier_surjective := hom.carrier_surjective

def carrierSurjectiveSaturationFunctor :
    CarrierSurjectiveResonanceObject.{u} ⥤
      CarrierSurjectiveResonanceObject.{u} where
  obj := carrierSurjectiveSaturateObject
  map := carrierSurjectiveSaturateMap
  map_id := by
    intro
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  map_comp := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl

def carrierSurjectiveSaturationUnit :
    𝟭 CarrierSurjectiveResonanceObject.{u} ⟶
      carrierSurjectiveSaturationFunctor where
  app object := {
    boundaryHom := boundarySurjectiveSaturationUnit.app object.val
    carrier_surjective := Function.surjective_id }
  naturality := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl

def carrierSurjectiveSaturationIdempotenceIso :
    carrierSurjectiveSaturationFunctor ⋙
        carrierSurjectiveSaturationFunctor ≅
      carrierSurjectiveSaturationFunctor where
  hom := {
    app := fun object => {
      boundaryHom := boundarySurjectiveSaturationIdempotenceIso.hom.app object.val
      carrier_surjective := Function.surjective_id }
    naturality := by
      intros
      apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl }
  inv := {
    app := fun object => {
      boundaryHom := boundarySurjectiveSaturationIdempotenceIso.inv.app object.val
      carrier_surjective := Function.surjective_id }
    naturality := by
      intros
      apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl }
  hom_inv_id := by
    ext object
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  inv_hom_id := by
    ext object
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl

def CarrierSurjectiveCongruentObject :=
  { object : CarrierSurjectiveResonanceObject.{u} //
    QuotientResonanceCongruent object.val.val.incidence }

instance carrierSurjectiveCongruentObjectCategory :
    Category CarrierSurjectiveCongruentObject.{u} where
  Hom source target := CarrierSurjectiveResonanceHom source.val target.val
  id source := CarrierSurjectiveResonanceHom.id source.val
  comp before after := after.comp before
  id_comp := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  comp_id := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  assoc := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl

def carrierSurjectiveCongruentInclusion :
    CarrierSurjectiveCongruentObject.{u} ⥤
      CarrierSurjectiveResonanceObject.{u} where
  obj object := object.val
  map hom := hom
  map_id := by intros; rfl
  map_comp := by intros; rfl

def carrierSurjectiveSaturationReflector :
    CarrierSurjectiveResonanceObject.{u} ⥤
      CarrierSurjectiveCongruentObject.{u} where
  obj object := ⟨carrierSurjectiveSaturateObject object,
    quotientResonanceCongruent_of_exact_descent
      (bisimulationResonanceSaturation_exactDescent
        object.val.val.incidence)⟩
  map := carrierSurjectiveSaturateMap
  map_id := by
    intro
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  map_comp := by
    intros
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl

def carrierSurjectiveSaturationHomEquiv
    (source : CarrierSurjectiveResonanceObject.{u})
    (target : CarrierSurjectiveCongruentObject.{u}) :
    (carrierSurjectiveSaturationReflector.obj source ⟶ target) ≃
      (source ⟶ carrierSurjectiveCongruentInclusion.obj target) where
  toFun hom := hom.comp (carrierSurjectiveSaturationUnit.app source)
  invFun hom := {
    boundaryHom := (boundarySurjectiveSaturationHomEquiv source.val
      ⟨target.val.val, target.property⟩).symm hom.boundaryHom
    carrier_surjective := hom.carrier_surjective }
  left_inv hom := by
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
  right_inv hom := by
    apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl

def carrierSurjectiveSaturationAdjunction :
    carrierSurjectiveSaturationReflector ⊣
      carrierSurjectiveCongruentInclusion :=
  Adjunction.mkOfHomEquiv {
    homEquiv := carrierSurjectiveSaturationHomEquiv
    homEquiv_naturality_left_symm := by
      intros
      apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl
    homEquiv_naturality_right := by
      intros
      apply CarrierSurjectiveResonanceHom.ext <;> funext value <;> rfl }

theorem carrierSurjectiveSaturation_factorization_unique
    (source : CarrierSurjectiveResonanceObject.{u})
    (target : CarrierSurjectiveCongruentObject.{u})
    (hom : source ⟶ carrierSurjectiveCongruentInclusion.obj target) :
    ∃! factor : carrierSurjectiveSaturationReflector.obj source ⟶ target,
      factor.comp (carrierSurjectiveSaturationUnit.app source) = hom := by
  let factor := (carrierSurjectiveSaturationHomEquiv source target).symm hom
  refine ⟨factor,
    (carrierSurjectiveSaturationHomEquiv source target).apply_symm_apply hom,
    ?_⟩
  intro candidate commutes
  apply (carrierSurjectiveSaturationHomEquiv source target).injective
  exact commutes.trans
    ((carrierSurjectiveSaturationHomEquiv source target).apply_symm_apply hom).symm

def boolGraphCarrierSurjectiveObject : CarrierSurjectiveResonanceObject where
  val := {
    val := {
      Carrier := Bool
      Role := GraphRole
      CellType := GraphType
      carrierDecidableEq := inferInstance
      incidence := rolePolymorphicTrivialIncidence } }

def unitUnitCarrierSurjectiveObject : CarrierSurjectiveResonanceObject where
  val := {
    val := {
      Carrier := Unit
      Role := Unit
      CellType := GraphType
      carrierDecidableEq := inferInstance
      incidence := rolePolymorphicTrivialIncidence } }

def boolGraphToUnitUnitCarrierSurjectiveHom :
    boolGraphCarrierSurjectiveObject ⟶ unitUnitCarrierSurjectiveObject where
  boundaryHom := {
    exactHom := {
      toFun := fun _ => ()
      roleMap := fun _ => ()
      typeMap := id
      map_type := by simp [boolGraphCarrierSurjectiveObject,
        unitUnitCarrierSurjectiveObject, rolePolymorphicTrivialIncidence]
      map_unit := rfl
      map_glue := by simp [boolGraphCarrierSurjectiveObject,
        unitUnitCarrierSurjectiveObject, rolePolymorphicTrivialIncidence]
      map_boundary_iff := by simp [boolGraphCarrierSurjectiveObject,
        unitUnitCarrierSurjectiveObject, rolePolymorphicTrivialIncidence]
      map_resonance := by simp [boolGraphCarrierSurjectiveObject,
        unitUnitCarrierSurjectiveObject, rolePolymorphicTrivialIncidence]
      map_bisimulation := by
        intro first second related
        exact rolePolymorphicTrivialIncidence_approxBisim_total () () }
    covers_boundary := by
      intro targetValue targetEndpoint member
      simp [unitUnitCarrierSurjectiveObject,
        rolePolymorphicTrivialIncidence] at member }
  carrier_surjective := by
    intro target
    cases target
    exact ⟨false, rfl⟩

theorem boolGraphToUnitUnitCarrierSurjectiveHom_surjective_not_injective :
    Function.Surjective
        boolGraphToUnitUnitCarrierSurjectiveHom.boundaryHom.exactHom.toFun ∧
      ¬ Function.Injective
        boolGraphToUnitUnitCarrierSurjectiveHom.boundaryHom.exactHom.toFun := by
  constructor
  · exact boolGraphToUnitUnitCarrierSurjectiveHom.carrier_surjective
  · intro injective
    have impossible := injective
      (show boolGraphToUnitUnitCarrierSurjectiveHom.boundaryHom.exactHom.toFun false =
        boolGraphToUnitUnitCarrierSurjectiveHom.boundaryHom.exactHom.toFun true by rfl)
    simp at impossible

end IncidenceCore
