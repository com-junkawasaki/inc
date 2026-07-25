import IncidenceTheory.RoleChangingResonanceSaturation

namespace IncidenceCore

open CategoryTheory

universe u

structure BoundarySurjectiveResonanceObject where
  val : RoleChangingResonanceObject.{u}

structure BoundarySurjectiveResonanceHom
    (source target : BoundarySurjectiveResonanceObject.{u}) where
  exactHom : RoleChangingExactResonanceHom source.val target.val
  covers_boundary : ∀ targetValue targetEndpoint,
    targetEndpoint ∈ target.val.incidence.boundary targetValue →
      ∃ sourceValue sourceEndpoint,
        exactHom.toFun sourceValue = targetValue ∧
        sourceEndpoint ∈ source.val.incidence.boundary sourceValue ∧
        mapRoleChangingEndpoint exactHom.toFun exactHom.roleMap sourceEndpoint =
          targetEndpoint

@[ext] theorem BoundarySurjectiveResonanceHom.ext
    {source target : BoundarySurjectiveResonanceObject.{u}}
    {first second : BoundarySurjectiveResonanceHom source target}
    (cellEqual : first.exactHom.toFun = second.exactHom.toFun)
    (roleEqual : first.exactHom.roleMap = second.exactHom.roleMap)
    (typeEqual : first.exactHom.typeMap = second.exactHom.typeMap) :
    first = second := by
  cases first
  cases second
  simp_all [RoleChangingExactResonanceHom.ext_iff]

def BoundarySurjectiveResonanceHom.id
    (object : BoundarySurjectiveResonanceObject.{u}) :
    BoundarySurjectiveResonanceHom object object where
  exactHom := RoleChangingExactResonanceHom.id object.val
  covers_boundary := by
    intro targetValue targetEndpoint member
    refine ⟨targetValue, targetEndpoint, rfl, member, ?_⟩
    change mapRoleChangingEndpoint (fun value => value) (fun role => role)
      targetEndpoint = targetEndpoint
    cases targetEndpoint
    rfl

def BoundarySurjectiveResonanceHom.comp
    {first second third : BoundarySurjectiveResonanceObject.{u}}
    (after : BoundarySurjectiveResonanceHom second third)
    (before : BoundarySurjectiveResonanceHom first second) :
    BoundarySurjectiveResonanceHom first third where
  exactHom := after.exactHom.comp before.exactHom
  covers_boundary := by
    intro targetValue targetEndpoint member
    rcases after.covers_boundary targetValue targetEndpoint member with
      ⟨middleValue, middleEndpoint, middleValueEq, middleMember,
        middleEndpointEq⟩
    rcases before.covers_boundary middleValue middleEndpoint middleMember with
      ⟨sourceValue, sourceEndpoint, sourceValueEq, sourceMember,
        sourceEndpointEq⟩
    refine ⟨sourceValue, sourceEndpoint, ?_, sourceMember, ?_⟩
    · exact congrArg after.exactHom.toFun sourceValueEq |>.trans middleValueEq
    · change mapRoleChangingEndpoint
        (after.exactHom.toFun ∘ before.exactHom.toFun)
        (after.exactHom.roleMap ∘ before.exactHom.roleMap) sourceEndpoint = _
      rw [mapRoleChangingEndpoint_comp, sourceEndpointEq, middleEndpointEq]

instance boundarySurjectiveResonanceObjectCategory :
    Category BoundarySurjectiveResonanceObject.{u} where
  Hom := BoundarySurjectiveResonanceHom
  id := BoundarySurjectiveResonanceHom.id
  comp before after := after.comp before
  id_comp := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  comp_id := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  assoc := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl

def boundarySurjectiveForgetful :
    BoundarySurjectiveResonanceObject.{u} ⥤
      RoleChangingResonanceObject.{u} where
  obj object := object.val
  map hom := hom.exactHom
  map_id := by intros; rfl
  map_comp := by intros; rfl

def boundarySurjectiveSaturateObject
    (object : BoundarySurjectiveResonanceObject.{u}) :
    BoundarySurjectiveResonanceObject where
  val := roleChangingSaturateObject object.val

def boundarySurjectiveSaturateMap
    {source target : BoundarySurjectiveResonanceObject.{u}}
    (hom : source ⟶ target) :
    boundarySurjectiveSaturateObject source ⟶
      boundarySurjectiveSaturateObject target where
  exactHom := roleChangingSaturateMap hom.exactHom
  covers_boundary := hom.covers_boundary

def boundarySurjectiveSaturationFunctor :
    BoundarySurjectiveResonanceObject.{u} ⥤
      BoundarySurjectiveResonanceObject.{u} where
  obj := boundarySurjectiveSaturateObject
  map := boundarySurjectiveSaturateMap
  map_id := by
    intro
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  map_comp := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl

def boundarySurjectiveSaturationUnit :
    𝟭 BoundarySurjectiveResonanceObject.{u} ⟶
      boundarySurjectiveSaturationFunctor where
  app object := {
    exactHom := roleChangingSaturationUnit.app object.val
    covers_boundary := by
      intro targetValue targetEndpoint member
      refine ⟨targetValue, targetEndpoint, rfl, member, ?_⟩
      change mapRoleChangingEndpoint (fun value => value) (fun role => role)
        targetEndpoint = targetEndpoint
      cases targetEndpoint
      rfl }
  naturality := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl

def boundarySurjectiveSaturationIdempotenceIso :
    boundarySurjectiveSaturationFunctor ⋙
        boundarySurjectiveSaturationFunctor ≅
      boundarySurjectiveSaturationFunctor where
  hom := {
    app := fun object => {
      exactHom := roleChangingSaturationIdempotenceIso.hom.app object.val
      covers_boundary := by
        intro targetValue targetEndpoint member
        refine ⟨targetValue, targetEndpoint, rfl, member, ?_⟩
        change mapRoleChangingEndpoint (fun value => value) (fun role => role)
          targetEndpoint = targetEndpoint
        cases targetEndpoint
        rfl }
    naturality := by
      intros
      apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl }
  inv := {
    app := fun object => {
      exactHom := roleChangingSaturationIdempotenceIso.inv.app object.val
      covers_boundary := by
        intro targetValue targetEndpoint member
        refine ⟨targetValue, targetEndpoint, rfl, member, ?_⟩
        change mapRoleChangingEndpoint (fun value => value) (fun role => role)
          targetEndpoint = targetEndpoint
        cases targetEndpoint
        rfl }
    naturality := by
      intros
      apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl }
  hom_inv_id := by
    ext object
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  inv_hom_id := by
    ext object
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl

def BoundarySurjectiveCongruentObject :=
  { object : BoundarySurjectiveResonanceObject.{u} //
    QuotientResonanceCongruent object.val.incidence }

instance boundarySurjectiveCongruentObjectCategory :
    Category BoundarySurjectiveCongruentObject.{u} where
  Hom source target := BoundarySurjectiveResonanceHom source.val target.val
  id source := BoundarySurjectiveResonanceHom.id source.val
  comp before after := after.comp before
  id_comp := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  comp_id := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  assoc := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl

def boundarySurjectiveCongruentInclusion :
    BoundarySurjectiveCongruentObject.{u} ⥤
      BoundarySurjectiveResonanceObject.{u} where
  obj object := object.val
  map hom := hom
  map_id := by intros; rfl
  map_comp := by intros; rfl

def boundarySurjectiveSaturationReflector :
    BoundarySurjectiveResonanceObject.{u} ⥤
      BoundarySurjectiveCongruentObject.{u} where
  obj object := ⟨boundarySurjectiveSaturateObject object,
    quotientResonanceCongruent_of_exact_descent
      (bisimulationResonanceSaturation_exactDescent
        object.val.incidence)⟩
  map := boundarySurjectiveSaturateMap
  map_id := by
    intro
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  map_comp := by
    intros
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl

def boundarySurjectiveSaturationHomEquiv
    (source : BoundarySurjectiveResonanceObject.{u})
    (target : BoundarySurjectiveCongruentObject.{u}) :
    (boundarySurjectiveSaturationReflector.obj source ⟶ target) ≃
      (source ⟶ boundarySurjectiveCongruentInclusion.obj target) where
  toFun hom := hom.comp (boundarySurjectiveSaturationUnit.app source)
  invFun hom := {
    exactHom := (roleChangingSaturationHomEquiv source.val
      ⟨target.val.val, target.property⟩).symm hom.exactHom
    covers_boundary := hom.covers_boundary }
  left_inv hom := by
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
  right_inv hom := by
    apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl

def boundarySurjectiveSaturationAdjunction :
    boundarySurjectiveSaturationReflector ⊣
      boundarySurjectiveCongruentInclusion :=
  Adjunction.mkOfHomEquiv {
    homEquiv := boundarySurjectiveSaturationHomEquiv
    homEquiv_naturality_left_symm := by
      intros
      apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl
    homEquiv_naturality_right := by
      intros
      apply BoundarySurjectiveResonanceHom.ext <;> funext value <;> rfl }

theorem boundarySurjectiveSaturation_factorization_unique
    (source : BoundarySurjectiveResonanceObject.{u})
    (target : BoundarySurjectiveCongruentObject.{u})
    (hom : source ⟶ boundarySurjectiveCongruentInclusion.obj target) :
    ∃! factor : boundarySurjectiveSaturationReflector.obj source ⟶ target,
      factor.comp (boundarySurjectiveSaturationUnit.app source) = hom := by
  let factor := (boundarySurjectiveSaturationHomEquiv source target).symm hom
  refine ⟨factor,
    (boundarySurjectiveSaturationHomEquiv source target).apply_symm_apply hom,
    ?_⟩
  intro candidate commutes
  apply (boundarySurjectiveSaturationHomEquiv source target).injective
  exact commutes.trans
    ((boundarySurjectiveSaturationHomEquiv source target).apply_symm_apply hom).symm

def unitGraphBoundarySurjectiveObject :
    BoundarySurjectiveResonanceObject where
  val := unitGraphRoleChangingObject

def boolUnitBoundarySurjectiveObject :
    BoundarySurjectiveResonanceObject where
  val := boolUnitRoleChangingObject

def unitGraphToBoolUnitBoundarySurjectiveHom :
    unitGraphBoundarySurjectiveObject ⟶
      boolUnitBoundarySurjectiveObject where
  exactHom := unitGraphToBoolUnitExactHom
  covers_boundary := by
    intro targetValue targetEndpoint member
    simp [boolUnitBoundarySurjectiveObject, boolUnitRoleChangingObject,
      rolePolymorphicTrivialIncidence] at member

theorem unitGraphToBoolUnitBoundarySurjectiveHom_nontrivial :
    ¬ Function.Surjective
      unitGraphToBoolUnitBoundarySurjectiveHom.exactHom.toFun ∧
    (∀ targetValue targetEndpoint,
      targetEndpoint ∈ boolUnitBoundarySurjectiveObject.val.incidence.boundary
        targetValue →
      ∃ sourceValue sourceEndpoint,
        unitGraphToBoolUnitBoundarySurjectiveHom.exactHom.toFun sourceValue =
          targetValue ∧
        sourceEndpoint ∈
          unitGraphBoundarySurjectiveObject.val.incidence.boundary sourceValue ∧
        mapRoleChangingEndpoint
          unitGraphToBoolUnitBoundarySurjectiveHom.exactHom.toFun
          unitGraphToBoolUnitBoundarySurjectiveHom.exactHom.roleMap
          sourceEndpoint = targetEndpoint) := by
  exact ⟨unitGraphToBoolUnitExactHom_changes_role_and_carrier.1,
    unitGraphToBoolUnitBoundarySurjectiveHom.covers_boundary⟩

end IncidenceCore
