import IncidenceTheory.GlobalResonanceSaturation

namespace IncidenceCore

open CategoryTheory

universe u

def mapRoleChangingEndpoint
    {I J SourceRole TargetRole : Type u}
    (cellMap : I → J) (roleMap : SourceRole → TargetRole)
    (endpoint : Endpoint I SourceRole) : Endpoint J TargetRole :=
  ⟨cellMap endpoint.i, roleMap endpoint.role, endpoint.sign,
    endpoint.mult, endpoint.mult_pos⟩

@[simp] theorem mapRoleChangingEndpoint_id
    {I Role : Type u} (endpoint : Endpoint I Role) :
    mapRoleChangingEndpoint id id endpoint = endpoint := by
  cases endpoint
  rfl

@[simp] theorem mapRoleChangingEndpoint_comp
    {I J K Role₁ Role₂ Role₃ : Type u}
    (cellAfter : J → K) (cellBefore : I → J)
    (roleAfter : Role₂ → Role₃) (roleBefore : Role₁ → Role₂)
    (endpoint : Endpoint I Role₁) :
    mapRoleChangingEndpoint (cellAfter ∘ cellBefore)
        (roleAfter ∘ roleBefore) endpoint =
      mapRoleChangingEndpoint cellAfter roleAfter
        (mapRoleChangingEndpoint cellBefore roleBefore endpoint) := by
  cases endpoint
  rfl

structure RoleChangingResonanceObject where
  Carrier : Type u
  Role : Type u
  CellType : Type u
  carrierDecidableEq : DecidableEq Carrier
  incidence : @Incidence Carrier Role CellType carrierDecidableEq

attribute [instance] RoleChangingResonanceObject.carrierDecidableEq

/- Boundary membership is exact on every mapped occurrence, strengthening the
   forward-only boundary law used by `StructuredIncidenceHom`. -/
structure RoleChangingExactResonanceHom
    (source target : RoleChangingResonanceObject.{u}) where
  toFun : source.Carrier → target.Carrier
  roleMap : source.Role → target.Role
  typeMap : source.CellType → target.CellType
  map_type : ∀ value,
    target.incidence.typeFunc (toFun value) =
      typeMap (source.incidence.typeFunc value)
  map_unit : toFun source.incidence.unit = target.incidence.unit
  map_glue : ∀ left right output,
    source.incidence.glue left right = some output →
      target.incidence.glue (toFun left) (toFun right) = some (toFun output)
  map_boundary_iff : ∀ value endpoint,
    mapRoleChangingEndpoint toFun roleMap endpoint ∈
        target.incidence.boundary (toFun value) ↔
      endpoint ∈ source.incidence.boundary value
  map_resonance : ∀ left right output,
    source.incidence.resonance left right output →
      target.incidence.resonance (toFun left) (toFun right) (toFun output)
  map_bisimulation : ∀ {first second},
    approxBisim source.incidence first second →
      approxBisim target.incidence (toFun first) (toFun second)

@[ext] theorem RoleChangingExactResonanceHom.ext
    {source target : RoleChangingResonanceObject.{u}}
    {first second : RoleChangingExactResonanceHom source target}
    (cellEqual : first.toFun = second.toFun)
    (roleEqual : first.roleMap = second.roleMap)
    (typeEqual : first.typeMap = second.typeMap) : first = second := by
  cases first
  cases second
  simp_all

def RoleChangingExactResonanceHom.id
    (object : RoleChangingResonanceObject.{u}) :
    RoleChangingExactResonanceHom object object where
  toFun := fun value => value
  roleMap := fun role => role
  typeMap := fun cellType => cellType
  map_type := fun _ => rfl
  map_unit := rfl
  map_glue := fun _ _ _ selected => selected
  map_boundary_iff := by
    intro value endpoint
    cases endpoint
    rfl
  map_resonance := fun _ _ _ resonant => resonant
  map_bisimulation := fun related => related

def RoleChangingExactResonanceHom.comp
    {first second third : RoleChangingResonanceObject.{u}}
    (after : RoleChangingExactResonanceHom second third)
    (before : RoleChangingExactResonanceHom first second) :
    RoleChangingExactResonanceHom first third where
  toFun := after.toFun ∘ before.toFun
  roleMap := after.roleMap ∘ before.roleMap
  typeMap := after.typeMap ∘ before.typeMap
  map_type := by
    intro value
    rw [Function.comp_apply, after.map_type, Function.comp_apply,
      before.map_type]
  map_unit := by rw [Function.comp_apply, before.map_unit, after.map_unit]
  map_glue := by
    intro left right output selected
    exact after.map_glue _ _ _ (before.map_glue _ _ _ selected)
  map_boundary_iff := by
    intro value endpoint
    rw [mapRoleChangingEndpoint_comp]
    exact (after.map_boundary_iff (before.toFun value)
      (mapRoleChangingEndpoint before.toFun before.roleMap endpoint)).trans
        (before.map_boundary_iff value endpoint)
  map_resonance := by
    intro left right output resonant
    exact after.map_resonance _ _ _
      (before.map_resonance _ _ _ resonant)
  map_bisimulation := fun related =>
    after.map_bisimulation (before.map_bisimulation related)

instance roleChangingResonanceObjectCategory :
    Category RoleChangingResonanceObject.{u} where
  Hom := RoleChangingExactResonanceHom
  id := RoleChangingExactResonanceHom.id
  comp before after := after.comp before
  id_comp := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  comp_id := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  assoc := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl

def roleChangingSaturateObject
    (object : RoleChangingResonanceObject.{u}) :
    RoleChangingResonanceObject where
  Carrier := object.Carrier
  Role := object.Role
  CellType := object.CellType
  carrierDecidableEq := object.carrierDecidableEq
  incidence := bisimulationResonanceSaturation object.incidence

def roleChangingSaturateMap
    {source target : RoleChangingResonanceObject.{u}}
    (hom : source ⟶ target) :
    roleChangingSaturateObject source ⟶ roleChangingSaturateObject target where
  toFun := hom.toFun
  roleMap := hom.roleMap
  typeMap := hom.typeMap
  map_type := hom.map_type
  map_unit := hom.map_unit
  map_glue := hom.map_glue
  map_boundary_iff := hom.map_boundary_iff
  map_resonance := by
    intro left right output saturated
    rcases saturated with
      ⟨sourceLeft, sourceRight, sourceOutput,
        leftEq, rightEq, outputEq, resonant⟩
    refine ⟨hom.toFun sourceLeft, hom.toFun sourceRight,
      hom.toFun sourceOutput, ?_, ?_, ?_,
      hom.map_resonance _ _ _ resonant⟩
    · exact Quotient.sound (hom.map_bisimulation (Quotient.exact leftEq))
    · exact Quotient.sound (hom.map_bisimulation (Quotient.exact rightEq))
    · exact Quotient.sound (hom.map_bisimulation (Quotient.exact outputEq))
  map_bisimulation := hom.map_bisimulation

def roleChangingSaturationFunctor :
    RoleChangingResonanceObject.{u} ⥤ RoleChangingResonanceObject.{u} where
  obj := roleChangingSaturateObject
  map := roleChangingSaturateMap
  map_id := by
    intro
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  map_comp := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl

def roleChangingSaturationUnit :
    𝟭 RoleChangingResonanceObject.{u} ⟶ roleChangingSaturationFunctor where
  app object := {
    toFun := fun value => value
    roleMap := fun role => role
    typeMap := fun cellType => cellType
    map_type := fun _ => rfl
    map_unit := rfl
    map_glue := fun _ _ _ selected => selected
    map_boundary_iff := by
      intro value endpoint
      cases endpoint
      rfl
    map_resonance := fun _ _ _ resonant =>
      resonance_implies_bisimulationResonanceSaturation resonant
    map_bisimulation := fun related => related }
  naturality := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl

set_option maxHeartbeats 800000 in
def roleChangingSaturationIdempotenceIso :
    roleChangingSaturationFunctor ⋙ roleChangingSaturationFunctor ≅
      roleChangingSaturationFunctor where
  hom := {
    app := fun object => {
      toFun := fun value => value
      roleMap := fun role => role
      typeMap := fun cellType => cellType
      map_type := fun _ => rfl
      map_unit := rfl
      map_glue := fun _ _ _ selected => selected
      map_boundary_iff := by
        intro value endpoint
        cases endpoint
        rfl
      map_resonance := by
        intro left right output resonant
        exact (bisimulationResonanceSaturation_idempotent
          object.incidence left right output).mp resonant
      map_bisimulation := fun related => related }
    naturality := by
      intros
      apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl }
  inv := {
    app := fun object => {
      toFun := fun value => value
      roleMap := fun role => role
      typeMap := fun cellType => cellType
      map_type := fun _ => rfl
      map_unit := rfl
      map_glue := fun _ _ _ selected => selected
      map_boundary_iff := by
        intro value endpoint
        cases endpoint
        rfl
      map_resonance := fun _ _ _ resonant =>
        resonance_implies_bisimulationResonanceSaturation resonant
      map_bisimulation := fun related => related }
    naturality := by
      intros
      apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl }
  hom_inv_id := by
    ext object
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  inv_hom_id := by
    ext object
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl

def RoleChangingCongruentResonanceObject :=
  { object : RoleChangingResonanceObject.{u} //
    QuotientResonanceCongruent object.incidence }

instance roleChangingCongruentResonanceObjectCategory :
    Category RoleChangingCongruentResonanceObject.{u} where
  Hom source target := RoleChangingExactResonanceHom source.val target.val
  id source := RoleChangingExactResonanceHom.id source.val
  comp before after := after.comp before
  id_comp := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  comp_id := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  assoc := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl

def roleChangingCongruentResonanceInclusion :
    RoleChangingCongruentResonanceObject.{u} ⥤
      RoleChangingResonanceObject.{u} where
  obj object := object.val
  map hom := hom
  map_id := by intros; rfl
  map_comp := by intros; rfl

def roleChangingSaturationReflector :
    RoleChangingResonanceObject.{u} ⥤
      RoleChangingCongruentResonanceObject.{u} where
  obj object := ⟨roleChangingSaturateObject object,
    quotientResonanceCongruent_of_exact_descent
      (bisimulationResonanceSaturation_exactDescent object.incidence)⟩
  map := roleChangingSaturateMap
  map_id := by
    intro
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  map_comp := by
    intros
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl

def roleChangingSaturationHomEquiv
    (source : RoleChangingResonanceObject.{u})
    (target : RoleChangingCongruentResonanceObject.{u}) :
    (roleChangingSaturationReflector.obj source ⟶ target) ≃
      (source ⟶ roleChangingCongruentResonanceInclusion.obj target) where
  toFun hom := hom.comp (roleChangingSaturationUnit.app source)
  invFun hom := {
    toFun := hom.toFun
    roleMap := hom.roleMap
    typeMap := hom.typeMap
    map_type := hom.map_type
    map_unit := hom.map_unit
    map_glue := hom.map_glue
    map_boundary_iff := hom.map_boundary_iff
    map_resonance := by
      intro left right output saturated
      rcases saturated with
        ⟨sourceLeft, sourceRight, sourceOutput,
          leftEq, rightEq, outputEq, resonant⟩
      have leftRelated := hom.map_bisimulation (Quotient.exact leftEq)
      have rightRelated := hom.map_bisimulation (Quotient.exact rightEq)
      have outputRelated := hom.map_bisimulation (Quotient.exact outputEq)
      exact (target.property leftRelated rightRelated outputRelated).mp
        (hom.map_resonance _ _ _ resonant)
    map_bisimulation := hom.map_bisimulation }
  left_inv hom := by
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
  right_inv hom := by
    apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl

def roleChangingSaturationAdjunction :
    roleChangingSaturationReflector ⊣
      roleChangingCongruentResonanceInclusion :=
  Adjunction.mkOfHomEquiv {
    homEquiv := roleChangingSaturationHomEquiv
    homEquiv_naturality_left_symm := by
      intros
      apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl
    homEquiv_naturality_right := by
      intros
      apply RoleChangingExactResonanceHom.ext <;> funext value <;> rfl }

theorem roleChangingSaturation_factorization_unique
    (source : RoleChangingResonanceObject.{u})
    (target : RoleChangingCongruentResonanceObject.{u})
    (hom : source ⟶ roleChangingCongruentResonanceInclusion.obj target) :
    ∃! factor : roleChangingSaturationReflector.obj source ⟶ target,
      factor.comp (roleChangingSaturationUnit.app source) = hom := by
  let factor := (roleChangingSaturationHomEquiv source target).symm hom
  refine ⟨factor, (roleChangingSaturationHomEquiv source target).apply_symm_apply hom,
    ?_⟩
  intro candidate commutes
  apply (roleChangingSaturationHomEquiv source target).injective
  exact commutes.trans
    ((roleChangingSaturationHomEquiv source target).apply_symm_apply hom).symm

def rolePolymorphicTrivialIncidence
    {I Role : Type u} [Inhabited I] [DecidableEq I] :
    Incidence I Role GraphType where
  boundary := fun _ => []
  typeFunc := fun _ => .unit
  glue := fun left right =>
    if left = default then some right
    else if right = default then some left
    else some left
  unit := default
  guards := Guards.permissive _
  type_consistent := by simp
  sign_rules := by intros; simp_all
  multiplicities := by intros; simp_all
  well_founded := by simp
  unit_left := by simp
  unit_right := by intro value; by_cases h : value = default <;> simp [h]
  type_preserve := by simp

theorem rolePolymorphicTrivialIncidence_approxBisim_total
    {I Role : Type u} [Inhabited I] [DecidableEq I] (first second : I) :
    approxBisim
      (rolePolymorphicTrivialIncidence : Incidence I Role GraphType)
      first second := by
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro left right related
  refine ⟨rfl, ?_⟩
  simp [boundaryMatched, rolePolymorphicTrivialIncidence]

def unitGraphRoleChangingObject : RoleChangingResonanceObject where
  Carrier := Unit
  Role := GraphRole
  CellType := GraphType
  carrierDecidableEq := inferInstance
  incidence := rolePolymorphicTrivialIncidence

def boolUnitRoleChangingObject : RoleChangingResonanceObject where
  Carrier := Bool
  Role := Unit
  CellType := GraphType
  carrierDecidableEq := inferInstance
  incidence := rolePolymorphicTrivialIncidence

def unitGraphToBoolUnitExactHom :
    unitGraphRoleChangingObject ⟶ boolUnitRoleChangingObject where
  toFun := fun _ => false
  roleMap := fun _ => ()
  typeMap := id
  map_type := by simp [unitGraphRoleChangingObject,
    boolUnitRoleChangingObject, rolePolymorphicTrivialIncidence]
  map_unit := rfl
  map_glue := by simp [unitGraphRoleChangingObject,
    boolUnitRoleChangingObject, rolePolymorphicTrivialIncidence]
  map_boundary_iff := by simp [unitGraphRoleChangingObject,
    boolUnitRoleChangingObject, rolePolymorphicTrivialIncidence]
  map_resonance := by simp [unitGraphRoleChangingObject,
    boolUnitRoleChangingObject, rolePolymorphicTrivialIncidence]
  map_bisimulation := by
    intro first second related
    exact rolePolymorphicTrivialIncidence_approxBisim_total false false

theorem unitGraphToBoolUnitExactHom_changes_role_and_carrier :
    ¬ Function.Surjective unitGraphToBoolUnitExactHom.toFun ∧
      Nonempty (unitGraphRoleChangingObject.Role →
        boolUnitRoleChangingObject.Role) := by
  constructor
  · intro surjective
    rcases surjective true with ⟨source, impossible⟩
    cases source
    simp [unitGraphToBoolUnitExactHom] at impossible
  · exact ⟨unitGraphToBoolUnitExactHom.roleMap⟩

end IncidenceCore
