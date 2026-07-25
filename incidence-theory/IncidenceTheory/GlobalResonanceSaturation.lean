import IncidenceTheory.ResonanceSaturation

namespace IncidenceCore

open CategoryTheory

universe u

/- Incidences with varying carriers and cell types, but a fixed boundary-role
   type.  Fixing roles is exactly the scope of `StructuredIncidenceHom`; carrier
   changes remain fully general. -/
structure GlobalResonanceObject (Role : Type u) where
  Carrier : Type u
  CellType : Type u
  carrierDecidableEq : DecidableEq Carrier
  incidence : @Incidence Carrier Role CellType carrierDecidableEq

attribute [instance] GlobalResonanceObject.carrierDecidableEq

structure GlobalResonanceHom {Role : Type u}
    (source target : GlobalResonanceObject Role) where
  structured : StructuredIncidenceHom source.incidence target.incidence
  map_bisimulation : ∀ {first second},
    approxBisim source.incidence first second →
      approxBisim target.incidence
        (structured.toFun first) (structured.toFun second)

@[ext] theorem GlobalResonanceHom.ext
    {Role : Type u} {source target : GlobalResonanceObject Role}
    {first second : GlobalResonanceHom source target}
    (equal : first.structured.toFun = second.structured.toFun) :
    first = second := by
  cases first
  cases second
  simp_all [StructuredIncidenceHom.ext_iff]

def GlobalResonanceHom.id {Role : Type u}
    (object : GlobalResonanceObject Role) :
    GlobalResonanceHom object object where
  structured := StructuredIncidenceHom.id object.incidence
  map_bisimulation := fun related => related

def GlobalResonanceHom.comp {Role : Type u}
    {first second third : GlobalResonanceObject Role}
    (after : GlobalResonanceHom second third)
    (before : GlobalResonanceHom first second) :
    GlobalResonanceHom first third where
  structured := after.structured.comp before.structured
  map_bisimulation := fun related =>
    after.map_bisimulation (before.map_bisimulation related)

instance globalResonanceObjectCategory (Role : Type u) :
    Category (GlobalResonanceObject Role) where
  Hom := GlobalResonanceHom
  id := GlobalResonanceHom.id
  comp before after := after.comp before
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

def globalResonanceSaturateObject {Role : Type u}
    (object : GlobalResonanceObject Role) : GlobalResonanceObject Role where
  Carrier := object.Carrier
  CellType := object.CellType
  carrierDecidableEq := object.carrierDecidableEq
  incidence := bisimulationResonanceSaturation object.incidence

def globalResonanceSaturateMap {Role : Type u}
    {source target : GlobalResonanceObject Role}
    (hom : source ⟶ target) :
    globalResonanceSaturateObject source ⟶
      globalResonanceSaturateObject target where
  structured := {
    toFun := hom.structured.toFun
    map_unit := hom.structured.map_unit
    map_glue := hom.structured.map_glue
    map_boundary := hom.structured.map_boundary
    map_resonance := by
      intro left right output saturated
      rcases saturated with
        ⟨sourceLeft, sourceRight, sourceOutput,
          leftEq, rightEq, outputEq, resonant⟩
      refine ⟨hom.structured.toFun sourceLeft,
        hom.structured.toFun sourceRight,
        hom.structured.toFun sourceOutput, ?_, ?_, ?_,
        hom.structured.map_resonance _ _ _ resonant⟩
      · exact Quotient.sound (hom.map_bisimulation (Quotient.exact leftEq))
      · exact Quotient.sound (hom.map_bisimulation (Quotient.exact rightEq))
      · exact Quotient.sound (hom.map_bisimulation (Quotient.exact outputEq)) }
  map_bisimulation := hom.map_bisimulation

def globalResonanceSaturationFunctor (Role : Type u) :
    GlobalResonanceObject Role ⥤ GlobalResonanceObject Role where
  obj := globalResonanceSaturateObject
  map := globalResonanceSaturateMap
  map_id := by intro; apply GlobalResonanceHom.ext; rfl
  map_comp := by intros; apply GlobalResonanceHom.ext; rfl

def globalResonanceSaturationUnit (Role : Type u) :
    𝟭 (GlobalResonanceObject Role) ⟶
      globalResonanceSaturationFunctor Role where
  app object := {
    structured := {
      toFun := id
      map_unit := rfl
      map_glue := fun _ _ _ selected => selected
      map_boundary := fun _ _ member => member
      map_resonance := fun _ _ _ resonant =>
        resonance_implies_bisimulationResonanceSaturation resonant }
    map_bisimulation := fun related => related }
  naturality := by intros; apply GlobalResonanceHom.ext; rfl

def globalResonanceSaturationIdempotenceIso (Role : Type u) :
    globalResonanceSaturationFunctor Role ⋙
        globalResonanceSaturationFunctor Role ≅
      globalResonanceSaturationFunctor Role where
  hom := {
    app := fun object => {
      structured := {
        toFun := id
        map_unit := rfl
        map_glue := fun _ _ _ selected => selected
        map_boundary := fun _ _ member => member
        map_resonance := by
          intro left right output resonant
          exact (bisimulationResonanceSaturation_idempotent
            object.incidence left right output).mp resonant }
      map_bisimulation := fun related => related }
    naturality := by intros; apply GlobalResonanceHom.ext; rfl }
  inv := {
    app := fun object => {
      structured := {
        toFun := id
        map_unit := rfl
        map_glue := fun _ _ _ selected => selected
        map_boundary := fun _ _ member => member
        map_resonance := fun _ _ _ resonant =>
          resonance_implies_bisimulationResonanceSaturation resonant }
      map_bisimulation := fun related => related }
    naturality := by intros; apply GlobalResonanceHom.ext; rfl }
  hom_inv_id := by ext object; apply GlobalResonanceHom.ext; rfl
  inv_hom_id := by ext object; apply GlobalResonanceHom.ext; rfl

def GlobalCongruentResonanceObject (Role : Type u) :=
  { object : GlobalResonanceObject Role //
    QuotientResonanceCongruent object.incidence }

instance globalCongruentResonanceObjectCategory (Role : Type u) :
    Category (GlobalCongruentResonanceObject Role) where
  Hom source target := GlobalResonanceHom source.val target.val
  id source := GlobalResonanceHom.id source.val
  comp before after := after.comp before
  id_comp := by intros; apply GlobalResonanceHom.ext; rfl
  comp_id := by intros; apply GlobalResonanceHom.ext; rfl
  assoc := by intros; apply GlobalResonanceHom.ext; rfl

def globalCongruentResonanceInclusion (Role : Type u) :
    GlobalCongruentResonanceObject Role ⥤ GlobalResonanceObject Role where
  obj object := object.val
  map hom := hom
  map_id := by intros; rfl
  map_comp := by intros; rfl

def globalResonanceSaturationReflector (Role : Type u) :
    GlobalResonanceObject Role ⥤ GlobalCongruentResonanceObject Role where
  obj object := ⟨globalResonanceSaturateObject object,
    quotientResonanceCongruent_of_exact_descent
      (bisimulationResonanceSaturation_exactDescent object.incidence)⟩
  map := globalResonanceSaturateMap
  map_id := by intro; apply GlobalResonanceHom.ext; rfl
  map_comp := by intros; apply GlobalResonanceHom.ext; rfl

def globalResonanceReflectionHomEquiv (Role : Type u)
    (source : GlobalResonanceObject Role)
    (target : GlobalCongruentResonanceObject Role) :
    ((globalResonanceSaturationReflector Role).obj source ⟶ target) ≃
      (source ⟶ (globalCongruentResonanceInclusion Role).obj target) where
  toFun hom := hom.comp ((globalResonanceSaturationUnit Role).app source)
  invFun hom := {
    structured := {
      toFun := hom.structured.toFun
      map_unit := hom.structured.map_unit
      map_glue := hom.structured.map_glue
      map_boundary := hom.structured.map_boundary
      map_resonance := by
        intro left right output saturated
        rcases saturated with
          ⟨sourceLeft, sourceRight, sourceOutput,
            leftEq, rightEq, outputEq, resonant⟩
        have leftRelated := hom.map_bisimulation (Quotient.exact leftEq)
        have rightRelated := hom.map_bisimulation (Quotient.exact rightEq)
        have outputRelated := hom.map_bisimulation (Quotient.exact outputEq)
        exact (target.property leftRelated rightRelated outputRelated).mp
          (hom.structured.map_resonance _ _ _ resonant) }
    map_bisimulation := hom.map_bisimulation }
  left_inv hom := by apply GlobalResonanceHom.ext; rfl
  right_inv hom := by apply GlobalResonanceHom.ext; rfl

def globalResonanceSaturationAdjunction (Role : Type u) :
    globalResonanceSaturationReflector Role ⊣
      globalCongruentResonanceInclusion Role :=
  Adjunction.mkOfHomEquiv {
    homEquiv := globalResonanceReflectionHomEquiv Role
    homEquiv_naturality_left_symm := by
      intros; apply GlobalResonanceHom.ext; rfl
    homEquiv_naturality_right := by
      intros; apply GlobalResonanceHom.ext; rfl }

theorem globalResonanceSaturation_factorization_unique
    {Role : Type u} (source : GlobalResonanceObject Role)
    (target : GlobalCongruentResonanceObject Role)
    (hom : source ⟶ (globalCongruentResonanceInclusion Role).obj target) :
    ∃! factor : (globalResonanceSaturationReflector Role).obj source ⟶ target,
      factor.comp ((globalResonanceSaturationUnit Role).app source) = hom := by
  let factor := (globalResonanceReflectionHomEquiv Role source target).symm hom
  refine ⟨factor, (globalResonanceReflectionHomEquiv Role source target).apply_symm_apply hom,
    ?_⟩
  intro candidate commutes
  apply (globalResonanceReflectionHomEquiv Role source target).injective
  exact commutes.trans
    ((globalResonanceReflectionHomEquiv Role source target).apply_symm_apply hom).symm

def unitTrivialGlobalResonanceObject :
    GlobalResonanceObject GraphRole where
  Carrier := Unit
  CellType := GraphType
  carrierDecidableEq := inferInstance
  incidence := trivialIncidence

def boolTrivialGlobalResonanceObject :
    GlobalResonanceObject GraphRole where
  Carrier := Bool
  CellType := GraphType
  carrierDecidableEq := inferInstance
  incidence := trivialIncidence

def unitToBoolGlobalResonanceHom :
    unitTrivialGlobalResonanceObject ⟶
      boolTrivialGlobalResonanceObject where
  structured := {
    toFun := fun _ => false
    map_unit := rfl
    map_glue := by
      intro left right output selected
      cases left; cases right; cases output
      simp [boolTrivialGlobalResonanceObject, trivialIncidence]
    map_boundary := by
      intro value endpoint member
      simp [unitTrivialGlobalResonanceObject, trivialIncidence] at member
    map_resonance := by
      intro left right output resonant
      cases left; cases right; cases output
      simp [boolTrivialGlobalResonanceObject, trivialIncidence] }
  map_bisimulation := by
    intro first second related
    exact trivial_approxBisim_total false false

theorem unitToBoolGlobalResonanceHom_not_surjective :
    ¬ Function.Surjective unitToBoolGlobalResonanceHom.structured.toFun := by
  intro surjective
  rcases surjective true with ⟨source, impossible⟩
  cases source
  simp [unitToBoolGlobalResonanceHom] at impossible

theorem globalSaturation_maps_nontrivial_carrier_change :
    (globalResonanceSaturationFunctor GraphRole).map
        unitToBoolGlobalResonanceHom =
      globalResonanceSaturateMap unitToBoolGlobalResonanceHom :=
  rfl

end IncidenceCore
