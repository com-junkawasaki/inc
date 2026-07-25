import IncidenceTheory.SumQuotientImage

/-!
  Naturality of the controlled-sum quotient/image comparison.

  A morphism of controlled sums is the minimal behavioral notion needed here:
  a carrier map preserving both ternary resonance and bisimulation. Such maps
  induce morphisms on bisimulation quotients. Conjugating by the canonical
  quotient/image isomorphisms induces the corresponding classifier-image map,
  and the comparison square commutes.
-/

namespace IncidenceCore

universe u

open CategoryTheory

structure ControlledSumMap
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    (source1 : Incidence I1 R1 T1) (source2 : Incidence I2 R2 T2)
    (target1 : Incidence J1 S1 U1) (target2 : Incidence J2 S2 U2) where
  toFun : I1 ⊕ I2 → J1 ⊕ J2
  preserves_bisim : ∀ {first second},
    approxBisim (incidenceSum source1 source2) first second →
      approxBisim (incidenceSum target1 target2) (toFun first) (toFun second)
  preserves_resonance : ∀ {left right output},
    (incidenceSum source1 source2).resonance left right output →
      (incidenceSum target1 target2).resonance
        (toFun left) (toFun right) (toFun output)

@[ext] theorem ControlledSumMap.ext
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {target1 : Incidence J1 S1 U1} {target2 : Incidence J2 S2 U2}
    {first second : ControlledSumMap source1 source2 target1 target2}
    (equal : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  simp_all

def ControlledSumMap.id
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    ControlledSumMap inc1 inc2 inc1 inc2 where
  toFun := fun value => value
  preserves_bisim := fun related => related
  preserves_resonance := fun resonant => resonant

def ControlledSumMap.comp
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 K1 V1 W1 K2 V2 W2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    [DecidableEq K1] [DecidableEq K2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {middle1 : Incidence J1 S1 U1} {middle2 : Incidence J2 S2 U2}
    {target1 : Incidence K1 V1 W1} {target2 : Incidence K2 V2 W2}
    (after : ControlledSumMap middle1 middle2 target1 target2)
    (before : ControlledSumMap source1 source2 middle1 middle2) :
    ControlledSumMap source1 source2 target1 target2 where
  toFun := after.toFun ∘ before.toFun
  preserves_bisim := fun related =>
    after.preserves_bisim (before.preserves_bisim related)
  preserves_resonance := fun resonant =>
    after.preserves_resonance (before.preserves_resonance resonant)

@[simp] theorem ControlledSumMap.id_toFun
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    (ControlledSumMap.id inc1 inc2).toFun = (fun value => value) := rfl

@[simp] theorem ControlledSumMap.comp_toFun
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 K1 V1 W1 K2 V2 W2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    [DecidableEq K1] [DecidableEq K2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {middle1 : Incidence J1 S1 U1} {middle2 : Incidence J2 S2 U2}
    {target1 : Incidence K1 V1 W1} {target2 : Incidence K2 V2 W2}
    (after : ControlledSumMap middle1 middle2 target1 target2)
    (before : ControlledSumMap source1 source2 middle1 middle2) :
    (after.comp before).toFun = after.toFun ∘ before.toFun := rfl

def ControlledSumMap.toResonanceHom
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {target1 : Incidence J1 S1 U1} {target2 : Incidence J2 S2 U2}
    (map : ControlledSumMap source1 source2 target1 target2) :
    TernaryResonanceHom (incidenceSum source1 source2).resonanceSystem
      (incidenceSum target1 target2).resonanceSystem where
  toFun := map.toFun
  preserves := map.preserves_resonance

def ControlledSumMap.quotientMap
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {target1 : Incidence J1 S1 U1} {target2 : Incidence J2 S2 U2}
    (map : ControlledSumMap source1 source2 target1 target2) :
    TernaryResonanceHom
      (bisimulationQuotientResonanceSystem (incidenceSum source1 source2))
      (bisimulationQuotientResonanceSystem (incidenceSum target1 target2)) :=
  bisimulationQuotientResonanceLift {
    toFun := fun value =>
      Quotient.mk (approxBisimSetoid (incidenceSum target1 target2))
        (map.toFun value)
    preserves := fun resonant =>
      quotientResonance_of_resonance (map.preserves_resonance resonant)
  } (fun {_ _} related => Quotient.sound (map.preserves_bisim related))

@[simp] theorem ControlledSumMap.quotientMap_mk
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {target1 : Incidence J1 S1 U1} {target2 : Incidence J2 S2 U2}
    (map : ControlledSumMap source1 source2 target1 target2)
    (value : I1 ⊕ I2) :
    map.quotientMap.toFun
        (Quotient.mk (approxBisimSetoid (incidenceSum source1 source2)) value) =
      Quotient.mk (approxBisimSetoid (incidenceSum target1 target2))
        (map.toFun value) := by
  rfl

noncomputable def ControlledSumMap.classifierImageMap
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {target1 : Incidence J1 S1 U1} {target2 : Incidence J2 S2 U2}
    (sourceControl : SumQuotientControlSpec source1 source2)
    (targetControl : SumQuotientControlSpec target1 target2)
    (map : ControlledSumMap source1 source2 target1 target2) :
    TernaryResonanceHom
      (sumQuotientClassifierImageResonanceSystem source1 source2)
      (sumQuotientClassifierImageResonanceSystem target1 target2) :=
  (sumBisimulationQuotientIsoClassifierImage
    target1 target2 targetControl).hom.comp
    (map.quotientMap.comp
      (sumBisimulationQuotientIsoClassifierImage
        source1 source2 sourceControl).inv)

/-- The quotient/image comparison is natural with respect to every controlled
sum map. -/
theorem sumBisimulationQuotientIsoClassifierImage_natural
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {target1 : Incidence J1 S1 U1} {target2 : Incidence J2 S2 U2}
    (sourceControl : SumQuotientControlSpec source1 source2)
    (targetControl : SumQuotientControlSpec target1 target2)
    (map : ControlledSumMap source1 source2 target1 target2) :
    (map.classifierImageMap sourceControl targetControl).comp
        (sumBisimulationQuotientIsoClassifierImage
          source1 source2 sourceControl).hom =
      (sumBisimulationQuotientIsoClassifierImage
        target1 target2 targetControl).hom.comp map.quotientMap := by
  apply TernaryResonanceHom.ext
  funext quotient
  change (sumBisimulationQuotientEquivClassifierImage
      target1 target2 targetControl)
      (map.quotientMap.toFun
        ((sumBisimulationQuotientEquivClassifierImage
          source1 source2 sourceControl).symm
          ((sumBisimulationQuotientEquivClassifierImage
            source1 source2 sourceControl) quotient))) =
    (sumBisimulationQuotientEquivClassifierImage
      target1 target2 targetControl) (map.quotientMap.toFun quotient)
  rw [(sumBisimulationQuotientEquivClassifierImage
    source1 source2 sourceControl).symm_apply_apply]

/-- On represented observations, the induced image map is the expected map of
canonical classifiers. -/
theorem ControlledSumMap.classifierImageMap_on_value
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {target1 : Incidence J1 S1 U1} {target2 : Incidence J2 S2 U2}
    (sourceControl : SumQuotientControlSpec source1 source2)
    (targetControl : SumQuotientControlSpec target1 target2)
    (map : ControlledSumMap source1 source2 target1 target2)
    (value : I1 ⊕ I2) :
    (map.classifierImageMap sourceControl targetControl).toFun
        ((sumQuotientClassifierImageHom source1 source2).toFun value) =
      (sumQuotientClassifierImageHom target1 target2).toFun
        (map.toFun value) := by
  have natural := congrArg TernaryResonanceHom.toFun
    (sumBisimulationQuotientIsoClassifierImage_natural
      sourceControl targetControl map)
  exact congrFun natural
    (Quotient.mk (approxBisimSetoid (incidenceSum source1 source2)) value)

@[simp] theorem ControlledSumMap.quotientMap_id
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2) :
    (ControlledSumMap.id inc1 inc2).quotientMap =
      TernaryResonanceHom.id
        (bisimulationQuotientResonanceSystem (incidenceSum inc1 inc2)) := by
  apply TernaryResonanceHom.ext
  funext quotient
  induction quotient using Quotient.ind with
  | _ value => rfl

@[simp] theorem ControlledSumMap.quotientMap_comp
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 K1 V1 W1 K2 V2 W2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    [DecidableEq K1] [DecidableEq K2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {middle1 : Incidence J1 S1 U1} {middle2 : Incidence J2 S2 U2}
    {target1 : Incidence K1 V1 W1} {target2 : Incidence K2 V2 W2}
    (after : ControlledSumMap middle1 middle2 target1 target2)
    (before : ControlledSumMap source1 source2 middle1 middle2) :
    (after.comp before).quotientMap =
      after.quotientMap.comp before.quotientMap := by
  apply TernaryResonanceHom.ext
  funext quotient
  induction quotient using Quotient.ind with
  | _ value => rfl

@[simp] theorem ControlledSumMap.classifierImageMap_id
    {I1 R1 T1 I2 R2 T2 : Type u} [DecidableEq I1] [DecidableEq I2]
    (inc1 : Incidence I1 R1 T1) (inc2 : Incidence I2 R2 T2)
    (control : SumQuotientControlSpec inc1 inc2) :
    (ControlledSumMap.id inc1 inc2).classifierImageMap control control =
      TernaryResonanceHom.id
        (sumQuotientClassifierImageResonanceSystem inc1 inc2) := by
  apply TernaryResonanceHom.ext
  funext observed
  rcases observed.property with ⟨value, realizes⟩
  have represented :
      (sumQuotientClassifierImageHom inc1 inc2).toFun value = observed := by
    apply Subtype.ext
    exact realizes
  rw [← represented]
  exact (ControlledSumMap.id inc1 inc2).classifierImageMap_on_value
    control control value

@[simp] theorem ControlledSumMap.classifierImageMap_comp
    {I1 R1 T1 I2 R2 T2 J1 S1 U1 J2 S2 U2 K1 V1 W1 K2 V2 W2 : Type u}
    [DecidableEq I1] [DecidableEq I2] [DecidableEq J1] [DecidableEq J2]
    [DecidableEq K1] [DecidableEq K2]
    {source1 : Incidence I1 R1 T1} {source2 : Incidence I2 R2 T2}
    {middle1 : Incidence J1 S1 U1} {middle2 : Incidence J2 S2 U2}
    {target1 : Incidence K1 V1 W1} {target2 : Incidence K2 V2 W2}
    (sourceControl : SumQuotientControlSpec source1 source2)
    (middleControl : SumQuotientControlSpec middle1 middle2)
    (targetControl : SumQuotientControlSpec target1 target2)
    (after : ControlledSumMap middle1 middle2 target1 target2)
    (before : ControlledSumMap source1 source2 middle1 middle2) :
    (after.comp before).classifierImageMap sourceControl targetControl =
      (after.classifierImageMap middleControl targetControl).comp
        (before.classifierImageMap sourceControl middleControl) := by
  apply TernaryResonanceHom.ext
  funext observed
  rcases observed.property with ⟨value, realizes⟩
  have represented :
      (sumQuotientClassifierImageHom source1 source2).toFun value =
        observed := by
    apply Subtype.ext
    exact realizes
  rw [← represented]
  rw [(after.comp before).classifierImageMap_on_value
    sourceControl targetControl]
  change (sumQuotientClassifierImageHom target1 target2).toFun
      (after.toFun (before.toFun value)) =
    (after.classifierImageMap middleControl targetControl).toFun
      ((before.classifierImageMap sourceControl middleControl).toFun
        ((sumQuotientClassifierImageHom source1 source2).toFun value))
  rw [before.classifierImageMap_on_value sourceControl middleControl]
  rw [after.classifierImageMap_on_value middleControl targetControl]

/-- A controlled sum bundled with the exact observational certificate used by
the quotient/image comparison. -/
structure ControlledSumObject where
  Left : Type u
  LeftRole : Type u
  LeftType : Type u
  Right : Type u
  RightRole : Type u
  RightType : Type u
  leftDecidableEq : DecidableEq Left
  rightDecidableEq : DecidableEq Right
  leftIncidence : Incidence Left LeftRole LeftType
  rightIncidence : Incidence Right RightRole RightType
  control : SumQuotientControlSpec leftIncidence rightIncidence

abbrev ControlledSumObject.Hom
    (source target : ControlledSumObject.{u}) :=
  @ControlledSumMap source.Left source.LeftRole source.LeftType
    source.Right source.RightRole source.RightType
    target.Left target.LeftRole target.LeftType
    target.Right target.RightRole target.RightType
    source.leftDecidableEq source.rightDecidableEq
    target.leftDecidableEq target.rightDecidableEq
    source.leftIncidence source.rightIncidence
    target.leftIncidence target.rightIncidence

def ControlledSumObject.idHom (object : ControlledSumObject.{u}) :
    object.Hom object :=
  @ControlledSumMap.id object.Left object.LeftRole object.LeftType
    object.Right object.RightRole object.RightType
    object.leftDecidableEq object.rightDecidableEq
    object.leftIncidence object.rightIncidence

def ControlledSumObject.compHom
    {first second third : ControlledSumObject.{u}}
    (after : second.Hom third) (before : first.Hom second) :
    first.Hom third :=
  @ControlledSumMap.comp
    first.Left first.LeftRole first.LeftType
    first.Right first.RightRole first.RightType
    second.Left second.LeftRole second.LeftType
    second.Right second.RightRole second.RightType
    third.Left third.LeftRole third.LeftType
    third.Right third.RightRole third.RightType
    first.leftDecidableEq first.rightDecidableEq
    second.leftDecidableEq second.rightDecidableEq
    third.leftDecidableEq third.rightDecidableEq
    first.leftIncidence first.rightIncidence
    second.leftIncidence second.rightIncidence
    third.leftIncidence third.rightIncidence after before

instance controlledSumObjectCategory : Category ControlledSumObject.{u} where
  Hom := ControlledSumObject.Hom
  id := ControlledSumObject.idHom
  comp before after := ControlledSumObject.compHom after before
  id_comp := by
    intro source target hom
    letI := source.leftDecidableEq
    letI := source.rightDecidableEq
    letI := target.leftDecidableEq
    letI := target.rightDecidableEq
    apply ControlledSumMap.ext
    rfl
  comp_id := by
    intro source target hom
    letI := source.leftDecidableEq
    letI := source.rightDecidableEq
    letI := target.leftDecidableEq
    letI := target.rightDecidableEq
    apply ControlledSumMap.ext
    rfl
  assoc := by
    intro first second third fourth firstMap secondMap thirdMap
    letI := first.leftDecidableEq
    letI := first.rightDecidableEq
    letI := second.leftDecidableEq
    letI := second.rightDecidableEq
    letI := third.leftDecidableEq
    letI := third.rightDecidableEq
    letI := fourth.leftDecidableEq
    letI := fourth.rightDecidableEq
    apply ControlledSumMap.ext
    rfl

def ControlledSumObject.quotientSystem (object : ControlledSumObject.{u}) :
    TernaryResonanceSystem.{u} := by
  letI := object.leftDecidableEq
  letI := object.rightDecidableEq
  exact bisimulationQuotientResonanceSystem
    (incidenceSum object.leftIncidence object.rightIncidence)

def ControlledSumObject.imageSystem (object : ControlledSumObject.{u}) :
    TernaryResonanceSystem.{u} := by
  letI := object.leftDecidableEq
  letI := object.rightDecidableEq
  exact sumQuotientClassifierImageResonanceSystem
    object.leftIncidence object.rightIncidence

def ControlledSumObject.quotientHom
    {source target : ControlledSumObject.{u}} (map : source.Hom target) :
    TernaryResonanceHom source.quotientSystem target.quotientSystem := by
  letI := source.leftDecidableEq
  letI := source.rightDecidableEq
  letI := target.leftDecidableEq
  letI := target.rightDecidableEq
  exact map.quotientMap

noncomputable def ControlledSumObject.imageHom
    {source target : ControlledSumObject.{u}} (map : source.Hom target) :
    TernaryResonanceHom source.imageSystem target.imageSystem := by
  letI := source.leftDecidableEq
  letI := source.rightDecidableEq
  letI := target.leftDecidableEq
  letI := target.rightDecidableEq
  exact map.classifierImageMap source.control target.control

noncomputable def ControlledSumObject.comparisonIso
    (object : ControlledSumObject.{u}) :
    object.quotientSystem ≅ object.imageSystem := by
  letI := object.leftDecidableEq
  letI := object.rightDecidableEq
  exact sumBisimulationQuotientIsoClassifierImage
    object.leftIncidence object.rightIncidence object.control

def controlledSumQuotientFunctor :
    ControlledSumObject.{u} ⥤ TernaryResonanceSystem.{u} where
  obj := ControlledSumObject.quotientSystem
  map := ControlledSumObject.quotientHom
  map_id object := by
    apply TernaryResonanceHom.ext
    funext quotient
    induction quotient using Quotient.ind with
    | _ value => rfl
  map_comp before after := by
    apply TernaryResonanceHom.ext
    funext quotient
    induction quotient using Quotient.ind with
    | _ value => rfl

noncomputable def controlledSumClassifierImageFunctor :
    ControlledSumObject.{u} ⥤ TernaryResonanceSystem.{u} where
  obj := ControlledSumObject.imageSystem
  map := ControlledSumObject.imageHom
  map_id object := by
    letI := object.leftDecidableEq
    letI := object.rightDecidableEq
    exact ControlledSumMap.classifierImageMap_id
      object.leftIncidence object.rightIncidence object.control
  map_comp {X Y Z} before after := by
    letI := X.leftDecidableEq
    letI := X.rightDecidableEq
    letI := Y.leftDecidableEq
    letI := Y.rightDecidableEq
    letI := Z.leftDecidableEq
    letI := Z.rightDecidableEq
    exact ControlledSumMap.classifierImageMap_comp
      X.control Y.control Z.control after before

/-- The objectwise quotient/image isomorphisms form a natural isomorphism. -/
noncomputable def controlledSumQuotientClassifierImageNatIso :
    controlledSumQuotientFunctor.{u} ≅
      controlledSumClassifierImageFunctor.{u} :=
  NatIso.ofComponents (fun object =>
    object.comparisonIso) (by
    intro source target map
    letI := source.leftDecidableEq
    letI := source.rightDecidableEq
    letI := target.leftDecidableEq
    letI := target.rightDecidableEq
    exact (sumBisimulationQuotientIsoClassifierImage_natural
      source.control target.control map).symm)

def natCycleControlledSumObject : ControlledSumObject where
  Left := Nat
  LeftRole := PeanoRole
  LeftType := GraphType
  Right := CycleId
  RightRole := CycleRoleFixed
  RightType := GraphType
  leftDecidableEq := inferInstance
  rightDecidableEq := inferInstance
  leftIncidence := natIncidence
  rightIncidence := cycleIncidenceFixed
  control := natCycleSumQuotientControl

theorem controlledSumQuotientClassifierImageNatIso_natCycle_component :
    controlledSumQuotientClassifierImageNatIso.hom.app
        natCycleControlledSumObject =
      natCycleSumBisimulationQuotientIsoClassifierImage.hom := rfl

def natCycleControlledSumId :
    ControlledSumMap natIncidence cycleIncidenceFixed
      natIncidence cycleIncidenceFixed :=
  ControlledSumMap.id natIncidence cycleIncidenceFixed

theorem natCycleSumQuotientClassifierImage_natural_identity :
    (natCycleControlledSumId.classifierImageMap
      natCycleSumQuotientControl natCycleSumQuotientControl).comp
        (sumBisimulationQuotientIsoClassifierImage
          natIncidence cycleIncidenceFixed natCycleSumQuotientControl).hom =
      (sumBisimulationQuotientIsoClassifierImage
        natIncidence cycleIncidenceFixed natCycleSumQuotientControl).hom.comp
        natCycleControlledSumId.quotientMap :=
  sumBisimulationQuotientIsoClassifierImage_natural
    natCycleSumQuotientControl natCycleSumQuotientControl
    natCycleControlledSumId

end IncidenceCore
