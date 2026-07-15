import IncidenceTheory.Quotient
import IncidenceTheory.Sum
import IncidenceTheory.ReferenceFoundationConservativity
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Perm
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
  Paper-facing universal property of the bisimulation quotient.  This module
  forgets boundary presentation data only at the final categorical boundary:
  objects retain the ternary resonance relation and morphisms preserve it.
-/

namespace IncidenceCore

universe u

open CategoryTheory

structure TernaryResonanceSystem where
  Carrier : Type u
  resonance : Carrier → Carrier → Carrier → Prop

structure TernaryResonanceHom
    (source target : TernaryResonanceSystem.{u}) where
  toFun : source.Carrier → target.Carrier
  preserves : ∀ {left right output}, source.resonance left right output →
    target.resonance (toFun left) (toFun right) (toFun output)

@[ext] theorem TernaryResonanceHom.ext
    {source target : TernaryResonanceSystem.{u}}
    {first second : TernaryResonanceHom source target}
    (equal : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  simp_all

def TernaryResonanceHom.id (system : TernaryResonanceSystem.{u}) :
    TernaryResonanceHom system system where
  toFun := fun value => value
  preserves := fun resonant => resonant

def TernaryResonanceHom.comp
    {first second third : TernaryResonanceSystem.{u}}
    (after : TernaryResonanceHom second third)
    (before : TernaryResonanceHom first second) :
    TernaryResonanceHom first third where
  toFun := after.toFun ∘ before.toFun
  preserves := fun resonant => after.preserves (before.preserves resonant)

@[simp] theorem TernaryResonanceHom.id_comp
    {source target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom source target) :
    (TernaryResonanceHom.id target).comp hom = hom := by
  apply TernaryResonanceHom.ext
  funext value
  rfl

@[simp] theorem TernaryResonanceHom.comp_id
    {source target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom source target) :
    hom.comp (TernaryResonanceHom.id source) = hom := by
  apply TernaryResonanceHom.ext
  funext value
  rfl

theorem TernaryResonanceHom.comp_assoc
    {first second third fourth : TernaryResonanceSystem.{u}}
    (thirdHom : TernaryResonanceHom third fourth)
    (secondHom : TernaryResonanceHom second third)
    (firstHom : TernaryResonanceHom first second) :
    (thirdHom.comp secondHom).comp firstHom =
      thirdHom.comp (secondHom.comp firstHom) := by
  apply TernaryResonanceHom.ext
  rfl

instance ternaryResonanceSystemCategory :
    CategoryTheory.Category TernaryResonanceSystem.{u} where
  Hom := TernaryResonanceHom
  id := TernaryResonanceHom.id
  comp before after := after.comp before
  id_comp := TernaryResonanceHom.id_comp
  comp_id := TernaryResonanceHom.comp_id
  assoc := by
    intro first second third fourth firstHom secondHom thirdHom
    exact TernaryResonanceHom.comp_assoc thirdHom secondHom firstHom

/- The abstract reflection underlying every exact resonance quotient.  The
   equivalence relation is bundled with the ternary congruence law, so its
   quotient is automatically a separated ternary resonance system. -/
structure CongruencedTernaryResonanceSystem where
  Carrier : Type u
  equivalent : Setoid Carrier
  resonance : Carrier → Carrier → Carrier → Prop
  congruent : ∀ {left₁ left₂ right₁ right₂ output₁ output₂},
    equivalent.r left₁ left₂ → equivalent.r right₁ right₂ →
    equivalent.r output₁ output₂ →
      (resonance left₁ right₁ output₁ ↔ resonance left₂ right₂ output₂)

def CongruencedTernaryResonanceSystem.toSystem
    (system : CongruencedTernaryResonanceSystem.{u}) :
    TernaryResonanceSystem.{u} where
  Carrier := system.Carrier
  resonance := system.resonance

abbrev CongruencedTernaryResonanceSystem.QuotientCarrier
    (system : CongruencedTernaryResonanceSystem.{u}) :=
  Quotient system.equivalent

def CongruencedTernaryResonanceSystem.quotientResonance
    (system : CongruencedTernaryResonanceSystem.{u})
    (left right output : system.QuotientCarrier) : Prop :=
  ∃ leftRep rightRep outputRep,
    Quotient.mk system.equivalent leftRep = left ∧
    Quotient.mk system.equivalent rightRep = right ∧
    Quotient.mk system.equivalent outputRep = output ∧
    system.resonance leftRep rightRep outputRep

def CongruencedTernaryResonanceSystem.quotientSystem
    (system : CongruencedTernaryResonanceSystem.{u}) :
    TernaryResonanceSystem.{u} where
  Carrier := system.QuotientCarrier
  resonance := system.quotientResonance

theorem CongruencedTernaryResonanceSystem.quotientResonance_mk_iff
    (system : CongruencedTernaryResonanceSystem.{u})
    (left right output : system.Carrier) :
    system.quotientResonance
        (Quotient.mk system.equivalent left)
        (Quotient.mk system.equivalent right)
        (Quotient.mk system.equivalent output) ↔
      system.resonance left right output := by
  constructor
  · rintro ⟨leftRep, rightRep, outputRep,
      leftEqual, rightEqual, outputEqual, resonant⟩
    exact (system.congruent (Quotient.exact leftEqual)
      (Quotient.exact rightEqual) (Quotient.exact outputEqual)).mp resonant
  · intro resonant
    exact ⟨left, right, output, rfl, rfl, rfl, resonant⟩

def CongruencedTernaryResonanceSystem.projection
    (system : CongruencedTernaryResonanceSystem.{u}) :
    TernaryResonanceHom system.toSystem system.quotientSystem where
  toFun := Quotient.mk system.equivalent
  preserves := by
    intro left right output resonant
    exact ⟨left, right, output, rfl, rfl, rfl, resonant⟩

def CongruenceInvariantTernaryResonanceHom
    (system : CongruencedTernaryResonanceSystem.{u})
    (target : TernaryResonanceSystem.{u})
    (hom : TernaryResonanceHom system.toSystem target) : Prop :=
  ∀ {first second}, system.equivalent.r first second →
    hom.toFun first = hom.toFun second

def congruenceQuotientResonanceLift
    {system : CongruencedTernaryResonanceSystem.{u}}
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom system.toSystem target)
    (invariant : CongruenceInvariantTernaryResonanceHom system target hom) :
    TernaryResonanceHom system.quotientSystem target where
  toFun := Quotient.lift hom.toFun (fun _ _ related => invariant related)
  preserves := by
    intro left right output resonant
    rcases resonant with
      ⟨leftRep, rightRep, outputRep, rfl, rfl, rfl, sourceResonant⟩
    exact hom.preserves sourceResonant

theorem congruenceQuotientResonanceLift_comp_projection
    {system : CongruencedTernaryResonanceSystem.{u}}
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom system.toSystem target)
    (invariant : CongruenceInvariantTernaryResonanceHom system target hom) :
    (congruenceQuotientResonanceLift hom invariant).comp system.projection =
      hom := by
  apply TernaryResonanceHom.ext
  funext value
  rfl

theorem congruenceQuotientResonanceLift_unique
    {system : CongruencedTernaryResonanceSystem.{u}}
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom system.toSystem target)
    (invariant : CongruenceInvariantTernaryResonanceHom system target hom)
    (candidate : TernaryResonanceHom system.quotientSystem target)
    (commutes : candidate.comp system.projection = hom) :
    candidate = congruenceQuotientResonanceLift hom invariant := by
  apply TernaryResonanceHom.ext
  funext quotientValue
  induction quotientValue using Quotient.ind with
  | _ value =>
    exact congrFun (congrArg TernaryResonanceHom.toFun commutes) value

structure TernaryCongruenceReflection
    (system : CongruencedTernaryResonanceSystem.{u}) where
  quotient : TernaryResonanceSystem.{u}
  unit : TernaryResonanceHom system.toSystem quotient
  factor : ∀ {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom system.toSystem target),
    CongruenceInvariantTernaryResonanceHom system target hom →
      TernaryResonanceHom quotient target
  factor_comp : ∀ {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom system.toSystem target)
    (invariant : CongruenceInvariantTernaryResonanceHom system target hom),
    (factor hom invariant).comp unit = hom
  factor_unique : ∀ {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom system.toSystem target)
    (invariant : CongruenceInvariantTernaryResonanceHom system target hom)
    (candidate : TernaryResonanceHom quotient target),
    candidate.comp unit = hom → candidate = factor hom invariant

def ternaryCongruenceQuotientReflection
    (system : CongruencedTernaryResonanceSystem.{u}) :
    TernaryCongruenceReflection system where
  quotient := system.quotientSystem
  unit := system.projection
  factor := fun hom invariant => congruenceQuotientResonanceLift hom invariant
  factor_comp := congruenceQuotientResonanceLift_comp_projection
  factor_unique := by
    intro target hom invariant candidate commutes
    exact congruenceQuotientResonanceLift_unique hom invariant candidate commutes

structure CongruencedTernaryResonanceHom
    (source target : CongruencedTernaryResonanceSystem.{u}) where
  toFun : source.Carrier → target.Carrier
  preserves_resonance : ∀ {left right output}, source.resonance left right output →
    target.resonance (toFun left) (toFun right) (toFun output)
  preserves_equivalent : ∀ {first second}, source.equivalent.r first second →
    target.equivalent.r (toFun first) (toFun second)

@[ext] theorem CongruencedTernaryResonanceHom.ext
    {source target : CongruencedTernaryResonanceSystem.{u}}
    {first second : CongruencedTernaryResonanceHom source target}
    (equal : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  simp_all

def CongruencedTernaryResonanceHom.id
    (system : CongruencedTernaryResonanceSystem.{u}) :
    CongruencedTernaryResonanceHom system system where
  toFun := fun value => value
  preserves_resonance := fun resonant => resonant
  preserves_equivalent := fun related => related

def CongruencedTernaryResonanceHom.comp
    {first second third : CongruencedTernaryResonanceSystem.{u}}
    (after : CongruencedTernaryResonanceHom second third)
    (before : CongruencedTernaryResonanceHom first second) :
    CongruencedTernaryResonanceHom first third where
  toFun := after.toFun ∘ before.toFun
  preserves_resonance := fun resonant =>
    after.preserves_resonance (before.preserves_resonance resonant)
  preserves_equivalent := fun related =>
    after.preserves_equivalent (before.preserves_equivalent related)

instance congruencedTernaryResonanceSystemCategory :
    CategoryTheory.Category CongruencedTernaryResonanceSystem.{u} where
  Hom := CongruencedTernaryResonanceHom
  id := CongruencedTernaryResonanceHom.id
  comp before after := after.comp before
  id_comp := by
    intro X Y hom
    apply CongruencedTernaryResonanceHom.ext
    rfl
  comp_id := by
    intro X Y hom
    apply CongruencedTernaryResonanceHom.ext
    rfl
  assoc := by
    intro W X Y Z first second third
    apply CongruencedTernaryResonanceHom.ext
    rfl

def equalityCongruencedSystem (system : TernaryResonanceSystem.{u}) :
    CongruencedTernaryResonanceSystem.{u} where
  Carrier := system.Carrier
  equivalent := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  resonance := system.resonance
  congruent := by
    intro left₁ left₂ right₁ right₂ output₁ output₂
      leftEqual rightEqual outputEqual
    subst left₂
    subst right₂
    subst output₂
    rfl

def equalityCongruenceEmbedding :
    TernaryResonanceSystem.{u} ⥤ CongruencedTernaryResonanceSystem.{u} where
  obj := equalityCongruencedSystem
  map hom := {
    toFun := hom.toFun
    preserves_resonance := hom.preserves
    preserves_equivalent := fun equal => congrArg hom.toFun equal }
  map_id := by
    intro system
    apply CongruencedTernaryResonanceHom.ext
    rfl
  map_comp := by
    intro first second third before after
    apply CongruencedTernaryResonanceHom.ext
    rfl

def congruenceQuotientMap
    {source target : CongruencedTernaryResonanceSystem.{u}}
    (hom : CongruencedTernaryResonanceHom source target) :
    TernaryResonanceHom source.quotientSystem target.quotientSystem where
  toFun := Quotient.lift
    (fun value => Quotient.mk target.equivalent (hom.toFun value))
    (fun _ _ related => Quotient.sound (hom.preserves_equivalent related))
  preserves := by
    rintro left right output
      ⟨leftRep, rightRep, outputRep, rfl, rfl, rfl, resonant⟩
    exact ⟨hom.toFun leftRep, hom.toFun rightRep, hom.toFun outputRep,
      rfl, rfl, rfl, hom.preserves_resonance resonant⟩

def congruenceQuotientFunctor :
    CongruencedTernaryResonanceSystem.{u} ⥤ TernaryResonanceSystem.{u} where
  obj := CongruencedTernaryResonanceSystem.quotientSystem
  map := congruenceQuotientMap
  map_id := by
    intro system
    apply TernaryResonanceHom.ext
    funext value
    induction value using Quotient.ind with
    | _ representative => rfl
  map_comp := by
    intro first second third before after
    apply TernaryResonanceHom.ext
    funext value
    induction value using Quotient.ind with
    | _ representative => rfl

def congruenceReflectionHomEquiv
    (source : CongruencedTernaryResonanceSystem.{u})
    (target : TernaryResonanceSystem.{u}) :
    (congruenceQuotientFunctor.obj source ⟶ target) ≃
      (source ⟶ equalityCongruenceEmbedding.obj target) where
  toFun hom := {
    toFun := hom.toFun ∘ Quotient.mk source.equivalent
    preserves_resonance := fun resonant => hom.preserves
      ⟨_, _, _, rfl, rfl, rfl, resonant⟩
    preserves_equivalent := fun related => congrArg hom.toFun
      (Quotient.sound related) }
  invFun hom := congruenceQuotientResonanceLift {
    toFun := hom.toFun
    preserves := hom.preserves_resonance } (fun related =>
      hom.preserves_equivalent related)
  left_inv hom := by
    apply TernaryResonanceHom.ext
    funext value
    induction value using Quotient.ind with
    | _ representative => rfl
  right_inv hom := by
    apply CongruencedTernaryResonanceHom.ext
    rfl

def congruenceQuotientAdjunction :
    congruenceQuotientFunctor ⊣ equalityCongruenceEmbedding :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := congruenceReflectionHomEquiv
    homEquiv_naturality_left_symm := by
      intro source' source target before hom
      apply TernaryResonanceHom.ext
      funext value
      induction value using Quotient.ind with
      | _ representative => rfl
    homEquiv_naturality_right := by
      intro source target target' before after
      apply CongruencedTernaryResonanceHom.ext
      rfl }

def Incidence.resonanceSystem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    TernaryResonanceSystem where
  Carrier := I
  resonance := inc.resonance

def Incidence.congruencedResonanceSystem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (congruent : QuotientResonanceCongruent inc) :
    CongruencedTernaryResonanceSystem where
  Carrier := I
  equivalent := approxBisimSetoid inc
  resonance := inc.resonance
  congruent := congruent

def bisimulationQuotientResonanceSystem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    TernaryResonanceSystem where
  Carrier := IncidenceQuotient inc
  resonance := quotientResonance inc

theorem incidenceCongruenceQuotientSystem_eq
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (congruent : QuotientResonanceCongruent inc) :
    (inc.congruencedResonanceSystem congruent).quotientSystem =
      bisimulationQuotientResonanceSystem inc := by
  rfl

def incidenceBisimulationQuotientReflection
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (congruent : QuotientResonanceCongruent inc) :
    TernaryCongruenceReflection (inc.congruencedResonanceSystem congruent) :=
  ternaryCongruenceQuotientReflection (inc.congruencedResonanceSystem congruent)

def bisimulationQuotientProjection
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    TernaryResonanceHom inc.resonanceSystem
      (bisimulationQuotientResonanceSystem inc) where
  toFun := Quotient.mk (approxBisimSetoid inc)
  preserves := quotientResonance_of_resonance

def ResonanceRelationDescendsExactly
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop :=
  ∃ descended : IncidenceQuotient inc → IncidenceQuotient inc →
      IncidenceQuotient inc → Prop,
    ∀ i j k,
      descended (Quotient.mk (approxBisimSetoid inc) i)
          (Quotient.mk (approxBisimSetoid inc) j)
          (Quotient.mk (approxBisimSetoid inc) k) ↔
        inc.resonance i j k

theorem quotientResonanceCongruent_of_exact_descent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (descent : ResonanceRelationDescendsExactly inc) :
    QuotientResonanceCongruent inc := by
  rcases descent with ⟨descended, exactOnRepresentatives⟩
  intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk
  have hiEq : Quotient.mk (approxBisimSetoid inc) i₁ =
      Quotient.mk (approxBisimSetoid inc) i₂ := Quotient.sound hi
  have hjEq : Quotient.mk (approxBisimSetoid inc) j₁ =
      Quotient.mk (approxBisimSetoid inc) j₂ := Quotient.sound hj
  have hkEq : Quotient.mk (approxBisimSetoid inc) k₁ =
      Quotient.mk (approxBisimSetoid inc) k₂ := Quotient.sound hk
  rw [← exactOnRepresentatives i₁ j₁ k₁,
    ← exactOnRepresentatives i₂ j₂ k₂, hiEq, hjEq, hkEq]

theorem exact_descent_of_quotientResonanceCongruent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (congruent : QuotientResonanceCongruent inc) :
    ResonanceRelationDescendsExactly inc :=
  ⟨quotientResonance inc, fun _ _ _ => quotientResonance_mk_iff congruent⟩

theorem resonanceRelationDescendsExactly_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      QuotientResonanceCongruent inc :=
  ⟨quotientResonanceCongruent_of_exact_descent,
    exact_descent_of_quotientResonanceCongruent⟩

theorem exact_descended_resonance_unique
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (congruent : QuotientResonanceCongruent inc)
    (descended : IncidenceQuotient inc → IncidenceQuotient inc →
      IncidenceQuotient inc → Prop)
    (exactOnRepresentatives : ∀ i j k,
      descended (Quotient.mk (approxBisimSetoid inc) i)
          (Quotient.mk (approxBisimSetoid inc) j)
          (Quotient.mk (approxBisimSetoid inc) k) ↔
        inc.resonance i j k) :
    descended = quotientResonance inc := by
  funext left right output
  refine Quotient.inductionOn₃ left right output ?_
  intro i j k
  apply propext
  exact (exactOnRepresentatives i j k).trans
    (quotientResonance_mk_iff congruent).symm

theorem exact_descended_resonance_unique_without_assumption
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (descended : IncidenceQuotient inc → IncidenceQuotient inc →
      IncidenceQuotient inc → Prop)
    (exactOnRepresentatives : ∀ i j k,
      descended (Quotient.mk (approxBisimSetoid inc) i)
          (Quotient.mk (approxBisimSetoid inc) j)
          (Quotient.mk (approxBisimSetoid inc) k) ↔
        inc.resonance i j k) :
    descended = quotientResonance inc := by
  have congruent : QuotientResonanceCongruent inc :=
    quotientResonanceCongruent_of_exact_descent
      ⟨descended, exactOnRepresentatives⟩
  exact exact_descended_resonance_unique congruent descended
    exactOnRepresentatives

def BisimulationInvariantResonanceHom
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (target : TernaryResonanceSystem.{u})
    (hom : TernaryResonanceHom inc.resonanceSystem target) : Prop :=
  ∀ ⦃left right⦄, approxBisim inc left right →
    hom.toFun left = hom.toFun right

def bisimulationQuotientResonanceLift
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom inc.resonanceSystem target)
    (invariant : BisimulationInvariantResonanceHom inc target hom) :
    TernaryResonanceHom (bisimulationQuotientResonanceSystem inc) target where
  toFun := Quotient.lift hom.toFun
    (fun _ _ bisimilar => invariant bisimilar)
  preserves := by
    rintro left right output ⟨i, j, k, rfl, rfl, rfl, resonant⟩
    exact hom.preserves resonant

@[simp] theorem bisimulationQuotientResonanceLift_mk
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom inc.resonanceSystem target)
    (invariant : BisimulationInvariantResonanceHom inc target hom)
    (value : I) :
    (bisimulationQuotientResonanceLift hom invariant).toFun
        (Quotient.mk (approxBisimSetoid inc) value) = hom.toFun value := rfl

theorem bisimulationQuotientResonanceLift_unique
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom inc.resonanceSystem target)
    (invariant : BisimulationInvariantResonanceHom inc target hom)
    (candidate : TernaryResonanceHom
      (bisimulationQuotientResonanceSystem inc) target)
    (factors : ∀ value,
      candidate.toFun (Quotient.mk (approxBisimSetoid inc) value) =
        hom.toFun value) :
    candidate = bisimulationQuotientResonanceLift hom invariant := by
  apply TernaryResonanceHom.ext
  funext quotient
  induction quotient using Quotient.ind with
  | _ representative => exact factors representative

theorem bisimulationQuotientResonance_universal
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom inc.resonanceSystem target)
    (invariant : BisimulationInvariantResonanceHom inc target hom) :
    ∃ lift : TernaryResonanceHom
        (bisimulationQuotientResonanceSystem inc) target,
      (∀ value,
        lift.toFun (Quotient.mk (approxBisimSetoid inc) value) =
          hom.toFun value) ∧
      ∀ candidate : TernaryResonanceHom
          (bisimulationQuotientResonanceSystem inc) target,
        (∀ value,
          candidate.toFun (Quotient.mk (approxBisimSetoid inc) value) =
            hom.toFun value) → candidate = lift := by
  refine ⟨bisimulationQuotientResonanceLift hom invariant,
    fun _ => rfl, ?_⟩
  intro candidate factors
  exact bisimulationQuotientResonanceLift_unique hom invariant candidate factors

/- The bisimulation relation as an internal kernel-pair object. Its resonance
   relation is defined componentwise, so both projections are resonance
   homomorphisms. -/
def bisimulationKernelPairResonanceSystem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    TernaryResonanceSystem where
  Carrier := { pair : I × I // approxBisim inc pair.1 pair.2 }
  resonance := fun left right output =>
    inc.resonance left.val.1 right.val.1 output.val.1 ∧
      inc.resonance left.val.2 right.val.2 output.val.2

def bisimulationKernelPairFirst
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    TernaryResonanceHom (bisimulationKernelPairResonanceSystem inc)
      inc.resonanceSystem where
  toFun := fun pair => pair.val.1
  preserves := fun resonant => resonant.1

def bisimulationKernelPairSecond
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    TernaryResonanceHom (bisimulationKernelPairResonanceSystem inc)
      inc.resonanceSystem where
  toFun := fun pair => pair.val.2
  preserves := fun resonant => resonant.2

def EqualizesBisimulationKernelPair
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom inc.resonanceSystem target) : Prop :=
  hom.comp (bisimulationKernelPairFirst inc) =
    hom.comp (bisimulationKernelPairSecond inc)

theorem equalizesBisimulationKernelPair_iff_invariant
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    {target : TernaryResonanceSystem.{u}}
    (hom : TernaryResonanceHom inc.resonanceSystem target) :
    EqualizesBisimulationKernelPair inc hom ↔
      BisimulationInvariantResonanceHom inc target hom := by
  constructor
  · intro equalizes left right related
    have functionEqual :
        (hom.comp (bisimulationKernelPairFirst inc)).toFun =
          (hom.comp (bisimulationKernelPairSecond inc)).toFun :=
      congrArg TernaryResonanceHom.toFun equalizes
    exact congrFun functionEqual ⟨(left, right), related⟩
  · intro invariant
    apply TernaryResonanceHom.ext
    funext pair
    exact invariant pair.property

theorem bisimulationQuotientProjection_equalizes_kernelPair
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    EqualizesBisimulationKernelPair inc
      (bisimulationQuotientProjection inc) := by
  apply (equalizesBisimulationKernelPair_iff_invariant inc _).mpr
  intro left right related
  exact Quotient.sound related

structure BisimulationQuotientCoequalizer
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  equalizes : EqualizesBisimulationKernelPair inc
    (bisimulationQuotientProjection inc)
  universal : ∀ {target : TernaryResonanceSystem.{u}}
      (hom : TernaryResonanceHom inc.resonanceSystem target),
    EqualizesBisimulationKernelPair inc hom →
      ∃ lift : TernaryResonanceHom
          (bisimulationQuotientResonanceSystem inc) target,
        lift.comp (bisimulationQuotientProjection inc) = hom ∧
        ∀ candidate : TernaryResonanceHom
            (bisimulationQuotientResonanceSystem inc) target,
          candidate.comp (bisimulationQuotientProjection inc) = hom →
            candidate = lift

theorem bisimulationQuotient_is_resonanceCoequalizer
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BisimulationQuotientCoequalizer inc where
  equalizes := bisimulationQuotientProjection_equalizes_kernelPair inc
  universal := by
    intro target hom equalizes
    have invariant :=
      (equalizesBisimulationKernelPair_iff_invariant inc hom).mp equalizes
    rcases bisimulationQuotientResonance_universal hom invariant with
      ⟨lift, factors, unique⟩
    refine ⟨lift, ?_, ?_⟩
    · apply TernaryResonanceHom.ext
      funext value
      exact factors value
    · intro candidate candidateEqualizes
      apply unique candidate
      intro value
      have functionEqual :
          (candidate.comp (bisimulationQuotientProjection inc)).toFun =
            hom.toFun := congrArg TernaryResonanceHom.toFun candidateEqualizes
      exact congrFun functionEqual value

open CategoryTheory CategoryTheory.Limits

def bisimulationQuotientResonanceCofork
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    @Cofork TernaryResonanceSystem.{u} ternaryResonanceSystemCategory
      (bisimulationKernelPairResonanceSystem inc) inc.resonanceSystem
      (bisimulationKernelPairFirst inc) (bisimulationKernelPairSecond inc) :=
  Cofork.ofπ (bisimulationQuotientProjection inc)
    (bisimulationQuotientProjection_equalizes_kernelPair inc)

noncomputable def bisimulationQuotientResonanceCofork_isColimit
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    IsColimit (bisimulationQuotientResonanceCofork inc) := by
  refine Cofork.IsColimit.mk'
    (bisimulationQuotientResonanceCofork inc) ?_
  intro cofork
  have invariant : BisimulationInvariantResonanceHom inc cofork.pt cofork.π :=
    (equalizesBisimulationKernelPair_iff_invariant inc cofork.π).mp
      cofork.condition
  let lift := bisimulationQuotientResonanceLift cofork.π invariant
  refine ⟨lift, ?_, ?_⟩
  · apply TernaryResonanceHom.ext
    funext value
    rfl
  · intro candidate candidateFactors
    apply bisimulationQuotientResonanceLift_unique
      cofork.π invariant candidate
    intro value
    have functionEqual :
        (candidate.comp (bisimulationQuotientProjection inc)).toFun =
          cofork.π.toFun := congrArg TernaryResonanceHom.toFun candidateFactors
    exact congrFun functionEqual value

theorem bisimulationQuotientResonanceCofork_homIso_natural
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    {target target' : TernaryResonanceSystem.{u}}
    (lift : (bisimulationQuotientResonanceCofork inc).pt ⟶ target)
    (postcompose : target ⟶ target') :
    (Cofork.IsColimit.homIso
        (bisimulationQuotientResonanceCofork_isColimit inc) target'
        (lift ≫ postcompose) : inc.resonanceSystem ⟶ target') =
      (Cofork.IsColimit.homIso
        (bisimulationQuotientResonanceCofork_isColimit inc) target lift :
          inc.resonanceSystem ⟶ target) ≫
        postcompose := by
  exact Cofork.IsColimit.homIso_natural
    postcompose (bisimulationQuotientResonanceCofork_isColimit inc) lift

theorem no_exact_resonance_quotient_of_not_congruent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (notCongruent : ¬ QuotientResonanceCongruent inc) :
    ¬ ResonanceRelationDescendsExactly inc :=
  fun descent => notCongruent
    (quotientResonanceCongruent_of_exact_descent descent)

/- The coproduct of two natural-number incidence structures is a concrete
   obstruction: its two units become bisimilar, but resonance can still tell
   which summand supplied the unit.  Hence no exact quotient relation exists. -/
theorem natSum_has_no_exact_resonance_quotient :
    ¬ ResonanceRelationDescendsExactly
      (incidenceSum natIncidence natIncidence) :=
  no_exact_resonance_quotient_of_not_congruent
    incidenceSum_nat_not_quotientResonanceCongruent

/- A non-faithful positive model.  It retains the boundary geometry and the
   three bisimulation classes of the 2-simplex, while treating every triple as
   a possible resonance mode.  This is deliberately the saturated endpoint of
   the theory: unlike the functional simplex selector, its relational
   resonance is invariant under change of representatives. -/
def saturatedSimplexIncidence :
    Incidence SimplexId SimplexRole GraphType where
  boundary := simplexIncidence.boundary
  typeFunc := simplexIncidence.typeFunc
  glue := simplexIncidence.glue
  resonance := fun _ _ _ => True
  selected_resonates := fun _ => True.intro
  unit := simplexIncidence.unit
  guards := simplexIncidence.guards
  boundaryMatrix := simplexIncidence.boundaryMatrix
  laplacian := simplexIncidence.laplacian
  type_consistent := simplexIncidence.type_consistent
  sign_rules := simplexIncidence.sign_rules
  multiplicities := simplexIncidence.multiplicities
  well_founded := simplexIncidence.well_founded
  unit_left := simplexIncidence.unit_left
  unit_right := simplexIncidence.unit_right
  type_preserve := simplexIncidence.type_preserve

theorem saturatedSimplex_approxBisim_iff (x y : SimplexId) :
    approxBisim saturatedSimplexIncidence x y ↔
      approxBisim simplexIncidence x y := by
  rfl

theorem saturatedSimplex_three_shape_classification (x y : SimplexId) :
    simplexToShape x = simplexToShape y ↔
      approxBisim saturatedSimplexIncidence x y := by
  rw [saturatedSimplex_approxBisim_iff]
  exact simplexToShape_iff_approxBisim x y

theorem saturatedSimplex_quotientResonanceCongruent :
    QuotientResonanceCongruent saturatedSimplexIncidence := by
  intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk
  simp [saturatedSimplexIncidence]

theorem saturatedSimplex_resonance_descends_exactly :
    ResonanceRelationDescendsExactly saturatedSimplexIncidence :=
  exact_descent_of_quotientResonanceCongruent
    saturatedSimplex_quotientResonanceCongruent

theorem saturatedSimplex_is_nonfaithful :
    approxBisim saturatedSimplexIncidence .v0 .v1 ∧
      SimplexId.v0 ≠ SimplexId.v1 := by
  constructor
  · exact (saturatedSimplex_three_shape_classification .v0 .v1).mp rfl
  · decide

theorem saturatedSimplex_has_distinct_vertex_and_edge_classes :
    ¬ approxBisim saturatedSimplexIncidence .v0 .e01 := by
  intro bisimilar
  have equalShape :=
    (saturatedSimplex_three_shape_classification .v0 .e01).mpr bisimilar
  cases equalShape

/- A domain-motivated nontrivial relational model.  Interacting simplex cells
   may resonate in either participant's geometric dimension, but not in an
   unrelated third dimension.  Thus vertex/face interaction has vertex and
   face modes, while excluding edge modes. -/
def simplexShapeModeResonance (left right output : SimplexId) : Prop :=
  simplexToShape output = simplexToShape left ∨
    simplexToShape output = simplexToShape right

def shapeModeSimplexIncidence :
    Incidence SimplexId SimplexRole GraphType where
  boundary := simplexIncidence.boundary
  typeFunc := simplexIncidence.typeFunc
  glue := simplexIncidence.glue
  resonance := simplexShapeModeResonance
  selected_resonates := by
    intro left right output selected
    by_cases unitLeft : left = SimplexId.v0
    · subst left
      simp [simplexIncidence] at selected
      subst output
      exact Or.inr rfl
    · simp [simplexIncidence, unitLeft] at selected
      subst output
      exact Or.inl rfl
  unit := simplexIncidence.unit
  guards := simplexIncidence.guards
  boundaryMatrix := simplexIncidence.boundaryMatrix
  laplacian := simplexIncidence.laplacian
  type_consistent := simplexIncidence.type_consistent
  sign_rules := simplexIncidence.sign_rules
  multiplicities := simplexIncidence.multiplicities
  well_founded := simplexIncidence.well_founded
  unit_left := simplexIncidence.unit_left
  unit_right := simplexIncidence.unit_right
  type_preserve := simplexIncidence.type_preserve

theorem shapeModeSimplex_approxBisim_iff (x y : SimplexId) :
    approxBisim shapeModeSimplexIncidence x y ↔
      approxBisim simplexIncidence x y := by
  rfl

theorem shapeModeSimplex_shape_classification (x y : SimplexId) :
    simplexToShape x = simplexToShape y ↔
      approxBisim shapeModeSimplexIncidence x y := by
  rw [shapeModeSimplex_approxBisim_iff]
  exact simplexToShape_iff_approxBisim x y

theorem shapeModeSimplex_quotientResonanceCongruent :
    QuotientResonanceCongruent shapeModeSimplexIncidence := by
  intro left₁ left₂ right₁ right₂ output₁ output₂
    leftRelated rightRelated outputRelated
  have leftShape :=
    (shapeModeSimplex_shape_classification left₁ left₂).mpr leftRelated
  have rightShape :=
    (shapeModeSimplex_shape_classification right₁ right₂).mpr rightRelated
  have outputShape :=
    (shapeModeSimplex_shape_classification output₁ output₂).mpr outputRelated
  simp only [shapeModeSimplexIncidence, simplexShapeModeResonance]
  rw [leftShape, rightShape, outputShape]

theorem shapeModeSimplex_resonance_descends_exactly :
    ResonanceRelationDescendsExactly shapeModeSimplexIncidence :=
  exact_descent_of_quotientResonanceCongruent
    shapeModeSimplex_quotientResonanceCongruent

theorem shapeModeSimplex_vertex_face_has_two_shape_modes :
    shapeModeSimplexIncidence.resonance .v0 .face .v1 ∧
      shapeModeSimplexIncidence.resonance .v0 .face .face := by
  constructor <;> simp [shapeModeSimplexIncidence, simplexShapeModeResonance,
    simplexToShape]

theorem shapeModeSimplex_vertex_face_excludes_edge_mode :
    ¬ shapeModeSimplexIncidence.resonance .v0 .face .e01 := by
  simp [shapeModeSimplexIncidence, simplexShapeModeResonance, simplexToShape]

theorem shapeModeSimplex_is_genuinely_multivalued :
    ∃ left right first second,
      first ≠ second ∧
      shapeModeSimplexIncidence.resonance left right first ∧
      shapeModeSimplexIncidence.resonance left right second :=
  ⟨.v0, .face, .v1, .face, by decide,
    shapeModeSimplex_vertex_face_has_two_shape_modes.1,
    shapeModeSimplex_vertex_face_has_two_shape_modes.2⟩

theorem shapeModeSimplex_is_not_saturated :
    ∃ left right output,
      ¬ shapeModeSimplexIncidence.resonance left right output :=
  ⟨.v0, .face, .e01, shapeModeSimplex_vertex_face_excludes_edge_mode⟩

def simplexShapeModeSystem : TernaryResonanceSystem where
  Carrier := SimplexShape
  resonance := fun left right output => output = left ∨ output = right

def shapeModeSimplexClassificationHom :
    TernaryResonanceHom shapeModeSimplexIncidence.resonanceSystem
      simplexShapeModeSystem where
  toFun := simplexToShape
  preserves := by
    intro left right output resonant
    exact resonant

theorem shapeModeSimplexClassificationHom_invariant :
    BisimulationInvariantResonanceHom shapeModeSimplexIncidence
      simplexShapeModeSystem shapeModeSimplexClassificationHom := by
  intro left right related
  exact (shapeModeSimplex_shape_classification left right).mpr related

def shapeModeSimplexQuotientRepresentation :
    TernaryResonanceHom
      (bisimulationQuotientResonanceSystem shapeModeSimplexIncidence)
      simplexShapeModeSystem :=
  bisimulationQuotientResonanceLift shapeModeSimplexClassificationHom
    shapeModeSimplexClassificationHom_invariant

theorem shapeModeSimplex_quotientResonance_representation
    (left right output : SimplexId) :
    quotientResonance shapeModeSimplexIncidence
        (Quotient.mk (approxBisimSetoid shapeModeSimplexIncidence) left)
        (Quotient.mk (approxBisimSetoid shapeModeSimplexIncidence) right)
        (Quotient.mk (approxBisimSetoid shapeModeSimplexIncidence) output) ↔
      simplexShapeModeSystem.resonance
        (simplexToShape left) (simplexToShape right)
          (simplexToShape output) := by
  rw [quotientResonance_mk_iff shapeModeSimplex_quotientResonanceCongruent]
  rfl

/- A finite obstruction certificate records the six representatives needed to
   refute extensionality of a ternary relation.  Keeping the certificate free
   of proof fields makes the entire candidate space finitely enumerable. -/
structure ResonanceDescentCandidate (I : Type u) where
  left₁ : I
  left₂ : I
  right₁ : I
  right₂ : I
  output₁ : I
  output₂ : I
deriving DecidableEq

instance {I : Type u} [Fintype I] : Fintype (ResonanceDescentCandidate I) :=
  Fintype.ofEquiv (I × I × I × I × I × I) {
    toFun := fun tuple =>
      ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
        tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩
    invFun := fun candidate =>
      (candidate.left₁, candidate.left₂, candidate.right₁,
        candidate.right₂, candidate.output₁, candidate.output₂)
    left_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl
    right_inv := by intro candidate; cases candidate; rfl }

def ResonanceDescentCandidate.IsObstruction
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (candidate : ResonanceDescentCandidate I) : Prop :=
  approxBisim inc candidate.left₁ candidate.left₂ ∧
  approxBisim inc candidate.right₁ candidate.right₂ ∧
  approxBisim inc candidate.output₁ candidate.output₂ ∧
  ¬ (inc.resonance candidate.left₁ candidate.right₁ candidate.output₁ ↔
      inc.resonance candidate.left₂ candidate.right₂ candidate.output₂)

noncomputable def finiteResonanceDescentObstructions
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) : Finset (ResonanceDescentCandidate I) := by
  classical
  exact Finset.univ.filter (ResonanceDescentCandidate.IsObstruction inc)

theorem mem_finiteResonanceDescentObstructions_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) (candidate : ResonanceDescentCandidate I) :
    candidate ∈ finiteResonanceDescentObstructions inc ↔
      candidate.IsObstruction inc := by
  classical
  simp [finiteResonanceDescentObstructions]

theorem finiteResonanceDescentObstructions_empty_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    finiteResonanceDescentObstructions inc = ∅ ↔
      QuotientResonanceCongruent inc := by
  classical
  constructor
  · intro empty i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk
    by_cases exactRelation :
        inc.resonance i₁ j₁ k₁ ↔ inc.resonance i₂ j₂ k₂
    · exact exactRelation
    · let candidate : ResonanceDescentCandidate I :=
        ⟨i₁, i₂, j₁, j₂, k₁, k₂⟩
      have obstructs : candidate.IsObstruction inc :=
        ⟨hi, hj, hk, exactRelation⟩
      have member : candidate ∈ finiteResonanceDescentObstructions inc :=
        (mem_finiteResonanceDescentObstructions_iff inc candidate).mpr obstructs
      rw [empty] at member
      simp at member
  · intro congruent
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate member
    have obstruction :=
      (mem_finiteResonanceDescentObstructions_iff inc candidate).mp member
    exact obstruction.2.2.2
      (congruent obstruction.1 obstruction.2.1 obstruction.2.2.1)

/- Finite classification theorem: exact descent is decidable by exhaustively
   checking a finite set of six-representative obstruction certificates. -/
theorem finite_exact_resonance_descent_iff_no_obstructions
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      finiteResonanceDescentObstructions inc = ∅ := by
  rw [resonanceRelationDescendsExactly_iff,
    finiteResonanceDescentObstructions_empty_iff]

theorem finite_no_exact_descent_iff_obstruction_exists
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    ¬ ResonanceRelationDescendsExactly inc ↔
      ∃ candidate, candidate ∈ finiteResonanceDescentObstructions inc := by
  rw [finite_exact_resonance_descent_iff_no_obstructions]
  exact Finset.nonempty_iff_ne_empty.symm

def simplexSelectorObstruction : ResonanceDescentCandidate SimplexId :=
  ⟨.v0, .v1, .face, .face, .face, .face⟩

instance simplexIdFintype : Fintype SimplexId :=
  ⟨{.v0, .v1, .v2, .e01, .e02, .e12, .face}, by
    intro value
    cases value <;> simp⟩

theorem simplexSelectorObstruction_isObstruction :
    simplexSelectorObstruction.IsObstruction simplexIncidence := by
  refine ⟨(simplexToShape_iff_approxBisim .v0 .v1).mp rfl,
    approxBisim_refl _ _, approxBisim_refl _ _, ?_⟩
  simp [simplexSelectorObstruction, simplexIncidence]

theorem simplexIncidence_finite_obstruction_nonempty :
    ∃ candidate,
      candidate ∈ finiteResonanceDescentObstructions simplexIncidence := by
  classical
  exact ⟨simplexSelectorObstruction,
    (mem_finiteResonanceDescentObstructions_iff
      simplexIncidence simplexSelectorObstruction).mpr
        simplexSelectorObstruction_isObstruction⟩

theorem simplexIncidence_has_no_exact_resonance_descent :
    ¬ ResonanceRelationDescendsExactly simplexIncidence := by
  intro descent
  have congruent : QuotientResonanceCongruent simplexIncidence :=
    quotientResonanceCongruent_of_exact_descent
      (inc := simplexIncidence) descent
  exact simplexSelectorObstruction_isObstruction.2.2.2
    (congruent simplexSelectorObstruction_isObstruction.1
      simplexSelectorObstruction_isObstruction.2.1
      simplexSelectorObstruction_isObstruction.2.2.1)

/- Congruence can be checked one coordinate at a time.  This is the structural
   reduction behind a smaller finite obstruction search: each local witness has
   four representatives rather than six. -/
def LeftResonanceCongruent
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop :=
  ∀ {left₁ left₂ right output}, approxBisim inc left₁ left₂ →
    (inc.resonance left₁ right output ↔ inc.resonance left₂ right output)

def RightResonanceCongruent
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop :=
  ∀ {left right₁ right₂ output}, approxBisim inc right₁ right₂ →
    (inc.resonance left right₁ output ↔ inc.resonance left right₂ output)

def OutputResonanceCongruent
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop :=
  ∀ {left right output₁ output₂}, approxBisim inc output₁ output₂ →
    (inc.resonance left right output₁ ↔ inc.resonance left right output₂)

theorem quotientResonanceCongruent_iff_coordinatewise
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    QuotientResonanceCongruent inc ↔
      LeftResonanceCongruent inc ∧ RightResonanceCongruent inc ∧
        OutputResonanceCongruent inc := by
  constructor
  · intro congruent
    refine ⟨?_, ?_, ?_⟩
    · intro left₁ left₂ right output related
      exact congruent related (approxBisim_refl inc right)
        (approxBisim_refl inc output)
    · intro left right₁ right₂ output related
      exact congruent (approxBisim_refl inc left) related
        (approxBisim_refl inc output)
    · intro left right output₁ output₂ related
      exact congruent (approxBisim_refl inc left)
        (approxBisim_refl inc right) related
  · rintro ⟨leftCongruent, rightCongruent, outputCongruent⟩
    intro left₁ left₂ right₁ right₂ output₁ output₂ hleft hright houtput
    exact (leftCongruent hleft).trans
      ((rightCongruent hright).trans (outputCongruent houtput))

theorem resonanceRelationDescendsExactly_iff_coordinatewise
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      LeftResonanceCongruent inc ∧ RightResonanceCongruent inc ∧
        OutputResonanceCongruent inc := by
  rw [resonanceRelationDescendsExactly_iff,
    quotientResonanceCongruent_iff_coordinatewise]

inductive ResonanceCoordinate where
  | left
  | right
  | output
deriving DecidableEq, Repr

instance resonanceCoordinateFintype : Fintype ResonanceCoordinate :=
  ⟨{.left, .right, .output}, by
    intro coordinate
    cases coordinate <;> simp⟩

structure LocalResonanceDescentCandidate (I : Type u) where
  coordinate : ResonanceCoordinate
  first : I
  second : I
  fixed₁ : I
  fixed₂ : I
deriving DecidableEq

instance {I : Type u} [Fintype I] :
    Fintype (LocalResonanceDescentCandidate I) :=
  Fintype.ofEquiv (ResonanceCoordinate × I × I × I × I) {
    toFun := fun tuple =>
      ⟨tuple.1, tuple.2.1, tuple.2.2.1,
        tuple.2.2.2.1, tuple.2.2.2.2⟩
    invFun := fun candidate =>
      (candidate.coordinate,
        candidate.first, candidate.second, candidate.fixed₁, candidate.fixed₂)
    left_inv := by rintro ⟨coordinate, first, second, fixed₁, fixed₂⟩; rfl
    right_inv := by
      intro candidate
      cases candidate
      rfl }

def LocalResonanceDescentCandidate.IsObstruction
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (candidate : LocalResonanceDescentCandidate I) : Prop :=
  approxBisim inc candidate.first candidate.second ∧
    match candidate.coordinate with
    | .left =>
        ¬ (inc.resonance candidate.first candidate.fixed₁ candidate.fixed₂ ↔
          inc.resonance candidate.second candidate.fixed₁ candidate.fixed₂)
    | .right =>
        ¬ (inc.resonance candidate.fixed₁ candidate.first candidate.fixed₂ ↔
          inc.resonance candidate.fixed₁ candidate.second candidate.fixed₂)
    | .output =>
        ¬ (inc.resonance candidate.fixed₁ candidate.fixed₂ candidate.first ↔
          inc.resonance candidate.fixed₁ candidate.fixed₂ candidate.second)

noncomputable def finiteLocalResonanceDescentObstructions
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    Finset (LocalResonanceDescentCandidate I) := by
  classical
  exact Finset.univ.filter
    (LocalResonanceDescentCandidate.IsObstruction inc)

theorem mem_finiteLocalResonanceDescentObstructions_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    (candidate : LocalResonanceDescentCandidate I) :
    candidate ∈ finiteLocalResonanceDescentObstructions inc ↔
      candidate.IsObstruction inc := by
  classical
  simp [finiteLocalResonanceDescentObstructions]

theorem finiteLocalResonanceDescentObstructions_empty_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    finiteLocalResonanceDescentObstructions inc = ∅ ↔
      LeftResonanceCongruent inc ∧ RightResonanceCongruent inc ∧
        OutputResonanceCongruent inc := by
  classical
  constructor
  · intro empty
    have noObstruction : ∀ candidate : LocalResonanceDescentCandidate I,
        ¬ candidate.IsObstruction inc := by
      intro candidate obstruction
      have member :=
        (mem_finiteLocalResonanceDescentObstructions_iff inc candidate).mpr
          obstruction
      rw [empty] at member
      simp at member
    refine ⟨?_, ?_, ?_⟩
    · intro first second fixed₁ fixed₂ related
      by_cases exactRelation :
          inc.resonance first fixed₁ fixed₂ ↔
            inc.resonance second fixed₁ fixed₂
      · exact exactRelation
      · exact False.elim (noObstruction
          ⟨.left, first, second, fixed₁, fixed₂⟩ ⟨related, exactRelation⟩)
    · intro fixed₁ first second fixed₂ related
      by_cases exactRelation :
          inc.resonance fixed₁ first fixed₂ ↔
            inc.resonance fixed₁ second fixed₂
      · exact exactRelation
      · exact False.elim (noObstruction
          ⟨.right, first, second, fixed₁, fixed₂⟩ ⟨related, exactRelation⟩)
    · intro fixed₁ fixed₂ first second related
      by_cases exactRelation :
          inc.resonance fixed₁ fixed₂ first ↔
            inc.resonance fixed₁ fixed₂ second
      · exact exactRelation
      · exact False.elim (noObstruction
          ⟨.output, first, second, fixed₁, fixed₂⟩ ⟨related, exactRelation⟩)
  · rintro ⟨leftCongruent, rightCongruent, outputCongruent⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate member
    have obstruction :=
      (mem_finiteLocalResonanceDescentObstructions_iff inc candidate).mp member
    rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
    cases coordinate with
    | left => exact obstruction.2 (leftCongruent obstruction.1)
    | right => exact obstruction.2 (rightCongruent obstruction.1)
    | output => exact obstruction.2 (outputCongruent obstruction.1)

theorem finite_exact_descent_iff_no_local_obstructions
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      finiteLocalResonanceDescentObstructions inc = ∅ := by
  rw [resonanceRelationDescendsExactly_iff_coordinatewise,
    finiteLocalResonanceDescentObstructions_empty_iff]

/- Swapping the two bisimilar representatives does not change a local
   obstruction.  This is the intrinsic Z₂-symmetry of every local certificate. -/
def LocalResonanceDescentCandidate.swap
    {I : Type u} (candidate : LocalResonanceDescentCandidate I) :
    LocalResonanceDescentCandidate I :=
  { candidate with
    first := candidate.second
    second := candidate.first }

@[simp] theorem LocalResonanceDescentCandidate.swap_swap
    {I : Type u} (candidate : LocalResonanceDescentCandidate I) :
    candidate.swap.swap = candidate := by
  cases candidate
  rfl

theorem LocalResonanceDescentCandidate.isObstruction_swap_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (candidate : LocalResonanceDescentCandidate I) :
    candidate.swap.IsObstruction inc ↔ candidate.IsObstruction inc := by
  rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
  cases coordinate <;> simp only [swap, IsObstruction] <;>
    constructor
  all_goals
    rintro ⟨related, mismatch⟩
    refine ⟨approxBisim_symm related, ?_⟩
    intro reverseRelation
    exact mismatch reverseRelation.symm

theorem LocalResonanceDescentCandidate.distinct_representatives_of_obstruction
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {candidate : LocalResonanceDescentCandidate I}
    (obstruction : candidate.IsObstruction inc) :
    candidate.first ≠ candidate.second := by
  intro equal
  rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
  simp only at equal
  subst second
  cases coordinate <;> exact obstruction.2 (Iff.rfl)

theorem LocalResonanceDescentCandidate.swap_ne_of_obstruction
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {candidate : LocalResonanceDescentCandidate I}
    (obstruction : candidate.IsObstruction inc) :
    candidate.swap ≠ candidate := by
  intro equal
  have firstEqual : candidate.second = candidate.first := by
    exact congrArg LocalResonanceDescentCandidate.first equal
  exact LocalResonanceDescentCandidate.distinct_representatives_of_obstruction
    obstruction firstEqual.symm

def LocalResonanceDescentCandidate.SwapRelated
    {I : Type u} (first second : LocalResonanceDescentCandidate I) : Prop :=
  second = first ∨ second = first.swap

theorem LocalResonanceDescentCandidate.swapRelated_equivalence
    {I : Type u} :
    Equivalence
      (LocalResonanceDescentCandidate.SwapRelated (I := I)) := by
  constructor
  · intro candidate
    exact Or.inl rfl
  · intro first second related
    rcases related with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (LocalResonanceDescentCandidate.swap_swap first).symm
  · intro first second third firstSecond secondThird
    rcases firstSecond with rfl | rfl
    · exact secondThird
    · rcases secondThird with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (LocalResonanceDescentCandidate.swap_swap first)

def localResonanceDescentSwapSetoid (I : Type u) :
    Setoid (LocalResonanceDescentCandidate I) where
  r := LocalResonanceDescentCandidate.SwapRelated
  iseqv := LocalResonanceDescentCandidate.swapRelated_equivalence

abbrev LocalResonanceObstructionOrbit (I : Type u) :=
  Quotient (localResonanceDescentSwapSetoid I)

def LocalResonanceObstructionOrbit.IsObstruction
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    LocalResonanceObstructionOrbit I → Prop :=
  Quotient.lift (LocalResonanceDescentCandidate.IsObstruction inc) (by
    intro first second related
    rcases related with rfl | rfl
    · rfl
    · apply propext
      exact (first.isObstruction_swap_iff inc).symm)

@[simp] theorem localResonanceObstructionOrbit_mk_isObstruction_iff
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (candidate : LocalResonanceDescentCandidate I) :
    LocalResonanceObstructionOrbit.IsObstruction inc
        (Quotient.mk (localResonanceDescentSwapSetoid I) candidate) ↔
      candidate.IsObstruction inc :=
  Iff.rfl

theorem exact_descent_iff_no_local_obstruction_orbit
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      ¬ ∃ orbit : LocalResonanceObstructionOrbit I,
        orbit.IsObstruction inc := by
  rw [resonanceRelationDescendsExactly_iff_coordinatewise]
  constructor
  · rintro ⟨leftCongruent, rightCongruent, outputCongruent⟩ ⟨orbit, obstructs⟩
    induction orbit using Quotient.ind with
    | _ candidate =>
      have obstruction : candidate.IsObstruction inc := obstructs
      rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
      cases coordinate with
      | left => exact obstruction.2 (leftCongruent obstruction.1)
      | right => exact obstruction.2 (rightCongruent obstruction.1)
      | output => exact obstruction.2 (outputCongruent obstruction.1)
  · intro noOrbit
    refine ⟨?_, ?_, ?_⟩
    · intro first second fixed₁ fixed₂ related
      by_cases exactRelation :
          inc.resonance first fixed₁ fixed₂ ↔
            inc.resonance second fixed₁ fixed₂
      · exact exactRelation
      · exact False.elim (noOrbit ⟨Quotient.mk _
          ⟨.left, first, second, fixed₁, fixed₂⟩, ⟨related, exactRelation⟩⟩)
    · intro fixed₁ first second fixed₂ related
      by_cases exactRelation :
          inc.resonance fixed₁ first fixed₂ ↔
            inc.resonance fixed₁ second fixed₂
      · exact exactRelation
      · exact False.elim (noOrbit ⟨Quotient.mk _
          ⟨.right, first, second, fixed₁, fixed₂⟩, ⟨related, exactRelation⟩⟩)
    · intro fixed₁ fixed₂ first second related
      by_cases exactRelation :
          inc.resonance fixed₁ fixed₂ first ↔
            inc.resonance fixed₁ fixed₂ second
      · exact exactRelation
      · exact False.elim (noOrbit ⟨Quotient.mk _
          ⟨.output, first, second, fixed₁, fixed₂⟩, ⟨related, exactRelation⟩⟩)

/- The support of a local certificate forgets repetitions.  Minimality below
   is therefore intrinsic to the finite configuration witnessed by a
   certificate, rather than to its four displayed slots. -/
def LocalResonanceDescentCandidate.support
    {I : Type u} [DecidableEq I]
    (candidate : LocalResonanceDescentCandidate I) : Finset I :=
  {candidate.first, candidate.second, candidate.fixed₁, candidate.fixed₂}

def LocalResonanceDescentCandidate.IsSupportMinimalObstruction
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (candidate : LocalResonanceDescentCandidate I) : Prop :=
  candidate.IsObstruction inc ∧
    ∀ other : LocalResonanceDescentCandidate I, other.IsObstruction inc →
      candidate.support.card ≤ other.support.card

theorem exists_supportMinimalObstruction_of_not_exact_descent
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    (failure : ¬ ResonanceRelationDescendsExactly inc) :
    ∃ candidate : LocalResonanceDescentCandidate I,
      candidate.IsSupportMinimalObstruction inc := by
  classical
  have existsObstruction :
      ∃ candidate : LocalResonanceDescentCandidate I,
        candidate.IsObstruction inc := by
    by_contra none
    push_neg at none
    have empty : finiteLocalResonanceDescentObstructions inc = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro candidate member
      exact none candidate
        ((mem_finiteLocalResonanceDescentObstructions_iff inc candidate).mp member)
    exact failure ((finite_exact_descent_iff_no_local_obstructions inc).mpr empty)
  let hasObstructionOfSize : Nat → Prop := fun size =>
    ∃ candidate : LocalResonanceDescentCandidate I,
      candidate.IsObstruction inc ∧ candidate.support.card = size
  have existsSize : ∃ size, hasObstructionOfSize size := by
    rcases existsObstruction with ⟨candidate, obstruction⟩
    exact ⟨candidate.support.card, candidate, obstruction, rfl⟩
  rcases Nat.find_spec existsSize with
    ⟨candidate, candidateObstruction, candidateSize⟩
  refine ⟨candidate, candidateObstruction, ?_⟩
  intro other otherObstruction
  rw [candidateSize]
  exact Nat.find_min' existsSize ⟨other, otherObstruction, rfl⟩

theorem LocalResonanceDescentCandidate.two_le_support_card_of_obstruction
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {candidate : LocalResonanceDescentCandidate I}
    (obstruction : candidate.IsObstruction inc) :
    2 ≤ candidate.support.card := by
  have distinct := candidate.distinct_representatives_of_obstruction obstruction
  have subset : ({candidate.first, candidate.second} : Finset I) ⊆
      candidate.support := by
    intro value member
    have equal : value = candidate.first ∨ value = candidate.second := by
      simpa using member
    rcases equal with rfl | rfl <;>
      simp [LocalResonanceDescentCandidate.support]
  have pairCard : ({candidate.first, candidate.second} : Finset I).card = 2 := by
    simp [distinct]
  rw [← pairCard]
  exact Finset.card_le_card subset

theorem LocalResonanceDescentCandidate.support_eq_representativePair
    {I : Type u} [DecidableEq I]
    (candidate : LocalResonanceDescentCandidate I)
    (fixed₁InPair : candidate.fixed₁ = candidate.first ∨
      candidate.fixed₁ = candidate.second)
    (fixed₂InPair : candidate.fixed₂ = candidate.first ∨
      candidate.fixed₂ = candidate.second) :
    candidate.support = {candidate.first, candidate.second} := by
  rcases fixed₁InPair with fixed₁Equal | fixed₁Equal <;>
    rcases fixed₂InPair with fixed₂Equal | fixed₂Equal <;>
    ext value <;>
    simp [LocalResonanceDescentCandidate.support, fixed₁Equal, fixed₂Equal,
      or_comm]

theorem LocalResonanceDescentCandidate.support_card_eq_two_of_pair
    {I : Type u} [DecidableEq I]
    (candidate : LocalResonanceDescentCandidate I)
    (distinct : candidate.first ≠ candidate.second)
    (fixed₁InPair : candidate.fixed₁ = candidate.first ∨
      candidate.fixed₁ = candidate.second)
    (fixed₂InPair : candidate.fixed₂ = candidate.first ∨
      candidate.fixed₂ = candidate.second) :
    candidate.support.card = 2 := by
  rw [candidate.support_eq_representativePair fixed₁InPair fixed₂InPair]
  simp [distinct]

theorem LocalResonanceDescentCandidate.isSupportMinimal_of_pair
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (candidate : LocalResonanceDescentCandidate I)
    (obstruction : candidate.IsObstruction inc)
    (fixed₁InPair : candidate.fixed₁ = candidate.first ∨
      candidate.fixed₁ = candidate.second)
    (fixed₂InPair : candidate.fixed₂ = candidate.first ∨
      candidate.fixed₂ = candidate.second) :
    candidate.IsSupportMinimalObstruction inc := by
  refine ⟨obstruction, ?_⟩
  intro other otherObstruction
  rw [candidate.support_card_eq_two_of_pair
    (candidate.distinct_representatives_of_obstruction obstruction)
    fixed₁InPair fixed₂InPair]
  exact other.two_le_support_card_of_obstruction otherObstruction

theorem LocalResonanceDescentCandidate.support_eq_pair_of_card_eq_two
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (candidate : LocalResonanceDescentCandidate I)
    (obstruction : candidate.IsObstruction inc)
    (supportCard : candidate.support.card = 2) :
    candidate.support = {candidate.first, candidate.second} := by
  have pairSubset : ({candidate.first, candidate.second} : Finset I) ⊆
      candidate.support := by
    intro value member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;>
      simp [LocalResonanceDescentCandidate.support]
  have pairCard : ({candidate.first, candidate.second} : Finset I).card = 2 := by
    simp [candidate.distinct_representatives_of_obstruction obstruction]
  exact (Finset.eq_of_subset_of_card_le pairSubset (by
    rw [supportCard, pairCard])).symm

theorem LocalResonanceDescentCandidate.fixedSlots_mem_pair_of_card_eq_two
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (candidate : LocalResonanceDescentCandidate I)
    (obstruction : candidate.IsObstruction inc)
    (supportCard : candidate.support.card = 2) :
    (candidate.fixed₁ = candidate.first ∨
        candidate.fixed₁ = candidate.second) ∧
      (candidate.fixed₂ = candidate.first ∨
        candidate.fixed₂ = candidate.second) := by
  have supportEq := candidate.support_eq_pair_of_card_eq_two
    obstruction supportCard
  have fixed₁Mem : candidate.fixed₁ ∈ candidate.support := by
    simp [LocalResonanceDescentCandidate.support]
  have fixed₂Mem : candidate.fixed₂ ∈ candidate.support := by
    simp [LocalResonanceDescentCandidate.support]
  rw [supportEq] at fixed₁Mem fixed₂Mem
  simpa using And.intro fixed₁Mem fixed₂Mem

/- The ordinary simplex selector already has a smallest possible obstruction:
   changing v0 to the bisimilar v1 changes selection at the pair (v0,v0), so
   only the two vertices are needed in its support. -/
def simplexTwoVertexLocalObstruction :
    LocalResonanceDescentCandidate SimplexId :=
  ⟨.left, .v0, .v1, .v0, .v0⟩

theorem simplexTwoVertexLocalObstruction_isObstruction :
    simplexTwoVertexLocalObstruction.IsObstruction simplexIncidence := by
  refine ⟨(simplexToShape_iff_approxBisim .v0 .v1).mp rfl, ?_⟩
  simp [simplexTwoVertexLocalObstruction, simplexIncidence]

theorem simplexTwoVertexLocalObstruction_support_card :
    simplexTwoVertexLocalObstruction.support.card = 2 := by
  decide

theorem simplexTwoVertexLocalObstruction_isSupportMinimal :
    simplexTwoVertexLocalObstruction.IsSupportMinimalObstruction
      simplexIncidence := by
  refine ⟨simplexTwoVertexLocalObstruction_isObstruction, ?_⟩
  intro other otherObstruction
  rw [simplexTwoVertexLocalObstruction_support_card]
  exact other.two_le_support_card_of_obstruction otherObstruction

/- An automorphism used for obstruction classification must preserve both the
   behavioural equivalence and the ternary resonance relation.  This is the
   exact amount of structure needed for transporting local certificates. -/
structure ResonanceBisimulationAutomorphism
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  toEquiv : I ≃ I
  map_approxBisim_iff : ∀ first second,
    approxBisim inc (toEquiv first) (toEquiv second) ↔
      approxBisim inc first second
  map_resonance_iff : ∀ left right output,
    inc.resonance (toEquiv left) (toEquiv right) (toEquiv output) ↔
      inc.resonance left right output

def ResonanceBisimulationAutomorphism.mapCandidate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (automorphism : ResonanceBisimulationAutomorphism inc)
    (candidate : LocalResonanceDescentCandidate I) :
    LocalResonanceDescentCandidate I :=
  ⟨candidate.coordinate,
    automorphism.toEquiv candidate.first,
    automorphism.toEquiv candidate.second,
    automorphism.toEquiv candidate.fixed₁,
    automorphism.toEquiv candidate.fixed₂⟩

def simplexResonanceAutomorphismOfEquiv
    (equiv : SimplexId ≃ SimplexId)
    (fixesUnit : equiv .v0 = .v0)
    (preservesShape : ∀ value,
      simplexToShape (equiv value) = simplexToShape value) :
    ResonanceBisimulationAutomorphism simplexIncidence where
  toEquiv := equiv
  map_approxBisim_iff := by
    intro first second
    rw [← simplexToShape_iff_approxBisim,
      ← simplexToShape_iff_approxBisim,
      preservesShape, preservesShape]
  map_resonance_iff := by
    intro left right output
    have mapsUnit : equiv left = SimplexId.v0 ↔ left = SimplexId.v0 := by
      constructor
      · intro mapped
        apply equiv.injective
        simpa [fixesUnit] using mapped
      · rintro rfl
        exact fixesUnit
    by_cases unitLeft : left = SimplexId.v0
    · subst left
      simp [simplexIncidence, fixesUnit, equiv.injective.eq_iff]
    · have mappedNonunit : equiv left ≠ SimplexId.v0 :=
        fun mapped => unitLeft (mapsUnit.mp mapped)
      simp [simplexIncidence, unitLeft, mappedNonunit,
        equiv.injective.eq_iff]

def simplexSwapAutomorphism
    (first second : SimplexId)
    (sameShape : simplexToShape first = simplexToShape second)
    (firstNonunit : first ≠ SimplexId.v0)
    (secondNonunit : second ≠ SimplexId.v0) :
    ResonanceBisimulationAutomorphism simplexIncidence :=
  simplexResonanceAutomorphismOfEquiv (Equiv.swap first second) (by
    exact Equiv.swap_apply_of_ne_of_ne firstNonunit.symm secondNonunit.symm) (by
    intro value
    by_cases valueFirst : value = first
    · subst value
      simp [sameShape]
    · by_cases valueSecond : value = second
      · subst value
        simp [sameShape]
      · simp [Equiv.swap_apply_def, valueFirst, valueSecond])

@[simp] theorem simplexSwapAutomorphism_apply
    (first second : SimplexId)
    (sameShape : simplexToShape first = simplexToShape second)
    (firstNonunit : first ≠ SimplexId.v0)
    (secondNonunit : second ≠ SimplexId.v0)
    (value : SimplexId) :
    (simplexSwapAutomorphism first second sameShape firstNonunit
      secondNonunit).toEquiv value = Equiv.swap first second value :=
  rfl

def ResonanceBisimulationAutomorphism.refl
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceBisimulationAutomorphism inc where
  toEquiv := Equiv.refl I
  map_approxBisim_iff := fun _ _ => Iff.rfl
  map_resonance_iff := fun _ _ _ => Iff.rfl

def ResonanceBisimulationAutomorphism.symm
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (automorphism : ResonanceBisimulationAutomorphism inc) :
    ResonanceBisimulationAutomorphism inc where
  toEquiv := automorphism.toEquiv.symm
  map_approxBisim_iff := by
    intro first second
    simpa using (automorphism.map_approxBisim_iff
      (automorphism.toEquiv.symm first) (automorphism.toEquiv.symm second)).symm
  map_resonance_iff := by
    intro left right output
    simpa using (automorphism.map_resonance_iff
      (automorphism.toEquiv.symm left) (automorphism.toEquiv.symm right)
      (automorphism.toEquiv.symm output)).symm

def ResonanceBisimulationAutomorphism.trans
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (first second : ResonanceBisimulationAutomorphism inc) :
    ResonanceBisimulationAutomorphism inc where
  toEquiv := first.toEquiv.trans second.toEquiv
  map_approxBisim_iff := by
    intro left right
    exact (second.map_approxBisim_iff _ _).trans
      (first.map_approxBisim_iff _ _)
  map_resonance_iff := by
    intro left right output
    exact (second.map_resonance_iff _ _ _).trans
      (first.map_resonance_iff _ _ _)

/- These two transitivity lemmas are the non-enumerative group-action input
   needed by the structural obstruction classification.  The distinguished
   vertex `v0` is fixed by every resonance automorphism.  The other two
   vertices form one orbit, while the three edges admit all transpositions. -/
theorem simplex_vertex_pair_automorphism
    {first second : SimplexId}
    (firstVertex : simplexToShape first = .vertex)
    (secondVertex : simplexToShape second = .vertex)
    (distinct : first ≠ second) :
    (first = .v0 ∧ ∃ automorphism :
        ResonanceBisimulationAutomorphism simplexIncidence,
        automorphism.toEquiv first = .v0 ∧
          automorphism.toEquiv second = .v1) ∨
      (second = .v0 ∧ ∃ automorphism :
        ResonanceBisimulationAutomorphism simplexIncidence,
        automorphism.toEquiv first = .v1 ∧
          automorphism.toEquiv second = .v0) ∨
      (first ≠ .v0 ∧ second ≠ .v0 ∧
        ∃ automorphism : ResonanceBisimulationAutomorphism simplexIncidence,
          automorphism.toEquiv first = .v1 ∧
            automorphism.toEquiv second = .v2) := by
  cases first <;> cases second <;>
    simp [simplexToShape] at firstVertex secondVertex distinct ⊢
  · exact ⟨ResonanceBisimulationAutomorphism.refl simplexIncidence,
      rfl, rfl⟩
  · exact ⟨simplexSwapAutomorphism .v2 .v1 (by rfl) (by simp) (by simp),
      by simp [simplexSwapAutomorphism, simplexResonanceAutomorphismOfEquiv,
        Equiv.swap_apply_def],
      by simp [simplexSwapAutomorphism, simplexResonanceAutomorphismOfEquiv]⟩
  · exact ⟨ResonanceBisimulationAutomorphism.refl simplexIncidence,
      rfl, rfl⟩
  · exact ⟨ResonanceBisimulationAutomorphism.refl simplexIncidence,
      rfl, rfl⟩
  · exact ⟨simplexSwapAutomorphism .v1 .v2 (by rfl) (by simp) (by simp),
      by simp [simplexSwapAutomorphism, simplexResonanceAutomorphismOfEquiv],
      by simp [simplexSwapAutomorphism, simplexResonanceAutomorphismOfEquiv,
        Equiv.swap_apply_def]⟩
  · exact ⟨simplexSwapAutomorphism .v1 .v2 (by rfl) (by simp) (by simp),
      by simp [simplexSwapAutomorphism, simplexResonanceAutomorphismOfEquiv],
      by simp [simplexSwapAutomorphism, simplexResonanceAutomorphismOfEquiv]⟩

theorem simplex_edge_pair_automorphism
    {first second : SimplexId}
    (firstEdge : simplexToShape first = .edgeShape)
    (secondEdge : simplexToShape second = .edgeShape)
    (distinct : first ≠ second) :
    ∃ automorphism : ResonanceBisimulationAutomorphism simplexIncidence,
      automorphism.toEquiv first = .e01 ∧
        automorphism.toEquiv second = .e02 := by
  cases first <;> cases second <;>
    simp [simplexToShape] at firstEdge secondEdge distinct ⊢
  · exact ⟨ResonanceBisimulationAutomorphism.refl simplexIncidence,
      rfl, rfl⟩
  · exact ⟨simplexSwapAutomorphism .e02 .e12 (by rfl) (by simp) (by simp),
      by decide, by decide⟩
  · exact ⟨simplexSwapAutomorphism .e01 .e02 (by rfl) (by simp) (by simp),
      by decide, by decide⟩
  · exact ⟨(simplexSwapAutomorphism .e01 .e02 (by rfl) (by simp) (by simp)).trans
        (simplexSwapAutomorphism .e02 .e12 (by rfl) (by simp) (by simp)),
      by decide, by decide⟩
  · exact ⟨(simplexSwapAutomorphism .e01 .e12 (by rfl) (by simp) (by simp)).trans
        (simplexSwapAutomorphism .e02 .e12 (by rfl) (by simp) (by simp)),
      by decide, by decide⟩
  · exact ⟨simplexSwapAutomorphism .e01 .e12 (by rfl) (by simp) (by simp),
      by decide, by decide⟩

theorem ResonanceBisimulationAutomorphism.mapCandidate_isObstruction_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (automorphism : ResonanceBisimulationAutomorphism inc)
    (candidate : LocalResonanceDescentCandidate I) :
    (automorphism.mapCandidate candidate).IsObstruction inc ↔
      candidate.IsObstruction inc := by
  rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
  cases coordinate <;>
    simp only [mapCandidate, LocalResonanceDescentCandidate.IsObstruction,
      automorphism.map_approxBisim_iff, automorphism.map_resonance_iff]

theorem ResonanceBisimulationAutomorphism.mapCandidate_support
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (automorphism : ResonanceBisimulationAutomorphism inc)
    (candidate : LocalResonanceDescentCandidate I) :
    (automorphism.mapCandidate candidate).support =
      candidate.support.image automorphism.toEquiv := by
  ext value
  simp [mapCandidate, LocalResonanceDescentCandidate.support]

theorem ResonanceBisimulationAutomorphism.mapCandidate_support_card
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (automorphism : ResonanceBisimulationAutomorphism inc)
    (candidate : LocalResonanceDescentCandidate I) :
    (automorphism.mapCandidate candidate).support.card =
      candidate.support.card := by
  rw [automorphism.mapCandidate_support]
  apply Finset.card_image_iff.mpr
  exact Set.injOn_of_injective automorphism.toEquiv.injective

theorem ResonanceBisimulationAutomorphism.mapCandidate_supportMinimal
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (automorphism : ResonanceBisimulationAutomorphism inc)
    {candidate : LocalResonanceDescentCandidate I}
    (minimal : candidate.IsSupportMinimalObstruction inc) :
    (automorphism.mapCandidate candidate).IsSupportMinimalObstruction inc := by
  refine ⟨(automorphism.mapCandidate_isObstruction_iff candidate).mpr minimal.1,
    ?_⟩
  rw [automorphism.mapCandidate_support_card]
  exact minimal.2

@[simp] theorem ResonanceBisimulationAutomorphism.refl_mapCandidate
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (candidate : LocalResonanceDescentCandidate I) :
    (ResonanceBisimulationAutomorphism.refl inc).mapCandidate candidate =
      candidate := by
  cases candidate
  rfl

@[simp] theorem ResonanceBisimulationAutomorphism.symm_mapCandidate_mapCandidate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (automorphism : ResonanceBisimulationAutomorphism inc)
    (candidate : LocalResonanceDescentCandidate I) :
    automorphism.symm.mapCandidate (automorphism.mapCandidate candidate) =
      candidate := by
  cases candidate
  simp [mapCandidate, symm]

@[simp] theorem ResonanceBisimulationAutomorphism.trans_mapCandidate
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (first second : ResonanceBisimulationAutomorphism inc)
    (candidate : LocalResonanceDescentCandidate I) :
    (first.trans second).mapCandidate candidate =
      second.mapCandidate (first.mapCandidate candidate) := by
  rfl

def LocalResonanceDescentCandidate.AutomorphismRelated
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (first second : LocalResonanceDescentCandidate I) : Prop :=
  ∃ automorphism : ResonanceBisimulationAutomorphism inc,
    automorphism.mapCandidate first = second

theorem LocalResonanceDescentCandidate.automorphismRelated_equivalence
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    Equivalence
      (LocalResonanceDescentCandidate.AutomorphismRelated inc) := by
  constructor
  · intro candidate
    exact ⟨ResonanceBisimulationAutomorphism.refl inc,
      ResonanceBisimulationAutomorphism.refl_mapCandidate inc candidate⟩
  · intro first second related
    rcases related with ⟨automorphism, rfl⟩
    exact ⟨automorphism.symm,
      automorphism.symm_mapCandidate_mapCandidate first⟩
  · intro first second third firstSecond secondThird
    rcases firstSecond with ⟨firstAutomorphism, rfl⟩
    rcases secondThird with ⟨secondAutomorphism, rfl⟩
    exact ⟨firstAutomorphism.trans secondAutomorphism,
      firstAutomorphism.trans_mapCandidate secondAutomorphism first⟩

def localResonanceAutomorphismSetoid
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    Setoid (LocalResonanceDescentCandidate I) where
  r := LocalResonanceDescentCandidate.AutomorphismRelated inc
  iseqv := LocalResonanceDescentCandidate.automorphismRelated_equivalence inc

abbrev LocalResonanceAutomorphismOrbit
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :=
  Quotient (localResonanceAutomorphismSetoid inc)

def LocalResonanceAutomorphismOrbit.IsObstruction
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    LocalResonanceAutomorphismOrbit inc → Prop :=
  Quotient.lift (LocalResonanceDescentCandidate.IsObstruction inc) (by
    intro first second related
    rcases related with ⟨automorphism, rfl⟩
    apply propext
    exact (automorphism.mapCandidate_isObstruction_iff first).symm)

theorem exact_descent_iff_no_automorphism_obstruction_orbit
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      ¬ ∃ orbit : LocalResonanceAutomorphismOrbit inc,
        orbit.IsObstruction inc := by
  constructor
  · intro descent
    have coordinatewise :=
      (resonanceRelationDescendsExactly_iff_coordinatewise inc).mp descent
    rintro ⟨orbit, obstruction⟩
    induction orbit using Quotient.ind with
    | _ candidate =>
      rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
      cases coordinate with
      | left => exact obstruction.2 (coordinatewise.1 obstruction.1)
      | right => exact obstruction.2 (coordinatewise.2.1 obstruction.1)
      | output => exact obstruction.2 (coordinatewise.2.2 obstruction.1)
  · intro noOrbit
    rw [resonanceRelationDescendsExactly_iff_coordinatewise]
    refine ⟨?_, ?_, ?_⟩
    · intro first second fixed₁ fixed₂ related
      by_cases exactRelation :
          inc.resonance first fixed₁ fixed₂ ↔
            inc.resonance second fixed₁ fixed₂
      · exact exactRelation
      · exact False.elim (noOrbit ⟨Quotient.mk _
          ⟨.left, first, second, fixed₁, fixed₂⟩, ⟨related, exactRelation⟩⟩)
    · intro fixed₁ first second fixed₂ related
      by_cases exactRelation :
          inc.resonance fixed₁ first fixed₂ ↔
            inc.resonance fixed₁ second fixed₂
      · exact exactRelation
      · exact False.elim (noOrbit ⟨Quotient.mk _
          ⟨.right, first, second, fixed₁, fixed₂⟩, ⟨related, exactRelation⟩⟩)
    · intro fixed₁ fixed₂ first second related
      by_cases exactRelation :
          inc.resonance fixed₁ fixed₂ first ↔
            inc.resonance fixed₁ fixed₂ second
      · exact exactRelation
      · exact False.elim (noOrbit ⟨Quotient.mk _
          ⟨.output, first, second, fixed₁, fixed₂⟩, ⟨related, exactRelation⟩⟩)

/- For finite, decidable models the abstract automorphism quotient has an
   executable presentation: enumerate all permutations, retain exactly those
   preserving bisimulation and resonance, then image each certificate. -/
def IsResonanceBisimulationAutomorphismEquiv
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (equiv : I ≃ I) : Prop :=
  (∀ first second,
    (approxBisim inc (equiv first) (equiv second) ↔
      approxBisim inc first second)) ∧
  (∀ left right output,
    (inc.resonance (equiv left) (equiv right) (equiv output) ↔
      inc.resonance left right output))

def resonanceBisimulationAutomorphismEquivCheck
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (equiv : I ≃ I) : Bool := by
  letI bisimDecision : Decidable
      (∀ first second,
        (approxBisim inc (equiv first) (equiv second) ↔
          approxBisim inc first second)) :=
    Fintype.decidableForallFintype
  letI resonanceDecision : Decidable
      (∀ left right output,
        (inc.resonance (equiv left) (equiv right) (equiv output) ↔
          inc.resonance left right output)) :=
    Fintype.decidableForallFintype
  letI fullDecision : Decidable
      (IsResonanceBisimulationAutomorphismEquiv inc equiv) :=
    decidable_of_iff
      ((∀ first second,
          (approxBisim inc (equiv first) (equiv second) ↔
            approxBisim inc first second)) ∧
        (∀ left right output,
          (inc.resonance (equiv left) (equiv right) (equiv output) ↔
            inc.resonance left right output))) Iff.rfl
  exact decide (IsResonanceBisimulationAutomorphismEquiv inc equiv)

theorem resonanceBisimulationAutomorphismEquivCheck_eq_true_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (equiv : I ≃ I) :
    resonanceBisimulationAutomorphismEquivCheck inc equiv = true ↔
      IsResonanceBisimulationAutomorphismEquiv inc equiv := by
  simp [resonanceBisimulationAutomorphismEquivCheck,
    IsResonanceBisimulationAutomorphismEquiv]

def finiteResonanceBisimulationAutomorphisms
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)] :
    Finset (I ≃ I) :=
  Finset.univ.filter fun equiv =>
    resonanceBisimulationAutomorphismEquivCheck inc equiv

theorem mem_finiteResonanceBisimulationAutomorphisms_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (equiv : I ≃ I) :
    equiv ∈ finiteResonanceBisimulationAutomorphisms inc ↔
      IsResonanceBisimulationAutomorphismEquiv inc equiv := by
  simp [finiteResonanceBisimulationAutomorphisms,
    resonanceBisimulationAutomorphismEquivCheck_eq_true_iff]

def resonanceBisimulationAutomorphismOfEquiv
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {equiv : I ≃ I}
    (preserves : IsResonanceBisimulationAutomorphismEquiv inc equiv) :
    ResonanceBisimulationAutomorphism inc where
  toEquiv := equiv
  map_approxBisim_iff := preserves.1
  map_resonance_iff := preserves.2

def mapLocalResonanceCandidateEquiv
    {I : Type u} (equiv : I ≃ I)
    (candidate : LocalResonanceDescentCandidate I) :
    LocalResonanceDescentCandidate I :=
  ⟨candidate.coordinate, equiv candidate.first, equiv candidate.second,
    equiv candidate.fixed₁, equiv candidate.fixed₂⟩

theorem mapLocalResonanceCandidateEquiv_eq
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    {equiv : I ≃ I}
    (preserves : IsResonanceBisimulationAutomorphismEquiv inc equiv)
    (candidate : LocalResonanceDescentCandidate I) :
    mapLocalResonanceCandidateEquiv equiv candidate =
      (resonanceBisimulationAutomorphismOfEquiv preserves).mapCandidate
        candidate := by
  rfl

def finiteLocalResonanceAutomorphismOrbit
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (candidate : LocalResonanceDescentCandidate I) :
    Finset (LocalResonanceDescentCandidate I) :=
  (finiteResonanceBisimulationAutomorphisms inc).image
    (fun equiv => mapLocalResonanceCandidateEquiv equiv candidate)

theorem mem_finiteLocalResonanceAutomorphismOrbit_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (first second : LocalResonanceDescentCandidate I) :
    second ∈ finiteLocalResonanceAutomorphismOrbit inc first ↔
      first.AutomorphismRelated inc second := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨equiv, equivMem, rfl⟩
    have preserves :=
      (mem_finiteResonanceBisimulationAutomorphisms_iff inc equiv).mp equivMem
    exact ⟨resonanceBisimulationAutomorphismOfEquiv preserves, rfl⟩
  · rintro ⟨automorphism, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨automorphism.toEquiv, ?_, rfl⟩
    apply (mem_finiteResonanceBisimulationAutomorphisms_iff
      inc automorphism.toEquiv).mpr
    exact ⟨automorphism.map_approxBisim_iff,
      automorphism.map_resonance_iff⟩

theorem finiteLocalResonanceAutomorphismOrbit_eq_of_related
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    {first second : LocalResonanceDescentCandidate I}
    (related : first.AutomorphismRelated inc second) :
    finiteLocalResonanceAutomorphismOrbit inc first =
      finiteLocalResonanceAutomorphismOrbit inc second := by
  ext candidate
  rw [mem_finiteLocalResonanceAutomorphismOrbit_iff,
    mem_finiteLocalResonanceAutomorphismOrbit_iff]
  constructor
  · intro firstRelated
    have equivalence :=
      LocalResonanceDescentCandidate.automorphismRelated_equivalence inc
    exact equivalence.trans (equivalence.symm related) firstRelated
  · intro secondRelated
    have equivalence :=
      LocalResonanceDescentCandidate.automorphismRelated_equivalence inc
    exact equivalence.trans related secondRelated

def localResonanceObstructionCheck
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (candidate : LocalResonanceDescentCandidate I) : Bool :=
  decide (approxBisim inc candidate.first candidate.second) &&
    match candidate.coordinate with
    | .left => decide (¬ (inc.resonance candidate.first candidate.fixed₁
          candidate.fixed₂ ↔
        inc.resonance candidate.second candidate.fixed₁ candidate.fixed₂))
    | .right => decide (¬ (inc.resonance candidate.fixed₁ candidate.first
          candidate.fixed₂ ↔
        inc.resonance candidate.fixed₁ candidate.second candidate.fixed₂))
    | .output => decide (¬ (inc.resonance candidate.fixed₁ candidate.fixed₂
          candidate.first ↔
        inc.resonance candidate.fixed₁ candidate.fixed₂ candidate.second))

theorem localResonanceObstructionCheck_eq_true_iff
    {I R T : Type u} [DecidableEq I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (candidate : LocalResonanceDescentCandidate I) :
    localResonanceObstructionCheck inc candidate = true ↔
      candidate.IsObstruction inc := by
  rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
  cases coordinate <;>
    simp [localResonanceObstructionCheck,
      LocalResonanceDescentCandidate.IsObstruction]

def supportMinimalObstructionCheck
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (candidate : LocalResonanceDescentCandidate I) : Bool := by
  letI obstructionDecision (other : LocalResonanceDescentCandidate I) :
      Decidable (other.IsObstruction inc) :=
    decidable_of_iff (localResonanceObstructionCheck inc other = true)
      (localResonanceObstructionCheck_eq_true_iff inc other)
  letI minimalDecision : Decidable
      (∀ other : LocalResonanceDescentCandidate I,
        other.IsObstruction inc →
          candidate.support.card ≤ other.support.card) :=
    Fintype.decidableForallFintype
  letI fullDecision : Decidable
      (candidate.IsSupportMinimalObstruction inc) :=
    decidable_of_iff
      (candidate.IsObstruction inc ∧
        ∀ other : LocalResonanceDescentCandidate I,
          other.IsObstruction inc →
            candidate.support.card ≤ other.support.card) Iff.rfl
  exact decide (candidate.IsSupportMinimalObstruction inc)

theorem supportMinimalObstructionCheck_eq_true_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (candidate : LocalResonanceDescentCandidate I) :
    supportMinimalObstructionCheck inc candidate = true ↔
      candidate.IsSupportMinimalObstruction inc := by
  simp [supportMinimalObstructionCheck]

def finiteSupportMinimalObstructionOrbits
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)] :
    Finset (Finset (LocalResonanceDescentCandidate I)) :=
  (Finset.univ.filter fun candidate =>
      supportMinimalObstructionCheck inc candidate).image
    (finiteLocalResonanceAutomorphismOrbit inc)

theorem mem_finiteSupportMinimalObstructionOrbits_iff
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)]
    (orbit : Finset (LocalResonanceDescentCandidate I)) :
    orbit ∈ finiteSupportMinimalObstructionOrbits inc ↔
      ∃ candidate, candidate.IsSupportMinimalObstruction inc ∧
        orbit = finiteLocalResonanceAutomorphismOrbit inc candidate := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨candidate, candidateMem, rfl⟩
    exact ⟨candidate,
      (supportMinimalObstructionCheck_eq_true_iff inc candidate).mp
        (Finset.mem_filter.mp candidateMem).2,
      rfl⟩
  · rintro ⟨candidate, minimal, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨candidate, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (supportMinimalObstructionCheck_eq_true_iff inc candidate).mpr minimal⟩,
      rfl⟩

theorem finiteSupportMinimalObstructionOrbits_empty_iff_exactDescent
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)] :
    finiteSupportMinimalObstructionOrbits inc = ∅ ↔
      ResonanceRelationDescendsExactly inc := by
  constructor
  · intro empty
    by_contra failure
    rcases exists_supportMinimalObstruction_of_not_exact_descent inc failure with
      ⟨candidate, minimal⟩
    have member : finiteLocalResonanceAutomorphismOrbit inc candidate ∈
        finiteSupportMinimalObstructionOrbits inc :=
      (mem_finiteSupportMinimalObstructionOrbits_iff inc _).mpr
        ⟨candidate, minimal, rfl⟩
    rw [empty] at member
    simp at member
  · intro descent
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro orbit member
    rcases (mem_finiteSupportMinimalObstructionOrbits_iff inc orbit).mp member with
      ⟨candidate, minimal, rfl⟩
    have coordinatewise :=
      (resonanceRelationDescendsExactly_iff_coordinatewise inc).mp descent
    rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
    cases coordinate with
    | left => exact minimal.1.2 (coordinatewise.1 minimal.1.1)
    | right => exact minimal.1.2 (coordinatewise.2.1 minimal.1.1)
    | output => exact minimal.1.2 (coordinatewise.2.2 minimal.1.1)

theorem finiteSupportMinimalObstructionOrbits_nonempty_iff_failure
    {I R T : Type u} [DecidableEq I] [Fintype I]
    (inc : Incidence I R T)
    [DecidableRel (approxBisim inc)]
    [∀ left right output, Decidable (inc.resonance left right output)] :
    (finiteSupportMinimalObstructionOrbits inc).Nonempty ↔
      ¬ ResonanceRelationDescendsExactly inc := by
  constructor
  · intro nonempty descent
    have empty :=
      (finiteSupportMinimalObstructionOrbits_empty_iff_exactDescent inc).mpr
        descent
    rw [empty] at nonempty
    exact Finset.not_nonempty_empty nonempty
  · intro failure
    apply Finset.nonempty_iff_ne_empty.mpr
    intro empty
    exact failure
      ((finiteSupportMinimalObstructionOrbits_empty_iff_exactDescent inc).mp
        empty)

def simplexApproxBisimDecidable :
    DecidableRel (approxBisim simplexIncidence) :=
  fun first second =>
    decidable_of_iff (simplexToShape first = simplexToShape second)
      (simplexToShape_iff_approxBisim first second)

def simplexResonanceDecidable :
    ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
  fun left right output =>
    decidable_of_iff
      ((if left = SimplexId.v0 then some right else some left) = some output)
      Iff.rfl

def simplexFiniteSupportMinimalObstructionOrbits :
    Finset (Finset (LocalResonanceDescentCandidate SimplexId)) := by
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  exact finiteSupportMinimalObstructionOrbits simplexIncidence

theorem simplexTwoVertexOrbit_mem_finiteMinimalOrbits :
    (by
      letI : DecidableRel (approxBisim simplexIncidence) :=
        simplexApproxBisimDecidable
      letI : ∀ left right output,
          Decidable (simplexIncidence.resonance left right output) :=
        simplexResonanceDecidable
      exact finiteLocalResonanceAutomorphismOrbit simplexIncidence
        simplexTwoVertexLocalObstruction) ∈
      simplexFiniteSupportMinimalObstructionOrbits := by
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  apply (mem_finiteSupportMinimalObstructionOrbits_iff simplexIncidence _).mpr
  exact ⟨simplexTwoVertexLocalObstruction,
    simplexTwoVertexLocalObstruction_isSupportMinimal, rfl⟩

theorem simplexFiniteSupportMinimalObstructionOrbits_nonempty :
    simplexFiniteSupportMinimalObstructionOrbits.Nonempty := by
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  exact (finiteSupportMinimalObstructionOrbits_nonempty_iff_failure
    simplexIncidence).mpr simplexIncidence_has_no_exact_resonance_descent

def simplexFiniteAutomorphismCount : Nat := by
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  exact (finiteResonanceBisimulationAutomorphisms simplexIncidence).card

theorem simplex_finite_automorphism_count :
    simplexFiniteAutomorphismCount = 12 := by
  native_decide

theorem simplex_minimal_obstruction_orbit_count_computed :
    simplexFiniteSupportMinimalObstructionOrbits.card = 32 := by
  native_decide

/- The 32 computed orbits admit a short structural taxonomy.  A family records
   the varying coordinate together with the shapes of the two fixed slots.
   Only five combinations occur for support-minimal simplex obstructions. -/
inductive SimplexMinimalObstructionFamily where
  | leftVertexVertex
  | leftEdgeEdge
  | rightVertexVertex
  | outputVertexVertex
  | outputEdgeEdge
deriving DecidableEq, Repr

instance simplexMinimalObstructionFamilyFintype :
    Fintype SimplexMinimalObstructionFamily :=
  ⟨{.leftVertexVertex, .leftEdgeEdge, .rightVertexVertex,
      .outputVertexVertex, .outputEdgeEdge}, by
    intro family
    cases family <;> simp⟩

def simplexMinimalObstructionFamilyOfCandidate
    (candidate : LocalResonanceDescentCandidate SimplexId) :
    Option SimplexMinimalObstructionFamily :=
  match candidate.coordinate, simplexToShape candidate.fixed₁,
      simplexToShape candidate.fixed₂ with
  | .left, .vertex, .vertex => some .leftVertexVertex
  | .left, .edgeShape, .edgeShape => some .leftEdgeEdge
  | .right, .vertex, .vertex => some .rightVertexVertex
  | .output, .vertex, .vertex => some .outputVertexVertex
  | .output, .edgeShape, .edgeShape => some .outputEdgeEdge
  | _, _, _ => none

def simplexMinimalObstructionOrbitsOfFamily
    (family : SimplexMinimalObstructionFamily) :
    Finset (Finset (LocalResonanceDescentCandidate SimplexId)) :=
  simplexFiniteSupportMinimalObstructionOrbits.filter fun orbit =>
    ∃ candidate ∈ orbit,
      simplexMinimalObstructionFamilyOfCandidate candidate = some family

def simplexMinimalObstructionFamilyCounts :
    SimplexMinimalObstructionFamily → Nat
  | .leftVertexVertex => 8
  | .leftEdgeEdge => 4
  | .rightVertexVertex => 4
  | .outputVertexVertex => 12
  | .outputEdgeEdge => 4

theorem simplex_minimal_obstruction_family_count
    (family : SimplexMinimalObstructionFamily) :
    (simplexMinimalObstructionOrbitsOfFamily family).card =
      simplexMinimalObstructionFamilyCounts family := by
  have allFamilies : ∀ family : SimplexMinimalObstructionFamily,
      (simplexMinimalObstructionOrbitsOfFamily family).card =
        simplexMinimalObstructionFamilyCounts family := by
    native_decide
  exact allFamilies family

theorem simplex_minimal_obstruction_family_partition :
    Finset.univ.biUnion simplexMinimalObstructionOrbitsOfFamily =
      simplexFiniteSupportMinimalObstructionOrbits := by
  native_decide

theorem simplex_minimal_obstruction_family_count_sum :
    simplexMinimalObstructionFamilyCounts .leftVertexVertex +
      simplexMinimalObstructionFamilyCounts .leftEdgeEdge +
      simplexMinimalObstructionFamilyCounts .rightVertexVertex +
      simplexMinimalObstructionFamilyCounts .outputVertexVertex +
      simplexMinimalObstructionFamilyCounts .outputEdgeEdge = 32 := by
  native_decide

/- A non-enumerative count predicted by the orbit structure.  Resonance
   automorphisms fix `v0`, act transitively on `{v1,v2}`, and act transitively
   on ordered pairs of distinct edges.  Hence ordered distinct vertex pairs
   have three orbit types: `(v0,x)`, `(x,v0)`, and `(v1,v2)`; edge pairs have
   one.  With support exactly `{first,second}`, the two fixed slots have four
   binary equality patterns.  The selector equation removes the patterns
   recorded in the five formulas below. -/
def simplexLeftVertexStructuralOrbitCount : Nat := 2 + 2 + 4
def simplexLeftEdgeStructuralOrbitCount : Nat := 4
def simplexRightVertexStructuralOrbitCount : Nat := 2 + 2
def simplexOutputVertexStructuralOrbitCount : Nat := 3 * 4
def simplexOutputEdgeStructuralOrbitCount : Nat := 4

theorem simplex_structural_family_orbit_counts :
    simplexLeftVertexStructuralOrbitCount = 8 ∧
      simplexLeftEdgeStructuralOrbitCount = 4 ∧
      simplexRightVertexStructuralOrbitCount = 4 ∧
      simplexOutputVertexStructuralOrbitCount = 12 ∧
      simplexOutputEdgeStructuralOrbitCount = 4 := by
  decide

theorem simplex_structural_orbit_count :
    simplexLeftVertexStructuralOrbitCount +
      simplexLeftEdgeStructuralOrbitCount +
      simplexRightVertexStructuralOrbitCount +
      simplexOutputVertexStructuralOrbitCount +
      simplexOutputEdgeStructuralOrbitCount = 32 := by
  decide

/- An explicit finite parameter space for the structural count.  The first
   three summands are the three left/vertex ordered-pair cases, followed by
   left/edge, the two right/vertex cases, output/vertex, and output/edge. -/
abbrev SimplexStructuralObstructionOrbitParameter :=
  Fin 2 ⊕ Fin 2 ⊕ Fin 4 ⊕ Fin 4 ⊕ Fin 2 ⊕ Fin 2 ⊕
    (Fin 3 × Fin 4) ⊕ Fin 4

def simplexLeftVertexUnitFirstParameter (choice : Fin 2) :
    SimplexStructuralObstructionOrbitParameter := .inl choice

def simplexLeftVertexUnitSecondParameter (choice : Fin 2) :
    SimplexStructuralObstructionOrbitParameter := .inr (.inl choice)

def simplexLeftVertexNonunitParameter (pattern : Fin 4) :
    SimplexStructuralObstructionOrbitParameter := .inr (.inr (.inl pattern))

def simplexLeftEdgeParameter (pattern : Fin 4) :
    SimplexStructuralObstructionOrbitParameter :=
  .inr (.inr (.inr (.inl pattern)))

def simplexRightVertexUnitFirstParameter (choice : Fin 2) :
    SimplexStructuralObstructionOrbitParameter :=
  .inr (.inr (.inr (.inr (.inl choice))))

def simplexRightVertexUnitSecondParameter (choice : Fin 2) :
    SimplexStructuralObstructionOrbitParameter :=
  .inr (.inr (.inr (.inr (.inr (.inl choice)))))

def simplexOutputVertexParameter (pairCase : Fin 3) (pattern : Fin 4) :
    SimplexStructuralObstructionOrbitParameter :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (pairCase, pattern)))))))

def simplexOutputEdgeParameter (pattern : Fin 4) :
    SimplexStructuralObstructionOrbitParameter :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr pattern))))))

theorem simplex_structural_orbit_parameter_card :
    Fintype.card SimplexStructuralObstructionOrbitParameter = 32 := by
  simp [SimplexStructuralObstructionOrbitParameter]

def simplexChooseRepresentative
    (first second : SimplexId) (choice : Fin 2) : SimplexId :=
  if choice.val = 0 then first else second

def simplexFixedSlotPattern
    (first second : SimplexId) (pattern : Fin 4) : SimplexId × SimplexId :=
  (simplexChooseRepresentative first second ⟨pattern.val / 2, by omega⟩,
    simplexChooseRepresentative first second ⟨pattern.val % 2, by omega⟩)

theorem simplexChooseRepresentative_mem_pair
    (first second : SimplexId) (choice : Fin 2) :
    simplexChooseRepresentative first second choice = first ∨
      simplexChooseRepresentative first second choice = second := by
  unfold simplexChooseRepresentative
  split <;> simp

theorem simplexFixedSlotPattern_mem_pair
    (first second : SimplexId) (pattern : Fin 4) :
    ((simplexFixedSlotPattern first second pattern).1 = first ∨
        (simplexFixedSlotPattern first second pattern).1 = second) ∧
      ((simplexFixedSlotPattern first second pattern).2 = first ∨
        (simplexFixedSlotPattern first second pattern).2 = second) := by
  constructor
  · exact simplexChooseRepresentative_mem_pair first second _
  · exact simplexChooseRepresentative_mem_pair first second _

theorem exists_simplexChooseRepresentative_eq_of_mem_pair
    {first second value : SimplexId}
    (member : value = first ∨ value = second) :
    ∃ choice : Fin 2,
      simplexChooseRepresentative first second choice = value := by
  rcases member with rfl | rfl
  · exact ⟨0, by simp [simplexChooseRepresentative]⟩
  · exact ⟨1, by simp [simplexChooseRepresentative]⟩

theorem exists_simplexFixedSlotPattern_eq_of_mem_pair
    {first second fixed₁ fixed₂ : SimplexId}
    (fixed₁Member : fixed₁ = first ∨ fixed₁ = second)
    (fixed₂Member : fixed₂ = first ∨ fixed₂ = second) :
    ∃ pattern : Fin 4,
      simplexFixedSlotPattern first second pattern = (fixed₁, fixed₂) := by
  rcases fixed₁Member with rfl | rfl <;>
    rcases fixed₂Member with rfl | rfl
  · exact ⟨0, by simp [simplexFixedSlotPattern,
      simplexChooseRepresentative]⟩
  · exact ⟨1, by simp [simplexFixedSlotPattern,
      simplexChooseRepresentative]⟩
  · exact ⟨2, by simp [simplexFixedSlotPattern,
      simplexChooseRepresentative]⟩
  · exact ⟨3, by simp [simplexFixedSlotPattern,
      simplexChooseRepresentative]⟩

def simplexStructuralCanonicalCandidate :
    SimplexStructuralObstructionOrbitParameter →
      LocalResonanceDescentCandidate SimplexId
  | .inl outputChoice =>
      ⟨.left, .v0, .v1, .v0,
        simplexChooseRepresentative .v0 .v1 outputChoice⟩
  | .inr (.inl outputChoice) =>
      ⟨.left, .v1, .v0, .v0,
        simplexChooseRepresentative .v1 .v0 outputChoice⟩
  | .inr (.inr (.inl pattern)) =>
      let fixed := simplexFixedSlotPattern .v1 .v2 pattern
      ⟨.left, .v1, .v2, fixed.1, fixed.2⟩
  | .inr (.inr (.inr (.inl pattern))) =>
      let fixed := simplexFixedSlotPattern .e01 .e02 pattern
      ⟨.left, .e01, .e02, fixed.1, fixed.2⟩
  | .inr (.inr (.inr (.inr (.inl outputChoice)))) =>
      ⟨.right, .v0, .v1, .v0,
        simplexChooseRepresentative .v0 .v1 outputChoice⟩
  | .inr (.inr (.inr (.inr (.inr (.inl outputChoice))))) =>
      ⟨.right, .v1, .v0, .v0,
        simplexChooseRepresentative .v1 .v0 outputChoice⟩
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl pairAndPattern)))))) =>
      let pair : SimplexId × SimplexId :=
        if pairAndPattern.1.val = 0 then (.v0, .v1)
        else if pairAndPattern.1.val = 1 then (.v1, .v0)
        else (.v1, .v2)
      let fixed := simplexFixedSlotPattern pair.1 pair.2 pairAndPattern.2
      ⟨.output, pair.1, pair.2, fixed.1, fixed.2⟩
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr pattern)))))) =>
      let fixed := simplexFixedSlotPattern .e01 .e02 pattern
      ⟨.output, .e01, .e02, fixed.1, fixed.2⟩

theorem simplexStructuralCanonicalCandidate_fixedSlots_mem_pair
    (parameter : SimplexStructuralObstructionOrbitParameter) :
    let candidate := simplexStructuralCanonicalCandidate parameter
    (candidate.fixed₁ = candidate.first ∨
        candidate.fixed₁ = candidate.second) ∧
      (candidate.fixed₂ = candidate.first ∨
        candidate.fixed₂ = candidate.second) := by
  rcases parameter with parameter | parameter
  · simp [simplexStructuralCanonicalCandidate,
      simplexChooseRepresentative_mem_pair]
  · rcases parameter with parameter | parameter
    · simp [simplexStructuralCanonicalCandidate,
        simplexChooseRepresentative_mem_pair]
    · rcases parameter with parameter | parameter
      · simpa [simplexStructuralCanonicalCandidate] using
          simplexFixedSlotPattern_mem_pair .v1 .v2 parameter
      · rcases parameter with parameter | parameter
        · simpa [simplexStructuralCanonicalCandidate] using
            simplexFixedSlotPattern_mem_pair .e01 .e02 parameter
        · rcases parameter with parameter | parameter
          · simp [simplexStructuralCanonicalCandidate,
              simplexChooseRepresentative_mem_pair]
          · rcases parameter with parameter | parameter
            · simp [simplexStructuralCanonicalCandidate,
                simplexChooseRepresentative_mem_pair]
            · rcases parameter with parameter | parameter
              · simpa [simplexStructuralCanonicalCandidate] using
                  simplexFixedSlotPattern_mem_pair
                    (if parameter.1.val = 0 then
                        (SimplexId.v0, SimplexId.v1)
                      else if parameter.1.val = 1 then
                        (SimplexId.v1, SimplexId.v0)
                      else (SimplexId.v1, SimplexId.v2)).1
                    (if parameter.1.val = 0 then
                        (SimplexId.v0, SimplexId.v1)
                      else if parameter.1.val = 1 then
                        (SimplexId.v1, SimplexId.v0)
                      else (SimplexId.v1, SimplexId.v2)).2
                    parameter.2
              · simpa [simplexStructuralCanonicalCandidate] using
                  simplexFixedSlotPattern_mem_pair .e01 .e02 parameter

def simplexStructuralCanonicalOrbit
    (parameter : SimplexStructuralObstructionOrbitParameter) :
    Finset (LocalResonanceDescentCandidate SimplexId) := by
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  exact finiteLocalResonanceAutomorphismOrbit simplexIncidence
    (simplexStructuralCanonicalCandidate parameter)

theorem simplexStructuralCanonicalCandidate_mem_orbit
    (parameter : SimplexStructuralObstructionOrbitParameter) :
    simplexStructuralCanonicalCandidate parameter ∈
      simplexStructuralCanonicalOrbit parameter := by
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  apply (mem_finiteLocalResonanceAutomorphismOrbit_iff simplexIncidence
    (simplexStructuralCanonicalCandidate parameter)
    (simplexStructuralCanonicalCandidate parameter)).mpr
  exact ⟨ResonanceBisimulationAutomorphism.refl simplexIncidence,
    ResonanceBisimulationAutomorphism.refl_mapCandidate simplexIncidence _⟩



theorem simplex_computed_orbit_count_agrees_with_structural_count :
    simplexFiniteSupportMinimalObstructionOrbits.card =
      simplexLeftVertexStructuralOrbitCount +
        simplexLeftEdgeStructuralOrbitCount +
        simplexRightVertexStructuralOrbitCount +
        simplexOutputVertexStructuralOrbitCount +
        simplexOutputEdgeStructuralOrbitCount := by
  rw [simplex_minimal_obstruction_orbit_count_computed,
    simplex_structural_orbit_count]

/- Within the five coarse families, an orbit is completely identified by the
   following coordinate normal form.  Besides shapes it records whether an
   ordered representative is the distinguished selector unit `v0`, and the
   equality pattern of the two fixed slots against the ordered pair. -/
structure SimplexMinimalObstructionNormalForm where
  coordinate : ResonanceCoordinate
  varyingShape : SimplexShape
  fixed₁Shape : SimplexShape
  fixed₂Shape : SimplexShape
  firstIsV0 : Bool
  secondIsV0 : Bool
  fixed₁IsFirst : Bool
  fixed₁IsSecond : Bool
  fixed₂IsFirst : Bool
  fixed₂IsSecond : Bool
  fixedSlotsEqual : Bool
deriving DecidableEq, Repr

def simplexMinimalObstructionNormalForm
    (candidate : LocalResonanceDescentCandidate SimplexId) :
    SimplexMinimalObstructionNormalForm where
  coordinate := candidate.coordinate
  varyingShape := simplexToShape candidate.first
  fixed₁Shape := simplexToShape candidate.fixed₁
  fixed₂Shape := simplexToShape candidate.fixed₂
  firstIsV0 := decide (candidate.first = .v0)
  secondIsV0 := decide (candidate.second = .v0)
  fixed₁IsFirst := decide (candidate.fixed₁ = candidate.first)
  fixed₁IsSecond := decide (candidate.fixed₁ = candidate.second)
  fixed₂IsFirst := decide (candidate.fixed₂ = candidate.first)
  fixed₂IsSecond := decide (candidate.fixed₂ = candidate.second)
  fixedSlotsEqual := decide (candidate.fixed₁ = candidate.fixed₂)

def simplexMinimalObstructionNormalForms :
    Finset SimplexMinimalObstructionNormalForm :=
  simplexFiniteSupportMinimalObstructionOrbits.biUnion fun orbit =>
    orbit.image simplexMinimalObstructionNormalForm

def simplexMinimalObstructionNonconstantNormalFormOrbits :
    Finset (Finset (LocalResonanceDescentCandidate SimplexId)) :=
  simplexFiniteSupportMinimalObstructionOrbits.filter fun orbit =>
    (orbit.image simplexMinimalObstructionNormalForm).card ≠ 1

def simplexMinimalObstructionNormalFormCollisions :
    Finset ((Finset (LocalResonanceDescentCandidate SimplexId)) ×
      Finset (LocalResonanceDescentCandidate SimplexId)) :=
  (simplexFiniteSupportMinimalObstructionOrbits ×ˢ
      simplexFiniteSupportMinimalObstructionOrbits).filter fun pair =>
    pair.1 ≠ pair.2 ∧
      ((pair.1.image simplexMinimalObstructionNormalForm) ∩
        (pair.2.image simplexMinimalObstructionNormalForm)).Nonempty

theorem simplex_minimal_obstruction_normal_form_classification :
    simplexMinimalObstructionNormalForms.card = 32 ∧
      simplexMinimalObstructionNonconstantNormalFormOrbits = ∅ ∧
      simplexMinimalObstructionNormalFormCollisions = ∅ := by
  native_decide

theorem simplex_minimal_obstruction_normal_form_count :
    simplexMinimalObstructionNormalForms.card = 32 :=
  simplex_minimal_obstruction_normal_form_classification.1

theorem simplex_minimal_obstruction_normal_form_constant_on_orbits :
    simplexMinimalObstructionNonconstantNormalFormOrbits = ∅ :=
  simplex_minimal_obstruction_normal_form_classification.2.1

theorem simplex_minimal_obstruction_normal_form_separates_orbits :
    simplexMinimalObstructionNormalFormCollisions = ∅ :=
  simplex_minimal_obstruction_normal_form_classification.2.2

theorem simplexStructuralCanonicalNormalForm_injective :
    Function.Injective (fun parameter :
      SimplexStructuralObstructionOrbitParameter =>
        simplexMinimalObstructionNormalForm
          (simplexStructuralCanonicalCandidate parameter)) := by
  native_decide

theorem simplex_minimal_orbit_normalForm_eq
    {orbit : Finset (LocalResonanceDescentCandidate SimplexId)}
    (orbitMem : orbit ∈ simplexFiniteSupportMinimalObstructionOrbits)
    {first second : LocalResonanceDescentCandidate SimplexId}
    (firstMem : first ∈ orbit) (secondMem : second ∈ orbit) :
    simplexMinimalObstructionNormalForm first =
      simplexMinimalObstructionNormalForm second := by
  have imageCard : (orbit.image simplexMinimalObstructionNormalForm).card = 1 := by
    by_contra notOne
    have member : orbit ∈
        simplexMinimalObstructionNonconstantNormalFormOrbits :=
      Finset.mem_filter.mpr ⟨orbitMem, notOne⟩
    rw [simplex_minimal_obstruction_normal_form_constant_on_orbits] at member
    simp at member
  rcases Finset.card_eq_one.mp imageCard with ⟨normalForm, imageEq⟩
  have firstImage : simplexMinimalObstructionNormalForm first ∈
      orbit.image simplexMinimalObstructionNormalForm :=
    Finset.mem_image.mpr ⟨first, firstMem, rfl⟩
  have secondImage : simplexMinimalObstructionNormalForm second ∈
      orbit.image simplexMinimalObstructionNormalForm :=
    Finset.mem_image.mpr ⟨second, secondMem, rfl⟩
  have firstEq : simplexMinimalObstructionNormalForm first = normalForm := by
    rw [imageEq] at firstImage
    simpa using firstImage
  have secondEq : simplexMinimalObstructionNormalForm second = normalForm := by
    rw [imageEq] at secondImage
    simpa using secondImage
  exact firstEq.trans secondEq.symm


/- The algebraic core of a free incidence.  `none` is the unit; non-unit
   elements are binary trees over generators.  This representation enforces
   the unit equations by construction rather than quotienting raw syntax. -/
inductive FreeIncidenceAtom (Generator : Type u) where
  | generator : Generator → FreeIncidenceAtom Generator
  | glue : FreeIncidenceAtom Generator → FreeIncidenceAtom Generator →
      FreeIncidenceAtom Generator
deriving DecidableEq

abbrev FreeIncidenceTerm (Generator : Type u) :=
  Option (FreeIncidenceAtom Generator)

def freeIncidenceGlue {Generator : Type u}
    (left right : FreeIncidenceTerm Generator) :
    FreeIncidenceTerm Generator :=
  match left, right with
  | none, value => value
  | value, none => value
  | some leftAtom, some rightAtom =>
      some (.glue leftAtom rightAtom)

def freeIncidenceGenerator {Generator : Type u}
    (generator : Generator) : FreeIncidenceTerm Generator :=
  some (.generator generator)

def freeIncidence (Generator : Type u) [DecidableEq Generator] :
    Incidence (FreeIncidenceTerm Generator)
      (ULift.{u} Unit) (ULift.{u} Unit) where
  boundary := fun _ => []
  typeFunc := fun _ => ULift.up ()
  glue := fun left right => some (freeIncidenceGlue left right)
  unit := none
  guards := Guards.permissive _
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := by simp
  sign_rules := by simp
  multiplicities := by simp
  well_founded := by simp
  unit_left := by intro value; simp [freeIncidenceGlue]
  unit_right := by intro value; cases value <;> simp [freeIncidenceGlue]
  type_preserve := by simp

structure TotalGlueSpec
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) where
  operation : I → I → I
  glue_eq : ∀ left right,
    inc.glue left right = some (operation left right)

theorem TotalGlueSpec.operation_unit_left
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (spec : TotalGlueSpec inc) (value : I) :
    spec.operation inc.unit value = value := by
  have equal := (spec.glue_eq inc.unit value).symm.trans (inc.unit_left value)
  exact Option.some.inj equal

theorem TotalGlueSpec.operation_unit_right
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (spec : TotalGlueSpec inc) (value : I) :
    spec.operation value inc.unit = value := by
  have equal := (spec.glue_eq value inc.unit).symm.trans (inc.unit_right value)
  exact Option.some.inj equal

def freeIncidenceAtomFold
    {Generator I : Type u} (operation : I → I → I)
    (onGenerator : Generator → I) : FreeIncidenceAtom Generator → I
  | .generator generator => onGenerator generator
  | .glue left right =>
      operation (freeIncidenceAtomFold operation onGenerator left)
        (freeIncidenceAtomFold operation onGenerator right)

def freeIncidenceFold
    {Generator I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I) : FreeIncidenceTerm Generator → I
  | none => inc.unit
  | some atom => freeIncidenceAtomFold spec.operation onGenerator atom

@[simp] theorem freeIncidenceFold_unit
    {Generator I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I) :
    freeIncidenceFold spec onGenerator none = inc.unit := rfl

@[simp] theorem freeIncidenceFold_generator
    {Generator I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I) (generator : Generator) :
    freeIncidenceFold spec onGenerator (freeIncidenceGenerator generator) =
      onGenerator generator := by
  simp [freeIncidenceFold, freeIncidenceGenerator, freeIncidenceAtomFold]

theorem freeIncidenceFold_glue
    {Generator I R T : Type u} [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I)
    (left right : FreeIncidenceTerm Generator) :
    freeIncidenceFold spec onGenerator (freeIncidenceGlue left right) =
      spec.operation (freeIncidenceFold spec onGenerator left)
        (freeIncidenceFold spec onGenerator right) := by
  cases left with
  | none =>
      simp [freeIncidenceGlue, freeIncidenceFold,
        spec.operation_unit_left]
  | some leftAtom =>
      cases right with
      | none =>
          simp [freeIncidenceGlue, freeIncidenceFold,
            spec.operation_unit_right]
      | some rightAtom =>
          simp [freeIncidenceGlue, freeIncidenceFold,
            freeIncidenceAtomFold]

structure IncidenceGluingHom
    {I J R₁ R₂ T₁ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    (source : Incidence I R₁ T₁) (target : Incidence J R₂ T₂) where
  toFun : I → J
  map_unit : toFun source.unit = target.unit
  map_glue : ∀ left right output,
    source.glue left right = some output →
      target.glue (toFun left) (toFun right) = some (toFun output)

@[ext] theorem IncidenceGluingHom.ext
    {I J R₁ R₂ T₁ T₂ : Type u} [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {first second : IncidenceGluingHom source target}
    (equal : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  simp_all

def freeIncidenceFoldHom
    {Generator I R T : Type u} [DecidableEq Generator] [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I) :
    IncidenceGluingHom (freeIncidence Generator) inc where
  toFun := freeIncidenceFold spec onGenerator
  map_unit := rfl
  map_glue := by
    intro left right output selected
    simp only [freeIncidence] at selected
    cases selected
    rw [freeIncidenceFold_glue]
    exact spec.glue_eq _ _

theorem IncidenceGluingHom.free_ext
    {Generator I R T : Type u} [DecidableEq Generator] [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I)
    (hom : IncidenceGluingHom (freeIncidence Generator) inc)
    (on_generators : ∀ generator,
      hom.toFun (freeIncidenceGenerator generator) = onGenerator generator) :
    hom.toFun = freeIncidenceFold spec onGenerator := by
  funext term
  cases term with
  | none => exact hom.map_unit
  | some atom =>
      induction atom with
      | generator generator => exact on_generators generator
      | glue left right leftIH rightIH =>
          have sourceSelected :
              (freeIncidence Generator).glue (some left) (some right) =
                some (some (.glue left right)) := rfl
          have mapped := hom.map_glue _ _ _ sourceSelected
          rw [spec.glue_eq] at mapped
          have operationEqual :
              spec.operation (hom.toFun (some left)) (hom.toFun (some right)) =
                hom.toFun (some (.glue left right)) := Option.some.inj mapped
          rw [← operationEqual, leftIH, rightIH]
          simp [freeIncidenceFold, freeIncidenceAtomFold]

theorem freeIncidence_universal
    {Generator I R T : Type u} [DecidableEq Generator] [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I) :
    ∃! hom : IncidenceGluingHom (freeIncidence Generator) inc,
      ∀ generator,
        hom.toFun (freeIncidenceGenerator generator) = onGenerator generator := by
  refine ⟨freeIncidenceFoldHom spec onGenerator, ?_, ?_⟩
  · intro generator
    exact freeIncidenceFold_generator spec onGenerator generator
  · intro hom onGenerators
    apply IncidenceGluingHom.ext
    exact IncidenceGluingHom.free_ext spec onGenerator hom onGenerators

def freeIncidenceFoldResonanceHom
    {Generator I R T : Type u} [DecidableEq Generator] [DecidableEq I]
    {inc : Incidence I R T} (spec : TotalGlueSpec inc)
    (onGenerator : Generator → I) :
    ResonanceHomomorphism (freeIncidence Generator) inc where
  toFun := freeIncidenceFold spec onGenerator
  preserves := by
    intro left right output resonant
    have selected :
        (freeIncidence Generator).glue left right = some output := resonant
    exact inc.selected_resonates
      ((freeIncidenceFoldHom spec onGenerator).map_glue
        left right output selected)

theorem freeIncidenceGenerator_injective
    {Generator : Type u} [DecidableEq Generator] :
    Function.Injective
      (freeIncidenceGenerator : Generator → FreeIncidenceTerm Generator) := by
  intro first second equal
  exact FreeIncidenceAtom.generator.inj (Option.some.inj equal)

/- A presentation may now prescribe genuine nonempty boundaries and additional
   relational resonance generators.  Irreflexivity of generator boundaries is
   exactly the condition required by the current Incidence well-foundedness
   field (which excludes self endpoints). -/
structure IncidencePresentation
    (Generator Role : Type u) [DecidableEq Generator] where
  boundaryGenerators : Generator → Boundary Generator Role
  boundary_irreflexive : ∀ generator endpoint,
    endpoint ∈ boundaryGenerators generator → endpoint.i ≠ generator
  resonanceGenerators : List (Generator × Generator × Generator)

def freeIncidenceEndpoint
    {Generator Role : Type u} (endpoint : Endpoint Generator Role) :
    Endpoint (FreeIncidenceTerm Generator) Role where
  i := freeIncidenceGenerator endpoint.i
  role := endpoint.role
  sign := endpoint.sign
  mult := endpoint.mult
  mult_pos := endpoint.mult_pos

def presentedFreeBoundary
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : IncidencePresentation Generator Role) :
    FreeIncidenceTerm Generator → Boundary (FreeIncidenceTerm Generator) Role
  | some (.generator generator) =>
      (presentation.boundaryGenerators generator).map freeIncidenceEndpoint
  | _ => []

def presentedFreeResonance
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : IncidencePresentation Generator Role)
    (left right output : FreeIncidenceTerm Generator) : Prop :=
  output = freeIncidenceGlue left right ∨
    ∃ leftGenerator rightGenerator outputGenerator,
      (leftGenerator, rightGenerator, outputGenerator) ∈
        presentation.resonanceGenerators ∧
      left = freeIncidenceGenerator leftGenerator ∧
      right = freeIncidenceGenerator rightGenerator ∧
      output = freeIncidenceGenerator outputGenerator

def presentedFreeIncidence
    (Generator Role : Type u) [DecidableEq Generator]
    (presentation : IncidencePresentation Generator Role) :
    Incidence (FreeIncidenceTerm Generator) Role (ULift.{u} Unit) where
  boundary := presentedFreeBoundary presentation
  typeFunc := fun _ => ULift.up ()
  glue := fun left right => some (freeIncidenceGlue left right)
  resonance := presentedFreeResonance presentation
  selected_resonates := by
    intro left right output selected
    exact Or.inl (Option.some.inj selected).symm
  unit := none
  guards := Guards.permissive _
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := by simp
  sign_rules := by
    intro value endpoint member
    cases endpoint.sign <;> simp
  multiplicities := by
    intro value endpoint member
    exact endpoint.mult_pos
  well_founded := by
    intro value self
    rcases self with ⟨endpoint, member, endpointSelf⟩
    cases value with
    | none => simp [presentedFreeBoundary] at member
    | some atom =>
      cases atom with
      | generator generator =>
        simp only [presentedFreeBoundary] at member
        rcases List.mem_map.mp member with
          ⟨sourceEndpoint, sourceMember, rfl⟩
        have endpointEqual : sourceEndpoint.i = generator := by
          exact freeIncidenceGenerator_injective endpointSelf
        exact presentation.boundary_irreflexive generator sourceEndpoint
          sourceMember endpointEqual
      | glue left right => simp [presentedFreeBoundary] at member
  unit_left := by intro value; simp [freeIncidenceGlue]
  unit_right := by intro value; cases value <;> simp [freeIncidenceGlue]
  type_preserve := by simp

def mapIncidenceEndpoint
    {I J Role : Type u} (map : I → J) (endpoint : Endpoint I Role) :
    Endpoint J Role where
  i := map endpoint.i
  role := endpoint.role
  sign := endpoint.sign
  mult := endpoint.mult
  mult_pos := endpoint.mult_pos

structure PresentedIncidenceAlgebra
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    (presentation : IncidencePresentation Generator Role)
    (target : Incidence I Role T) extends TotalGlueSpec target where
  onGenerator : Generator → I
  boundary_preserves : ∀ generator endpoint,
    endpoint ∈ presentation.boundaryGenerators generator →
      mapIncidenceEndpoint onGenerator endpoint ∈
        target.boundary (onGenerator generator)
  resonance_preserves : ∀ left right output,
    (left, right, output) ∈ presentation.resonanceGenerators →
      target.resonance (onGenerator left) (onGenerator right)
        (onGenerator output)

structure PresentedIncidenceHom
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    (presentation : IncidencePresentation Generator Role)
    (target : Incidence I Role T)
    extends IncidenceGluingHom
      (presentedFreeIncidence Generator Role presentation) target where
  map_boundary : ∀ source endpoint,
    endpoint ∈ (presentedFreeIncidence Generator Role presentation).boundary source →
      mapIncidenceEndpoint toFun endpoint ∈ target.boundary (toFun source)
  map_resonance : ∀ left right output,
    (presentedFreeIncidence Generator Role presentation).resonance
        left right output →
      target.resonance (toFun left) (toFun right) (toFun output)

@[ext] theorem PresentedIncidenceHom.ext
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : IncidencePresentation Generator Role}
    {target : Incidence I Role T}
    {first second : PresentedIncidenceHom presentation target}
    (equal : first.toFun = second.toFun) : first = second := by
  have baseEqual : first.toIncidenceGluingHom =
      second.toIncidenceGluingHom :=
    IncidenceGluingHom.ext equal
  cases first
  cases second
  cases baseEqual
  rfl

def presentedIncidenceFoldHom
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : IncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (algebra : PresentedIncidenceAlgebra presentation target) :
    PresentedIncidenceHom presentation target where
  toFun := freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator
  map_unit := rfl
  map_glue := (freeIncidenceFoldHom algebra.toTotalGlueSpec
    algebra.onGenerator).map_glue
  map_boundary := by
    intro source endpoint member
    cases source with
    | none => simp [presentedFreeIncidence, presentedFreeBoundary] at member
    | some atom =>
      cases atom with
      | generator generator =>
        simp only [presentedFreeIncidence, presentedFreeBoundary] at member
        rcases List.mem_map.mp member with
          ⟨sourceEndpoint, sourceMember, rfl⟩
        simpa [mapIncidenceEndpoint, freeIncidenceFold_generator] using
          algebra.boundary_preserves generator sourceEndpoint sourceMember
      | glue left right =>
          simp [presentedFreeIncidence, presentedFreeBoundary] at member
  map_resonance := by
    intro left right output resonant
    rcases resonant with selected | generated
    · subst output
      exact target.selected_resonates
        ((freeIncidenceFoldHom algebra.toTotalGlueSpec
          algebra.onGenerator).map_glue left right _ rfl)
    · rcases generated with
        ⟨leftGenerator, rightGenerator, outputGenerator, member, rfl, rfl, rfl⟩
      simpa using algebra.resonance_preserves leftGenerator rightGenerator
        outputGenerator member

theorem presentedFreeIncidence_universal
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : IncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (algebra : PresentedIncidenceAlgebra presentation target) :
    ∃! hom : PresentedIncidenceHom presentation target,
      ∀ generator,
        hom.toFun (freeIncidenceGenerator generator) =
          algebra.onGenerator generator := by
  refine ⟨presentedIncidenceFoldHom algebra, ?_, ?_⟩
  · intro generator
    exact freeIncidenceFold_generator algebra.toTotalGlueSpec
      algebra.onGenerator generator
  · intro hom onGenerators
    apply PresentedIncidenceHom.ext
    let baseHom : IncidenceGluingHom (freeIncidence Generator) target := {
      toFun := hom.toFun
      map_unit := hom.map_unit
      map_glue := by
        intro left right output selected
        apply hom.map_glue left right output
        simpa [freeIncidence, presentedFreeIncidence] using selected }
    exact IncidenceGluingHom.free_ext algebra.toTotalGlueSpec
      algebra.onGenerator baseHom onGenerators

structure EquationalIncidencePresentation
    (Generator Role : Type u) [DecidableEq Generator]
    extends IncidencePresentation Generator Role where
  equations : List (FreeIncidenceTerm Generator × FreeIncidenceTerm Generator)

inductive PresentedTermCongruence
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :
    FreeIncidenceTerm Generator → FreeIncidenceTerm Generator → Prop
  | refl term : PresentedTermCongruence presentation term term
  | symm {first second} : PresentedTermCongruence presentation first second →
      PresentedTermCongruence presentation second first
  | trans {first second third} :
      PresentedTermCongruence presentation first second →
      PresentedTermCongruence presentation second third →
      PresentedTermCongruence presentation first third
  | equation {first second} :
      (first, second) ∈ presentation.equations →
      PresentedTermCongruence presentation first second
  | glue {left₁ left₂ right₁ right₂} :
      PresentedTermCongruence presentation left₁ left₂ →
      PresentedTermCongruence presentation right₁ right₂ →
      PresentedTermCongruence presentation
        (freeIncidenceGlue left₁ right₁) (freeIncidenceGlue left₂ right₂)

def presentedTermSetoid
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :
    Setoid (FreeIncidenceTerm Generator) where
  r := PresentedTermCongruence presentation
  iseqv := ⟨PresentedTermCongruence.refl,
    fun related => PresentedTermCongruence.symm related,
    fun first second => PresentedTermCongruence.trans first second⟩

abbrev PresentedIncidenceQuotient
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :=
  Quotient (presentedTermSetoid presentation)

noncomputable instance presentedIncidenceQuotientDecidableEq
    {Generator Role : Type u} [DecidableEq Generator]
    {presentation : EquationalIncidencePresentation Generator Role} :
    DecidableEq (PresentedIncidenceQuotient presentation) :=
  Classical.decEq _

def presentedQuotientGlue
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :
    PresentedIncidenceQuotient presentation →
      PresentedIncidenceQuotient presentation →
      PresentedIncidenceQuotient presentation :=
  Quotient.lift₂
    (fun left right => Quotient.mk (presentedTermSetoid presentation)
      (freeIncidenceGlue left right))
    (by
      intro left₁ right₁ left₂ right₂ leftRelated rightRelated
      exact Quotient.sound
        (PresentedTermCongruence.glue leftRelated rightRelated))

def quotientPresentedEndpoint
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role)
    (endpoint : Endpoint (FreeIncidenceTerm Generator) Role) :
    Endpoint (PresentedIncidenceQuotient presentation) Role :=
  mapIncidenceEndpoint
    (Quotient.mk (presentedTermSetoid presentation)) endpoint

def quotientPresentedBoundaryOnRepresentatives
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role)
    (term : FreeIncidenceTerm Generator) :
    Boundary (PresentedIncidenceQuotient presentation) Role :=
  ((presentedFreeIncidence Generator Role presentation.toIncidencePresentation).boundary
    term).map (quotientPresentedEndpoint presentation)

def PresentedBoundaryCongruent
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) : Prop :=
  ∀ {first second}, PresentedTermCongruence presentation first second →
    quotientPresentedBoundaryOnRepresentatives presentation first =
      quotientPresentedBoundaryOnRepresentatives presentation second

def PresentedBoundaryDescendsExactly
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) : Prop :=
  ∃ descended : PresentedIncidenceQuotient presentation →
      Boundary (PresentedIncidenceQuotient presentation) Role,
    ∀ term,
      descended (Quotient.mk (presentedTermSetoid presentation) term) =
        quotientPresentedBoundaryOnRepresentatives presentation term

def PresentedResonanceCongruent
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) : Prop :=
  ∀ {left₁ left₂ right₁ right₂ output₁ output₂},
    PresentedTermCongruence presentation left₁ left₂ →
    PresentedTermCongruence presentation right₁ right₂ →
    PresentedTermCongruence presentation output₁ output₂ →
    (presentedFreeResonance presentation.toIncidencePresentation
        left₁ right₁ output₁ ↔
      presentedFreeResonance presentation.toIncidencePresentation
        left₂ right₂ output₂)

def PresentedQuotientBoundaryIrreflexive
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) : Prop :=
  ∀ term endpoint,
    endpoint ∈ quotientPresentedBoundaryOnRepresentatives presentation term →
      endpoint.i ≠ Quotient.mk (presentedTermSetoid presentation) term

def presentedQuotientBoundary
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role)
    (congruent : PresentedBoundaryCongruent presentation) :
    PresentedIncidenceQuotient presentation →
      Boundary (PresentedIncidenceQuotient presentation) Role :=
  Quotient.lift (quotientPresentedBoundaryOnRepresentatives presentation)
    (fun _ _ related => congruent related)

theorem presentedBoundary_descendsExactly_iff_congruent
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :
    PresentedBoundaryDescendsExactly presentation ↔
      PresentedBoundaryCongruent presentation := by
  constructor
  · rintro ⟨descended, exactOnRepresentatives⟩ first second related
    rw [← exactOnRepresentatives first, ← exactOnRepresentatives second,
      Quotient.sound related]
  · intro congruent
    exact ⟨presentedQuotientBoundary presentation congruent, fun _ => rfl⟩

def PresentedQuotientBoundaryWellFounded
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role)
    (congruent : PresentedBoundaryCongruent presentation) : Prop :=
  ∀ value, ¬ ∃ endpoint ∈ presentedQuotientBoundary presentation congruent value,
    endpoint.i = value

theorem presentedQuotientBoundary_wellFounded_iff_irreflexive
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role)
    (congruent : PresentedBoundaryCongruent presentation) :
    PresentedQuotientBoundaryWellFounded presentation congruent ↔
      PresentedQuotientBoundaryIrreflexive presentation := by
  constructor
  · intro wellFounded term endpoint member endpointSelf
    exact wellFounded (Quotient.mk (presentedTermSetoid presentation) term)
      ⟨endpoint, member, endpointSelf⟩
  · intro irreflexive value
    induction value using Quotient.ind with
    | _ term =>
      rintro ⟨endpoint, member, endpointSelf⟩
      exact irreflexive term endpoint member endpointSelf

def presentedQuotientResonance
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :
    PresentedIncidenceQuotient presentation →
      PresentedIncidenceQuotient presentation →
      PresentedIncidenceQuotient presentation → Prop :=
  fun left right output =>
    ∃ leftTerm rightTerm outputTerm,
      Quotient.mk (presentedTermSetoid presentation) leftTerm = left ∧
      Quotient.mk (presentedTermSetoid presentation) rightTerm = right ∧
      Quotient.mk (presentedTermSetoid presentation) outputTerm = output ∧
      presentedFreeResonance presentation.toIncidencePresentation
        leftTerm rightTerm outputTerm

theorem presentedQuotientResonance_mk_iff
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role)
    (congruent : PresentedResonanceCongruent presentation)
    (left right output : FreeIncidenceTerm Generator) :
    presentedQuotientResonance presentation
        (Quotient.mk (presentedTermSetoid presentation) left)
        (Quotient.mk (presentedTermSetoid presentation) right)
        (Quotient.mk (presentedTermSetoid presentation) output) ↔
      presentedFreeResonance presentation.toIncidencePresentation
        left right output := by
  constructor
  · rintro ⟨leftTerm, rightTerm, outputTerm,
      leftEqual, rightEqual, outputEqual, resonant⟩
    exact (congruent (Quotient.exact leftEqual) (Quotient.exact rightEqual)
      (Quotient.exact outputEqual)).mp resonant
  · intro resonant
    exact ⟨left, right, output, rfl, rfl, rfl, resonant⟩

def PresentedResonanceDescendsExactly
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) : Prop :=
  ∀ left right output,
    presentedQuotientResonance presentation
        (Quotient.mk (presentedTermSetoid presentation) left)
        (Quotient.mk (presentedTermSetoid presentation) right)
        (Quotient.mk (presentedTermSetoid presentation) output) ↔
      presentedFreeResonance presentation.toIncidencePresentation
        left right output

theorem presentedResonance_descendsExactly_iff_congruent
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :
    PresentedResonanceDescendsExactly presentation ↔
      PresentedResonanceCongruent presentation := by
  constructor
  · intro exactDescent left₁ left₂ right₁ right₂ output₁ output₂
      leftRelated rightRelated outputRelated
    have leftEqual :
        (Quotient.mk (presentedTermSetoid presentation) left₁ :
          PresentedIncidenceQuotient presentation) =
        Quotient.mk (presentedTermSetoid presentation) left₂ :=
      Quotient.sound leftRelated
    have rightEqual :
        (Quotient.mk (presentedTermSetoid presentation) right₁ :
          PresentedIncidenceQuotient presentation) =
        Quotient.mk (presentedTermSetoid presentation) right₂ :=
      Quotient.sound rightRelated
    have outputEqual :
        (Quotient.mk (presentedTermSetoid presentation) output₁ :
          PresentedIncidenceQuotient presentation) =
        Quotient.mk (presentedTermSetoid presentation) output₂ :=
      Quotient.sound outputRelated
    calc
      _ ↔ presentedQuotientResonance presentation
          (Quotient.mk _ left₁) (Quotient.mk _ right₁)
          (Quotient.mk _ output₁) := (exactDescent _ _ _).symm
      _ ↔ presentedQuotientResonance presentation
          (Quotient.mk _ left₂) (Quotient.mk _ right₂)
          (Quotient.mk _ output₂) := by rw [leftEqual, rightEqual, outputEqual]
      _ ↔ _ := exactDescent _ _ _
  · intro congruent left right output
    exact presentedQuotientResonance_mk_iff presentation congruent
      left right output

structure EquationalPresentationQuotientAdmissible
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) : Prop where
  boundaryDescent : PresentedBoundaryCongruent presentation
  boundaryWellFounded : PresentedQuotientBoundaryIrreflexive presentation
  resonanceDescent : PresentedResonanceCongruent presentation

theorem equationalPresentationQuotientAdmissible_iff
    {Generator Role : Type u} [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role) :
    EquationalPresentationQuotientAdmissible presentation ↔
      PresentedBoundaryDescendsExactly presentation ∧
      (∃ congruent : PresentedBoundaryCongruent presentation,
        PresentedQuotientBoundaryWellFounded presentation congruent) ∧
      PresentedResonanceDescendsExactly presentation := by
  constructor
  · intro admissible
    exact ⟨(presentedBoundary_descendsExactly_iff_congruent presentation).mpr
        admissible.boundaryDescent,
      ⟨admissible.boundaryDescent,
        (presentedQuotientBoundary_wellFounded_iff_irreflexive presentation
          admissible.boundaryDescent).mpr admissible.boundaryWellFounded⟩,
      (presentedResonance_descendsExactly_iff_congruent presentation).mpr
        admissible.resonanceDescent⟩
  · rintro ⟨boundaryDescent, ⟨congruent, wellFounded⟩, resonanceDescent⟩
    exact ⟨(presentedBoundary_descendsExactly_iff_congruent presentation).mp
        boundaryDescent,
      (presentedQuotientBoundary_wellFounded_iff_irreflexive presentation
        congruent).mp wellFounded,
      (presentedResonance_descendsExactly_iff_congruent presentation).mp
        resonanceDescent⟩

noncomputable def equationalPresentedFreeIncidence
    (Generator Role : Type u) [DecidableEq Generator]
    (presentation : EquationalIncidencePresentation Generator Role)
    (boundaryCongruent : PresentedBoundaryCongruent presentation)
    (irreflexive : PresentedQuotientBoundaryIrreflexive presentation) :
    Incidence (PresentedIncidenceQuotient presentation) Role (ULift.{u} Unit) where
  boundary := presentedQuotientBoundary presentation boundaryCongruent
  typeFunc := fun _ => ULift.up ()
  glue := fun left right => some (presentedQuotientGlue presentation left right)
  resonance := presentedQuotientResonance presentation
  selected_resonates := by
    intro left right output selected
    induction left using Quotient.ind with
    | _ leftTerm =>
      induction right using Quotient.ind with
      | _ rightTerm =>
        cases selected
        exact ⟨leftTerm, rightTerm, freeIncidenceGlue leftTerm rightTerm,
          rfl, rfl, rfl, Or.inl rfl⟩
  unit := Quotient.mk (presentedTermSetoid presentation) none
  guards := Guards.permissive _
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := by simp
  sign_rules := by
    intro value endpoint member
    cases endpoint.sign <;> simp
  multiplicities := by
    intro value endpoint member
    exact endpoint.mult_pos
  well_founded := by
    intro value
    induction value using Quotient.ind with
    | _ term =>
      rintro ⟨endpoint, member, equal⟩
      exact irreflexive term endpoint member equal
  unit_left := by
    intro value
    induction value using Quotient.ind with
    | _ term =>
      apply congrArg some
      exact Quotient.sound (by
        simpa [freeIncidenceGlue] using
          (PresentedTermCongruence.refl term))
  unit_right := by
    intro value
    induction value using Quotient.ind with
    | _ term =>
      apply congrArg some
      exact Quotient.sound (by
        cases term <;> exact PresentedTermCongruence.refl _)
  type_preserve := by simp

structure EquationalPresentedIncidenceAlgebra
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    (presentation : EquationalIncidencePresentation Generator Role)
    (target : Incidence I Role T)
    extends PresentedIncidenceAlgebra presentation.toIncidencePresentation target where
  equations_preserve : ∀ first second,
    (first, second) ∈ presentation.equations →
      freeIncidenceFold toPresentedIncidenceAlgebra.toTotalGlueSpec
          toPresentedIncidenceAlgebra.onGenerator first =
        freeIncidenceFold toPresentedIncidenceAlgebra.toTotalGlueSpec
          toPresentedIncidenceAlgebra.onGenerator second

theorem EquationalPresentedIncidenceAlgebra.fold_respects_congruence
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : EquationalIncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (algebra : EquationalPresentedIncidenceAlgebra presentation target)
    {first second : FreeIncidenceTerm Generator}
    (related : PresentedTermCongruence presentation first second) :
    freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator first =
      freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator second := by
  induction related with
  | refl term => rfl
  | symm related ih => exact ih.symm
  | trans first second firstIH secondIH => exact firstIH.trans secondIH
  | equation member => exact algebra.equations_preserve _ _ member
  | glue leftRelated rightRelated leftIH rightIH =>
      rw [freeIncidenceFold_glue, freeIncidenceFold_glue, leftIH, rightIH]

def equationalPresentedIncidenceFold
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : EquationalIncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (algebra : EquationalPresentedIncidenceAlgebra presentation target) :
    PresentedIncidenceQuotient presentation → I :=
  Quotient.lift
    (freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator)
    (fun _ _ related => algebra.fold_respects_congruence related)

@[simp] theorem equationalPresentedIncidenceFold_mk
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : EquationalIncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (algebra : EquationalPresentedIncidenceAlgebra presentation target)
    (term : FreeIncidenceTerm Generator) :
    equationalPresentedIncidenceFold algebra
        (Quotient.mk (presentedTermSetoid presentation) term) =
      freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator term := rfl

theorem equationalPresentedIncidenceFold_universal
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : EquationalIncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (algebra : EquationalPresentedIncidenceAlgebra presentation target) :
    ∃! factor : PresentedIncidenceQuotient presentation → I,
      ∀ term,
        factor (Quotient.mk (presentedTermSetoid presentation) term) =
          freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator term := by
  refine ⟨equationalPresentedIncidenceFold algebra, fun _ => rfl, ?_⟩
  intro factor agrees
  funext quotientTerm
  induction quotientTerm using Quotient.ind with
  | _ term => exact agrees term

structure StructuredIncidenceHom
    {I J Role SourceType TargetType : Type u}
    [DecidableEq I] [DecidableEq J]
    (source : Incidence I Role SourceType)
    (target : Incidence J Role TargetType) where
  toFun : I → J
  map_unit : toFun source.unit = target.unit
  map_glue : ∀ left right output,
    source.glue left right = some output →
      target.glue (toFun left) (toFun right) = some (toFun output)
  map_boundary : ∀ value endpoint,
    endpoint ∈ source.boundary value →
      mapIncidenceEndpoint toFun endpoint ∈ target.boundary (toFun value)
  map_resonance : ∀ left right output,
    source.resonance left right output →
      target.resonance (toFun left) (toFun right) (toFun output)

@[ext] theorem StructuredIncidenceHom.ext
    {I J Role SourceType TargetType : Type u}
    [DecidableEq I] [DecidableEq J]
    {source : Incidence I Role SourceType}
    {target : Incidence J Role TargetType}
    {first second : StructuredIncidenceHom source target}
    (equal : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  simp_all

/- Grilliette--Rusnak incidence hypergraphs are three-sorted diagrams
   `Incidence → Vertex` and `Incidence → Edge`.  An Incidence boundary has
   a canonical such underlying diagram: cells occur both as vertices and as
   boundary-bearing edges, while every concrete endpoint occurrence is an
   incidence.  Signs, roles, multiplicities, glue, and resonance are forgotten.
   The construction is functorial for boundary-preserving morphisms. -/
structure CategoricalIncidenceHypergraph where
  Vertex : Type u
  Edge : Type u
  IncidencePoint : Type u
  vertexOf : IncidencePoint → Vertex
  edgeOf : IncidencePoint → Edge

structure CategoricalIncidenceHypergraphHom
    (source target : CategoricalIncidenceHypergraph.{u}) where
  vertexMap : source.Vertex → target.Vertex
  edgeMap : source.Edge → target.Edge
  incidenceMap : source.IncidencePoint → target.IncidencePoint
  map_vertexOf : ∀ incidence,
    vertexMap (source.vertexOf incidence) =
      target.vertexOf (incidenceMap incidence)
  map_edgeOf : ∀ incidence,
    edgeMap (source.edgeOf incidence) =
      target.edgeOf (incidenceMap incidence)

@[ext] theorem CategoricalIncidenceHypergraphHom.ext
    {source target : CategoricalIncidenceHypergraph.{u}}
    {first second : CategoricalIncidenceHypergraphHom source target}
    (vertexEqual : first.vertexMap = second.vertexMap)
    (edgeEqual : first.edgeMap = second.edgeMap)
    (incidenceEqual : first.incidenceMap = second.incidenceMap) :
    first = second := by
  cases first
  cases second
  simp_all

def CategoricalIncidenceHypergraphHom.id
    (hypergraph : CategoricalIncidenceHypergraph.{u}) :
    CategoricalIncidenceHypergraphHom hypergraph hypergraph where
  vertexMap := fun value => value
  edgeMap := fun value => value
  incidenceMap := fun value => value
  map_vertexOf := fun _ => rfl
  map_edgeOf := fun _ => rfl

def CategoricalIncidenceHypergraphHom.comp
    {first second third : CategoricalIncidenceHypergraph.{u}}
    (after : CategoricalIncidenceHypergraphHom second third)
    (before : CategoricalIncidenceHypergraphHom first second) :
    CategoricalIncidenceHypergraphHom first third where
  vertexMap := after.vertexMap ∘ before.vertexMap
  edgeMap := after.edgeMap ∘ before.edgeMap
  incidenceMap := after.incidenceMap ∘ before.incidenceMap
  map_vertexOf := by
    intro incidence
    rw [Function.comp_apply, before.map_vertexOf,
      Function.comp_apply, after.map_vertexOf]
  map_edgeOf := by
    intro incidence
    rw [Function.comp_apply, before.map_edgeOf,
      Function.comp_apply, after.map_edgeOf]

def incidenceBoundaryHypergraph
    {I Role CellType : Type u} [DecidableEq I]
    (incidence : Incidence I Role CellType) :
    CategoricalIncidenceHypergraph where
  Vertex := I
  Edge := I
  IncidencePoint :=
    { occurrence : I × Endpoint I Role //
      occurrence.2 ∈ incidence.boundary occurrence.1 }
  vertexOf := fun occurrence => occurrence.val.2.i
  edgeOf := fun occurrence => occurrence.val.1

def StructuredIncidenceHom.id
    {I Role CellType : Type u} [DecidableEq I]
    (incidence : Incidence I Role CellType) :
    StructuredIncidenceHom incidence incidence where
  toFun := fun value => value
  map_unit := rfl
  map_glue := by simp
  map_boundary := by
    intro value endpoint member
    simpa [mapIncidenceEndpoint]
  map_resonance := by simp

def StructuredIncidenceHom.comp
    {I J K Role Type₁ Type₂ Type₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I Role Type₁}
    {second : Incidence J Role Type₂}
    {third : Incidence K Role Type₃}
    (after : StructuredIncidenceHom second third)
    (before : StructuredIncidenceHom first second) :
    StructuredIncidenceHom first third where
  toFun := after.toFun ∘ before.toFun
  map_unit := by rw [Function.comp_apply, before.map_unit, after.map_unit]
  map_glue := by
    intro left right output selected
    exact after.map_glue _ _ _ (before.map_glue _ _ _ selected)
  map_boundary := by
    intro value endpoint member
    exact after.map_boundary _ _ (before.map_boundary _ _ member)
  map_resonance := by
    intro left right output resonant
    exact after.map_resonance _ _ _ (before.map_resonance _ _ _ resonant)

def StructuredIncidenceHom.toCategoricalIncidenceHypergraphHom
    {I J Role SourceType TargetType : Type u}
    [DecidableEq I] [DecidableEq J]
    {source : Incidence I Role SourceType}
    {target : Incidence J Role TargetType}
    (hom : StructuredIncidenceHom source target) :
    CategoricalIncidenceHypergraphHom
      (incidenceBoundaryHypergraph source)
      (incidenceBoundaryHypergraph target) where
  vertexMap := hom.toFun
  edgeMap := hom.toFun
  incidenceMap := fun occurrence =>
    ⟨(hom.toFun occurrence.val.1,
      mapIncidenceEndpoint hom.toFun occurrence.val.2),
      hom.map_boundary occurrence.val.1 occurrence.val.2 occurrence.property⟩
  map_vertexOf := fun _ => rfl
  map_edgeOf := fun _ => rfl

@[simp] theorem StructuredIncidenceHom.toHypergraphHom_id
    {I Role CellType : Type u} [DecidableEq I]
    (incidence : Incidence I Role CellType) :
    StructuredIncidenceHom.toCategoricalIncidenceHypergraphHom
        (StructuredIncidenceHom.id incidence) =
      CategoricalIncidenceHypergraphHom.id
        (incidenceBoundaryHypergraph incidence) := by
  apply CategoricalIncidenceHypergraphHom.ext <;> rfl

@[simp] theorem StructuredIncidenceHom.toHypergraphHom_comp
    {I J K Role Type₁ Type₂ Type₃ : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {first : Incidence I Role Type₁}
    {second : Incidence J Role Type₂}
    {third : Incidence K Role Type₃}
    (after : StructuredIncidenceHom second third)
    (before : StructuredIncidenceHom first second) :
    (after.comp before).toCategoricalIncidenceHypergraphHom =
      after.toCategoricalIncidenceHypergraphHom.comp
        before.toCategoricalIncidenceHypergraphHom := by
  apply CategoricalIncidenceHypergraphHom.ext <;> rfl

noncomputable def equationalPresentedIncidenceFoldHom
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : EquationalIncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (boundaryCongruent : PresentedBoundaryCongruent presentation)
    (irreflexive : PresentedQuotientBoundaryIrreflexive presentation)
    (algebra : EquationalPresentedIncidenceAlgebra presentation target) :
    StructuredIncidenceHom
      (equationalPresentedFreeIncidence Generator Role presentation
        boundaryCongruent irreflexive) target where
  toFun := equationalPresentedIncidenceFold algebra
  map_unit := rfl
  map_glue := by
    intro left right output selected
    induction left using Quotient.ind with
    | _ leftTerm =>
      induction right using Quotient.ind with
      | _ rightTerm =>
        cases selected
        change target.glue
            (freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator
              leftTerm)
            (freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator
              rightTerm) =
          some (freeIncidenceFold algebra.toTotalGlueSpec algebra.onGenerator
            (freeIncidenceGlue leftTerm rightTerm))
        rw [freeIncidenceFold_glue]
        exact algebra.glue_eq _ _
  map_boundary := by
    intro value endpoint member
    induction value using Quotient.ind with
    | _ term =>
      change endpoint ∈
        quotientPresentedBoundaryOnRepresentatives presentation term at member
      rcases List.mem_map.mp member with
        ⟨sourceEndpoint, sourceMember, rfl⟩
      simpa [quotientPresentedEndpoint, mapIncidenceEndpoint,
        equationalPresentedIncidenceFold_mk] using
        (presentedIncidenceFoldHom algebra.toPresentedIncidenceAlgebra).map_boundary
          term sourceEndpoint sourceMember
  map_resonance := by
    intro left right output resonant
    rcases resonant with
      ⟨leftTerm, rightTerm, outputTerm, rfl, rfl, rfl, sourceResonant⟩
    simpa [equationalPresentedIncidenceFold_mk] using
      (presentedIncidenceFoldHom algebra.toPresentedIncidenceAlgebra).map_resonance
        leftTerm rightTerm outputTerm sourceResonant

theorem equationalPresentedIncidenceFoldHom_universal
    {Generator Role I T : Type u}
    [DecidableEq Generator] [DecidableEq I]
    {presentation : EquationalIncidencePresentation Generator Role}
    {target : Incidence I Role T}
    (boundaryCongruent : PresentedBoundaryCongruent presentation)
    (irreflexive : PresentedQuotientBoundaryIrreflexive presentation)
    (algebra : EquationalPresentedIncidenceAlgebra presentation target) :
    ∃! hom : StructuredIncidenceHom
        (equationalPresentedFreeIncidence Generator Role presentation
          boundaryCongruent irreflexive) target,
      ∀ generator,
        hom.toFun (Quotient.mk (presentedTermSetoid presentation)
          (freeIncidenceGenerator generator)) = algebra.onGenerator generator := by
  refine ⟨equationalPresentedIncidenceFoldHom boundaryCongruent irreflexive
    algebra, ?_, ?_⟩
  · intro generator
    exact freeIncidenceFold_generator algebra.toTotalGlueSpec
      algebra.onGenerator generator
  · intro hom onGenerators
    apply StructuredIncidenceHom.ext
    funext quotientTerm
    induction quotientTerm using Quotient.ind with
    | _ term =>
      let baseHom : IncidenceGluingHom (freeIncidence Generator) target := {
        toFun := fun sourceTerm => hom.toFun
          (Quotient.mk (presentedTermSetoid presentation) sourceTerm)
        map_unit := hom.map_unit
        map_glue := by
          intro left right output selected
          cases selected
          exact hom.map_glue _ _ _ rfl }
      have equal := IncidenceGluingHom.free_ext algebra.toTotalGlueSpec
        algebra.onGenerator baseHom onGenerators
      exact congrFun equal term

/- A minimal resonance-sensitive logic.  Its three variables are enough to
   observe every ternary congruence failure; propositional connectives then
   show that atomic invariance propagates to all formulas. -/
inductive ResonanceVariable where
  | left
  | right
  | output
deriving DecidableEq, Repr

inductive ResonanceFormula where
  | truth
  | falsity
  | atom : ResonanceVariable → ResonanceVariable → ResonanceVariable →
      ResonanceFormula
  | and : ResonanceFormula → ResonanceFormula → ResonanceFormula
  | or : ResonanceFormula → ResonanceFormula → ResonanceFormula
  | implication : ResonanceFormula → ResonanceFormula → ResonanceFormula
deriving DecidableEq, Repr

def ResonanceFormula.Realize
    {I : Type u} (resonance : I → I → I → Prop)
    (valuation : ResonanceVariable → I) : ResonanceFormula → Prop
  | .truth => True
  | .falsity => False
  | .atom leftVar rightVar outputVar =>
      resonance (valuation leftVar) (valuation rightVar) (valuation outputVar)
  | .and first second =>
      first.Realize resonance valuation ∧ second.Realize resonance valuation
  | .or first second =>
      first.Realize resonance valuation ∨ second.Realize resonance valuation
  | .implication first second =>
      first.Realize resonance valuation → second.Realize resonance valuation

def ResonanceFormula.BisimulationInvariant
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : ResonanceFormula) : Prop :=
  ∀ first second : ResonanceVariable → I,
    (∀ var, approxBisim inc (first var) (second var)) →
      (formula.Realize inc.resonance first ↔
        formula.Realize inc.resonance second)

theorem ResonanceFormula.bisimulationInvariant_of_congruent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (congruent : QuotientResonanceCongruent inc)
    (formula : ResonanceFormula) :
    formula.BisimulationInvariant inc := by
  intro first second related
  induction formula with
  | truth => exact Iff.rfl
  | falsity => exact Iff.rfl
  | atom leftVar rightVar outputVar =>
      exact congruent (related leftVar) (related rightVar) (related outputVar)
  | and firstFormula secondFormula firstIH secondIH =>
      exact and_congr firstIH secondIH
  | or firstFormula secondFormula firstIH secondIH =>
      exact or_congr firstIH secondIH
  | implication firstFormula secondFormula firstIH secondIH =>
      exact imp_congr firstIH secondIH

def resonanceObservationFormula : ResonanceFormula :=
  .atom .left .right .output

theorem quotientResonanceCongruent_of_observation_invariant
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (invariant : resonanceObservationFormula.BisimulationInvariant inc) :
    QuotientResonanceCongruent inc := by
  intro left₁ left₂ right₁ right₂ output₁ output₂
    leftRelated rightRelated outputRelated
  let first : ResonanceVariable → I
    | .left => left₁
    | .right => right₁
    | .output => output₁
  let second : ResonanceVariable → I
    | .left => left₂
    | .right => right₂
    | .output => output₂
  have related : ∀ var, approxBisim inc (first var) (second var) := by
    intro var
    cases var with
    | left => exact leftRelated
    | right => exact rightRelated
    | output => exact outputRelated
  simpa [resonanceObservationFormula, ResonanceFormula.Realize, first, second]
    using invariant first second related

theorem quotientResonanceCongruent_iff_all_formula_invariant
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    QuotientResonanceCongruent inc ↔
      ∀ formula : ResonanceFormula,
        formula.BisimulationInvariant inc := by
  constructor
  · intro congruent formula
    exact formula.bisimulationInvariant_of_congruent congruent
  · intro allInvariant
    exact quotientResonanceCongruent_of_observation_invariant
      (allInvariant resonanceObservationFormula)

theorem exactDescent_iff_all_resonanceFormula_invariant
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      ∀ formula : ResonanceFormula,
        formula.BisimulationInvariant inc := by
  rw [resonanceRelationDescendsExactly_iff,
    quotientResonanceCongruent_iff_all_formula_invariant]

theorem exactDescent_of_resonanceFormula_preservation
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (preserves : ∀ formula : ResonanceFormula,
      formula.BisimulationInvariant inc) :
    ResonanceRelationDescendsExactly inc :=
  (exactDescent_iff_all_resonanceFormula_invariant inc).mpr preserves

theorem observation_not_invariant_of_no_exactDescent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (failure : ¬ ResonanceRelationDescendsExactly inc) :
    ¬ resonanceObservationFormula.BisimulationInvariant inc := by
  intro invariant
  exact failure
    ((resonanceRelationDescendsExactly_iff inc).mpr
      (quotientResonanceCongruent_of_observation_invariant invariant))

/- Integration with the existing conservative `IncProof` syntax.  A valuation
   closes the three-variable observation language into physical resonance atoms.
   The same `forget` retraction used by the conservativity theorem then erases
   every such atom to truth. -/
def ResonanceFormula.toIncProof
    {I : Type u} (encode : I → HFSet)
    (valuation : ResonanceVariable → I) :
    ResonanceFormula → ReferenceFoundation.IncProof.Formula
  | .truth => .top
  | .falsity => .bot
  | .atom leftVar rightVar outputVar =>
      .resonance (encode (valuation leftVar)) (encode (valuation rightVar))
        (encode (valuation outputVar))
  | .and first second =>
      .and (first.toIncProof encode valuation) (second.toIncProof encode valuation)
  | .or first second =>
      .or (first.toIncProof encode valuation) (second.toIncProof encode valuation)
  | .implication first second =>
      .imp (first.toIncProof encode valuation) (second.toIncProof encode valuation)

def ResonanceFormula.referenceForget :
    ResonanceFormula → ReferenceFoundation.Formula
  | .truth => .top
  | .falsity => .bot
  | .atom _ _ _ => .top
  | .and first second => .and first.referenceForget second.referenceForget
  | .or first second => .or first.referenceForget second.referenceForget
  | .implication first second =>
      .imp first.referenceForget second.referenceForget

@[simp] theorem ResonanceFormula.forget_toIncProof
    {I : Type u} (encode : I → HFSet)
    (valuation : ResonanceVariable → I) (formula : ResonanceFormula) :
    (formula.toIncProof encode valuation).forget = formula.referenceForget := by
  induction formula <;>
    simp [ResonanceFormula.toIncProof, ResonanceFormula.referenceForget,
      ReferenceFoundation.IncProof.Formula.forget, *]

def ReferenceFoundation.IncProof.Formula.RealizeWith
    (referenceTruth : ReferenceFoundation.Formula → Prop)
    (resonanceTruth : HFSet → HFSet → HFSet → Prop) :
    ReferenceFoundation.IncProof.Formula → Prop
  | .reference formula => referenceTruth formula
  | .resonance left right output => resonanceTruth left right output
  | .top => True
  | .bot => False
  | .and first second =>
      first.RealizeWith referenceTruth resonanceTruth ∧
        second.RealizeWith referenceTruth resonanceTruth
  | .or first second =>
      first.RealizeWith referenceTruth resonanceTruth ∨
        second.RealizeWith referenceTruth resonanceTruth
  | .imp first second =>
      first.RealizeWith referenceTruth resonanceTruth →
        second.RealizeWith referenceTruth resonanceTruth

theorem ResonanceFormula.toIncProof_realize_iff
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (encode : I → HFSet)
    (referenceTruth : ReferenceFoundation.Formula → Prop)
    (resonanceTruth : HFSet → HFSet → HFSet → Prop)
    (agrees : ∀ leftValue rightValue outputValue,
      resonanceTruth (encode leftValue) (encode rightValue)
          (encode outputValue) ↔
        inc.resonance leftValue rightValue outputValue)
    (valuation : ResonanceVariable → I) (formula : ResonanceFormula) :
    (formula.toIncProof encode valuation).RealizeWith
        referenceTruth resonanceTruth ↔
      formula.Realize inc.resonance valuation := by
  induction formula with
  | truth => exact Iff.rfl
  | falsity => exact Iff.rfl
  | atom leftVar rightVar outputVar => exact agrees _ _ _
  | and first second firstIH secondIH => exact and_congr firstIH secondIH
  | or first second firstIH secondIH => exact or_congr firstIH secondIH
  | implication first second firstIH secondIH => exact imp_congr firstIH secondIH

def ResonanceFormula.IncProofBisimulationInvariant
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (encode : I → HFSet)
    (referenceTruth : ReferenceFoundation.Formula → Prop)
    (resonanceTruth : HFSet → HFSet → HFSet → Prop)
    (formula : ResonanceFormula) : Prop :=
  ∀ first second : ResonanceVariable → I,
    (∀ var, approxBisim inc (first var) (second var)) →
      ((formula.toIncProof encode first).RealizeWith
          referenceTruth resonanceTruth ↔
        (formula.toIncProof encode second).RealizeWith
          referenceTruth resonanceTruth)

theorem exactDescent_iff_all_translatedIncProof_invariant
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (encode : I → HFSet)
    (referenceTruth : ReferenceFoundation.Formula → Prop)
    (resonanceTruth : HFSet → HFSet → HFSet → Prop)
    (agrees : ∀ leftValue rightValue outputValue,
      resonanceTruth (encode leftValue) (encode rightValue)
          (encode outputValue) ↔
        inc.resonance leftValue rightValue outputValue) :
    ResonanceRelationDescendsExactly inc ↔
      ∀ formula : ResonanceFormula,
        formula.IncProofBisimulationInvariant inc encode
          referenceTruth resonanceTruth := by
  rw [exactDescent_iff_all_resonanceFormula_invariant]
  constructor <;> intro invariant formula first second related
  · rw [formula.toIncProof_realize_iff encode referenceTruth resonanceTruth
        agrees first,
      formula.toIncProof_realize_iff encode referenceTruth resonanceTruth
        agrees second]
    exact invariant formula first second related
  · rw [← formula.toIncProof_realize_iff encode referenceTruth resonanceTruth
        agrees first,
      ← formula.toIncProof_realize_iff encode referenceTruth resonanceTruth
        agrees second]
    exact invariant formula first second related

theorem exactDescent_iff_hfIncProof_translation_invariant
    (referenceTruth : ReferenceFoundation.Formula → Prop) :
    ResonanceRelationDescendsExactly hfIncidence ↔
      ∀ formula : ResonanceFormula,
        formula.IncProofBisimulationInvariant hfIncidence id
          referenceTruth hfIncidence.resonance := by
  exact exactDescent_iff_all_translatedIncProof_invariant hfIncidence id
    referenceTruth hfIncidence.resonance (fun _ _ _ => Iff.rfl)

/- Structural obstruction generators for functional resonance.  A selector
   disagreement at bisimilar inputs creates a local input obstruction, while a
   non-singleton bisimulation class around a selected output creates an output
   obstruction.  These avoid exhaustive search entirely. -/
theorem functional_left_selector_disagreement_obstructs
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    {left₁ left₂ right output₁ output₂ : I}
    (related : approxBisim inc left₁ left₂)
    (firstSelected : inc.glue left₁ right = some output₁)
    (secondSelected : inc.glue left₂ right = some output₂)
    (different : output₁ ≠ output₂) :
    LocalResonanceDescentCandidate.IsObstruction inc
      ⟨.left, left₁, left₂, right, output₁⟩ := by
  refine ⟨related, ?_⟩
  intro exactRelation
  have firstResonates : inc.resonance left₁ right output₁ :=
    inc.selected_resonates firstSelected
  have secondResonates : inc.resonance left₂ right output₁ :=
    exactRelation.mp firstResonates
  have secondAlsoSelects := selectedComplete secondResonates
  rw [secondSelected] at secondAlsoSelects
  exact different (Option.some.inj secondAlsoSelects.symm)

theorem functional_right_selector_disagreement_obstructs
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    {left right₁ right₂ output₁ output₂ : I}
    (related : approxBisim inc right₁ right₂)
    (firstSelected : inc.glue left right₁ = some output₁)
    (secondSelected : inc.glue left right₂ = some output₂)
    (different : output₁ ≠ output₂) :
    LocalResonanceDescentCandidate.IsObstruction inc
      ⟨.right, right₁, right₂, left, output₁⟩ := by
  refine ⟨related, ?_⟩
  intro exactRelation
  have firstResonates : inc.resonance left right₁ output₁ :=
    inc.selected_resonates firstSelected
  have secondResonates : inc.resonance left right₂ output₁ :=
    exactRelation.mp firstResonates
  have secondAlsoSelects := selectedComplete secondResonates
  rw [secondSelected] at secondAlsoSelects
  exact different (Option.some.inj secondAlsoSelects.symm)

theorem functional_selected_output_class_obstructs
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    {left right output₁ output₂ : I}
    (selected : inc.glue left right = some output₁)
    (related : approxBisim inc output₁ output₂)
    (different : output₁ ≠ output₂) :
    LocalResonanceDescentCandidate.IsObstruction inc
      ⟨.output, output₁, output₂, left, right⟩ := by
  refine ⟨related, ?_⟩
  intro exactRelation
  have firstResonates : inc.resonance left right output₁ :=
    inc.selected_resonates selected
  have secondResonates : inc.resonance left right output₂ :=
    exactRelation.mp firstResonates
  have secondSelected := selectedComplete secondResonates
  rw [selected] at secondSelected
  exact different (Option.some.inj secondSelected)

theorem functional_left_selector_disagreement_obstructs_at_either_output
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    {left₁ left₂ right output₁ output₂ testOutput : I}
    (related : approxBisim inc left₁ left₂)
    (firstSelected : inc.glue left₁ right = some output₁)
    (secondSelected : inc.glue left₂ right = some output₂)
    (different : output₁ ≠ output₂)
    (testIsSelected : testOutput = output₁ ∨ testOutput = output₂) :
    LocalResonanceDescentCandidate.IsObstruction inc
      ⟨.left, left₁, left₂, right, testOutput⟩ := by
  rcases testIsSelected with rfl | rfl
  · exact functional_left_selector_disagreement_obstructs
      selectedComplete related firstSelected secondSelected different
  · have reversed : LocalResonanceDescentCandidate.IsObstruction inc
        ⟨.left, left₂, left₁, right, testOutput⟩ :=
      functional_left_selector_disagreement_obstructs selectedComplete
        (approxBisim_symm related) secondSelected firstSelected different.symm
    exact (LocalResonanceDescentCandidate.isObstruction_swap_iff inc
      ⟨.left, left₂, left₁, right, testOutput⟩).mpr reversed

theorem functional_right_selector_disagreement_obstructs_at_either_output
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    {left right₁ right₂ output₁ output₂ testOutput : I}
    (related : approxBisim inc right₁ right₂)
    (firstSelected : inc.glue left right₁ = some output₁)
    (secondSelected : inc.glue left right₂ = some output₂)
    (different : output₁ ≠ output₂)
    (testIsSelected : testOutput = output₁ ∨ testOutput = output₂) :
    LocalResonanceDescentCandidate.IsObstruction inc
      ⟨.right, right₁, right₂, left, testOutput⟩ := by
  rcases testIsSelected with rfl | rfl
  · exact functional_right_selector_disagreement_obstructs
      selectedComplete related firstSelected secondSelected different
  · have reversed : LocalResonanceDescentCandidate.IsObstruction inc
        ⟨.right, right₂, right₁, left, testOutput⟩ :=
      functional_right_selector_disagreement_obstructs selectedComplete
        (approxBisim_symm related) secondSelected firstSelected different.symm
    exact (LocalResonanceDescentCandidate.isObstruction_swap_iff inc
      ⟨.right, right₂, right₁, left, testOutput⟩).mpr reversed

theorem functional_selected_output_class_obstructs_at_either_representative
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    {left right output₁ output₂ selectedOutput : I}
    (selected : inc.glue left right = some selectedOutput)
    (related : approxBisim inc output₁ output₂)
    (different : output₁ ≠ output₂)
    (selectedIsRepresentative : selectedOutput = output₁ ∨
      selectedOutput = output₂) :
    LocalResonanceDescentCandidate.IsObstruction inc
      ⟨.output, output₁, output₂, left, right⟩ := by
  rcases selectedIsRepresentative with rfl | rfl
  · exact functional_selected_output_class_obstructs selectedComplete
      selected related different
  · have reversed : LocalResonanceDescentCandidate.IsObstruction inc
        ⟨.output, selectedOutput, output₁, left, right⟩ :=
      functional_selected_output_class_obstructs selectedComplete selected
        (approxBisim_symm related) different.symm
    exact (LocalResonanceDescentCandidate.isObstruction_swap_iff inc
      ⟨.output, selectedOutput, output₁, left, right⟩).mpr reversed

theorem simplex_output_pair_obstructs
    {first second left right : SimplexId}
    (sameShape : simplexToShape first = simplexToShape second)
    (distinct : first ≠ second)
    (leftInPair : left = first ∨ left = second)
    (rightInPair : right = first ∨ right = second) :
    LocalResonanceDescentCandidate.IsObstruction simplexIncidence
      ⟨.output, first, second, left, right⟩ := by
  have related : approxBisim simplexIncidence first second :=
    (simplexToShape_iff_approxBisim first second).mp sameShape
  by_cases unitLeft : left = SimplexId.v0
  · apply functional_selected_output_class_obstructs_at_either_representative
      (inc := simplexIncidence) (fun resonant => resonant)
      (selectedOutput := right)
    · simp [simplexIncidence, unitLeft]
    · exact related
    · exact distinct
    · exact rightInPair
  · apply functional_selected_output_class_obstructs_at_either_representative
      (inc := simplexIncidence) (fun resonant => resonant)
      (selectedOutput := left)
    · simp [simplexIncidence, unitLeft]
    · exact related
    · exact distinct
    · exact leftInPair

theorem simplex_left_selector_pair_obstructs
    {first second right output₁ output₂ testOutput : SimplexId}
    (sameShape : simplexToShape first = simplexToShape second)
    (firstSelected : simplexIncidence.glue first right = some output₁)
    (secondSelected : simplexIncidence.glue second right = some output₂)
    (different : output₁ ≠ output₂)
    (testInPair : testOutput = output₁ ∨ testOutput = output₂) :
    LocalResonanceDescentCandidate.IsObstruction simplexIncidence
      ⟨.left, first, second, right, testOutput⟩ :=
  functional_left_selector_disagreement_obstructs_at_either_output
    (inc := simplexIncidence) (fun resonant => resonant)
    ((simplexToShape_iff_approxBisim first second).mp sameShape)
    firstSelected secondSelected different testInPair

theorem simplex_right_selector_pair_obstructs
    {left first second output₁ output₂ testOutput : SimplexId}
    (sameShape : simplexToShape first = simplexToShape second)
    (firstSelected : simplexIncidence.glue left first = some output₁)
    (secondSelected : simplexIncidence.glue left second = some output₂)
    (different : output₁ ≠ output₂)
    (testInPair : testOutput = output₁ ∨ testOutput = output₂) :
    LocalResonanceDescentCandidate.IsObstruction simplexIncidence
      ⟨.right, first, second, left, testOutput⟩ :=
  functional_right_selector_disagreement_obstructs_at_either_output
    (inc := simplexIncidence) (fun resonant => resonant)
    ((simplexToShape_iff_approxBisim first second).mp sameShape)
    firstSelected secondSelected different testInPair

theorem simplexStructuralCanonicalCandidate_isObstruction
    (parameter : SimplexStructuralObstructionOrbitParameter) :
    (simplexStructuralCanonicalCandidate parameter).IsObstruction
      simplexIncidence := by
  rcases parameter with parameter | parameter
  · simpa [simplexStructuralCanonicalCandidate] using
      (simplex_left_selector_pair_obstructs
        (first := SimplexId.v0) (second := .v1) (right := .v0)
        (output₁ := .v0) (output₂ := .v1)
        (testOutput := simplexChooseRepresentative .v0 .v1 parameter)
        rfl (by simp [simplexIncidence]) (by simp [simplexIncidence])
        (by simp) (simplexChooseRepresentative_mem_pair .v0 .v1 parameter))
  · rcases parameter with parameter | parameter
    · simpa [simplexStructuralCanonicalCandidate] using
        (simplex_left_selector_pair_obstructs
          (first := SimplexId.v1) (second := .v0) (right := .v0)
          (output₁ := .v1) (output₂ := .v0)
          (testOutput := simplexChooseRepresentative .v1 .v0 parameter)
          rfl (by simp [simplexIncidence]) (by simp [simplexIncidence])
          (by simp) (simplexChooseRepresentative_mem_pair .v1 .v0 parameter))
    · rcases parameter with parameter | parameter
      · let fixed := simplexFixedSlotPattern SimplexId.v1 .v2 parameter
        have fixedMem := simplexFixedSlotPattern_mem_pair .v1 .v2 parameter
        simpa [simplexStructuralCanonicalCandidate, fixed] using
          (simplex_left_selector_pair_obstructs
            (first := SimplexId.v1) (second := .v2) (right := fixed.1)
            (output₁ := .v1) (output₂ := .v2) (testOutput := fixed.2)
            rfl (by simp [simplexIncidence]) (by simp [simplexIncidence])
            (by simp) fixedMem.2)
      · rcases parameter with parameter | parameter
        · let fixed := simplexFixedSlotPattern SimplexId.e01 .e02 parameter
          have fixedMem := simplexFixedSlotPattern_mem_pair .e01 .e02 parameter
          simpa [simplexStructuralCanonicalCandidate, fixed] using
            (simplex_left_selector_pair_obstructs
              (first := SimplexId.e01) (second := .e02) (right := fixed.1)
              (output₁ := .e01) (output₂ := .e02)
              (testOutput := fixed.2) rfl
              (by simp [simplexIncidence]) (by simp [simplexIncidence])
              (by simp) fixedMem.2)
        · rcases parameter with parameter | parameter
          · simpa [simplexStructuralCanonicalCandidate] using
              (simplex_right_selector_pair_obstructs
                (left := SimplexId.v0) (first := .v0) (second := .v1)
                (output₁ := .v0) (output₂ := .v1)
                (testOutput := simplexChooseRepresentative .v0 .v1 parameter)
                rfl (by simp [simplexIncidence]) (by simp [simplexIncidence])
                (by simp)
                (simplexChooseRepresentative_mem_pair .v0 .v1 parameter))
          · rcases parameter with parameter | parameter
            · simpa [simplexStructuralCanonicalCandidate] using
                (simplex_right_selector_pair_obstructs
                  (left := SimplexId.v0) (first := .v1) (second := .v0)
                  (output₁ := .v1) (output₂ := .v0)
                  (testOutput := simplexChooseRepresentative .v1 .v0 parameter)
                  rfl (by simp [simplexIncidence]) (by simp [simplexIncidence])
                  (by simp)
                  (simplexChooseRepresentative_mem_pair .v1 .v0 parameter))
            · rcases parameter with parameter | parameter
              · let pair : SimplexId × SimplexId :=
                    if parameter.1.val = 0 then (.v0, .v1)
                    else if parameter.1.val = 1 then (.v1, .v0)
                    else (.v1, .v2)
                let fixed := simplexFixedSlotPattern pair.1 pair.2 parameter.2
                have fixedMem := simplexFixedSlotPattern_mem_pair
                  pair.1 pair.2 parameter.2
                have pairFacts : simplexToShape pair.1 = simplexToShape pair.2 ∧
                    pair.1 ≠ pair.2 := by
                  by_cases firstCase : parameter.1.val = 0
                  · simp [pair, firstCase, simplexToShape]
                  · by_cases secondCase : parameter.1.val = 1
                    · simp [pair, secondCase, simplexToShape]
                    · simp [pair, firstCase, secondCase, simplexToShape]
                simpa [simplexStructuralCanonicalCandidate, pair, fixed] using
                  (simplex_output_pair_obstructs pairFacts.1 pairFacts.2
                    fixedMem.1 fixedMem.2)
              · let fixed := simplexFixedSlotPattern SimplexId.e01 .e02 parameter
                have fixedMem := simplexFixedSlotPattern_mem_pair .e01 .e02 parameter
                simpa [simplexStructuralCanonicalCandidate, fixed] using
                  (simplex_output_pair_obstructs (first := SimplexId.e01)
                    (second := .e02) (left := fixed.1) (right := fixed.2)
                    rfl (by simp) fixedMem.1 fixedMem.2)

theorem simplexStructuralCanonicalCandidate_isSupportMinimal
    (parameter : SimplexStructuralObstructionOrbitParameter) :
    (simplexStructuralCanonicalCandidate parameter).IsSupportMinimalObstruction
      simplexIncidence := by
  have fixedSlots :=
    simplexStructuralCanonicalCandidate_fixedSlots_mem_pair parameter
  exact (simplexStructuralCanonicalCandidate parameter).isSupportMinimal_of_pair
    (simplexStructuralCanonicalCandidate_isObstruction parameter)
    fixedSlots.1 fixedSlots.2

theorem simplex_support_card_eq_two_of_supportMinimal
    {candidate : LocalResonanceDescentCandidate SimplexId}
    (minimal : candidate.IsSupportMinimalObstruction simplexIncidence) :
    candidate.support.card = 2 := by
  let witnessParameter : SimplexStructuralObstructionOrbitParameter :=
    Sum.inl 0
  let witness := simplexStructuralCanonicalCandidate witnessParameter
  have witnessObstruction : witness.IsObstruction simplexIncidence :=
    simplexStructuralCanonicalCandidate_isObstruction witnessParameter
  have witnessFixed :=
    simplexStructuralCanonicalCandidate_fixedSlots_mem_pair witnessParameter
  have witnessCard : witness.support.card = 2 :=
    witness.support_card_eq_two_of_pair
      (witness.distinct_representatives_of_obstruction witnessObstruction)
      witnessFixed.1 witnessFixed.2
  have lower := candidate.two_le_support_card_of_obstruction minimal.1
  have upper := minimal.2 witness witnessObstruction
  omega

theorem simplex_supportMinimal_fixedSlots_mem_pair
    {candidate : LocalResonanceDescentCandidate SimplexId}
    (minimal : candidate.IsSupportMinimalObstruction simplexIncidence) :
    (candidate.fixed₁ = candidate.first ∨
        candidate.fixed₁ = candidate.second) ∧
      (candidate.fixed₂ = candidate.first ∨
        candidate.fixed₂ = candidate.second) :=
  candidate.fixedSlots_mem_pair_of_card_eq_two minimal.1
    (simplex_support_card_eq_two_of_supportMinimal minimal)

theorem simplex_supportMinimal_representative_shape
    {candidate : LocalResonanceDescentCandidate SimplexId}
    (minimal : candidate.IsSupportMinimalObstruction simplexIncidence) :
    (simplexToShape candidate.first = .vertex ∨
      simplexToShape candidate.first = .edgeShape) ∧
      simplexToShape candidate.first = simplexToShape candidate.second := by
  have sameShape := (simplexToShape_iff_approxBisim
    candidate.first candidate.second).mpr minimal.1.1
  have distinct :=
    candidate.distinct_representatives_of_obstruction minimal.1
  constructor
  · cases firstCase : candidate.first <;>
      cases secondCase : candidate.second <;>
      simp [firstCase, secondCase, simplexToShape] at sameShape distinct ⊢
  · exact sameShape

theorem simplex_output_supportMinimal_structural_normalization
    {first second fixed₁ fixed₂ : SimplexId}
    (minimal : LocalResonanceDescentCandidate.IsSupportMinimalObstruction
      simplexIncidence ⟨.output, first, second, fixed₁, fixed₂⟩) :
    ∃ parameter : SimplexStructuralObstructionOrbitParameter,
      ∃ automorphism : ResonanceBisimulationAutomorphism simplexIncidence,
        automorphism.mapCandidate
            ⟨.output, first, second, fixed₁, fixed₂⟩ =
          simplexStructuralCanonicalCandidate parameter := by
  let candidate : LocalResonanceDescentCandidate SimplexId :=
    ⟨.output, first, second, fixed₁, fixed₂⟩
  have fixedMem := simplex_supportMinimal_fixedSlots_mem_pair minimal
  have shape := simplex_supportMinimal_representative_shape minimal
  have distinct := candidate.distinct_representatives_of_obstruction minimal.1
  rcases shape.1 with vertexShape | edgeShape
  · have secondVertex : simplexToShape second = .vertex := by
      rw [← shape.2]
      exact vertexShape
    rcases simplex_vertex_pair_automorphism vertexShape secondVertex distinct with
      ⟨firstUnit, automorphism, mapsFirst, mapsSecond⟩ |
      ⟨secondUnit, automorphism, mapsFirst, mapsSecond⟩ |
      ⟨firstNonunit, secondNonunit, automorphism, mapsFirst, mapsSecond⟩
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v0 ∨
          automorphism.toEquiv fixed₁ = .v1 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v0 ∨
          automorphism.toEquiv fixed₂ = .v1 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      rcases exists_simplexFixedSlotPattern_eq_of_mem_pair
        mappedFixed₁ mappedFixed₂ with ⟨pattern, patternEq⟩
      refine ⟨simplexOutputVertexParameter 0 pattern, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexOutputVertexParameter, simplexStructuralCanonicalCandidate,
        mapsFirst, mapsSecond, patternEq]
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v1 ∨
          automorphism.toEquiv fixed₁ = .v0 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v1 ∨
          automorphism.toEquiv fixed₂ = .v0 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      rcases exists_simplexFixedSlotPattern_eq_of_mem_pair
        mappedFixed₁ mappedFixed₂ with ⟨pattern, patternEq⟩
      refine ⟨simplexOutputVertexParameter 1 pattern, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexOutputVertexParameter, simplexStructuralCanonicalCandidate,
        mapsFirst, mapsSecond, patternEq]
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v1 ∨
          automorphism.toEquiv fixed₁ = .v2 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v1 ∨
          automorphism.toEquiv fixed₂ = .v2 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      rcases exists_simplexFixedSlotPattern_eq_of_mem_pair
        mappedFixed₁ mappedFixed₂ with ⟨pattern, patternEq⟩
      refine ⟨simplexOutputVertexParameter 2 pattern, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexOutputVertexParameter, simplexStructuralCanonicalCandidate,
        mapsFirst, mapsSecond, patternEq]
  · have secondEdge : simplexToShape second = .edgeShape := by
      rw [← shape.2]
      exact edgeShape
    rcases simplex_edge_pair_automorphism edgeShape secondEdge distinct with
      ⟨automorphism, mapsFirst, mapsSecond⟩
    have mappedFixed₁ : automorphism.toEquiv fixed₁ = .e01 ∨
        automorphism.toEquiv fixed₁ = .e02 := by
      rcases fixedMem.1 with h | h
      · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
      · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
    have mappedFixed₂ : automorphism.toEquiv fixed₂ = .e01 ∨
        automorphism.toEquiv fixed₂ = .e02 := by
      rcases fixedMem.2 with h | h
      · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
      · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
    rcases exists_simplexFixedSlotPattern_eq_of_mem_pair
      mappedFixed₁ mappedFixed₂ with ⟨pattern, patternEq⟩
    refine ⟨simplexOutputEdgeParameter pattern, automorphism, ?_⟩
    simp [ResonanceBisimulationAutomorphism.mapCandidate,
      simplexOutputEdgeParameter, simplexStructuralCanonicalCandidate,
      mapsFirst, mapsSecond, patternEq]

theorem simplex_left_supportMinimal_structural_normalization
    {first second fixed₁ fixed₂ : SimplexId}
    (minimal : LocalResonanceDescentCandidate.IsSupportMinimalObstruction
      simplexIncidence ⟨.left, first, second, fixed₁, fixed₂⟩) :
    ∃ parameter : SimplexStructuralObstructionOrbitParameter,
      ∃ automorphism : ResonanceBisimulationAutomorphism simplexIncidence,
        automorphism.mapCandidate
            ⟨.left, first, second, fixed₁, fixed₂⟩ =
          simplexStructuralCanonicalCandidate parameter := by
  let candidate : LocalResonanceDescentCandidate SimplexId :=
    ⟨.left, first, second, fixed₁, fixed₂⟩
  have fixedMem := simplex_supportMinimal_fixedSlots_mem_pair minimal
  have shape := simplex_supportMinimal_representative_shape minimal
  have distinct := candidate.distinct_representatives_of_obstruction minimal.1
  rcases shape.1 with vertexShape | edgeShape
  · have secondVertex : simplexToShape second = .vertex := by
      rw [← shape.2]; exact vertexShape
    rcases simplex_vertex_pair_automorphism vertexShape secondVertex distinct with
      ⟨firstUnit, automorphism, mapsFirst, mapsSecond⟩ |
      ⟨secondUnit, automorphism, mapsFirst, mapsSecond⟩ |
      ⟨firstNonunit, secondNonunit, automorphism, mapsFirst, mapsSecond⟩
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v0 ∨
          automorphism.toEquiv fixed₁ = .v1 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v0 ∨
          automorphism.toEquiv fixed₂ = .v1 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have fixed₁Unit : automorphism.toEquiv fixed₁ = .v0 := by
        rcases mappedFixed₁ with h | h
        · exact h
        · exfalso
          have obstruction :=
            (automorphism.mapCandidate_supportMinimal minimal).1.2
          rcases mappedFixed₂ with h₂ | h₂ <;>
            simp [ResonanceBisimulationAutomorphism.mapCandidate,
              simplexIncidence, mapsFirst, mapsSecond, h, h₂] at obstruction
      rcases exists_simplexChooseRepresentative_eq_of_mem_pair mappedFixed₂ with
        ⟨choice, choiceEq⟩
      refine ⟨simplexLeftVertexUnitFirstParameter choice, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexLeftVertexUnitFirstParameter,
        simplexStructuralCanonicalCandidate, mapsFirst, mapsSecond,
        fixed₁Unit, choiceEq]
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v1 ∨
          automorphism.toEquiv fixed₁ = .v0 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v1 ∨
          automorphism.toEquiv fixed₂ = .v0 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have fixed₁Unit : automorphism.toEquiv fixed₁ = .v0 := by
        rcases mappedFixed₁ with h | h
        · exfalso
          have obstruction :=
            (automorphism.mapCandidate_supportMinimal minimal).1.2
          rcases mappedFixed₂ with h₂ | h₂ <;>
            simp [ResonanceBisimulationAutomorphism.mapCandidate,
              simplexIncidence, mapsFirst, mapsSecond, h, h₂] at obstruction
        · exact h
      rcases exists_simplexChooseRepresentative_eq_of_mem_pair mappedFixed₂ with
        ⟨choice, choiceEq⟩
      refine ⟨simplexLeftVertexUnitSecondParameter choice, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexLeftVertexUnitSecondParameter,
        simplexStructuralCanonicalCandidate, mapsFirst, mapsSecond,
        fixed₁Unit, choiceEq]
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v1 ∨
          automorphism.toEquiv fixed₁ = .v2 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v1 ∨
          automorphism.toEquiv fixed₂ = .v2 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      rcases exists_simplexFixedSlotPattern_eq_of_mem_pair
        mappedFixed₁ mappedFixed₂ with ⟨pattern, patternEq⟩
      refine ⟨simplexLeftVertexNonunitParameter pattern, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexLeftVertexNonunitParameter,
        simplexStructuralCanonicalCandidate, mapsFirst, mapsSecond, patternEq]
  · have secondEdge : simplexToShape second = .edgeShape := by
      rw [← shape.2]; exact edgeShape
    rcases simplex_edge_pair_automorphism edgeShape secondEdge distinct with
      ⟨automorphism, mapsFirst, mapsSecond⟩
    have mappedFixed₁ : automorphism.toEquiv fixed₁ = .e01 ∨
        automorphism.toEquiv fixed₁ = .e02 := by
      rcases fixedMem.1 with h | h
      · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
      · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
    have mappedFixed₂ : automorphism.toEquiv fixed₂ = .e01 ∨
        automorphism.toEquiv fixed₂ = .e02 := by
      rcases fixedMem.2 with h | h
      · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
      · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
    rcases exists_simplexFixedSlotPattern_eq_of_mem_pair
      mappedFixed₁ mappedFixed₂ with ⟨pattern, patternEq⟩
    refine ⟨simplexLeftEdgeParameter pattern, automorphism, ?_⟩
    simp [ResonanceBisimulationAutomorphism.mapCandidate,
      simplexLeftEdgeParameter, simplexStructuralCanonicalCandidate,
      mapsFirst, mapsSecond, patternEq]

theorem simplex_right_supportMinimal_structural_normalization
    {first second fixed₁ fixed₂ : SimplexId}
    (minimal : LocalResonanceDescentCandidate.IsSupportMinimalObstruction
      simplexIncidence ⟨.right, first, second, fixed₁, fixed₂⟩) :
    ∃ parameter : SimplexStructuralObstructionOrbitParameter,
      ∃ automorphism : ResonanceBisimulationAutomorphism simplexIncidence,
        automorphism.mapCandidate
            ⟨.right, first, second, fixed₁, fixed₂⟩ =
          simplexStructuralCanonicalCandidate parameter := by
  let candidate : LocalResonanceDescentCandidate SimplexId :=
    ⟨.right, first, second, fixed₁, fixed₂⟩
  have fixedMem := simplex_supportMinimal_fixedSlots_mem_pair minimal
  have shape := simplex_supportMinimal_representative_shape minimal
  have distinct := candidate.distinct_representatives_of_obstruction minimal.1
  rcases shape.1 with vertexShape | edgeShape
  · have secondVertex : simplexToShape second = .vertex := by
      rw [← shape.2]; exact vertexShape
    rcases simplex_vertex_pair_automorphism vertexShape secondVertex distinct with
      ⟨firstUnit, automorphism, mapsFirst, mapsSecond⟩ |
      ⟨secondUnit, automorphism, mapsFirst, mapsSecond⟩ |
      ⟨firstNonunit, secondNonunit, automorphism, mapsFirst, mapsSecond⟩
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v0 ∨
          automorphism.toEquiv fixed₁ = .v1 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v0 ∨
          automorphism.toEquiv fixed₂ = .v1 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have fixed₁Unit : automorphism.toEquiv fixed₁ = .v0 := by
        rcases mappedFixed₁ with h | h
        · exact h
        · exfalso
          have obstruction :=
            (automorphism.mapCandidate_supportMinimal minimal).1.2
          rcases mappedFixed₂ with h₂ | h₂ <;>
            simp [ResonanceBisimulationAutomorphism.mapCandidate,
              simplexIncidence, mapsFirst, mapsSecond, h, h₂] at obstruction
      rcases exists_simplexChooseRepresentative_eq_of_mem_pair mappedFixed₂ with
        ⟨choice, choiceEq⟩
      refine ⟨simplexRightVertexUnitFirstParameter choice, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexRightVertexUnitFirstParameter,
        simplexStructuralCanonicalCandidate, mapsFirst, mapsSecond,
        fixed₁Unit, choiceEq]
    · have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v1 ∨
          automorphism.toEquiv fixed₁ = .v0 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v1 ∨
          automorphism.toEquiv fixed₂ = .v0 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have fixed₁Unit : automorphism.toEquiv fixed₁ = .v0 := by
        rcases mappedFixed₁ with h | h
        · exfalso
          have obstruction :=
            (automorphism.mapCandidate_supportMinimal minimal).1.2
          rcases mappedFixed₂ with h₂ | h₂ <;>
            simp [ResonanceBisimulationAutomorphism.mapCandidate,
              simplexIncidence, mapsFirst, mapsSecond, h, h₂] at obstruction
        · exact h
      rcases exists_simplexChooseRepresentative_eq_of_mem_pair mappedFixed₂ with
        ⟨choice, choiceEq⟩
      refine ⟨simplexRightVertexUnitSecondParameter choice, automorphism, ?_⟩
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexRightVertexUnitSecondParameter,
        simplexStructuralCanonicalCandidate, mapsFirst, mapsSecond,
        fixed₁Unit, choiceEq]
    · exfalso
      have mappedFixed₁ : automorphism.toEquiv fixed₁ = .v1 ∨
          automorphism.toEquiv fixed₁ = .v2 := by
        rcases fixedMem.1 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have mappedFixed₂ : automorphism.toEquiv fixed₂ = .v1 ∨
          automorphism.toEquiv fixed₂ = .v2 := by
        rcases fixedMem.2 with h | h
        · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
        · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
      have obstruction :=
        (automorphism.mapCandidate_supportMinimal minimal).1.2
      rcases mappedFixed₁ with h₁ | h₁ <;>
        rcases mappedFixed₂ with h₂ | h₂ <;>
        simp [ResonanceBisimulationAutomorphism.mapCandidate,
          simplexIncidence, mapsFirst, mapsSecond, h₁, h₂] at obstruction
  · have secondEdge : simplexToShape second = .edgeShape := by
      rw [← shape.2]; exact edgeShape
    rcases simplex_edge_pair_automorphism edgeShape secondEdge distinct with
      ⟨automorphism, mapsFirst, mapsSecond⟩
    exfalso
    have mappedFixed₁ : automorphism.toEquiv fixed₁ = .e01 ∨
        automorphism.toEquiv fixed₁ = .e02 := by
      rcases fixedMem.1 with h | h
      · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
      · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
    have mappedFixed₂ : automorphism.toEquiv fixed₂ = .e01 ∨
        automorphism.toEquiv fixed₂ = .e02 := by
      rcases fixedMem.2 with h | h
      · left; exact (congrArg automorphism.toEquiv h).trans mapsFirst
      · right; exact (congrArg automorphism.toEquiv h).trans mapsSecond
    have obstruction :=
      (automorphism.mapCandidate_supportMinimal minimal).1.2
    rcases mappedFixed₁ with h₁ | h₁ <;>
      rcases mappedFixed₂ with h₂ | h₂ <;>
      simp [ResonanceBisimulationAutomorphism.mapCandidate,
        simplexIncidence, mapsFirst, mapsSecond, h₁, h₂] at obstruction

theorem simplex_supportMinimal_structural_normalization
    {candidate : LocalResonanceDescentCandidate SimplexId}
    (minimal : candidate.IsSupportMinimalObstruction simplexIncidence) :
    ∃ parameter : SimplexStructuralObstructionOrbitParameter,
      ∃ automorphism : ResonanceBisimulationAutomorphism simplexIncidence,
        automorphism.mapCandidate candidate =
          simplexStructuralCanonicalCandidate parameter := by
  rcases candidate with ⟨coordinate, first, second, fixed₁, fixed₂⟩
  cases coordinate with
  | left => exact simplex_left_supportMinimal_structural_normalization minimal
  | right => exact simplex_right_supportMinimal_structural_normalization minimal
  | output => exact simplex_output_supportMinimal_structural_normalization minimal

def SimplexMinimalObstructionOrbit :=
  {orbit : Finset (LocalResonanceDescentCandidate SimplexId) //
    orbit ∈ simplexFiniteSupportMinimalObstructionOrbits}

instance simplexMinimalObstructionOrbitFintype :
    Fintype SimplexMinimalObstructionOrbit :=
  ⟨simplexFiniteSupportMinimalObstructionOrbits.attach, by
    intro orbit
    simp [SimplexMinimalObstructionOrbit]⟩

def simplexStructuralMinimalOrbitMap
    (parameter : SimplexStructuralObstructionOrbitParameter) :
    SimplexMinimalObstructionOrbit := by
  refine ⟨simplexStructuralCanonicalOrbit parameter, ?_⟩
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  apply (mem_finiteSupportMinimalObstructionOrbits_iff simplexIncidence _).mpr
  exact ⟨simplexStructuralCanonicalCandidate parameter,
    simplexStructuralCanonicalCandidate_isSupportMinimal parameter, rfl⟩

theorem simplexStructuralMinimalOrbitMap_injective :
    Function.Injective simplexStructuralMinimalOrbitMap := by
  intro firstParameter secondParameter mapEqual
  have orbitEqual : simplexStructuralCanonicalOrbit firstParameter =
      simplexStructuralCanonicalOrbit secondParameter :=
    congrArg Subtype.val mapEqual
  have firstMem :=
    simplexStructuralCanonicalCandidate_mem_orbit firstParameter
  have secondMem : simplexStructuralCanonicalCandidate secondParameter ∈
      simplexStructuralCanonicalOrbit firstParameter := by
    rw [orbitEqual]
    exact simplexStructuralCanonicalCandidate_mem_orbit secondParameter
  apply simplexStructuralCanonicalNormalForm_injective
  exact simplex_minimal_orbit_normalForm_eq
    (simplexStructuralMinimalOrbitMap firstParameter).property
    firstMem secondMem

theorem simplexStructuralMinimalOrbitMap_surjective_without_card :
    Function.Surjective simplexStructuralMinimalOrbitMap := by
  intro target
  letI : DecidableRel (approxBisim simplexIncidence) :=
    simplexApproxBisimDecidable
  letI : ∀ left right output,
      Decidable (simplexIncidence.resonance left right output) :=
    simplexResonanceDecidable
  rcases (mem_finiteSupportMinimalObstructionOrbits_iff simplexIncidence
    target.val).mp target.property with ⟨candidate, minimal, orbitEq⟩
  rcases simplex_supportMinimal_structural_normalization minimal with
    ⟨parameter, automorphism, normalized⟩
  refine ⟨parameter, Subtype.ext ?_⟩
  change simplexStructuralCanonicalOrbit parameter = target.val
  rw [orbitEq]
  exact (finiteLocalResonanceAutomorphismOrbit_eq_of_related
    simplexIncidence ⟨automorphism, normalized⟩).symm

theorem simplexStructuralMinimalOrbitMap_bijective :
    Function.Bijective simplexStructuralMinimalOrbitMap := by
  exact ⟨simplexStructuralMinimalOrbitMap_injective,
    simplexStructuralMinimalOrbitMap_surjective_without_card⟩

noncomputable def simplexStructuralMinimalOrbitEquiv :
    SimplexStructuralObstructionOrbitParameter ≃
      SimplexMinimalObstructionOrbit :=
  Equiv.ofBijective simplexStructuralMinimalOrbitMap
    simplexStructuralMinimalOrbitMap_bijective

theorem simplexMinimalObstructionOrbit_card :
    Fintype.card SimplexMinimalObstructionOrbit = 32 := by
  rw [← simplex_structural_orbit_parameter_card]
  exact Fintype.card_congr simplexStructuralMinimalOrbitEquiv.symm

theorem simplex_minimal_obstruction_orbit_count :
    simplexFiniteSupportMinimalObstructionOrbits.card = 32 := by
  rw [← Finset.card_attach]
  exact simplexMinimalObstructionOrbit_card

theorem exact_descent_forces_functional_selected_output_classes_singleton
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    (descent : ResonanceRelationDescendsExactly inc)
    {left right output₁ output₂ : I}
    (selected : inc.glue left right = some output₁)
    (related : approxBisim inc output₁ output₂) :
    output₁ = output₂ := by
  by_contra different
  have obstruction := functional_selected_output_class_obstructs
    selectedComplete selected related different
  have coordinatewise :=
    (resonanceRelationDescendsExactly_iff_coordinatewise inc).mp descent
  exact obstruction.2 (coordinatewise.2.2 obstruction.1)

theorem exact_descent_forces_functional_left_selector_invariance
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (selectedComplete : ∀ {i j k}, inc.resonance i j k →
      inc.glue i j = some k)
    (descent : ResonanceRelationDescendsExactly inc)
    {left₁ left₂ right output₁ output₂ : I}
    (related : approxBisim inc left₁ left₂)
    (firstSelected : inc.glue left₁ right = some output₁)
    (secondSelected : inc.glue left₂ right = some output₂) :
    output₁ = output₂ := by
  by_contra different
  have obstruction := functional_left_selector_disagreement_obstructs
    selectedComplete related firstSelected secondSelected different
  have coordinatewise :=
    (resonanceRelationDescendsExactly_iff_coordinatewise inc).mp descent
  exact obstruction.2 (coordinatewise.1 obstruction.1)

theorem simplex_selector_obstruction_from_functionality :
    LocalResonanceDescentCandidate.IsObstruction simplexIncidence
      ⟨.left, SimplexId.v0, SimplexId.v1,
        SimplexId.face, SimplexId.face⟩ := by
  apply functional_left_selector_disagreement_obstructs
    (inc := simplexIncidence)
    (by intro i j k resonant; exact resonant)
  · exact (simplexToShape_iff_approxBisim .v0 .v1).mp rfl
  · rfl
  · rfl
  · decide

/- Relational positive criterion. `ResonanceRespects` transports a mode to
   some bisimilar mode at related inputs; output saturation then makes the
   particular representative irrelevant. Together these are exactly full
   ternary quotient congruence. -/
def BisimulationOutputSaturated
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop :=
  OutputResonanceCongruent inc

theorem quotientResonanceCongruent_iff_transport_and_outputSaturated
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    QuotientResonanceCongruent inc ↔
      ResonanceRespects inc (approxBisim inc) ∧
        BisimulationOutputSaturated inc := by
  constructor
  · intro congruent
    constructor
    · intro i₁ i₂ j₁ j₂ hi hj
      constructor
      · intro k₁ resonant
        exact ⟨k₁,
          (congruent hi hj (approxBisim_refl inc k₁)).mp resonant,
          approxBisim_refl inc k₁⟩
      · intro k₂ resonant
        exact ⟨k₂,
          (congruent hi hj (approxBisim_refl inc k₂)).mpr resonant,
          approxBisim_refl inc k₂⟩
    · exact (quotientResonanceCongruent_iff_coordinatewise inc).mp
        congruent |>.2.2
  · rintro ⟨transport, outputSaturated⟩
    intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk
    constructor
    · intro resonant
      rcases (transport hi hj).1 resonant with
        ⟨transported, transportedResonant, outputRelated⟩
      have transportedToFirst : inc.resonance i₂ j₂ k₁ :=
        (outputSaturated (approxBisim_symm outputRelated)).mp
          transportedResonant
      exact (outputSaturated hk).mp transportedToFirst
    · intro resonant
      rcases (transport hi hj).2 resonant with
        ⟨transported, transportedResonant, outputRelated⟩
      have transportedToSecond : inc.resonance i₁ j₁ k₂ :=
        (outputSaturated outputRelated).mp transportedResonant
      exact (outputSaturated (approxBisim_symm hk)).mp transportedToSecond

theorem resonanceRelationDescendsExactly_iff_transport_and_outputSaturated
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceRelationDescendsExactly inc ↔
      ResonanceRespects inc (approxBisim inc) ∧
        BisimulationOutputSaturated inc := by
  rw [resonanceRelationDescendsExactly_iff,
    quotientResonanceCongruent_iff_transport_and_outputSaturated]

structure RelationalResonanceDescentSpec
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  transport : ResonanceRespects inc (approxBisim inc)
  outputSaturated : BisimulationOutputSaturated inc

theorem RelationalResonanceDescentSpec.exactDescent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (spec : RelationalResonanceDescentSpec inc) :
    ResonanceRelationDescendsExactly inc :=
  (resonanceRelationDescendsExactly_iff_transport_and_outputSaturated inc).mpr
    ⟨spec.transport, spec.outputSaturated⟩

theorem RelationalResonanceDescentSpec.ofExactDescent
    {I R T : Type u} [DecidableEq I] {inc : Incidence I R T}
    (descent : ResonanceRelationDescendsExactly inc) :
    RelationalResonanceDescentSpec inc := by
  rcases
    (resonanceRelationDescendsExactly_iff_transport_and_outputSaturated inc).mp
      descent with ⟨transport, outputSaturated⟩
  exact ⟨transport, outputSaturated⟩

theorem saturatedSimplex_relationalDescentSpec :
    RelationalResonanceDescentSpec saturatedSimplexIncidence :=
  RelationalResonanceDescentSpec.ofExactDescent
    saturatedSimplex_resonance_descends_exactly

theorem shapeModeSimplex_relationalDescentSpec :
    RelationalResonanceDescentSpec shapeModeSimplexIncidence :=
  RelationalResonanceDescentSpec.ofExactDescent
    shapeModeSimplex_resonance_descends_exactly

/- Generic class-mode construction.  A classification may be a dimension,
   cell shape, color, orbit label, or any other behavioral invariant.  The
   relational interaction exposes either participant's class as an output
   mode. -/
def classModeResonance
    {I Class : Type u} (classify : I → Class)
    (left right output : I) : Prop :=
  classify output = classify left ∨ classify output = classify right

def SelectorClassModeCompatible
    {I R T Class : Type u} [DecidableEq I]
    (inc : Incidence I R T) (classify : I → Class) : Prop :=
  ∀ {left right output}, inc.glue left right = some output →
    classify output = classify left ∨ classify output = classify right

def Incidence.withClassModeResonance
    {I R T Class : Type u} [DecidableEq I]
    (inc : Incidence I R T) (classify : I → Class)
    (compatible : SelectorClassModeCompatible inc classify) :
    Incidence I R T where
  boundary := inc.boundary
  typeFunc := inc.typeFunc
  glue := inc.glue
  resonance := classModeResonance classify
  selected_resonates := compatible
  unit := inc.unit
  guards := inc.guards
  boundaryMatrix := inc.boundaryMatrix
  laplacian := inc.laplacian
  type_consistent := inc.type_consistent
  sign_rules := inc.sign_rules
  multiplicities := inc.multiplicities
  well_founded := inc.well_founded
  unit_left := inc.unit_left
  unit_right := inc.unit_right
  type_preserve := inc.type_preserve

theorem withClassModeResonance_approxBisim_iff
    {I R T Class : Type u} [DecidableEq I]
    (inc : Incidence I R T) (classify : I → Class)
    (compatible : SelectorClassModeCompatible inc classify)
    (left right : I) :
    approxBisim (inc.withClassModeResonance classify compatible) left right ↔
      approxBisim inc left right := by
  rfl

structure ClassModeQuotientSpec
    {I R T Class : Type u} [DecidableEq I]
    (inc : Incidence I R T) (classify : I → Class) : Prop where
  selectorCompatible : SelectorClassModeCompatible inc classify
  kernel : ∀ left right,
    classify left = classify right ↔ approxBisim inc left right
  surjective : ∀ classValue : Class, ∃ value, classify value = classValue

def ClassModeQuotientSpec.model
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) : Incidence I R T :=
  inc.withClassModeResonance classify spec.selectorCompatible

theorem ClassModeQuotientSpec.model_kernel
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) (left right : I) :
    classify left = classify right ↔
      approxBisim spec.model left right := by
  change classify left = classify right ↔
    approxBisim
      (inc.withClassModeResonance classify spec.selectorCompatible) left right
  rw [withClassModeResonance_approxBisim_iff]
  exact spec.kernel left right

theorem ClassModeQuotientSpec.quotientResonanceCongruent
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) :
    QuotientResonanceCongruent spec.model := by
  intro left₁ left₂ right₁ right₂ output₁ output₂
    leftRelated rightRelated outputRelated
  have leftClass := (spec.model_kernel left₁ left₂).mpr leftRelated
  have rightClass := (spec.model_kernel right₁ right₂).mpr rightRelated
  have outputClass := (spec.model_kernel output₁ output₂).mpr outputRelated
  simp only [ClassModeQuotientSpec.model, Incidence.withClassModeResonance,
    classModeResonance]
  rw [leftClass, rightClass, outputClass]

theorem ClassModeQuotientSpec.exactDescent
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) :
    ResonanceRelationDescendsExactly spec.model :=
  exact_descent_of_quotientResonanceCongruent
    spec.quotientResonanceCongruent

def classModeSystem (Class : Type u) : TernaryResonanceSystem where
  Carrier := Class
  resonance := fun left right output => output = left ∨ output = right

def ClassModeQuotientSpec.classificationHom
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) :
    TernaryResonanceHom spec.model.resonanceSystem
      (classModeSystem Class) where
  toFun := classify
  preserves := fun resonant => resonant

theorem ClassModeQuotientSpec.classificationHom_invariant
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) :
    BisimulationInvariantResonanceHom spec.model (classModeSystem Class)
      spec.classificationHom := by
  intro left right related
  exact (spec.model_kernel left right).mpr related

def ClassModeQuotientSpec.quotientRepresentation
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) :
    TernaryResonanceHom
      (bisimulationQuotientResonanceSystem spec.model)
      (classModeSystem Class) :=
  bisimulationQuotientResonanceLift spec.classificationHom
    spec.classificationHom_invariant

theorem ClassModeQuotientSpec.quotientResonance_representation
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify)
    (left right output : I) :
    quotientResonance spec.model
        (Quotient.mk (approxBisimSetoid spec.model) left)
        (Quotient.mk (approxBisimSetoid spec.model) right)
        (Quotient.mk (approxBisimSetoid spec.model) output) ↔
      (classify output = classify left ∨
        classify output = classify right) := by
  rw [quotientResonance_mk_iff spec.quotientResonanceCongruent]
  rfl

def ClassModeQuotientSpec.classification
    {I R T Class : Type u} [DecidableEq I]
    {inc : Incidence I R T} {classify : I → Class}
    (spec : ClassModeQuotientSpec inc classify) :
    BisimulationQuotientClassification (Q := Class) spec.model :=
  bisimulationQuotientClassificationOfKernel spec.model classify
    spec.model_kernel spec.surjective

structure GradedIncidenceQuotientSpec
    {I R T Grade : Type u} [DecidableEq I]
    (inc : Incidence I R T) (grade : I → Grade) : Prop where
  toClassModeSpec : ClassModeQuotientSpec inc grade

/- Standard abstract simplicial complexes: cells are nonempty finite vertex
   sets and the face predicate is downward closed among nonempty subsets. -/
structure FiniteSimplicialComplex (Vertex : Type) [DecidableEq Vertex] where
  IsFace : Finset Vertex → Prop
  decidableFace : DecidablePred IsFace
  face_nonempty : ∀ {vertices}, IsFace vertices → vertices.Nonempty
  downward_closed : ∀ {vertices}, IsFace vertices →
    ∀ {face}, face.Nonempty → face ⊆ vertices → IsFace face

instance FiniteSimplicialComplex.instDecidableFace
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) :
    DecidablePred complex.IsFace := complex.decidableFace

abbrev FiniteSimplicialComplex.Cell
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) :=
  {vertices : Finset Vertex // complex.IsFace vertices}

instance FiniteSimplicialComplex.cellDecidableEq
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) :
    DecidableEq complex.Cell := inferInstance

def FiniteSimplicialComplex.Cell.dimension
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    (cell : complex.Cell) : Nat := cell.val.card - 1

theorem FiniteSimplicialComplex.Cell.nonempty
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    (cell : complex.Cell) : cell.val.Nonempty :=
  complex.face_nonempty cell.property

def FiniteSimplicialComplex.Cell.eraseVertex
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    (cell : complex.Cell) (vertex : Vertex)
    (erasedNonempty : (cell.val.erase vertex).Nonempty) : complex.Cell :=
  ⟨cell.val.erase vertex,
    complex.downward_closed cell.property erasedNonempty
      (Finset.erase_subset vertex cell.val)⟩

theorem FiniteSimplicialComplex.Cell.eraseVertex_dimension
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    (cell : complex.Cell) (vertex : Vertex) (vertexMem : vertex ∈ cell.val)
    (erasedNonempty : (cell.val.erase vertex).Nonempty) :
    (cell.eraseVertex vertex erasedNonempty).dimension + 1 = cell.dimension := by
  have eraseCard := Finset.card_erase_add_one vertexMem
  have erasePositive : 0 < (cell.val.erase vertex).card :=
    Finset.card_pos.mpr erasedNonempty
  simp only [FiniteSimplicialComplex.Cell.dimension,
    FiniteSimplicialComplex.Cell.eraseVertex]
  omega

noncomputable def FiniteSimplicialComplex.Cell.codimensionOneFaces
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    (cell : complex.Cell) : List complex.Cell :=
  cell.val.attach.toList.filterMap fun vertex =>
    if erasedNonempty : (cell.val.erase vertex.val).Nonempty then
      some (cell.eraseVertex vertex.val erasedNonempty)
    else none

noncomputable def FiniteSimplicialComplex.boundary
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) :
    complex.Cell → Boundary complex.Cell PUnit :=
  fun cell => cell.codimensionOneFaces.map fun face =>
    { i := face, role := PUnit.unit, sign := Sign.zero, mult := 1 }

theorem FiniteSimplicialComplex.mem_codimensionOneFaces_dimension
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    {cell face : complex.Cell}
    (member : face ∈ cell.codimensionOneFaces) :
    face.dimension + 1 = cell.dimension := by
  simp only [FiniteSimplicialComplex.Cell.codimensionOneFaces,
    List.mem_filterMap] at member
  rcases member with ⟨vertex, vertexMem, produced⟩
  split at produced
  · simp only [Option.some.injEq] at produced
    subst face
    exact cell.eraseVertex_dimension vertex.val vertex.property _
  · simp at produced

theorem FiniteSimplicialComplex.boundary_dimension
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    {cell : complex.Cell} (endpoint : Endpoint complex.Cell PUnit)
    (member : endpoint ∈ complex.boundary cell) :
    endpoint.i.dimension + 1 = cell.dimension := by
  simp only [FiniteSimplicialComplex.boundary, List.mem_map] at member
  rcases member with ⟨face, faceMem, rfl⟩
  exact complex.mem_codimensionOneFaces_dimension faceMem

theorem FiniteSimplicialComplex.positiveDimension_has_boundary
    {Vertex : Type} [DecidableEq Vertex]
    {complex : FiniteSimplicialComplex Vertex}
    (cell : complex.Cell) (positive : 0 < cell.dimension) :
    ∃ endpoint, endpoint ∈ complex.boundary cell := by
  rcases cell.nonempty with ⟨vertex, vertexMem⟩
  have cellCard : 1 < cell.val.card := by
    simp only [FiniteSimplicialComplex.Cell.dimension] at positive
    omega
  have erasedNonempty : (cell.val.erase vertex).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem vertexMem]
    omega
  let face := cell.eraseVertex vertex erasedNonempty
  let endpoint : Endpoint complex.Cell PUnit :=
    { i := face, role := PUnit.unit, sign := Sign.zero, mult := 1 }
  refine ⟨endpoint, ?_⟩
  simp only [FiniteSimplicialComplex.boundary, List.mem_map]
  refine ⟨face, ?_, rfl⟩
  simp only [FiniteSimplicialComplex.Cell.codimensionOneFaces,
    List.mem_filterMap]
  refine ⟨⟨vertex, vertexMem⟩, ?_, ?_⟩
  · simp
  · simp [erasedNonempty, face]

noncomputable def FiniteSimplicialComplex.incidence
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) (unitCell : complex.Cell) :
    Incidence complex.Cell PUnit GraphType where
  boundary := complex.boundary
  typeFunc := fun _ => GraphType.unit
  glue := fun left right => if left = unitCell then some right else some left
  unit := unitCell
  guards := Guards.permissive complex.Cell
  type_consistent := by intros; rfl
  sign_rules := by
    intro cell endpoint member
    simp only [FiniteSimplicialComplex.boundary, List.mem_map] at member
    rcases member with ⟨face, _, rfl⟩
    simp
  multiplicities := by
    intro cell endpoint member
    simp only [FiniteSimplicialComplex.boundary, List.mem_map] at member
    rcases member with ⟨face, _, rfl⟩
    simp
  well_founded := by
    rintro cell ⟨endpoint, member, endpointSelf⟩
    have drop := complex.boundary_dimension endpoint member
    simp only [endpointSelf] at drop
    omega
  unit_left := by intro cell; simp
  unit_right := by
    intro cell
    by_cases equal : cell = unitCell <;> simp [equal]
  type_preserve := by intros; rfl

theorem FiniteSimplicialComplex.dimensionRelation_isBisimulation
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) (unitCell : complex.Cell) :
    IsBisimulation (complex.incidence unitCell)
      (fun left right => left.dimension = right.dimension) := by
  intro left right sameDimension
  refine ⟨rfl, ?_⟩
  constructor
  · intro endpoint endpointMem
    have leftDrop := complex.boundary_dimension endpoint endpointMem
    have rightPositive : 0 < right.dimension := by omega
    rcases complex.positiveDimension_has_boundary right rightPositive with
      ⟨otherEndpoint, otherMem⟩
    refine ⟨otherEndpoint, otherMem, ?_, ?_⟩
    · simp only [FiniteSimplicialComplex.incidence,
        FiniteSimplicialComplex.boundary, List.mem_map] at endpointMem otherMem
      rcases endpointMem with ⟨leftFace, _, rfl⟩
      rcases otherMem with ⟨rightFace, _, rfl⟩
      simp [boundaryCompatible]
    · have rightDrop := complex.boundary_dimension otherEndpoint otherMem
      omega
  · intro otherEndpoint otherMem
    have rightDrop := complex.boundary_dimension otherEndpoint otherMem
    have leftPositive : 0 < left.dimension := by omega
    rcases complex.positiveDimension_has_boundary left leftPositive with
      ⟨endpoint, endpointMem⟩
    refine ⟨endpoint, endpointMem, ?_, ?_⟩
    · simp only [FiniteSimplicialComplex.incidence,
        FiniteSimplicialComplex.boundary, List.mem_map] at endpointMem otherMem
      rcases endpointMem with ⟨leftFace, _, rfl⟩
      rcases otherMem with ⟨rightFace, _, rfl⟩
      simp [boundaryCompatible]
    · have leftDrop := complex.boundary_dimension endpoint endpointMem
      omega

theorem FiniteSimplicialComplex.approxBisim_preserves_dimension
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) (unitCell : complex.Cell)
    {left right : complex.Cell}
    (related : approxBisim (complex.incidence unitCell) left right) :
    left.dimension = right.dimension := by
  rcases related with ⟨relation, isBisimulation, related⟩
  have preserves : ∀ dimension cell other,
      cell.dimension = dimension → relation cell other →
        other.dimension = dimension := by
    intro dimension
    induction dimension with
    | zero =>
        intro cell other cellDimension cellOther
        by_contra otherNonzero
        have otherPositive : 0 < other.dimension :=
          Nat.pos_of_ne_zero otherNonzero
        rcases complex.positiveDimension_has_boundary other otherPositive with
          ⟨otherEndpoint, otherMem⟩
        rcases (isBisimulation cell other cellOther).2.2
            otherEndpoint otherMem with
          ⟨cellEndpoint, cellMem, _, _⟩
        have drop := complex.boundary_dimension cellEndpoint cellMem
        omega
    | succ dimension inductionHypothesis =>
        intro cell other cellDimension cellOther
        have cellPositive : 0 < cell.dimension := by omega
        rcases complex.positiveDimension_has_boundary cell cellPositive with
          ⟨cellEndpoint, cellMem⟩
        rcases (isBisimulation cell other cellOther).2.1
            cellEndpoint cellMem with
          ⟨otherEndpoint, otherMem, _, endpointRelated⟩
        have cellDrop := complex.boundary_dimension cellEndpoint cellMem
        have otherDrop := complex.boundary_dimension otherEndpoint otherMem
        have endpointDimension : cellEndpoint.i.dimension = dimension := by omega
        have preservedEndpoint := inductionHypothesis cellEndpoint.i
          otherEndpoint.i endpointDimension endpointRelated
        omega
  exact (preserves left.dimension left right rfl related).symm

theorem FiniteSimplicialComplex.dimension_iff_approxBisim
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) (unitCell : complex.Cell)
    (left right : complex.Cell) :
    left.dimension = right.dimension ↔
      approxBisim (complex.incidence unitCell) left right := by
  constructor
  · intro sameDimension
    exact ⟨(fun first second => first.dimension = second.dimension),
      complex.dimensionRelation_isBisimulation unitCell, sameDimension⟩
  · exact complex.approxBisim_preserves_dimension unitCell

abbrev FiniteSimplicialComplex.RepresentedDimension
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) :=
  {dimension : Nat // ∃ cell : complex.Cell, cell.dimension = dimension}

def FiniteSimplicialComplex.representedDimension
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) (cell : complex.Cell) :
    complex.RepresentedDimension := ⟨cell.dimension, cell, rfl⟩

noncomputable def FiniteSimplicialComplex.gradedQuotientSpec
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) (unitCell : complex.Cell) :
    GradedIncidenceQuotientSpec (complex.incidence unitCell)
      complex.representedDimension where
  toClassModeSpec :=
    { selectorCompatible := by
        intro left right output selected
        by_cases unitLeft : left = unitCell
        · subst left
          simp [FiniteSimplicialComplex.incidence] at selected
          subst output
          exact Or.inr rfl
        · simp [FiniteSimplicialComplex.incidence, unitLeft] at selected
          subst output
          exact Or.inl rfl
      kernel := by
        intro left right
        rw [← complex.dimension_iff_approxBisim unitCell]
        exact Subtype.ext_iff
      surjective := by
        rintro ⟨dimension, cell, cellDimension⟩
        refine ⟨cell, ?_⟩
        apply Subtype.ext
        exact cellDimension }

/- A conventional ranked cell complex normally presents its grading through
   the boundary: every face has codimension one and every positive-dimensional
   cell has a face.  These two facts force bisimulation to preserve dimension.
   Homogeneity of the labelled boundary profile gives the converse. -/
structure NatGradedBoundaryProfile
    {I R T : Type} [DecidableEq I]
    (inc : Incidence I R T) (grade : I → Nat) : Prop where
  typeHomogeneous : ∀ {left right}, grade left = grade right →
    inc.typeFunc left = inc.typeFunc right
  boundaryDrops : ∀ {cell} (endpoint : Endpoint I R),
    endpoint ∈ inc.boundary cell → grade endpoint.i + 1 = grade cell
  positiveBoundary : ∀ cell, 0 < grade cell →
    ∃ endpoint, endpoint ∈ inc.boundary cell
  sameGradeBoundaryMatched : ∀ {left right}, grade left = grade right →
    boundaryMatched inc (fun first second => grade first = grade second)
      left right
  selectorCompatible : SelectorClassModeCompatible inc grade
  surjective : ∀ dimension : Nat, ∃ cell, grade cell = dimension

theorem approxBisim_preserves_natGrade
    {I R T : Type} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Nat}
    (boundaryDrops : ∀ {cell} (endpoint : Endpoint I R),
      endpoint ∈ inc.boundary cell → grade endpoint.i + 1 = grade cell)
    (positiveBoundary : ∀ cell, 0 < grade cell →
      ∃ endpoint, endpoint ∈ inc.boundary cell)
    {left right : I} (related : approxBisim inc left right) :
    grade left = grade right := by
  rcases related with ⟨relation, isBisimulation, related⟩
  have preserves : ∀ dimension cell other,
      grade cell = dimension → relation cell other →
        grade other = dimension := by
    intro dimension
    induction dimension with
    | zero =>
        intro cell other cellGrade cellOther
        by_contra otherNonzero
        have otherPositive : 0 < grade other := Nat.pos_of_ne_zero otherNonzero
        rcases positiveBoundary other otherPositive with ⟨otherEndpoint, otherMem⟩
        rcases (isBisimulation cell other cellOther).2.2
            otherEndpoint otherMem with
          ⟨cellEndpoint, cellMem, _compatible, _endpointRelated⟩
        have drop := boundaryDrops cellEndpoint cellMem
        omega
    | succ dimension inductionHypothesis =>
        intro cell other cellGrade cellOther
        have cellPositive : 0 < grade cell := by omega
        rcases positiveBoundary cell cellPositive with ⟨cellEndpoint, cellMem⟩
        rcases (isBisimulation cell other cellOther).2.1
            cellEndpoint cellMem with
          ⟨otherEndpoint, otherMem, _compatible, endpointRelated⟩
        have cellDrop := boundaryDrops cellEndpoint cellMem
        have otherDrop := boundaryDrops otherEndpoint otherMem
        have endpointGrade : grade cellEndpoint.i = dimension := by omega
        have preservedEndpoint := inductionHypothesis cellEndpoint.i
          otherEndpoint.i endpointGrade endpointRelated
        omega
  exact (preserves (grade left) left right rfl related).symm

theorem NatGradedBoundaryProfile.grade_iff_approxBisim
    {I R T : Type} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Nat}
    (profile : NatGradedBoundaryProfile inc grade)
    (left right : I) :
    grade left = grade right ↔ approxBisim inc left right := by
  constructor
  · intro gradeEqual
    refine ⟨(fun first second => grade first = grade second), ?_, gradeEqual⟩
    intro first second equal
    exact ⟨profile.typeHomogeneous equal,
      profile.sameGradeBoundaryMatched equal⟩
  · exact fun related => approxBisim_preserves_natGrade
      profile.boundaryDrops profile.positiveBoundary related

def NatGradedBoundaryProfile.toGradedIncidenceQuotientSpec
    {I R T : Type} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Nat}
    (profile : NatGradedBoundaryProfile inc grade) :
    GradedIncidenceQuotientSpec inc grade where
  toClassModeSpec :=
    { selectorCompatible := profile.selectorCompatible
      kernel := profile.grade_iff_approxBisim
      surjective := profile.surjective }

/- Finite complexes use a bounded dimension type.  This variant avoids the
   impossible requirement that a finite carrier surject onto all of `Nat`;
   the preceding induction is applied to the underlying `Fin.val`. -/
structure BoundedGradedBoundaryProfile
    {I R T : Type} [DecidableEq I] (maxDimension : Nat)
    (inc : Incidence I R T) (grade : I → Fin (maxDimension + 1)) : Prop where
  typeHomogeneous : ∀ {left right}, grade left = grade right →
    inc.typeFunc left = inc.typeFunc right
  boundaryDrops : ∀ {cell} (endpoint : Endpoint I R),
    endpoint ∈ inc.boundary cell →
      (grade endpoint.i).val + 1 = (grade cell).val
  positiveBoundary : ∀ cell, 0 < (grade cell).val →
    ∃ endpoint, endpoint ∈ inc.boundary cell
  sameGradeBoundaryMatched : ∀ {left right}, grade left = grade right →
    boundaryMatched inc (fun first second => grade first = grade second)
      left right
  selectorCompatible : SelectorClassModeCompatible inc grade
  surjective : ∀ dimension : Fin (maxDimension + 1),
    ∃ cell, grade cell = dimension

theorem BoundedGradedBoundaryProfile.grade_iff_approxBisim
    {I R T : Type} [DecidableEq I] {maxDimension : Nat}
    {inc : Incidence I R T}
    {grade : I → Fin (maxDimension + 1)}
    (profile : BoundedGradedBoundaryProfile maxDimension inc grade)
    (left right : I) :
    grade left = grade right ↔ approxBisim inc left right := by
  constructor
  · intro gradeEqual
    refine ⟨(fun first second => grade first = grade second), ?_, gradeEqual⟩
    intro first second equal
    exact ⟨profile.typeHomogeneous equal,
      profile.sameGradeBoundaryMatched equal⟩
  · intro related
    apply Fin.ext
    exact approxBisim_preserves_natGrade profile.boundaryDrops
      profile.positiveBoundary related

def BoundedGradedBoundaryProfile.toGradedIncidenceQuotientSpec
    {I R T : Type} [DecidableEq I] {maxDimension : Nat}
    {inc : Incidence I R T}
    {grade : I → Fin (maxDimension + 1)}
    (profile : BoundedGradedBoundaryProfile maxDimension inc grade) :
    GradedIncidenceQuotientSpec inc grade where
  toClassModeSpec :=
    { selectorCompatible := profile.selectorCompatible
      kernel := profile.grade_iff_approxBisim
      surjective := profile.surjective }

def GradedIncidenceQuotientSpec.model
    {I R T Grade : Type u} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Grade}
    (spec : GradedIncidenceQuotientSpec inc grade) : Incidence I R T :=
  spec.toClassModeSpec.model

theorem FiniteSimplicialComplex.classMode_exactDescent
    {Vertex : Type} [DecidableEq Vertex]
    (complex : FiniteSimplicialComplex Vertex) (unitCell : complex.Cell) :
    ResonanceRelationDescendsExactly
      (complex.gradedQuotientSpec unitCell).model :=
  (complex.gradedQuotientSpec unitCell).toClassModeSpec.exactDescent

theorem GradedIncidenceQuotientSpec.exactDescent
    {I R T Grade : Type u} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Grade}
    (spec : GradedIncidenceQuotientSpec inc grade) :
    ResonanceRelationDescendsExactly spec.model :=
  spec.toClassModeSpec.exactDescent

theorem GradedIncidenceQuotientSpec.quotientResonance_representation
    {I R T Grade : Type u} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Grade}
    (spec : GradedIncidenceQuotientSpec inc grade)
    (left right output : I) :
    quotientResonance spec.model
        (Quotient.mk (approxBisimSetoid spec.model) left)
        (Quotient.mk (approxBisimSetoid spec.model) right)
        (Quotient.mk (approxBisimSetoid spec.model) output) ↔
      (grade output = grade left ∨ grade output = grade right) :=
  spec.toClassModeSpec.quotientResonance_representation left right output

structure GradedIncidenceMap
    {I J R₁ R₂ T₁ T₂ Grade : Type u}
    [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {sourceGrade : I → Grade} {targetGrade : J → Grade}
    (sourceSpec : GradedIncidenceQuotientSpec source sourceGrade)
    (targetSpec : GradedIncidenceQuotientSpec target targetGrade) where
  toFun : I → J
  preserves_grade : ∀ value, targetGrade (toFun value) = sourceGrade value

def GradedIncidenceMap.toResonanceHom
    {I J R₁ R₂ T₁ T₂ Grade : Type u}
    [DecidableEq I] [DecidableEq J]
    {source : Incidence I R₁ T₁} {target : Incidence J R₂ T₂}
    {sourceGrade : I → Grade} {targetGrade : J → Grade}
    {sourceSpec : GradedIncidenceQuotientSpec source sourceGrade}
    {targetSpec : GradedIncidenceQuotientSpec target targetGrade}
    (map : GradedIncidenceMap sourceSpec targetSpec) :
    TernaryResonanceHom sourceSpec.model.resonanceSystem
      targetSpec.model.resonanceSystem where
  toFun := map.toFun
  preserves := by
    intro left right output resonant
    change targetGrade (map.toFun output) = targetGrade (map.toFun left) ∨
      targetGrade (map.toFun output) = targetGrade (map.toFun right)
    change sourceGrade output = sourceGrade left ∨
      sourceGrade output = sourceGrade right at resonant
    simpa [map.preserves_grade] using resonant

def GradedIncidenceMap.id
    {I R T Grade : Type u} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Grade}
    (spec : GradedIncidenceQuotientSpec inc grade) :
    GradedIncidenceMap spec spec where
  toFun := fun value => value
  preserves_grade := fun _ => rfl

def GradedIncidenceMap.comp
    {I J K R₁ R₂ R₃ T₁ T₂ T₃ Grade : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {firstInc : Incidence I R₁ T₁} {secondInc : Incidence J R₂ T₂}
    {thirdInc : Incidence K R₃ T₃}
    {firstGrade : I → Grade} {secondGrade : J → Grade}
    {thirdGrade : K → Grade}
    {firstSpec : GradedIncidenceQuotientSpec firstInc firstGrade}
    {secondSpec : GradedIncidenceQuotientSpec secondInc secondGrade}
    {thirdSpec : GradedIncidenceQuotientSpec thirdInc thirdGrade}
    (after : GradedIncidenceMap secondSpec thirdSpec)
    (before : GradedIncidenceMap firstSpec secondSpec) :
    GradedIncidenceMap firstSpec thirdSpec where
  toFun := after.toFun ∘ before.toFun
  preserves_grade := by
    intro value
    change thirdGrade (after.toFun (before.toFun value)) = firstGrade value
    rw [after.preserves_grade, before.preserves_grade]

@[simp] theorem GradedIncidenceMap.id_toResonanceHom
    {I R T Grade : Type u} [DecidableEq I]
    {inc : Incidence I R T} {grade : I → Grade}
    (spec : GradedIncidenceQuotientSpec inc grade) :
    (GradedIncidenceMap.id spec).toResonanceHom =
      TernaryResonanceHom.id spec.model.resonanceSystem := by
  apply TernaryResonanceHom.ext
  funext value
  rfl

@[simp] theorem GradedIncidenceMap.comp_toResonanceHom
    {I J K R₁ R₂ R₃ T₁ T₂ T₃ Grade : Type u}
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {firstInc : Incidence I R₁ T₁} {secondInc : Incidence J R₂ T₂}
    {thirdInc : Incidence K R₃ T₃}
    {firstGrade : I → Grade} {secondGrade : J → Grade}
    {thirdGrade : K → Grade}
    {firstSpec : GradedIncidenceQuotientSpec firstInc firstGrade}
    {secondSpec : GradedIncidenceQuotientSpec secondInc secondGrade}
    {thirdSpec : GradedIncidenceQuotientSpec thirdInc thirdGrade}
    (after : GradedIncidenceMap secondSpec thirdSpec)
    (before : GradedIncidenceMap firstSpec secondSpec) :
    (after.comp before).toResonanceHom =
      after.toResonanceHom.comp before.toResonanceHom := by
  apply TernaryResonanceHom.ext
  rfl

def simplexClassModeQuotientSpec :
    ClassModeQuotientSpec simplexIncidence simplexToShape where
  selectorCompatible := by
    intro left right output selected
    by_cases unitLeft : left = SimplexId.v0
    · subst left
      simp [simplexIncidence] at selected
      subst output
      exact Or.inr rfl
    · simp [simplexIncidence, unitLeft] at selected
      subst output
      exact Or.inl rfl
  kernel := simplexToShape_iff_approxBisim
  surjective := by
    intro shape
    cases shape with
    | vertex => exact ⟨.v0, rfl⟩
    | edgeShape => exact ⟨.e01, rfl⟩
    | faceShape => exact ⟨.face, rfl⟩

def simplexGradedIncidenceQuotientSpec :
    GradedIncidenceQuotientSpec simplexIncidence simplexToShape where
  toClassModeSpec := simplexClassModeQuotientSpec

/- The infinite simplicial path supplies a second conventional cell-complex
   instance of the graded construction.  Unlike the finite triangle, every
   grade has infinitely many representatives.  Thus exact descent is not an
   artefact of finite enumeration: it follows from the structural
   node/edge classification of `pathIncidence`. -/
def pathClassModeQuotientSpec :
    ClassModeQuotientSpec pathIncidence pathToShape where
  selectorCompatible := by
    intro left right output selected
    by_cases unitLeft : left = PathId.node 0
    · subst left
      simp [pathIncidence] at selected
      subst output
      exact Or.inr rfl
    · simp [pathIncidence, unitLeft] at selected
      subst output
      exact Or.inl rfl
  kernel := pathToShape_iff_approxBisim
  surjective := by
    intro shape
    cases shape with
    | nodeShape => exact ⟨.node 0, rfl⟩
    | edgeShape => exact ⟨.edge 0, rfl⟩

def pathGradedIncidenceQuotientSpec :
    GradedIncidenceQuotientSpec pathIncidence pathToShape where
  toClassModeSpec := pathClassModeQuotientSpec

def simplexDimension : SimplexId → Fin 3
  | .v0 | .v1 | .v2 => 0
  | .e01 | .e02 | .e12 => 1
  | .face => 2

theorem pathClassMode_exactDescent :
    ResonanceRelationDescendsExactly pathClassModeQuotientSpec.model :=
  pathGradedIncidenceQuotientSpec.exactDescent

theorem pathClassMode_quotientResonance_representation
    (left right output : PathId) :
    quotientResonance pathClassModeQuotientSpec.model
        (Quotient.mk
          (approxBisimSetoid pathClassModeQuotientSpec.model) left)
        (Quotient.mk
          (approxBisimSetoid pathClassModeQuotientSpec.model) right)
        (Quotient.mk
          (approxBisimSetoid pathClassModeQuotientSpec.model) output) ↔
      (pathToShape output = pathToShape left ∨
        pathToShape output = pathToShape right) :=
  pathClassModeQuotientSpec.quotientResonance_representation
    left right output

theorem simplexClassMode_model_eq_shapeModeSimplex :
    simplexClassModeQuotientSpec.model = shapeModeSimplexIncidence := by
  rfl

theorem shapeModeSimplex_exactDescent_from_gradedFamily :
    ResonanceRelationDescendsExactly shapeModeSimplexIncidence := by
  simpa [GradedIncidenceQuotientSpec.model,
    simplexClassMode_model_eq_shapeModeSimplex] using
      simplexGradedIncidenceQuotientSpec.exactDescent

theorem shapeModeSimplex_exactDescent_from_generalConstruction :
    ResonanceRelationDescendsExactly shapeModeSimplexIncidence := by
  rw [← simplexClassMode_model_eq_shapeModeSimplex]
  exact simplexClassModeQuotientSpec.exactDescent

theorem shapeModeSimplex_representation_from_generalConstruction
    (left right output : SimplexId) :
    quotientResonance shapeModeSimplexIncidence
        (Quotient.mk (approxBisimSetoid shapeModeSimplexIncidence) left)
        (Quotient.mk (approxBisimSetoid shapeModeSimplexIncidence) right)
        (Quotient.mk (approxBisimSetoid shapeModeSimplexIncidence) output) ↔
      (simplexToShape output = simplexToShape left ∨
        simplexToShape output = simplexToShape right) := by
  simpa [simplexClassMode_model_eq_shapeModeSimplex] using
    simplexClassModeQuotientSpec.quotientResonance_representation
      left right output

/- A small reversible chemical-reaction network.  `forward` represents
   A → B and `reverse` represents B → A.  The empty-boundary solvent and
   molecular species form the molecular behavioural class; the two reactions
   form the reaction class because their signed reactant/product profiles
   match.  Resonance is deliberately relational: interacting reaction modes
   may expose any molecular mode, so it is not merely the graph of `glue`. -/
inductive ChemicalReactionCell where
  | solvent
  | speciesA
  | speciesB
  | forward
  | reverse
deriving DecidableEq, Repr

inductive ChemicalReactionRole where
  | reactant
  | product
deriving DecidableEq, Repr

inductive ChemicalReactionKind where
  | molecule
  | reaction
deriving DecidableEq, Repr

def chemicalReactionKind : ChemicalReactionCell → ChemicalReactionKind
  | .solvent | .speciesA | .speciesB => .molecule
  | .forward | .reverse => .reaction

def chemicalReactionBoundary :
    ChemicalReactionCell →
      Boundary ChemicalReactionCell ChemicalReactionRole
  | .solvent | .speciesA | .speciesB => []
  | .forward =>
      [⟨.speciesA, .reactant, .neg, 1, by omega⟩,
       ⟨.speciesB, .product, .pos, 1, by omega⟩]
  | .reverse =>
      [⟨.speciesB, .reactant, .neg, 1, by omega⟩,
       ⟨.speciesA, .product, .pos, 1, by omega⟩]

def chemicalReactionGlue
    (left right : ChemicalReactionCell) : Option ChemicalReactionCell :=
  if left = .solvent then some right
  else if right = .solvent then some left
  else none

def chemicalReactionResonance
    (left right output : ChemicalReactionCell) : Prop :=
  chemicalReactionKind output = chemicalReactionKind left ∨
    chemicalReactionKind output = chemicalReactionKind right ∨
    (chemicalReactionKind left = .reaction ∧
      chemicalReactionKind right = .reaction ∧
      chemicalReactionKind output = .molecule)

def chemicalReactionIncidence :
    Incidence ChemicalReactionCell ChemicalReactionRole Unit where
  boundary := chemicalReactionBoundary
  typeFunc := fun _ => ()
  glue := chemicalReactionGlue
  resonance := chemicalReactionResonance
  selected_resonates := by
    intro left right output selected
    by_cases leftUnit : left = .solvent
    · subst left
      simp [chemicalReactionGlue] at selected
      subst output
      simp [chemicalReactionResonance]
    · by_cases rightUnit : right = .solvent
      · subst right
        simp [chemicalReactionGlue, leftUnit] at selected
        subst output
        simp [chemicalReactionResonance]
      · simp [chemicalReactionGlue, leftUnit, rightUnit] at selected
  unit := .solvent
  guards := Guards.permissive _
  boundaryMatrix := fun _ _ => 0
  laplacian := fun _ _ => 0
  type_consistent := by simp
  sign_rules := by
    intro cell endpoint member
    cases endpoint.sign <;> simp
  multiplicities := by
    intro cell endpoint member
    exact endpoint.mult_pos
  well_founded := by
    intro cell
    cases cell <;> simp [chemicalReactionBoundary]
  unit_left := by intro cell; simp [chemicalReactionGlue]
  unit_right := by intro cell; cases cell <;> simp [chemicalReactionGlue]
  type_preserve := by simp

theorem chemicalReactionKind_implies_approxBisim
    {first second : ChemicalReactionCell}
    (sameKind : chemicalReactionKind first = chemicalReactionKind second) :
    approxBisim chemicalReactionIncidence first second := by
  let relation : ChemicalReactionCell → ChemicalReactionCell → Prop :=
    fun left right => chemicalReactionKind left = chemicalReactionKind right
  refine ⟨relation, ?_, sameKind⟩
  intro left right related
  constructor
  · rfl
  · cases left <;> cases right <;>
      simp_all [relation, chemicalReactionKind, chemicalReactionIncidence,
        chemicalReactionBoundary, boundaryMatched, boundaryCompatible]

theorem chemicalReaction_approxBisim_implies_kind
    {first second : ChemicalReactionCell}
    (bisimilar : approxBisim chemicalReactionIncidence first second) :
    chemicalReactionKind first = chemicalReactionKind second := by
  cases first <;> cases second <;> simp [chemicalReactionKind]
  all_goals
    first
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.forward ChemicalReactionCell.solvent
          (by rfl) ⟨.speciesA, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          bisimilar)
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.reverse ChemicalReactionCell.solvent
          (by rfl) ⟨.speciesB, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          bisimilar)
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.forward ChemicalReactionCell.speciesA
          (by rfl) ⟨.speciesA, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          bisimilar)
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.reverse ChemicalReactionCell.speciesA
          (by rfl) ⟨.speciesB, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          bisimilar)
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.forward ChemicalReactionCell.speciesB
          (by rfl) ⟨.speciesA, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          bisimilar)
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.reverse ChemicalReactionCell.speciesB
          (by rfl) ⟨.speciesB, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          bisimilar)
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.forward ChemicalReactionCell.solvent
          (by rfl) ⟨.speciesA, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          (approxBisim_symm bisimilar))
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.reverse ChemicalReactionCell.solvent
          (by rfl) ⟨.speciesB, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          (approxBisim_symm bisimilar))
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.forward ChemicalReactionCell.speciesA
          (by rfl) ⟨.speciesA, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          (approxBisim_symm bisimilar))
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.reverse ChemicalReactionCell.speciesA
          (by rfl) ⟨.speciesB, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          (approxBisim_symm bisimilar))
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.forward ChemicalReactionCell.speciesB
          (by rfl) ⟨.speciesA, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          (approxBisim_symm bisimilar))
    | exact False.elim
        ((not_approxBisim_empty_nonempty chemicalReactionIncidence
          ChemicalReactionCell.reverse ChemicalReactionCell.speciesB
          (by rfl) ⟨.speciesB, .reactant, .neg, 1, by omega⟩
          (by simp [chemicalReactionIncidence, chemicalReactionBoundary]))
          (approxBisim_symm bisimilar))

theorem chemicalReactionKind_iff_approxBisim
    (first second : ChemicalReactionCell) :
    chemicalReactionKind first = chemicalReactionKind second ↔
      approxBisim chemicalReactionIncidence first second :=
  ⟨chemicalReactionKind_implies_approxBisim,
    chemicalReaction_approxBisim_implies_kind⟩

theorem chemicalReaction_resonance_descends_exactly :
    ResonanceRelationDescendsExactly chemicalReactionIncidence := by
  apply exact_descent_of_quotientResonanceCongruent
  intro first₁ first₂ second₁ second₂ output₁ output₂
    firstBisim secondBisim outputBisim
  have firstKind :=
    (chemicalReactionKind_iff_approxBisim first₁ first₂).mpr firstBisim
  have secondKind :=
    (chemicalReactionKind_iff_approxBisim second₁ second₂).mpr secondBisim
  have outputKind :=
    (chemicalReactionKind_iff_approxBisim output₁ output₂).mpr outputBisim
  simp only [chemicalReactionIncidence, chemicalReactionResonance]
  rw [firstKind, secondKind, outputKind]

theorem chemicalReaction_quotientResonance_representation
    (left right output : ChemicalReactionCell) :
    quotientResonance chemicalReactionIncidence
        (Quotient.mk (approxBisimSetoid chemicalReactionIncidence) left)
        (Quotient.mk (approxBisimSetoid chemicalReactionIncidence) right)
        (Quotient.mk (approxBisimSetoid chemicalReactionIncidence) output) ↔
      chemicalReactionResonance left right output := by
  exact quotientResonance_mk_iff
    (quotientResonanceCongruent_of_exact_descent
      chemicalReaction_resonance_descends_exactly)

theorem chemicalReaction_model_nonfaithful_and_multivalued :
    approxBisim chemicalReactionIncidence .speciesA .speciesB ∧
      ChemicalReactionCell.speciesA ≠ .speciesB ∧
      chemicalReactionIncidence.resonance .forward .reverse .speciesA ∧
      chemicalReactionIncidence.resonance .forward .reverse .speciesB := by
  constructor
  · exact chemicalReactionKind_implies_approxBisim rfl
  · refine ⟨by decide, ?_⟩
    simp [chemicalReactionIncidence, chemicalReactionResonance,
      chemicalReactionKind]

structure IncidenceTheoryPaperCapstone : Type (u + 1) where
  exactDescentCriterion : ∀ {I R T : Type u} [DecidableEq I]
      (inc : Incidence I R T),
    ResonanceRelationDescendsExactly inc ↔ QuotientResonanceCongruent inc
  standardCoequalizer : ∀ {I R T : Type u} [DecidableEq I]
      (inc : Incidence I R T),
    IsColimit (bisimulationQuotientResonanceCofork inc)
  finiteLocalClassification : ∀ {I R T : Type u}
      [DecidableEq I] [Fintype I] (inc : Incidence I R T),
    ResonanceRelationDescendsExactly inc ↔
      finiteLocalResonanceDescentObstructions inc = ∅
  minimalObstructionExists : ∀ {I R T : Type u}
      [DecidableEq I] [Fintype I] (inc : Incidence I R T),
    ¬ ResonanceRelationDescendsExactly inc →
      ∃ candidate : LocalResonanceDescentCandidate I,
        candidate.IsSupportMinimalObstruction inc
  simplexMinimalObstruction :
    simplexTwoVertexLocalObstruction.IsSupportMinimalObstruction
      simplexIncidence
  automorphismOrbitClassification : ∀ {I R T : Type u}
      [DecidableEq I] (inc : Incidence I R T),
    ResonanceRelationDescendsExactly inc ↔
      ¬ ∃ orbit : LocalResonanceAutomorphismOrbit inc,
        orbit.IsObstruction inc
  freeIncidenceConstruction : ∀
      {Generator I R T : Type u}
      [DecidableEq Generator] [DecidableEq I]
      {inc : Incidence I R T} (_spec : TotalGlueSpec inc)
      (onGenerator : Generator → I),
    ∃! hom : IncidenceGluingHom (freeIncidence Generator) inc,
      ∀ generator,
        hom.toFun (freeIncidenceGenerator generator) = onGenerator generator
  logicalNecessity : ∀ {I R T : Type u} [DecidableEq I]
      (inc : Incidence I R T),
    (∀ formula : ResonanceFormula,
      formula.BisimulationInvariant inc) →
        ResonanceRelationDescendsExactly inc
  genericClassModeConstruction : ∀
      {I R T Class : Type u} [DecidableEq I]
      {inc : Incidence I R T} {classify : I → Class}
      (spec : ClassModeQuotientSpec inc classify),
    ResonanceRelationDescendsExactly spec.model
  functionalNegativeModel :
    ¬ ResonanceRelationDescendsExactly simplexIncidence
  relationalPositiveModel :
    ResonanceRelationDescendsExactly shapeModeSimplexIncidence
  positiveModelMultivalued :
    ∃ left right first second,
      first ≠ second ∧
      shapeModeSimplexIncidence.resonance left right first ∧
      shapeModeSimplexIncidence.resonance left right second
  positiveModelNotTotal :
    ∃ left right output,
      ¬ shapeModeSimplexIncidence.resonance left right output
  appliedChemicalModel :
    ResonanceRelationDescendsExactly chemicalReactionIncidence
  appliedChemicalModelNontrivial :
    approxBisim chemicalReactionIncidence .speciesA .speciesB ∧
      ChemicalReactionCell.speciesA ≠ .speciesB ∧
      chemicalReactionIncidence.resonance .forward .reverse .speciesA ∧
      chemicalReactionIncidence.resonance .forward .reverse .speciesB

noncomputable def incidenceTheoryPaperCapstone :
    IncidenceTheoryPaperCapstone where
  exactDescentCriterion := resonanceRelationDescendsExactly_iff
  standardCoequalizer := bisimulationQuotientResonanceCofork_isColimit
  finiteLocalClassification :=
    finite_exact_descent_iff_no_local_obstructions
  minimalObstructionExists :=
    exists_supportMinimalObstruction_of_not_exact_descent
  simplexMinimalObstruction :=
    simplexTwoVertexLocalObstruction_isSupportMinimal
  automorphismOrbitClassification :=
    exact_descent_iff_no_automorphism_obstruction_orbit
  freeIncidenceConstruction := freeIncidence_universal
  logicalNecessity := fun _ => exactDescent_of_resonanceFormula_preservation
  genericClassModeConstruction := fun spec => spec.exactDescent
  functionalNegativeModel := simplexIncidence_has_no_exact_resonance_descent
  relationalPositiveModel :=
    shapeModeSimplex_exactDescent_from_generalConstruction
  positiveModelMultivalued := shapeModeSimplex_is_genuinely_multivalued
  positiveModelNotTotal := shapeModeSimplex_is_not_saturated
  appliedChemicalModel := chemicalReaction_resonance_descends_exactly
  appliedChemicalModelNontrivial :=
    chemicalReaction_model_nonfaithful_and_multivalued

structure BisimulationQuotientResonanceTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  descent_iff : ResonanceRelationDescendsExactly inc ↔
    QuotientResonanceCongruent inc
  uniqueness : ∀ (descended : IncidenceQuotient inc → IncidenceQuotient inc →
        IncidenceQuotient inc → Prop),
    (∀ i j k,
      descended (Quotient.mk (approxBisimSetoid inc) i)
          (Quotient.mk (approxBisimSetoid inc) j)
          (Quotient.mk (approxBisimSetoid inc) k) ↔
        inc.resonance i j k) →
      descended = quotientResonance inc
  universal : ∀ {target : TernaryResonanceSystem.{u}}
      (hom : TernaryResonanceHom inc.resonanceSystem target),
    BisimulationInvariantResonanceHom inc target hom →
      ∃ lift : TernaryResonanceHom
          (bisimulationQuotientResonanceSystem inc) target,
        (∀ value,
          lift.toFun (Quotient.mk (approxBisimSetoid inc) value) =
            hom.toFun value) ∧
        ∀ candidate : TernaryResonanceHom
            (bisimulationQuotientResonanceSystem inc) target,
          (∀ value,
            candidate.toFun (Quotient.mk (approxBisimSetoid inc) value) =
              hom.toFun value) → candidate = lift

theorem bisimulationQuotientResonanceTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    BisimulationQuotientResonanceTheorem inc where
  descent_iff := resonanceRelationDescendsExactly_iff inc
  uniqueness := exact_descended_resonance_unique_without_assumption
  universal := bisimulationQuotientResonance_universal

end IncidenceCore
