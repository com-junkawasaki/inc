import IncidenceTheory.Peano
import IncidenceTheory.Pairs
import IncidenceTheory.PathComplex
import IncidenceTheory.Product

universe u v

/- Merkle-ID: implementation.graph_model.cross_instance
   story.jsonnet → implementation.nodes.cross_instance
   Research cycle 6 (see RESEARCH_LOG.md): cycles 1-5 each worked within
   a single `Incidence` instance at a time. This file asks whether
   there's a meaningful *homomorphism* connecting two different
   instances -- `natIncidence` and `pairIncidenceChained` -- since
   `PairId.atom : Nat → PairId` is a natural embedding candidate:
   `pairBoundaryChained`'s atom case was deliberately built to mirror
   `peanoBoundary`'s shape back in cycle 3.

   Finding, stated precisely rather than glossed: `PairId.atom`
   preserves `boundary` (naturally, up to a role-relabeling) and `unit`,
   but does *not* preserve `glue` -- a genuine, proven mixed result, not
   a full "Incidence homomorphism" in the strong algebraic sense. This
   reveals something real about `Incidence`'s shape: it bundles a
   coalgebraic layer (`boundary`, "what an element unfolds into") and an
   algebraic layer (`glue`, "how elements compose"), and a map that
   respects one doesn't automatically respect the other. In hindsight
   this isn't surprising -- `pairIncidenceChained.glue` was documented as
   a left-biased placeholder ("not the focus", cycles 2-3) with no
   claimed relationship to `PairId.pair`, the actual structural
   combinator -- but it's now proven rather than merely asserted. -/

namespace IncidenceCore

inductive IncRawType where
  | base : Nat → IncRawType
  | unit : IncRawType
  | product : IncRawType → IncRawType → IncRawType
  | function : IncRawType → IncRawType → IncRawType
  deriving DecidableEq, Repr

inductive IncRawTerm where
  | var : Nat → IncRawTerm
  | unit : IncRawTerm
  | pair : IncRawTerm → IncRawTerm → IncRawTerm
  | first : IncRawTerm → IncRawTerm
  | second : IncRawTerm → IncRawTerm
  | lambda : IncRawType → IncRawTerm → IncRawTerm
  | apply : IncRawTerm → IncRawTerm → IncRawTerm
  deriving DecidableEq, Repr

inductive IncRawLookup : List IncRawType → Nat → IncRawType → Type
  | here {context type} : IncRawLookup (type :: context) 0 type
  | there {context index type head} :
      IncRawLookup context index type →
        IncRawLookup (head :: context) (index + 1) type

inductive IncRawHasType : List IncRawType → IncRawTerm → IncRawType → Type
  | varRule {context index type} :
      IncRawLookup context index type →
        IncRawHasType context (.var index) type
  | unitRule {context} : IncRawHasType context .unit .unit
  | pairRule {context left right leftType rightType} :
      IncRawHasType context left leftType →
      IncRawHasType context right rightType →
      IncRawHasType context (.pair left right) (.product leftType rightType)
  | firstRule {context term leftType rightType} :
      IncRawHasType context term (.product leftType rightType) →
        IncRawHasType context (.first term) leftType
  | secondRule {context term leftType rightType} :
      IncRawHasType context term (.product leftType rightType) →
        IncRawHasType context (.second term) rightType
  | lambdaRule {context body domain codomain} :
      IncRawHasType (domain :: context) body codomain →
        IncRawHasType context (.lambda domain body) (.function domain codomain)
  | applyRule {context function argument domain codomain} :
      IncRawHasType context function (.function domain codomain) →
      IncRawHasType context argument domain →
        IncRawHasType context (.apply function argument) codomain

def incRawIdentity (type : IncRawType) : IncRawTerm :=
  .lambda type (.var 0)

def incRawIdentity_hasType (type : IncRawType) :
    IncRawHasType [] (incRawIdentity type) (.function type type) := by
  exact IncRawHasType.lambdaRule
    (IncRawHasType.varRule IncRawLookup.here)

def incRawSwap (left right : IncRawType) : IncRawTerm :=
  .lambda (.product left right)
    (.pair (.second (.var 0)) (.first (.var 0)))

def incRawSwap_hasType (left right : IncRawType) :
    IncRawHasType [] (incRawSwap left right)
      (.function (.product left right) (.product right left)) := by
  apply IncRawHasType.lambdaRule
  apply IncRawHasType.pairRule
  · apply IncRawHasType.secondRule
    exact IncRawHasType.varRule IncRawLookup.here
  · apply IncRawHasType.firstRule
    exact IncRawHasType.varRule IncRawLookup.here

theorem IncRawLookup.deterministic
    {context : List IncRawType} {index : Nat} {first second : IncRawType} :
    IncRawLookup context index first → IncRawLookup context index second →
      first = second := by
  intro firstLookup
  induction firstLookup generalizing second with
  | here =>
      intro secondLookup
      cases secondLookup
      rfl
  | there previous ih =>
      intro secondLookup
      cases secondLookup with
      | there secondPrevious => exact ih secondPrevious

theorem IncRawLookup.proof_unique
    {context : List IncRawType} {index : Nat} {type : IncRawType}
    (first second : IncRawLookup context index type) : first = second := by
  induction first with
  | here =>
      cases second
      rfl
  | there previous ih =>
      cases second with
      | there secondPrevious =>
          rw [ih secondPrevious]

theorem IncRawHasType.type_unique
    {context : List IncRawType} {term : IncRawTerm}
    {firstType secondType : IncRawType} :
    IncRawHasType context term firstType →
      IncRawHasType context term secondType → firstType = secondType := by
  intro firstTyping
  induction term generalizing context firstType secondType with
  | var index =>
      intro secondTyping
      cases firstTyping with
      | varRule firstLookup =>
          cases secondTyping with
          | varRule secondLookup =>
              exact IncRawLookup.deterministic firstLookup secondLookup
  | unit =>
      intro secondTyping
      cases firstTyping
      cases secondTyping
      rfl
  | pair left right ihLeft ihRight =>
      intro secondTyping
      cases firstTyping with
      | pairRule firstLeft firstRight =>
          cases secondTyping with
          | pairRule secondLeft secondRight =>
              rw [ihLeft firstLeft secondLeft, ihRight firstRight secondRight]
  | first term ih =>
      intro secondTyping
      cases firstTyping with
      | firstRule firstInner =>
          cases secondTyping with
          | firstRule secondInner =>
              have productsEqual := ih firstInner secondInner
              injection productsEqual
  | second term ih =>
      intro secondTyping
      cases firstTyping with
      | secondRule firstInner =>
          cases secondTyping with
          | secondRule secondInner =>
              have productsEqual := ih firstInner secondInner
              injection productsEqual
  | lambda domain body ih =>
      intro secondTyping
      cases firstTyping with
      | lambdaRule firstBody =>
          cases secondTyping with
          | lambdaRule secondBody =>
              exact _root_.congrArg (IncRawType.function domain)
                (ih firstBody secondBody)
  | apply function argument ihFunction ihArgument =>
      intro secondTyping
      cases firstTyping with
      | applyRule firstFunction firstArgument =>
          cases secondTyping with
          | applyRule secondFunction secondArgument =>
              have functionsEqual := ihFunction firstFunction secondFunction
              injection functionsEqual

theorem IncRawHasType.proof_unique
    {context : List IncRawType} {term : IncRawTerm} {type : IncRawType}
    (first second : IncRawHasType context term type) : first = second := by
  induction first with
  | varRule lookup =>
      cases second with
      | varRule secondLookup =>
          rw [IncRawLookup.proof_unique lookup secondLookup]
  | unitRule => cases second; rfl
  | pairRule leftTyping rightTyping ihLeft ihRight =>
      cases second with
      | pairRule secondLeft secondRight =>
          rw [ihLeft secondLeft, ihRight secondRight]
  | firstRule typing ih =>
      cases second with
      | firstRule secondTyping =>
          have productTypes := IncRawHasType.type_unique typing secondTyping
          injection productTypes with _ rightTypeEqual
          subst rightTypeEqual
          rw [ih secondTyping]
  | secondRule typing ih =>
      cases second with
      | secondRule secondTyping =>
          have productTypes := IncRawHasType.type_unique typing secondTyping
          injection productTypes with leftTypeEqual _
          subst leftTypeEqual
          rw [ih secondTyping]
  | lambdaRule typing ih =>
      cases second with
      | lambdaRule secondTyping => rw [ih secondTyping]
  | applyRule functionTyping argumentTyping ihFunction ihArgument =>
      cases second with
      | applyRule secondFunction secondArgument =>
          have functionTypes :=
            IncRawHasType.type_unique functionTyping secondFunction
          injection functionTypes with domainEqual _
          subst domainEqual
          rw [ihFunction secondFunction, ihArgument secondArgument]

def IncRawType.interpret (baseModel : Nat → Type u) : IncRawType → Type u
  | .base index => baseModel index
  | .unit => ULift.{u} Unit
  | .product left right => left.interpret baseModel × right.interpret baseModel
  | .function domain codomain =>
      domain.interpret baseModel → codomain.interpret baseModel

inductive IncRawEnvironment (baseModel : Nat → Type u) :
    List IncRawType → Type (u + 1)
  | empty : IncRawEnvironment baseModel []
  | extend {context type} :
      type.interpret baseModel → IncRawEnvironment baseModel context →
        IncRawEnvironment baseModel (type :: context)

noncomputable def IncRawLookup.evaluate
    {baseModel : Nat → Type u} {context : List IncRawType}
    {index : Nat} {type : IncRawType}
    (lookup : IncRawLookup context index type)
    (environment : IncRawEnvironment baseModel context) :
    type.interpret baseModel := by
  induction lookup with
  | here =>
      cases environment with
      | extend value _ => exact value
  | there previous ih =>
      cases environment with
      | extend _ tail => exact ih tail

noncomputable def IncRawHasType.evaluate
    {baseModel : Nat → Type u} {context : List IncRawType}
    {term : IncRawTerm} {type : IncRawType}
    (typing : IncRawHasType context term type)
    (environment : IncRawEnvironment baseModel context) :
    type.interpret baseModel := by
  induction typing with
  | varRule lookup => exact lookup.evaluate environment
  | unitRule => exact ⟨()⟩
  | pairRule _ _ leftEval rightEval =>
      exact ⟨leftEval environment, rightEval environment⟩
  | firstRule _ termEval =>
      exact (termEval environment).1
  | secondRule _ termEval =>
      exact (termEval environment).2
  | lambdaRule bodyTyping bodyEval =>
      exact fun argument =>
        bodyEval (IncRawEnvironment.extend argument environment)
  | applyRule _ _ functionEval argumentEval =>
      exact functionEval environment (argumentEval environment)

@[simp] theorem IncRawHasType.evaluate_varRule
    {baseModel : Nat → Type u} {context : List IncRawType}
    {index : Nat} {type : IncRawType}
    (lookup : IncRawLookup context index type)
    (environment : IncRawEnvironment baseModel context) :
    (IncRawHasType.varRule lookup).evaluate environment =
      lookup.evaluate environment := by
  rfl

@[simp] theorem IncRawHasType.evaluate_unitRule
    {baseModel : Nat → Type u} {context : List IncRawType}
    (environment : IncRawEnvironment baseModel context) :
    (IncRawHasType.unitRule : IncRawHasType context .unit .unit).evaluate environment =
      (⟨()⟩ : ULift.{u} Unit) := by
  rfl

@[simp] theorem IncRawHasType.evaluate_pairRule
    {baseModel : Nat → Type u} {context : List IncRawType}
    {left right : IncRawTerm} {leftType rightType : IncRawType}
    (leftTyping : IncRawHasType context left leftType)
    (rightTyping : IncRawHasType context right rightType)
    (environment : IncRawEnvironment baseModel context) :
    (IncRawHasType.pairRule leftTyping rightTyping).evaluate environment =
      (leftTyping.evaluate environment, rightTyping.evaluate environment) := by
  rfl

@[simp] theorem IncRawHasType.evaluate_firstRule
    {baseModel : Nat → Type u} {context : List IncRawType}
    {term : IncRawTerm} {leftType rightType : IncRawType}
    (typing : IncRawHasType context term (.product leftType rightType))
    (environment : IncRawEnvironment baseModel context) :
    (IncRawHasType.firstRule typing).evaluate environment =
      (typing.evaluate environment).1 := by
  rfl

@[simp] theorem IncRawHasType.evaluate_secondRule
    {baseModel : Nat → Type u} {context : List IncRawType}
    {term : IncRawTerm} {leftType rightType : IncRawType}
    (typing : IncRawHasType context term (.product leftType rightType))
    (environment : IncRawEnvironment baseModel context) :
    (IncRawHasType.secondRule typing).evaluate environment =
      (typing.evaluate environment).2 := by
  rfl

@[simp] theorem IncRawHasType.evaluate_lambdaRule
    {baseModel : Nat → Type u} {context : List IncRawType}
    {body : IncRawTerm} {domain codomain : IncRawType}
    (typing : IncRawHasType (domain :: context) body codomain)
    (environment : IncRawEnvironment baseModel context) :
    (IncRawHasType.lambdaRule typing).evaluate environment =
      fun argument => typing.evaluate
        (IncRawEnvironment.extend argument environment) := by
  rfl

@[simp] theorem IncRawHasType.evaluate_applyRule
    {baseModel : Nat → Type u} {context : List IncRawType}
    {function argument : IncRawTerm} {domain codomain : IncRawType}
    (functionTyping : IncRawHasType context function (.function domain codomain))
    (argumentTyping : IncRawHasType context argument domain)
    (environment : IncRawEnvironment baseModel context) :
    (IncRawHasType.applyRule functionTyping argumentTyping).evaluate environment =
      functionTyping.evaluate environment (argumentTyping.evaluate environment) := by
  rfl

theorem IncRawHasType.evaluate_congr
    {baseModel : Nat → Type u} {context : List IncRawType}
    {term : IncRawTerm} {type : IncRawType}
    (first second : IncRawHasType context term type)
    (environment : IncRawEnvironment baseModel context) :
    first.evaluate environment = second.evaluate environment := by
  rw [IncRawHasType.proof_unique first second]

theorem IncRawHasType.evaluate_irrelevant
    {baseModel : Nat → Type u} {context : List IncRawType}
    {term : IncRawTerm} {firstType secondType : IncRawType}
    (first : IncRawHasType context term firstType)
    (second : IncRawHasType context term secondType)
    (typesEqual : firstType = secondType)
    (environment : IncRawEnvironment baseModel context) :
    typesEqual ▸ first.evaluate environment = second.evaluate environment := by
  subst secondType
  exact IncRawHasType.evaluate_congr first second environment

theorem incRawIdentity_evaluate
    (baseModel : Nat → Type u) (type : IncRawType)
    (value : type.interpret baseModel) :
      (incRawIdentity_hasType type).evaluate IncRawEnvironment.empty value = value := by
  simp [incRawIdentity_hasType, IncRawHasType.evaluate,
    IncRawLookup.evaluate]

theorem incRawSwap_evaluate
    (baseModel : Nat → Type u) (left right : IncRawType)
    (value : (IncRawType.product left right).interpret baseModel) :
    (incRawSwap_hasType left right).evaluate IncRawEnvironment.empty value =
      (value.2, value.1) := by
  simp [incRawSwap_hasType, IncRawHasType.evaluate,
    IncRawLookup.evaluate]

def IncRawTerm.rename (renameMap : Nat → Nat) : IncRawTerm → IncRawTerm
  | .var index => .var (renameMap index)
  | .unit => .unit
  | .pair left right => .pair (left.rename renameMap) (right.rename renameMap)
  | .first term => .first (term.rename renameMap)
  | .second term => .second (term.rename renameMap)
  | .lambda domain body =>
      .lambda domain (body.rename fun index =>
        match index with
        | 0 => 0
        | next + 1 => renameMap next + 1)
  | .apply function argument =>
      .apply (function.rename renameMap) (argument.rename renameMap)

structure IncRawRenaming (source target : List IncRawType) where
  index : Nat → Nat
  preserves : ∀ {position type}, IncRawLookup source position type →
    IncRawLookup target (index position) type

def IncRawRenaming.identity (context : List IncRawType) :
    IncRawRenaming context context where
  index := id
  preserves := fun lookup => lookup

def IncRawRenaming.fromEmpty (target : List IncRawType) :
    IncRawRenaming [] target where
  index := id
  preserves := by
    intro position type lookup
    cases lookup

def IncRawRenaming.weaken (context : List IncRawType) (head : IncRawType) :
    IncRawRenaming context (head :: context) where
  index := Nat.succ
  preserves := IncRawLookup.there

def IncRawRenaming.lift
    {source target : List IncRawType}
    (renameMap : IncRawRenaming source target) (head : IncRawType) :
    IncRawRenaming (head :: source) (head :: target) where
  index
    | 0 => 0
    | next + 1 => renameMap.index next + 1
  preserves := by
    intro position type lookup
    cases lookup with
    | here => exact IncRawLookup.here
    | there previous => exact IncRawLookup.there (renameMap.preserves previous)

def IncRawRenaming.tail
    {source target : List IncRawType} {head : IncRawType}
    (renameMap : IncRawRenaming (head :: source) target) :
    IncRawRenaming source target where
  index := fun position => renameMap.index (position + 1)
  preserves := fun lookup => renameMap.preserves (IncRawLookup.there lookup)

def IncRawRenaming.skipTarget
    {source target : List IncRawType}
    (renameMap : IncRawRenaming source target) (head : IncRawType) :
    IncRawRenaming source (head :: target) where
  index := fun position => renameMap.index position + 1
  preserves := fun lookup => IncRawLookup.there (renameMap.preserves lookup)

noncomputable def IncRawRenaming.evaluate
    {baseModel : Nat → Type u} {target : List IncRawType} :
    {source : List IncRawType} →
      IncRawRenaming source target →
      IncRawEnvironment baseModel target →
      IncRawEnvironment baseModel source
  | [], _, _ => IncRawEnvironment.empty
  | _ :: _, renameMap, environment =>
      IncRawEnvironment.extend
        ((renameMap.preserves IncRawLookup.here).evaluate environment)
        (renameMap.tail.evaluate environment)

theorem IncRawRenaming.evaluate_lookup
    {baseModel : Nat → Type u} {source target : List IncRawType}
    (renameMap : IncRawRenaming source target)
    (environment : IncRawEnvironment baseModel target)
    {index : Nat} {type : IncRawType}
    (lookup : IncRawLookup source index type) :
    lookup.evaluate (renameMap.evaluate environment) =
      (renameMap.preserves lookup).evaluate environment := by
  induction lookup with
  | here => rfl
  | there previous ih =>
      change previous.evaluate (renameMap.tail.evaluate environment) = _
      exact ih renameMap.tail

theorem IncRawRenaming.skipTarget_evaluate
    {baseModel : Nat → Type u} {source target : List IncRawType}
    (renameMap : IncRawRenaming source target)
    (head : IncRawType) (value : head.interpret baseModel)
    (environment : IncRawEnvironment baseModel target) :
    (renameMap.skipTarget head).evaluate
        (IncRawEnvironment.extend value environment) =
      renameMap.evaluate environment := by
  induction source with
  | nil => rfl
  | cons sourceHead sourceTail ih =>
      simp only [IncRawRenaming.evaluate]
      have tails : (renameMap.skipTarget head).tail =
          renameMap.tail.skipTarget head := by
        cases renameMap
        congr
      rw [tails, ih renameMap.tail]
      rw [IncRawLookup.proof_unique
        ((renameMap.skipTarget head).preserves IncRawLookup.here)
        (IncRawLookup.there (renameMap.preserves IncRawLookup.here))]
      rfl

theorem IncRawRenaming.identity_evaluate
    {baseModel : Nat → Type u} {context : List IncRawType}
    (environment : IncRawEnvironment baseModel context) :
    (IncRawRenaming.identity context).evaluate environment = environment := by
  induction context with
  | nil => cases environment; rfl
  | cons head tail ih =>
      cases environment with
      | extend value tailEnvironment =>
          simp only [IncRawRenaming.evaluate]
          have tails : (IncRawRenaming.identity (head :: tail)).tail =
              (IncRawRenaming.identity tail).skipTarget head := by
            congr
          rw [tails, IncRawRenaming.skipTarget_evaluate,
            ih tailEnvironment]
          rfl

theorem IncRawRenaming.lift_evaluate
    {baseModel : Nat → Type u} {source target : List IncRawType}
    (renameMap : IncRawRenaming source target)
    (head : IncRawType)
    (value : head.interpret baseModel)
    (environment : IncRawEnvironment baseModel target) :
    (renameMap.lift head).evaluate
        (IncRawEnvironment.extend value environment) =
      IncRawEnvironment.extend value (renameMap.evaluate environment) := by
  simp only [IncRawRenaming.evaluate]
  have tailLift : (renameMap.lift head).tail =
      renameMap.skipTarget head := by
    cases renameMap
    congr
  rw [tailLift, renameMap.skipTarget_evaluate]
  rw [IncRawLookup.proof_unique
    ((renameMap.lift head).preserves IncRawLookup.here)
    IncRawLookup.here]
  rfl

noncomputable def IncRawHasType.rename
    {source target : List IncRawType}
    {term : IncRawTerm} {type : IncRawType}
    (typing : IncRawHasType source term type)
    (renameMap : IncRawRenaming source target) :
    IncRawHasType target (term.rename renameMap.index) type := by
  induction typing generalizing target with
  | varRule lookup =>
      exact IncRawHasType.varRule (renameMap.preserves lookup)
  | unitRule => exact IncRawHasType.unitRule
  | pairRule _ _ leftRename rightRename =>
      exact IncRawHasType.pairRule (leftRename renameMap) (rightRename renameMap)
  | firstRule _ termRename =>
      exact IncRawHasType.firstRule (termRename renameMap)
  | secondRule _ termRename =>
      exact IncRawHasType.secondRule (termRename renameMap)
  | lambdaRule bodyTyping bodyRename =>
      exact IncRawHasType.lambdaRule (bodyRename (renameMap.lift _))
  | applyRule _ _ functionRename argumentRename =>
      exact IncRawHasType.applyRule
        (functionRename renameMap) (argumentRename renameMap)

theorem IncRawHasType.evaluate_rename
    {baseModel : Nat → Type u} {source target : List IncRawType}
    {term : IncRawTerm} {type : IncRawType}
    (typing : IncRawHasType source term type)
    (renameMap : IncRawRenaming source target)
    (environment : IncRawEnvironment baseModel target) :
    (typing.rename renameMap).evaluate environment =
      typing.evaluate (renameMap.evaluate environment) := by
  induction typing generalizing target with
  | varRule lookup =>
      exact (renameMap.evaluate_lookup environment lookup).symm
  | unitRule => rfl
  | pairRule leftTyping rightTyping leftIH rightIH =>
      rw [IncRawHasType.evaluate_congr (IncRawHasType.rename
        (IncRawHasType.pairRule leftTyping rightTyping) renameMap)
        (IncRawHasType.pairRule (leftTyping.rename renameMap)
          (rightTyping.rename renameMap)) environment]
      simp only [IncRawHasType.evaluate_pairRule]
      rw [leftIH renameMap environment, rightIH renameMap environment]
  | firstRule typing ih =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.firstRule typing).rename renameMap)
        (IncRawHasType.firstRule (typing.rename renameMap)) environment]
      simp only [IncRawHasType.evaluate_firstRule]
      rw [ih renameMap environment]
  | secondRule typing ih =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.secondRule typing).rename renameMap)
        (IncRawHasType.secondRule (typing.rename renameMap)) environment]
      simp only [IncRawHasType.evaluate_secondRule]
      rw [ih renameMap environment]
  | lambdaRule bodyTyping bodyIH =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.lambdaRule bodyTyping).rename renameMap)
        (IncRawHasType.lambdaRule (bodyTyping.rename (renameMap.lift _)))
        environment]
      simp only [IncRawHasType.evaluate_lambdaRule]
      funext argument
      rw [bodyIH (renameMap.lift _)
        (IncRawEnvironment.extend argument environment)]
      rw [renameMap.lift_evaluate]
  | applyRule functionTyping argumentTyping functionIH argumentIH =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.applyRule functionTyping argumentTyping).rename renameMap)
        (IncRawHasType.applyRule (functionTyping.rename renameMap)
          (argumentTyping.rename renameMap)) environment]
      simp only [IncRawHasType.evaluate_applyRule]
      rw [functionIH renameMap environment, argumentIH renameMap environment]

noncomputable def IncRawHasType.weaken
    {context : List IncRawType} {term : IncRawTerm} {type : IncRawType}
    (typing : IncRawHasType context term type) (head : IncRawType) :
    IncRawHasType (head :: context)
      (term.rename Nat.succ) type :=
  typing.rename (IncRawRenaming.weaken context head)

theorem IncRawHasType.weaken_evaluate
    {baseModel : Nat → Type u} {context : List IncRawType}
    {term : IncRawTerm} {type head : IncRawType}
    (typing : IncRawHasType context term type)
    (value : head.interpret baseModel)
    (environment : IncRawEnvironment baseModel context) :
    (typing.weaken head).evaluate
        (IncRawEnvironment.extend value environment) =
      typing.evaluate environment := by
  change (typing.rename (IncRawRenaming.weaken context head)).evaluate
      (IncRawEnvironment.extend value environment) = _
  rw [IncRawHasType.evaluate_rename]
  have weakenAsSkip : IncRawRenaming.weaken context head =
      (IncRawRenaming.identity context).skipTarget head := by
    congr
  rw [weakenAsSkip, IncRawRenaming.skipTarget_evaluate,
    IncRawRenaming.identity_evaluate]

theorem IncRawTerm.rename_identity (term : IncRawTerm) :
    term.rename id = term := by
  induction term with
  | var index => rfl
  | unit => rfl
  | pair left right ihLeft ihRight => simp [IncRawTerm.rename, ihLeft, ihRight]
  | first term ih => simp [IncRawTerm.rename, ih]
  | second term ih => simp [IncRawTerm.rename, ih]
  | lambda domain body ih =>
      simp only [IncRawTerm.rename]
      congr 1
      have liftIdentity :
          (fun index => match index with
            | 0 => 0
            | next + 1 => id next + 1) = id := by
        funext index
        cases index <;> rfl
      rw [liftIdentity, ih]
  | apply function argument ihFunction ihArgument =>
      simp [IncRawTerm.rename, ihFunction, ihArgument]

def incRawApplyIdentity (type : IncRawType) (argument : IncRawTerm) : IncRawTerm :=
  .apply (incRawIdentity type) argument

noncomputable def incRawApplyIdentity_hasType
    {context : List IncRawType} {type : IncRawType} {argument : IncRawTerm}
    (argumentTyping : IncRawHasType context argument type) :
    IncRawHasType context (incRawApplyIdentity type argument) type :=
  IncRawHasType.applyRule
    ((incRawIdentity_hasType type).rename
      (IncRawRenaming.fromEmpty context))
    argumentTyping

theorem incRawApplyIdentity_evaluate
    {baseModel : Nat → Type u} {context : List IncRawType}
    {type : IncRawType} {argument : IncRawTerm}
    (argumentTyping : IncRawHasType context argument type)
    (environment : IncRawEnvironment baseModel context) :
    (incRawApplyIdentity_hasType argumentTyping).evaluate environment =
      argumentTyping.evaluate environment := by
  simp only [incRawApplyIdentity_hasType,
    IncRawHasType.evaluate_applyRule]
  change (((IncRawRenaming.fromEmpty context).lift type).preserves
      IncRawLookup.here).evaluate
        (IncRawEnvironment.extend (argumentTyping.evaluate environment) environment) = _
  rw [IncRawLookup.proof_unique
    (((IncRawRenaming.fromEmpty context).lift type).preserves IncRawLookup.here)
    IncRawLookup.here]
  rfl

def IncRawTerm.substitute (replacement : Nat → IncRawTerm) :
    IncRawTerm → IncRawTerm
  | .var index => replacement index
  | .unit => .unit
  | .pair left right =>
      .pair (left.substitute replacement) (right.substitute replacement)
  | .first term => .first (term.substitute replacement)
  | .second term => .second (term.substitute replacement)
  | .lambda domain body =>
      .lambda domain (body.substitute fun index =>
        match index with
        | 0 => .var 0
        | next + 1 => (replacement next).rename Nat.succ)
  | .apply function argument =>
      .apply (function.substitute replacement) (argument.substitute replacement)

structure IncRawSubstitution (source target : List IncRawType) where
  term : Nat → IncRawTerm
  preserves : ∀ {position type}, IncRawLookup target position type →
    IncRawHasType source (term position) type

def IncRawSubstitution.identity (context : List IncRawType) :
    IncRawSubstitution context context where
  term := IncRawTerm.var
  preserves := IncRawHasType.varRule

noncomputable def IncRawSubstitution.lift
    {source target : List IncRawType}
    (substitution : IncRawSubstitution source target)
    (head : IncRawType) :
    IncRawSubstitution (head :: source) (head :: target) where
  term
    | 0 => .var 0
    | next + 1 => (substitution.term next).rename Nat.succ
  preserves := by
    intro position type lookup
    cases lookup with
    | here => exact IncRawHasType.varRule IncRawLookup.here
    | there previous =>
        exact (substitution.preserves previous).weaken head

noncomputable def IncRawHasType.substitute
    {source target : List IncRawType}
    {term : IncRawTerm} {type : IncRawType}
    (typing : IncRawHasType target term type)
    (substitution : IncRawSubstitution source target) :
    IncRawHasType source (term.substitute substitution.term) type := by
  induction typing generalizing source with
  | varRule lookup => exact substitution.preserves lookup
  | unitRule => exact IncRawHasType.unitRule
  | pairRule _ _ leftSubstitute rightSubstitute =>
      exact IncRawHasType.pairRule
        (leftSubstitute substitution) (rightSubstitute substitution)
  | firstRule _ termSubstitute =>
      exact IncRawHasType.firstRule (termSubstitute substitution)
  | secondRule _ termSubstitute =>
      exact IncRawHasType.secondRule (termSubstitute substitution)
  | lambdaRule bodyTyping bodySubstitute =>
      exact IncRawHasType.lambdaRule
        (bodySubstitute (substitution.lift _))
  | applyRule _ _ functionSubstitute argumentSubstitute =>
      exact IncRawHasType.applyRule
        (functionSubstitute substitution) (argumentSubstitute substitution)

theorem IncRawTerm.substitute_identity (term : IncRawTerm) :
    term.substitute IncRawTerm.var = term := by
  induction term with
  | var index => rfl
  | unit => rfl
  | pair left right ihLeft ihRight =>
      simp [IncRawTerm.substitute, ihLeft, ihRight]
  | first term ih => simp [IncRawTerm.substitute, ih]
  | second term ih => simp [IncRawTerm.substitute, ih]
  | lambda domain body ih =>
      simp only [IncRawTerm.substitute]
      congr 1
      have liftedIdentity :
          (fun index => match index with
            | 0 => .var 0
            | next + 1 => (IncRawTerm.var next).rename Nat.succ) =
          IncRawTerm.var := by
        funext index
        cases index <;> rfl
      rw [liftedIdentity, ih]
  | apply function argument ihFunction ihArgument =>
      simp [IncRawTerm.substitute, ihFunction, ihArgument]

def IncRawSubstitution.drop
    {source tail : List IncRawType} {head : IncRawType}
    (substitution : IncRawSubstitution source (head :: tail)) :
    IncRawSubstitution source tail where
  term := fun index => substitution.term (index + 1)
  preserves := fun lookup =>
    substitution.preserves (IncRawLookup.there lookup)

noncomputable def IncRawSubstitution.evaluate
    {baseModel : Nat → Type u} {source : List IncRawType} :
    {target : List IncRawType} →
      IncRawSubstitution source target →
      IncRawEnvironment baseModel source →
      IncRawEnvironment baseModel target
  | [], _, _ => IncRawEnvironment.empty
  | _ :: _, substitution, environment =>
      IncRawEnvironment.extend
        ((substitution.preserves IncRawLookup.here).evaluate environment)
        (substitution.drop.evaluate environment)

theorem IncRawSubstitution.evaluate_lookup
    {baseModel : Nat → Type u} {source target : List IncRawType}
    (substitution : IncRawSubstitution source target)
    (environment : IncRawEnvironment baseModel source)
    {index : Nat} {type : IncRawType}
    (lookup : IncRawLookup target index type) :
    (substitution.preserves lookup).evaluate environment =
      lookup.evaluate (substitution.evaluate environment) := by
  induction lookup with
  | here => rfl
  | there previous ih =>
      change
        ((substitution.drop.preserves previous).evaluate environment) = _
      exact ih substitution.drop

theorem IncRawSubstitution.lift_drop_evaluate
    {baseModel : Nat → Type u} {source target : List IncRawType}
    (substitution : IncRawSubstitution source target)
    (head : IncRawType) (value : head.interpret baseModel)
    (environment : IncRawEnvironment baseModel source) :
    (substitution.lift head).drop.evaluate
        (IncRawEnvironment.extend value environment) =
      substitution.evaluate environment := by
  induction target with
  | nil => rfl
  | cons targetHead targetTail ih =>
      simp only [IncRawSubstitution.evaluate]
      congr 1
      · rw [IncRawHasType.evaluate_congr
          (((substitution.lift head).drop).preserves IncRawLookup.here)
          ((substitution.preserves IncRawLookup.here).weaken head)
          (IncRawEnvironment.extend value environment)]
        exact (substitution.preserves IncRawLookup.here).weaken_evaluate
          value environment
      · exact ih substitution.drop

theorem IncRawSubstitution.lift_evaluate
    {baseModel : Nat → Type u} {source target : List IncRawType}
    (substitution : IncRawSubstitution source target)
    (head : IncRawType) (value : head.interpret baseModel)
    (environment : IncRawEnvironment baseModel source) :
    (substitution.lift head).evaluate
        (IncRawEnvironment.extend value environment) =
      IncRawEnvironment.extend value (substitution.evaluate environment) := by
  simp only [IncRawSubstitution.evaluate]
  rw [substitution.lift_drop_evaluate]
  rw [IncRawHasType.evaluate_congr
    ((substitution.lift head).preserves IncRawLookup.here)
    (IncRawHasType.varRule IncRawLookup.here)
    (IncRawEnvironment.extend value environment)]
  rfl

theorem IncRawHasType.evaluate_substitute
    {baseModel : Nat → Type u} {source target : List IncRawType}
    {term : IncRawTerm} {type : IncRawType}
    (typing : IncRawHasType target term type)
    (substitution : IncRawSubstitution source target)
    (environment : IncRawEnvironment baseModel source) :
    (typing.substitute substitution).evaluate environment =
      typing.evaluate (substitution.evaluate environment) := by
  induction typing generalizing source with
  | varRule lookup =>
      exact substitution.evaluate_lookup environment lookup
  | unitRule => rfl
  | pairRule leftTyping rightTyping leftIH rightIH =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.pairRule leftTyping rightTyping).substitute substitution)
        (IncRawHasType.pairRule (leftTyping.substitute substitution)
          (rightTyping.substitute substitution)) environment]
      simp only [IncRawHasType.evaluate_pairRule]
      rw [leftIH substitution environment, rightIH substitution environment]
  | firstRule typing ih =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.firstRule typing).substitute substitution)
        (IncRawHasType.firstRule (typing.substitute substitution)) environment]
      simp only [IncRawHasType.evaluate_firstRule]
      rw [ih substitution environment]
  | secondRule typing ih =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.secondRule typing).substitute substitution)
        (IncRawHasType.secondRule (typing.substitute substitution)) environment]
      simp only [IncRawHasType.evaluate_secondRule]
      rw [ih substitution environment]
  | lambdaRule bodyTyping bodyIH =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.lambdaRule bodyTyping).substitute substitution)
        (IncRawHasType.lambdaRule
          (bodyTyping.substitute (substitution.lift _))) environment]
      simp only [IncRawHasType.evaluate_lambdaRule]
      funext argument
      rw [bodyIH (substitution.lift _)
        (IncRawEnvironment.extend argument environment)]
      rw [substitution.lift_evaluate]
  | applyRule functionTyping argumentTyping functionIH argumentIH =>
      rw [IncRawHasType.evaluate_congr
        ((IncRawHasType.applyRule functionTyping argumentTyping).substitute substitution)
        (IncRawHasType.applyRule (functionTyping.substitute substitution)
          (argumentTyping.substitute substitution)) environment]
      simp only [IncRawHasType.evaluate_applyRule]
      rw [functionIH substitution environment,
        argumentIH substitution environment]

mutual
  inductive IncDepRawType where
    | base : Nat → IncDepRawType
    | unit : IncDepRawType
    | pi : IncDepRawType → IncDepRawType → IncDepRawType
    | sigma : IncDepRawType → IncDepRawType → IncDepRawType
    | identity : IncDepRawType → IncDepRawTerm → IncDepRawTerm →
        IncDepRawType
    deriving DecidableEq, Repr

  inductive IncDepRawTerm where
    | var : Nat → IncDepRawTerm
    | unit : IncDepRawTerm
    | lambda : IncDepRawType → IncDepRawTerm → IncDepRawTerm
    | apply : IncDepRawTerm → IncDepRawTerm → IncDepRawTerm
    | pair : IncDepRawTerm → IncDepRawTerm → IncDepRawTerm
    | first : IncDepRawTerm → IncDepRawTerm
    | second : IncDepRawTerm → IncDepRawTerm
    | refl : IncDepRawTerm → IncDepRawTerm
    deriving DecidableEq, Repr
end

mutual
  def IncDepRawType.rename (renameMap : Nat → Nat) :
      IncDepRawType → IncDepRawType
    | .base index => .base index
    | .unit => .unit
    | .pi domain codomain =>
        .pi (domain.rename renameMap)
          (codomain.rename fun index => match index with
            | 0 => 0
            | next + 1 => renameMap next + 1)
    | .sigma domain codomain =>
        .sigma (domain.rename renameMap)
          (codomain.rename fun index => match index with
            | 0 => 0
            | next + 1 => renameMap next + 1)
    | .identity type left right =>
        .identity (type.rename renameMap) (left.rename renameMap)
          (right.rename renameMap)

  def IncDepRawTerm.rename (renameMap : Nat → Nat) :
      IncDepRawTerm → IncDepRawTerm
    | .var index => .var (renameMap index)
    | .unit => .unit
    | .lambda domain body =>
        .lambda (domain.rename renameMap)
          (body.rename fun index => match index with
            | 0 => 0
            | next + 1 => renameMap next + 1)
    | .apply function argument =>
        .apply (function.rename renameMap) (argument.rename renameMap)
    | .pair first second =>
        .pair (first.rename renameMap) (second.rename renameMap)
    | .first pair => .first (pair.rename renameMap)
    | .second pair => .second (pair.rename renameMap)
    | .refl term => .refl (term.rename renameMap)
end

def IncDepRawTerm.liftReplacement
    (replacement : Nat → IncDepRawTerm) : Nat → IncDepRawTerm
  | 0 => .var 0
  | index + 1 => (replacement index).rename Nat.succ

mutual
  def IncDepRawType.substitute (replacement : Nat → IncDepRawTerm) :
      IncDepRawType → IncDepRawType
    | .base index => .base index
    | .unit => .unit
    | .pi domain codomain =>
        .pi (domain.substitute replacement)
          (codomain.substitute (IncDepRawTerm.liftReplacement replacement))
    | .sigma domain codomain =>
        .sigma (domain.substitute replacement)
          (codomain.substitute (IncDepRawTerm.liftReplacement replacement))
    | .identity type left right =>
        .identity (type.substitute replacement) (left.substitute replacement)
          (right.substitute replacement)

  def IncDepRawTerm.substitute (replacement : Nat → IncDepRawTerm) :
      IncDepRawTerm → IncDepRawTerm
    | .var index => replacement index
    | .unit => .unit
    | .lambda domain body =>
        .lambda (domain.substitute replacement)
          (body.substitute (IncDepRawTerm.liftReplacement replacement))
    | .apply function argument =>
        .apply (function.substitute replacement) (argument.substitute replacement)
    | .pair first second =>
        .pair (first.substitute replacement) (second.substitute replacement)
    | .first pair => .first (pair.substitute replacement)
    | .second pair => .second (pair.substitute replacement)
    | .refl term => .refl (term.substitute replacement)
end

mutual
  theorem IncDepRawType.rename_identity (type : IncDepRawType) :
      type.rename id = type := by
    cases type with
    | base index => rfl
    | unit => rfl
    | pi domain codomain =>
        simp only [IncDepRawType.rename, IncDepRawType.rename_identity domain]
        have liftedIdentity :
            (fun index => match index with
              | 0 => 0
              | next + 1 => id next + 1) = id := by
          funext index
          cases index <;> rfl
        rw [liftedIdentity, IncDepRawType.rename_identity codomain]
    | sigma domain codomain =>
        simp only [IncDepRawType.rename, IncDepRawType.rename_identity domain]
        have liftedIdentity :
            (fun index => match index with
              | 0 => 0
              | next + 1 => id next + 1) = id := by
          funext index
          cases index <;> rfl
        rw [liftedIdentity, IncDepRawType.rename_identity codomain]
    | identity type left right =>
        simp [IncDepRawType.rename, IncDepRawType.rename_identity type,
          IncDepRawTerm.rename_identity left, IncDepRawTerm.rename_identity right]

  theorem IncDepRawTerm.rename_identity (term : IncDepRawTerm) :
      term.rename id = term := by
    cases term with
    | var index => rfl
    | unit => rfl
    | lambda domain body =>
        simp only [IncDepRawTerm.rename, IncDepRawType.rename_identity domain]
        have liftedIdentity :
            (fun index => match index with
              | 0 => 0
              | next + 1 => id next + 1) = id := by
          funext index
          cases index <;> rfl
        rw [liftedIdentity, IncDepRawTerm.rename_identity body]
    | apply function argument =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.rename_identity function,
          IncDepRawTerm.rename_identity argument]
    | pair first second =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.rename_identity first,
          IncDepRawTerm.rename_identity second]
    | first pair => simp [IncDepRawTerm.rename, IncDepRawTerm.rename_identity pair]
    | second pair => simp [IncDepRawTerm.rename, IncDepRawTerm.rename_identity pair]
    | refl term => simp [IncDepRawTerm.rename, IncDepRawTerm.rename_identity term]
end

def IncDepRawTerm.liftRename (renameMap : Nat → Nat) : Nat → Nat
  | 0 => 0
  | index + 1 => renameMap index + 1

theorem IncDepRawTerm.liftRename_comp
    (first second : Nat → Nat) :
    IncDepRawTerm.liftRename (second ∘ first) =
      IncDepRawTerm.liftRename second ∘ IncDepRawTerm.liftRename first := by
  funext index
  cases index <;> rfl

mutual
  theorem IncDepRawType.rename_comp (type : IncDepRawType)
      (first second : Nat → Nat) :
      (type.rename first).rename second = type.rename (second ∘ first) := by
    cases type with
    | base index => rfl
    | unit => rfl
    | pi domain codomain =>
        simp only [IncDepRawType.rename]
        rw [IncDepRawType.rename_comp domain first second]
        congr 1
        rw [IncDepRawType.rename_comp]
        congr 1
        funext index
        cases index <;> rfl
    | sigma domain codomain =>
        simp only [IncDepRawType.rename]
        rw [IncDepRawType.rename_comp domain first second]
        congr 1
        rw [IncDepRawType.rename_comp]
        congr 1
        funext index
        cases index <;> rfl
    | identity type left right =>
        simp only [IncDepRawType.rename]
        rw [IncDepRawType.rename_comp type first second,
          IncDepRawTerm.rename_comp left first second,
          IncDepRawTerm.rename_comp right first second]

  theorem IncDepRawTerm.rename_comp (term : IncDepRawTerm)
      (first second : Nat → Nat) :
      (term.rename first).rename second = term.rename (second ∘ first) := by
    cases term with
    | var index => rfl
    | unit => rfl
    | lambda domain body =>
        simp only [IncDepRawTerm.rename]
        rw [IncDepRawType.rename_comp domain first second]
        congr 1
        rw [IncDepRawTerm.rename_comp]
        congr 1
        funext index
        cases index <;> rfl
    | apply function argument =>
        simp only [IncDepRawTerm.rename]
        rw [IncDepRawTerm.rename_comp function first second,
          IncDepRawTerm.rename_comp argument first second]
    | pair firstTerm secondTerm =>
        simp only [IncDepRawTerm.rename]
        rw [IncDepRawTerm.rename_comp firstTerm first second,
          IncDepRawTerm.rename_comp secondTerm first second]
    | first pair =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.rename_comp pair first second]
    | second pair =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.rename_comp pair first second]
    | refl term =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.rename_comp term first second]
end

theorem IncDepRawTerm.liftReplacement_identity :
    IncDepRawTerm.liftReplacement IncDepRawTerm.var = IncDepRawTerm.var := by
  funext index
  cases index with
  | zero => rfl
  | succ next =>
      simp [IncDepRawTerm.liftReplacement, IncDepRawTerm.rename]

theorem IncDepRawTerm.liftReplacement_rename
    (replacement : Nat → IncDepRawTerm) (renameMap : Nat → Nat) :
    (fun index =>
      (IncDepRawTerm.liftReplacement replacement index).rename
        (IncDepRawTerm.liftRename renameMap)) =
    IncDepRawTerm.liftReplacement
      (fun index => (replacement index).rename renameMap) := by
  funext index
  cases index with
  | zero => rfl
  | succ next =>
      simp only [IncDepRawTerm.liftReplacement]
      rw [IncDepRawTerm.rename_comp, IncDepRawTerm.rename_comp]
      congr 1

mutual
  theorem IncDepRawType.substitute_rename (type : IncDepRawType)
      (replacement : Nat → IncDepRawTerm) (renameMap : Nat → Nat) :
      (type.substitute replacement).rename renameMap =
        type.substitute (fun index => (replacement index).rename renameMap) := by
    cases type with
    | base index => rfl
    | unit => rfl
    | pi domain codomain =>
        simp only [IncDepRawType.substitute, IncDepRawType.rename]
        rw [IncDepRawType.substitute_rename domain]
        rw [IncDepRawType.substitute_rename codomain]
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap next + 1) =
              IncDepRawTerm.liftRename renameMap := by
          funext index
          cases index <;> rfl
        rw [liftEq]
        rw [IncDepRawTerm.liftReplacement_rename]
    | sigma domain codomain =>
        simp only [IncDepRawType.substitute, IncDepRawType.rename]
        rw [IncDepRawType.substitute_rename domain]
        rw [IncDepRawType.substitute_rename codomain]
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap next + 1) =
              IncDepRawTerm.liftRename renameMap := by
          funext index
          cases index <;> rfl
        rw [liftEq]
        rw [IncDepRawTerm.liftReplacement_rename]
    | identity type left right =>
        simp only [IncDepRawType.substitute, IncDepRawType.rename]
        rw [IncDepRawType.substitute_rename type,
          IncDepRawTerm.substitute_rename left,
          IncDepRawTerm.substitute_rename right]

  theorem IncDepRawTerm.substitute_rename (term : IncDepRawTerm)
      (replacement : Nat → IncDepRawTerm) (renameMap : Nat → Nat) :
      (term.substitute replacement).rename renameMap =
        term.substitute (fun index => (replacement index).rename renameMap) := by
    cases term with
    | var index => rfl
    | unit => rfl
    | lambda domain body =>
        simp only [IncDepRawTerm.substitute, IncDepRawTerm.rename]
        rw [IncDepRawType.substitute_rename domain]
        rw [IncDepRawTerm.substitute_rename body]
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap next + 1) =
              IncDepRawTerm.liftRename renameMap := by
          funext index
          cases index <;> rfl
        rw [liftEq]
        rw [IncDepRawTerm.liftReplacement_rename]
    | apply function argument =>
        simp only [IncDepRawTerm.substitute, IncDepRawTerm.rename]
        rw [IncDepRawTerm.substitute_rename function,
          IncDepRawTerm.substitute_rename argument]
    | pair first second =>
        simp only [IncDepRawTerm.substitute, IncDepRawTerm.rename]
        rw [IncDepRawTerm.substitute_rename first,
          IncDepRawTerm.substitute_rename second]
    | first pair =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.rename,
          IncDepRawTerm.substitute_rename pair]
    | second pair =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.rename,
          IncDepRawTerm.substitute_rename pair]
    | refl term =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.rename,
          IncDepRawTerm.substitute_rename term]
end

theorem IncDepRawTerm.liftRename_substitute
    (renameMap : Nat → Nat) (replacement : Nat → IncDepRawTerm) :
    IncDepRawTerm.liftReplacement replacement ∘
        IncDepRawTerm.liftRename renameMap =
    IncDepRawTerm.liftReplacement (replacement ∘ renameMap) := by
  funext index
  cases index <;> rfl

mutual
  theorem IncDepRawType.rename_substitute (type : IncDepRawType)
      (renameMap : Nat → Nat) (replacement : Nat → IncDepRawTerm) :
      (type.rename renameMap).substitute replacement =
        type.substitute (replacement ∘ renameMap) := by
    cases type with
    | base index => rfl
    | unit => rfl
    | pi domain codomain =>
        simp only [IncDepRawType.rename, IncDepRawType.substitute]
        rw [IncDepRawType.rename_substitute domain]
        rw [IncDepRawType.rename_substitute codomain]
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap next + 1) =
              IncDepRawTerm.liftRename renameMap := by
          funext index
          cases index <;> rfl
        rw [liftEq]
        rw [IncDepRawTerm.liftRename_substitute]
    | sigma domain codomain =>
        simp only [IncDepRawType.rename, IncDepRawType.substitute]
        rw [IncDepRawType.rename_substitute domain]
        rw [IncDepRawType.rename_substitute codomain]
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap next + 1) =
              IncDepRawTerm.liftRename renameMap := by
          funext index
          cases index <;> rfl
        rw [liftEq]
        rw [IncDepRawTerm.liftRename_substitute]
    | identity type left right =>
        simp only [IncDepRawType.rename, IncDepRawType.substitute]
        rw [IncDepRawType.rename_substitute type,
          IncDepRawTerm.rename_substitute left,
          IncDepRawTerm.rename_substitute right]

  theorem IncDepRawTerm.rename_substitute (term : IncDepRawTerm)
      (renameMap : Nat → Nat) (replacement : Nat → IncDepRawTerm) :
      (term.rename renameMap).substitute replacement =
        term.substitute (replacement ∘ renameMap) := by
    cases term with
    | var index => rfl
    | unit => rfl
    | lambda domain body =>
        simp only [IncDepRawTerm.rename, IncDepRawTerm.substitute]
        rw [IncDepRawType.rename_substitute domain]
        rw [IncDepRawTerm.rename_substitute body]
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap next + 1) =
              IncDepRawTerm.liftRename renameMap := by
          funext index
          cases index <;> rfl
        rw [liftEq]
        rw [IncDepRawTerm.liftRename_substitute]
    | apply function argument =>
        simp only [IncDepRawTerm.rename, IncDepRawTerm.substitute]
        rw [IncDepRawTerm.rename_substitute function,
          IncDepRawTerm.rename_substitute argument]
    | pair first second =>
        simp only [IncDepRawTerm.rename, IncDepRawTerm.substitute]
        rw [IncDepRawTerm.rename_substitute first,
          IncDepRawTerm.rename_substitute second]
    | first pair =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.substitute,
          IncDepRawTerm.rename_substitute pair]
    | second pair =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.substitute,
          IncDepRawTerm.rename_substitute pair]
    | refl term =>
        simp [IncDepRawTerm.rename, IncDepRawTerm.substitute,
          IncDepRawTerm.rename_substitute term]
end

theorem IncDepRawTerm.liftReplacement_comp
    (first second : Nat → IncDepRawTerm) :
    (fun index =>
      (IncDepRawTerm.liftReplacement first index).substitute
        (IncDepRawTerm.liftReplacement second)) =
    IncDepRawTerm.liftReplacement
      (fun index => (first index).substitute second) := by
  funext index
  cases index with
  | zero => rfl
  | succ next =>
      simp only [IncDepRawTerm.liftReplacement]
      rw [IncDepRawTerm.rename_substitute,
        IncDepRawTerm.substitute_rename]
      congr 1

mutual
  theorem IncDepRawType.substitute_comp (type : IncDepRawType)
      (first second : Nat → IncDepRawTerm) :
      (type.substitute first).substitute second =
        type.substitute (fun index => (first index).substitute second) := by
    cases type with
    | base index => rfl
    | unit => rfl
    | pi domain codomain =>
        simp only [IncDepRawType.substitute]
        rw [IncDepRawType.substitute_comp domain]
        rw [IncDepRawType.substitute_comp codomain]
        rw [IncDepRawTerm.liftReplacement_comp]
    | sigma domain codomain =>
        simp only [IncDepRawType.substitute]
        rw [IncDepRawType.substitute_comp domain]
        rw [IncDepRawType.substitute_comp codomain]
        rw [IncDepRawTerm.liftReplacement_comp]
    | identity type left right =>
        simp only [IncDepRawType.substitute]
        rw [IncDepRawType.substitute_comp type,
          IncDepRawTerm.substitute_comp left,
          IncDepRawTerm.substitute_comp right]

  theorem IncDepRawTerm.substitute_comp (term : IncDepRawTerm)
      (first second : Nat → IncDepRawTerm) :
      (term.substitute first).substitute second =
        term.substitute (fun index => (first index).substitute second) := by
    cases term with
    | var index => rfl
    | unit => rfl
    | lambda domain body =>
        simp only [IncDepRawTerm.substitute]
        rw [IncDepRawType.substitute_comp domain]
        rw [IncDepRawTerm.substitute_comp body]
        rw [IncDepRawTerm.liftReplacement_comp]
    | apply function argument =>
        simp only [IncDepRawTerm.substitute]
        rw [IncDepRawTerm.substitute_comp function,
          IncDepRawTerm.substitute_comp argument]
    | pair firstTerm secondTerm =>
        simp only [IncDepRawTerm.substitute]
        rw [IncDepRawTerm.substitute_comp firstTerm,
          IncDepRawTerm.substitute_comp secondTerm]
    | first pair =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_comp pair]
    | second pair =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_comp pair]
    | refl term =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_comp term]
end

mutual
  theorem IncDepRawType.substitute_identity (type : IncDepRawType) :
      type.substitute IncDepRawTerm.var = type := by
    cases type with
    | base index => rfl
    | unit => rfl
    | pi domain codomain =>
        simp only [IncDepRawType.substitute, IncDepRawType.substitute_identity domain]
        rw [IncDepRawTerm.liftReplacement_identity,
          IncDepRawType.substitute_identity codomain]
    | sigma domain codomain =>
        simp only [IncDepRawType.substitute, IncDepRawType.substitute_identity domain]
        rw [IncDepRawTerm.liftReplacement_identity,
          IncDepRawType.substitute_identity codomain]
    | identity type left right =>
        simp [IncDepRawType.substitute, IncDepRawType.substitute_identity type,
          IncDepRawTerm.substitute_identity left,
          IncDepRawTerm.substitute_identity right]

  theorem IncDepRawTerm.substitute_identity (term : IncDepRawTerm) :
      term.substitute IncDepRawTerm.var = term := by
    cases term with
    | var index => rfl
    | unit => rfl
    | lambda domain body =>
        simp only [IncDepRawTerm.substitute,
          IncDepRawType.substitute_identity domain]
        rw [IncDepRawTerm.liftReplacement_identity,
          IncDepRawTerm.substitute_identity body]
    | apply function argument =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_identity function,
          IncDepRawTerm.substitute_identity argument]
    | pair first second =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_identity first,
          IncDepRawTerm.substitute_identity second]
    | first pair =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_identity pair]
    | second pair =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_identity pair]
    | refl term =>
        simp [IncDepRawTerm.substitute, IncDepRawTerm.substitute_identity term]
end

def IncDepRawType.instantiate (codomain : IncDepRawType)
    (argument : IncDepRawTerm) : IncDepRawType :=
  codomain.substitute fun index => match index with
    | 0 => argument
    | next + 1 => .var next

theorem IncDepRawType.instantiate_rename
    (codomain : IncDepRawType) (argument : IncDepRawTerm)
    (renameMap : Nat → Nat) :
    (codomain.instantiate argument).rename renameMap =
      (codomain.rename (IncDepRawTerm.liftRename renameMap)).instantiate
        (argument.rename renameMap) := by
  simp only [IncDepRawType.instantiate]
  rw [IncDepRawType.substitute_rename,
    IncDepRawType.rename_substitute]
  congr 1
  funext index
  cases index <;> rfl

theorem IncDepRawType.instantiate_substitute
    (codomain : IncDepRawType) (argument : IncDepRawTerm)
    (replacement : Nat → IncDepRawTerm) :
    (codomain.instantiate argument).substitute replacement =
      (codomain.substitute (IncDepRawTerm.liftReplacement replacement)).instantiate
        (argument.substitute replacement) := by
  simp only [IncDepRawType.instantiate]
  rw [IncDepRawType.substitute_comp, IncDepRawType.substitute_comp]
  congr 1
  funext index
  cases index with
  | zero => rfl
  | succ next =>
      simp only [IncDepRawTerm.liftReplacement, IncDepRawTerm.substitute]
      rw [IncDepRawTerm.rename_substitute]
      have mapIdentity :
          ((fun index => match index with
            | 0 => argument.substitute replacement
            | next + 1 => .var next) ∘ Nat.succ) = IncDepRawTerm.var := by
        funext index
        rfl
      rw [mapIdentity, IncDepRawTerm.substitute_identity]

inductive IncDepRawLookup : List IncDepRawType → Nat → IncDepRawType → Type
  | here {context type} :
      IncDepRawLookup (type :: context) 0 (type.rename Nat.succ)
  | there {context index type head} :
      IncDepRawLookup context index type →
        IncDepRawLookup (head :: context) (index + 1) (type.rename Nat.succ)

theorem IncDepRawLookup.deterministic
    {context : List IncDepRawType} {position : Nat}
    {firstType secondType : IncDepRawType} :
    IncDepRawLookup context position firstType →
    IncDepRawLookup context position secondType →
    firstType = secondType := by
  intro firstLookup
  induction firstLookup generalizing secondType with
  | here =>
      intro secondLookup
      cases secondLookup
      rfl
  | there previous ih =>
      intro secondLookup
      cases secondLookup with
      | there secondPrevious =>
          exact _root_.congrArg (fun type => type.rename Nat.succ)
            (ih secondPrevious)

structure IncDepRawRenaming
    (source target : List IncDepRawType) where
  index : Nat → Nat
  preserves : ∀ {position type}, IncDepRawLookup source position type →
    IncDepRawLookup target (index position) (type.rename index)

def IncDepRawRenaming.identity (context : List IncDepRawType) :
    IncDepRawRenaming context context where
  index := id
  preserves := by
    intro position type lookup
    rw [IncDepRawType.rename_identity]
    exact lookup

def IncDepRawRenaming.weakenTarget
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) (head : IncDepRawType) :
    IncDepRawRenaming source (head :: target) where
  index := fun position => renameMap.index position + 1
  preserves := by
    intro position type lookup
    have lifted := IncDepRawLookup.there (head := head)
      (renameMap.preserves lookup)
    rw [IncDepRawType.rename_comp] at lifted
    exact lifted

def IncDepRawRenaming.lift
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) (domain : IncDepRawType) :
    IncDepRawRenaming (domain :: source)
      (domain.rename renameMap.index :: target) where
  index := IncDepRawTerm.liftRename renameMap.index
  preserves := by
    intro position type lookup
    cases lookup with
    | here =>
        change IncDepRawLookup _ 0
          ((domain.rename Nat.succ).rename
            (IncDepRawTerm.liftRename renameMap.index))
        have newest : IncDepRawLookup
            (domain.rename renameMap.index :: target) 0
            ((domain.rename renameMap.index).rename Nat.succ) :=
          IncDepRawLookup.here
        rw [IncDepRawType.rename_comp] at newest ⊢
        have mapsEqual : IncDepRawTerm.liftRename renameMap.index ∘ Nat.succ =
            Nat.succ ∘ renameMap.index := by
          funext index
          rfl
        rw [mapsEqual]
        exact newest
    | there previous =>
        have older := IncDepRawLookup.there
          (head := domain.rename renameMap.index)
          (renameMap.preserves previous)
        rw [IncDepRawType.rename_comp] at older ⊢
        have mapsEqual : IncDepRawTerm.liftRename renameMap.index ∘ Nat.succ =
            Nat.succ ∘ renameMap.index := by
          funext index
          rfl
        rw [mapsEqual]
        exact older

mutual
  inductive IncDepRawWellFormed : List IncDepRawType → IncDepRawType → Type
    | base {context index} : IncDepRawWellFormed context (.base index)
    | unit {context} : IncDepRawWellFormed context .unit
    | pi {context domain codomain} :
        IncDepRawWellFormed context domain →
        IncDepRawWellFormed (domain :: context) codomain →
        IncDepRawWellFormed context (.pi domain codomain)
    | sigma {context domain codomain} :
        IncDepRawWellFormed context domain →
        IncDepRawWellFormed (domain :: context) codomain →
        IncDepRawWellFormed context (.sigma domain codomain)
    | identity {context type left right} :
        IncDepRawWellFormed context type →
        IncDepRawHasType context left type →
        IncDepRawHasType context right type →
        IncDepRawWellFormed context (.identity type left right)

  inductive IncDepRawHasType :
      List IncDepRawType → IncDepRawTerm → IncDepRawType → Type
    | varRule {context index type} :
        IncDepRawLookup context index type →
        IncDepRawHasType context (.var index) type
    | unitRule {context} : IncDepRawHasType context .unit .unit
    | lambdaRule {context domain codomain body} :
        IncDepRawWellFormed context domain →
        IncDepRawHasType (domain :: context) body codomain →
        IncDepRawHasType context (.lambda domain body) (.pi domain codomain)
    | applyRule {context domain codomain function argument} :
        IncDepRawHasType context function (.pi domain codomain) →
        IncDepRawHasType context argument domain →
        IncDepRawHasType context (.apply function argument)
          (codomain.instantiate argument)
    | pairRule {context domain codomain first second} :
        IncDepRawHasType context first domain →
        IncDepRawHasType context second (codomain.instantiate first) →
        IncDepRawHasType context (.pair first second) (.sigma domain codomain)
    | firstRule {context domain codomain pair} :
        IncDepRawHasType context pair (.sigma domain codomain) →
        IncDepRawHasType context (.first pair) domain
    | secondRule {context domain codomain pair} :
        IncDepRawHasType context pair (.sigma domain codomain) →
        IncDepRawHasType context (.second pair)
          (codomain.instantiate (.first pair))
    | reflRule {context type term} :
        IncDepRawHasType context term type →
        IncDepRawHasType context (.refl term) (.identity type term term)
end

mutual
  inductive IncDepRawCoherentFormationDispatchReady :
      {context : List IncDepRawType} → {type : IncDepRawType} →
      (formation : IncDepRawWellFormed context type) → Type
    | base {context index} : IncDepRawCoherentFormationDispatchReady
        (IncDepRawWellFormed.base (context := context) (index := index))
    | unit {context} : IncDepRawCoherentFormationDispatchReady
        (IncDepRawWellFormed.unit (context := context))
    | pi {context domain codomain}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawCoherentFormationDispatchReady domainFormation →
        IncDepRawCoherentFormationDispatchReady codomainFormation →
        IncDepRawCoherentFormationDispatchReady
          (IncDepRawWellFormed.pi domainFormation codomainFormation)
    | sigma {context domain codomain}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawCoherentFormationDispatchReady domainFormation →
        IncDepRawCoherentFormationDispatchReady codomainFormation →
        IncDepRawCoherentFormationDispatchReady
          (IncDepRawWellFormed.sigma domainFormation codomainFormation)
    | identity {context type left right}
        {typeFormation : IncDepRawWellFormed context type}
        {leftTyping : IncDepRawHasType context left type}
        {rightTyping : IncDepRawHasType context right type} :
        IncDepRawCoherentFormationDispatchReady typeFormation →
        IncDepRawCoherentTypingDispatchReady leftTyping typeFormation →
        IncDepRawCoherentTypingDispatchReady rightTyping typeFormation →
        IncDepRawCoherentFormationDispatchReady
          (IncDepRawWellFormed.identity typeFormation leftTyping rightTyping)

  inductive IncDepRawCoherentTypingDispatchReady :
      {context : List IncDepRawType} → {term : IncDepRawTerm} →
      {type : IncDepRawType} → (typing : IncDepRawHasType context term type) →
      (formation : IncDepRawWellFormed context type) → Type
    | varRule {context position type}
        {lookup : IncDepRawLookup context position type}
        {typeFormation : IncDepRawWellFormed context type} :
        IncDepRawCoherentFormationDispatchReady typeFormation →
        IncDepRawCoherentTypingDispatchReady
          (IncDepRawHasType.varRule lookup) typeFormation
    | unitRule {context} : IncDepRawCoherentTypingDispatchReady
        (IncDepRawHasType.unitRule (context := context))
        (IncDepRawWellFormed.unit (context := context))
    | lambdaRule {context domain codomain body}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {bodyTyping : IncDepRawHasType (domain :: context) body codomain} :
        IncDepRawCoherentFormationDispatchReady domainFormation →
        IncDepRawCoherentTypingDispatchReady bodyTyping codomainFormation →
        IncDepRawCoherentTypingDispatchReady
          (IncDepRawHasType.lambdaRule domainFormation bodyTyping)
          (IncDepRawWellFormed.pi domainFormation codomainFormation)
    | applyRule {context domain codomain function argument}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {functionTyping : IncDepRawHasType context function (.pi domain codomain)}
        {argumentTyping : IncDepRawHasType context argument domain}
        {resultFormation : IncDepRawWellFormed context
          (codomain.instantiate argument)} :
        IncDepRawCoherentFormationDispatchReady domainFormation →
        IncDepRawCoherentFormationDispatchReady codomainFormation →
        IncDepRawCoherentFormationDispatchReady resultFormation →
        IncDepRawCoherentTypingDispatchReady functionTyping
          (IncDepRawWellFormed.pi domainFormation codomainFormation) →
        IncDepRawCoherentTypingDispatchReady argumentTyping domainFormation →
        IncDepRawCoherentTypingDispatchReady
          (IncDepRawHasType.applyRule functionTyping argumentTyping)
          resultFormation
    | pairRule {context domain codomain first second}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {firstTyping : IncDepRawHasType context first domain}
        {secondTyping : IncDepRawHasType context second
          (codomain.instantiate first)}
        {resultFormation : IncDepRawWellFormed context
          (codomain.instantiate first)} :
        IncDepRawCoherentFormationDispatchReady domainFormation →
        IncDepRawCoherentFormationDispatchReady codomainFormation →
        IncDepRawCoherentFormationDispatchReady resultFormation →
        IncDepRawCoherentTypingDispatchReady firstTyping domainFormation →
        IncDepRawCoherentTypingDispatchReady secondTyping resultFormation →
        IncDepRawCoherentTypingDispatchReady
          (IncDepRawHasType.pairRule firstTyping secondTyping)
          (IncDepRawWellFormed.sigma domainFormation codomainFormation)
    | firstRule {context domain codomain pair}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)} :
        IncDepRawCoherentFormationDispatchReady domainFormation →
        IncDepRawCoherentFormationDispatchReady codomainFormation →
        IncDepRawCoherentTypingDispatchReady pairTyping
          (IncDepRawWellFormed.sigma domainFormation codomainFormation) →
        IncDepRawCoherentTypingDispatchReady
          (IncDepRawHasType.firstRule pairTyping) domainFormation
    | secondRule {context domain codomain pair}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
        {resultFormation : IncDepRawWellFormed context
          (codomain.instantiate (.first pair))} :
        IncDepRawCoherentFormationDispatchReady domainFormation →
        IncDepRawCoherentFormationDispatchReady codomainFormation →
        IncDepRawCoherentFormationDispatchReady resultFormation →
        IncDepRawCoherentTypingDispatchReady pairTyping
          (IncDepRawWellFormed.sigma domainFormation codomainFormation) →
        IncDepRawCoherentTypingDispatchReady
          (IncDepRawHasType.secondRule pairTyping) resultFormation
    | reflRule {context type term}
        {typeFormation : IncDepRawWellFormed context type}
        {termTyping : IncDepRawHasType context term type} :
        IncDepRawCoherentFormationDispatchReady typeFormation →
        IncDepRawCoherentTypingDispatchReady termTyping typeFormation →
        IncDepRawCoherentTypingDispatchReady
          (IncDepRawHasType.reflRule termTyping)
          (IncDepRawWellFormed.identity typeFormation termTyping termTyping)
end

structure IncDepRawCoherentReadinessAlignmentProvider where
  formationAlignment : ∀
    {context : List IncDepRawType} {type : IncDepRawType}
    {formation : IncDepRawWellFormed context type}
    (first second : IncDepRawCoherentFormationDispatchReady formation),
    first = second
  typingAlignment : ∀
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (first second : IncDepRawCoherentTypingDispatchReady typing formation),
    first = second

def IncDepRawCoherentReadinessAlignmentProvider.alignFormation
    (provider : IncDepRawCoherentReadinessAlignmentProvider)
    {context : List IncDepRawType} {type : IncDepRawType}
    {formation : IncDepRawWellFormed context type}
    (first second : IncDepRawCoherentFormationDispatchReady formation) :
    first = second :=
  provider.formationAlignment first second

def IncDepRawCoherentReadinessAlignmentProvider.alignTyping
    (provider : IncDepRawCoherentReadinessAlignmentProvider)
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (first second : IncDepRawCoherentTypingDispatchReady typing formation) :
    first = second :=
  provider.typingAlignment first second

mutual
  noncomputable def IncDepRawWellFormed.rename
      {source target : List IncDepRawType} {type : IncDepRawType}
      (formation : IncDepRawWellFormed source type)
      (renameMap : IncDepRawRenaming source target) :
      IncDepRawWellFormed target (type.rename renameMap.index) := by
    cases formation with
    | base => exact IncDepRawWellFormed.base
    | unit => exact IncDepRawWellFormed.unit
    | pi domainFormation codomainFormation =>
        exact IncDepRawWellFormed.pi
          (domainFormation.rename renameMap)
          (codomainFormation.rename (renameMap.lift _))
    | sigma domainFormation codomainFormation =>
        exact IncDepRawWellFormed.sigma
          (domainFormation.rename renameMap)
          (codomainFormation.rename (renameMap.lift _))
    | identity typeFormation leftTyping rightTyping =>
        exact IncDepRawWellFormed.identity
          (typeFormation.rename renameMap)
          (leftTyping.rename renameMap)
          (rightTyping.rename renameMap)

  noncomputable def IncDepRawHasType.rename
      {source target : List IncDepRawType}
      {term : IncDepRawTerm} {type : IncDepRawType}
      (typing : IncDepRawHasType source term type)
      (renameMap : IncDepRawRenaming source target) :
      IncDepRawHasType target (term.rename renameMap.index)
        (type.rename renameMap.index) := by
    cases typing with
    | varRule lookup =>
        exact IncDepRawHasType.varRule (renameMap.preserves lookup)
    | unitRule => exact IncDepRawHasType.unitRule
    | lambdaRule domainFormation bodyTyping =>
        exact IncDepRawHasType.lambdaRule
          (domainFormation.rename renameMap)
          (bodyTyping.rename (renameMap.lift _))
    | applyRule functionTyping argumentTyping =>
        have renamed := IncDepRawHasType.applyRule
          (functionTyping.rename renameMap)
          (argumentTyping.rename renameMap)
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap.index next + 1) =
              IncDepRawTerm.liftRename renameMap.index := by
          funext index
          cases index <;> rfl
        rw [liftEq] at renamed
        rw [← IncDepRawType.instantiate_rename] at renamed
        exact renamed
    | pairRule firstTyping secondTyping =>
        have renamedSecond := secondTyping.rename renameMap
        rw [IncDepRawType.instantiate_rename] at renamedSecond
        exact IncDepRawHasType.pairRule
          (firstTyping.rename renameMap) renamedSecond
    | firstRule pairTyping =>
        exact IncDepRawHasType.firstRule (pairTyping.rename renameMap)
    | @secondRule _ domain codomain pair pairTyping =>
        have renamed := IncDepRawHasType.secondRule
          (pairTyping.rename renameMap)
        have liftEq :
            (fun index => match index with
              | 0 => 0
              | next + 1 => renameMap.index next + 1) =
              IncDepRawTerm.liftRename renameMap.index := by
          funext index
          cases index <;> rfl
        rw [liftEq] at renamed
        have instantiation := IncDepRawType.instantiate_rename
          codomain (IncDepRawTerm.first pair) renameMap.index
        simp only [IncDepRawTerm.rename] at instantiation
        rw [← instantiation] at renamed
        exact renamed
    | reflRule termTyping =>
        exact IncDepRawHasType.reflRule (termTyping.rename renameMap)
end

structure IncDepRawSubstitution
    (source target : List IncDepRawType) where
  term : Nat → IncDepRawTerm
  preserves : ∀ {position type}, IncDepRawLookup target position type →
    IncDepRawHasType source (term position) (type.substitute term)

noncomputable def IncDepRawSubstitution.identity
    (context : List IncDepRawType) :
    IncDepRawSubstitution context context where
  term := IncDepRawTerm.var
  preserves := by
    intro position type lookup
    rw [IncDepRawType.substitute_identity]
    exact IncDepRawHasType.varRule lookup

noncomputable def IncDepRawSubstitution.lift
    {source target : List IncDepRawType}
    (substitution : IncDepRawSubstitution source target)
    (domain : IncDepRawType) :
    IncDepRawSubstitution
      (domain.substitute substitution.term :: source)
      (domain :: target) where
  term := IncDepRawTerm.liftReplacement substitution.term
  preserves := by
    intro position type lookup
    cases lookup with
    | here =>
        have newest : IncDepRawHasType
            (domain.substitute substitution.term :: source) (.var 0)
            ((domain.substitute substitution.term).rename Nat.succ) :=
          IncDepRawHasType.varRule IncDepRawLookup.here
        rw [IncDepRawType.substitute_rename] at newest
        have mapEq : (fun index =>
            (substitution.term index).rename Nat.succ) =
            IncDepRawTerm.liftReplacement substitution.term ∘ Nat.succ := by
          funext index
          rfl
        rw [mapEq] at newest
        rw [← IncDepRawType.rename_substitute] at newest
        exact newest
    | there previous =>
        have replacementTyping := substitution.preserves previous
        have weakened := replacementTyping.rename
          ((IncDepRawRenaming.identity source).weakenTarget
            (domain.substitute substitution.term))
        have indexEq :
            ((IncDepRawRenaming.identity source).weakenTarget
              (domain.substitute substitution.term)).index = Nat.succ := by
          funext index
          rfl
        rw [indexEq] at weakened
        rw [IncDepRawType.substitute_rename] at weakened
        have mapEq : (fun index =>
            (substitution.term index).rename Nat.succ) =
            IncDepRawTerm.liftReplacement substitution.term ∘ Nat.succ := by
          funext index
          rfl
        rw [mapEq] at weakened
        rw [← IncDepRawType.rename_substitute] at weakened
        exact weakened

mutual
  noncomputable def IncDepRawWellFormed.substitute
      {source target : List IncDepRawType} {type : IncDepRawType}
      (formation : IncDepRawWellFormed target type)
      (substitution : IncDepRawSubstitution source target) :
      IncDepRawWellFormed source (type.substitute substitution.term) := by
    cases formation with
    | base => exact IncDepRawWellFormed.base
    | unit => exact IncDepRawWellFormed.unit
    | pi domainFormation codomainFormation =>
        exact IncDepRawWellFormed.pi
          (domainFormation.substitute substitution)
          (codomainFormation.substitute (substitution.lift _))
    | sigma domainFormation codomainFormation =>
        exact IncDepRawWellFormed.sigma
          (domainFormation.substitute substitution)
          (codomainFormation.substitute (substitution.lift _))
    | identity typeFormation leftTyping rightTyping =>
        exact IncDepRawWellFormed.identity
          (typeFormation.substitute substitution)
          (leftTyping.substitute substitution)
          (rightTyping.substitute substitution)

  noncomputable def IncDepRawHasType.substitute
      {source target : List IncDepRawType}
      {term : IncDepRawTerm} {type : IncDepRawType}
      (typing : IncDepRawHasType target term type)
      (substitution : IncDepRawSubstitution source target) :
      IncDepRawHasType source (term.substitute substitution.term)
        (type.substitute substitution.term) := by
    cases typing with
    | varRule lookup => exact substitution.preserves lookup
    | unitRule => exact IncDepRawHasType.unitRule
    | lambdaRule domainFormation bodyTyping =>
        exact IncDepRawHasType.lambdaRule
          (domainFormation.substitute substitution)
          (bodyTyping.substitute (substitution.lift _))
    | applyRule functionTyping argumentTyping =>
        have substituted := IncDepRawHasType.applyRule
          (functionTyping.substitute substitution)
          (argumentTyping.substitute substitution)
        rw [← IncDepRawType.instantiate_substitute] at substituted
        exact substituted
    | pairRule firstTyping secondTyping =>
        have substitutedSecond := secondTyping.substitute substitution
        rw [IncDepRawType.instantiate_substitute] at substitutedSecond
        exact IncDepRawHasType.pairRule
          (firstTyping.substitute substitution) substitutedSecond
    | firstRule pairTyping =>
        exact IncDepRawHasType.firstRule (pairTyping.substitute substitution)
    | @secondRule _ domain codomain pair pairTyping =>
        have substituted := IncDepRawHasType.secondRule
          (pairTyping.substitute substitution)
        have instantiation := IncDepRawType.instantiate_substitute
          codomain (IncDepRawTerm.first pair) substitution.term
        simp only [IncDepRawTerm.substitute] at instantiation
        rw [← instantiation] at substituted
        exact substituted
    | reflRule termTyping =>
        exact IncDepRawHasType.reflRule
          (termTyping.substitute substitution)
end

inductive IncDepRawContext.WellFormed : List IncDepRawType → Type
  | empty : WellFormed []
  | extend {context type} :
      WellFormed context → IncDepRawWellFormed context type →
      WellFormed (type :: context)

structure IncDepRawCertifiedTyping
    (context : List IncDepRawType) (term : IncDepRawTerm)
    (type : IncDepRawType) where
  contextWellFormed : IncDepRawContext.WellFormed context
  typeWellFormed : IncDepRawWellFormed context type
  typing : IncDepRawHasType context term type

inductive IncDepRawTypingDeeplyWellFormed :
    {context : List IncDepRawType} → {term : IncDepRawTerm} →
    {type : IncDepRawType} → IncDepRawHasType context term type → Type
  | varRule {context position type}
      {lookup : IncDepRawLookup context position type} :
      IncDepRawWellFormed context type →
      IncDepRawTypingDeeplyWellFormed (IncDepRawHasType.varRule lookup)
  | unitRule {context} :
      IncDepRawTypingDeeplyWellFormed
        (IncDepRawHasType.unitRule (context := context))
  | lambdaRule {context domain codomain body}
      {domainFormation : IncDepRawWellFormed context domain}
      {bodyTyping : IncDepRawHasType (domain :: context) body codomain} :
      IncDepRawWellFormed (domain :: context) codomain →
      IncDepRawTypingDeeplyWellFormed bodyTyping →
      IncDepRawTypingDeeplyWellFormed
        (IncDepRawHasType.lambdaRule domainFormation bodyTyping)
  | applyRule {context domain codomain function argument}
      {functionTyping : IncDepRawHasType context function (.pi domain codomain)}
      {argumentTyping : IncDepRawHasType context argument domain} :
      IncDepRawWellFormed context domain →
      IncDepRawWellFormed (domain :: context) codomain →
      IncDepRawTypingDeeplyWellFormed functionTyping →
      IncDepRawTypingDeeplyWellFormed argumentTyping →
      IncDepRawTypingDeeplyWellFormed
        (IncDepRawHasType.applyRule functionTyping argumentTyping)
  | pairRule {context domain codomain first second}
      {firstTyping : IncDepRawHasType context first domain}
      {secondTyping : IncDepRawHasType context second (codomain.instantiate first)} :
      IncDepRawWellFormed context domain →
      IncDepRawWellFormed (domain :: context) codomain →
      IncDepRawTypingDeeplyWellFormed firstTyping →
      IncDepRawTypingDeeplyWellFormed secondTyping →
      IncDepRawTypingDeeplyWellFormed
        (IncDepRawHasType.pairRule firstTyping secondTyping)
  | firstRule {context domain codomain pair}
      {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)} :
      IncDepRawWellFormed context domain →
      IncDepRawWellFormed (domain :: context) codomain →
      IncDepRawTypingDeeplyWellFormed pairTyping →
      IncDepRawTypingDeeplyWellFormed
        (IncDepRawHasType.firstRule pairTyping)
  | secondRule {context domain codomain pair}
      {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)} :
      IncDepRawWellFormed context domain →
      IncDepRawWellFormed (domain :: context) codomain →
      IncDepRawTypingDeeplyWellFormed pairTyping →
      IncDepRawTypingDeeplyWellFormed
        (IncDepRawHasType.secondRule pairTyping)
  | reflRule {context type term}
      {termTyping : IncDepRawHasType context term type} :
      IncDepRawWellFormed context type →
      IncDepRawTypingDeeplyWellFormed termTyping →
      IncDepRawTypingDeeplyWellFormed
        (IncDepRawHasType.reflRule termTyping)

structure IncDepRawDeepCertifiedTyping
    (context : List IncDepRawType) (term : IncDepRawTerm)
    (type : IncDepRawType) extends IncDepRawCertifiedTyping context term type where
  deeplyWellFormed : IncDepRawTypingDeeplyWellFormed toIncDepRawCertifiedTyping.typing

mutual
  inductive IncDepRawFormationSemanticReady :
      {context : List IncDepRawType} → {type : IncDepRawType} →
      IncDepRawWellFormed context type → Type
    | base {context index} :
        IncDepRawFormationSemanticReady
          (IncDepRawWellFormed.base (context := context) (index := index))
    | unit {context} :
        IncDepRawFormationSemanticReady
          (IncDepRawWellFormed.unit (context := context))
    | pi {context domain codomain}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationSemanticReady domainFormation →
        IncDepRawFormationSemanticReady codomainFormation →
        IncDepRawFormationSemanticReady
          (IncDepRawWellFormed.pi domainFormation codomainFormation)
    | sigma {context domain codomain}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationSemanticReady domainFormation →
        IncDepRawFormationSemanticReady codomainFormation →
        IncDepRawFormationSemanticReady
          (IncDepRawWellFormed.sigma domainFormation codomainFormation)
    | identity {context type left right}
        {typeFormation : IncDepRawWellFormed context type}
        {leftTyping : IncDepRawHasType context left type}
        {rightTyping : IncDepRawHasType context right type} :
        IncDepRawFormationSemanticReady typeFormation →
        IncDepRawTypingSemanticReady leftTyping →
        IncDepRawTypingSemanticReady rightTyping →
        IncDepRawFormationSemanticReady
          (IncDepRawWellFormed.identity typeFormation leftTyping rightTyping)

  inductive IncDepRawTypingSemanticReady :
      {context : List IncDepRawType} → {term : IncDepRawTerm} →
      {type : IncDepRawType} → IncDepRawHasType context term type → Type
    | varRule {context position type}
        {lookup : IncDepRawLookup context position type}
        {typeFormation : IncDepRawWellFormed context type} :
        IncDepRawFormationSemanticReady typeFormation →
        IncDepRawTypingSemanticReady (IncDepRawHasType.varRule lookup)
    | unitRule {context} :
        IncDepRawTypingSemanticReady
          (IncDepRawHasType.unitRule (context := context))
    | lambdaRule {context domain codomain body}
        {domainFormation : IncDepRawWellFormed context domain}
        {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationSemanticReady domainFormation →
        IncDepRawFormationSemanticReady codomainFormation →
        IncDepRawTypingSemanticReady bodyTyping →
        IncDepRawTypingSemanticReady
          (IncDepRawHasType.lambdaRule domainFormation bodyTyping)
    | applyRule {context domain codomain function argument}
        {functionTyping : IncDepRawHasType context function (.pi domain codomain)}
        {argumentTyping : IncDepRawHasType context argument domain}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationSemanticReady domainFormation →
        IncDepRawFormationSemanticReady codomainFormation →
        IncDepRawTypingSemanticReady functionTyping →
        IncDepRawTypingSemanticReady argumentTyping →
        IncDepRawTypingSemanticReady
          (IncDepRawHasType.applyRule functionTyping argumentTyping)
    | pairRule {context : List IncDepRawType}
        {domain codomain : IncDepRawType} {first second : IncDepRawTerm}
        {firstTyping : IncDepRawHasType context first domain}
        {secondTyping : IncDepRawHasType context second (codomain.instantiate first)}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationSemanticReady domainFormation →
        IncDepRawFormationSemanticReady codomainFormation →
        IncDepRawTypingSemanticReady firstTyping →
        IncDepRawTypingSemanticReady secondTyping →
        IncDepRawTypingSemanticReady
          (IncDepRawHasType.pairRule firstTyping secondTyping)
    | firstRule {context domain codomain pair}
        {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationSemanticReady domainFormation →
        IncDepRawFormationSemanticReady codomainFormation →
        IncDepRawTypingSemanticReady pairTyping →
        IncDepRawTypingSemanticReady (IncDepRawHasType.firstRule pairTyping)
    | secondRule {context domain codomain pair}
        {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationSemanticReady domainFormation →
        IncDepRawFormationSemanticReady codomainFormation →
        IncDepRawTypingSemanticReady pairTyping →
        IncDepRawTypingSemanticReady (IncDepRawHasType.secondRule pairTyping)
    | reflRule {context type term}
        {termTyping : IncDepRawHasType context term type}
        {typeFormation : IncDepRawWellFormed context type} :
        IncDepRawFormationSemanticReady typeFormation →
        IncDepRawTypingSemanticReady termTyping →
        IncDepRawTypingSemanticReady (IncDepRawHasType.reflRule termTyping)
end

def IncDepRawFormationSemanticReady.formation
    {context : List IncDepRawType} {type : IncDepRawType}
    {formation : IncDepRawWellFormed context type}
    (_ready : IncDepRawFormationSemanticReady formation) :
    IncDepRawWellFormed context type :=
  formation

def IncDepRawFormationSemanticReady.renameBase
    {source target : List IncDepRawType} {index : Nat}
    (renameMap : IncDepRawRenaming source target) :
    IncDepRawFormationSemanticReady
      ((IncDepRawWellFormed.base (context := source) (index := index)).rename
        renameMap) :=
  IncDepRawFormationSemanticReady.base

def IncDepRawFormationSemanticReady.renameUnit
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) :
    IncDepRawFormationSemanticReady
      ((IncDepRawWellFormed.unit (context := source)).rename renameMap) :=
  IncDepRawFormationSemanticReady.unit

def IncDepRawTypingSemanticReady.renameUnit
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) :
    IncDepRawTypingSemanticReady
      ((IncDepRawHasType.unitRule (context := source)).rename renameMap) :=
  IncDepRawTypingSemanticReady.unitRule

structure IncDepRawFormationRenamedReadyResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {formation : IncDepRawWellFormed source type}
    (_ready : IncDepRawFormationSemanticReady formation)
    (renameMap : IncDepRawRenaming source target) where
  renamedFormation : IncDepRawWellFormed target
    (type.rename renameMap.index)
  renamedReady : IncDepRawFormationSemanticReady renamedFormation

structure IncDepRawTypingRenamedReadyResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType source term type}
    (_ready : IncDepRawTypingSemanticReady typing)
    (renameMap : IncDepRawRenaming source target) where
  renamedTyping : IncDepRawHasType target
    (term.rename renameMap.index) (type.rename renameMap.index)
  renamedReady : IncDepRawTypingSemanticReady renamedTyping

def IncDepRawFormationRenamedReadyResult.base
    {source target : List IncDepRawType} {index : Nat}
    (renameMap : IncDepRawRenaming source target) :
    IncDepRawFormationRenamedReadyResult
      (IncDepRawFormationSemanticReady.base (context := source) (index := index))
      renameMap where
  renamedFormation := IncDepRawWellFormed.base
  renamedReady := IncDepRawFormationSemanticReady.base

def IncDepRawFormationRenamedReadyResult.unit
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) :
    IncDepRawFormationRenamedReadyResult
      (IncDepRawFormationSemanticReady.unit (context := source)) renameMap where
  renamedFormation := IncDepRawWellFormed.unit
  renamedReady := IncDepRawFormationSemanticReady.unit

def IncDepRawTypingRenamedReadyResult.unit
    {source target : List IncDepRawType}
    (renameMap : IncDepRawRenaming source target) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.unitRule (context := source)) renameMap where
  renamedTyping := IncDepRawHasType.unitRule
  renamedReady := IncDepRawTypingSemanticReady.unitRule

def IncDepRawTypingRenamedReadyResult.variable
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType} {lookup : IncDepRawLookup source position type}
    {typeFormation : IncDepRawWellFormed source type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    (renameMap : IncDepRawRenaming source target)
    (typeResult : IncDepRawFormationRenamedReadyResult typeReady renameMap) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.varRule (lookup := lookup) typeReady)
      renameMap where
  renamedTyping := IncDepRawHasType.varRule (renameMap.preserves lookup)
  renamedReady := IncDepRawTypingSemanticReady.varRule typeResult.renamedReady

def IncDepRawFormationRenamedReadyResult.pi
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed source domain}
    {codomainFormation : IncDepRawWellFormed (domain :: source) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    (renameMap : IncDepRawRenaming source target)
    (domainResult : IncDepRawFormationRenamedReadyResult domainReady renameMap)
    (codomainResult : IncDepRawFormationRenamedReadyResult codomainReady
      (renameMap.lift domain)) :
    IncDepRawFormationRenamedReadyResult
      (IncDepRawFormationSemanticReady.pi domainReady codomainReady)
      renameMap where
  renamedFormation := IncDepRawWellFormed.pi
    domainResult.renamedFormation codomainResult.renamedFormation
  renamedReady := IncDepRawFormationSemanticReady.pi
    domainResult.renamedReady codomainResult.renamedReady

def IncDepRawFormationRenamedReadyResult.sigma
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {domainFormation : IncDepRawWellFormed source domain}
    {codomainFormation : IncDepRawWellFormed (domain :: source) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    (renameMap : IncDepRawRenaming source target)
    (domainResult : IncDepRawFormationRenamedReadyResult domainReady renameMap)
    (codomainResult : IncDepRawFormationRenamedReadyResult codomainReady
      (renameMap.lift domain)) :
    IncDepRawFormationRenamedReadyResult
      (IncDepRawFormationSemanticReady.sigma domainReady codomainReady)
      renameMap where
  renamedFormation := IncDepRawWellFormed.sigma
    domainResult.renamedFormation codomainResult.renamedFormation
  renamedReady := IncDepRawFormationSemanticReady.sigma
    domainResult.renamedReady codomainResult.renamedReady

def IncDepRawFormationRenamedReadyResult.identity
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed source type}
    {leftTyping : IncDepRawHasType source left type}
    {rightTyping : IncDepRawHasType source right type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {leftReady : IncDepRawTypingSemanticReady leftTyping}
    {rightReady : IncDepRawTypingSemanticReady rightTyping}
    (renameMap : IncDepRawRenaming source target)
    (typeResult : IncDepRawFormationRenamedReadyResult typeReady renameMap)
    (leftResult : IncDepRawTypingRenamedReadyResult leftReady renameMap)
    (rightResult : IncDepRawTypingRenamedReadyResult rightReady renameMap) :
    IncDepRawFormationRenamedReadyResult
      (IncDepRawFormationSemanticReady.identity typeReady leftReady rightReady)
      renameMap where
  renamedFormation := IncDepRawWellFormed.identity typeResult.renamedFormation
    leftResult.renamedTyping rightResult.renamedTyping
  renamedReady := IncDepRawFormationSemanticReady.identity typeResult.renamedReady
    leftResult.renamedReady rightResult.renamedReady

def IncDepRawTypingRenamedReadyResult.lambda
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed source domain}
    {codomainFormation : IncDepRawWellFormed (domain :: source) codomain}
    {bodyTyping : IncDepRawHasType (domain :: source) body codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {bodyReady : IncDepRawTypingSemanticReady bodyTyping}
    (renameMap : IncDepRawRenaming source target)
    (domainResult : IncDepRawFormationRenamedReadyResult domainReady renameMap)
    (codomainResult : IncDepRawFormationRenamedReadyResult codomainReady
      (renameMap.lift domain))
    (bodyResult : IncDepRawTypingRenamedReadyResult bodyReady
      (renameMap.lift domain)) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.lambdaRule domainReady codomainReady bodyReady)
      renameMap where
  renamedTyping := IncDepRawHasType.lambdaRule domainResult.renamedFormation
    bodyResult.renamedTyping
  renamedReady := IncDepRawTypingSemanticReady.lambdaRule
    domainResult.renamedReady codomainResult.renamedReady bodyResult.renamedReady

def IncDepRawTypingRenamedReadyResult.first
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {pairTyping : IncDepRawHasType source pair (.sigma domain codomain)}
    {domainFormation : IncDepRawWellFormed source domain}
    {codomainFormation : IncDepRawWellFormed (domain :: source) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {pairReady : IncDepRawTypingSemanticReady pairTyping}
    (renameMap : IncDepRawRenaming source target)
    (domainResult : IncDepRawFormationRenamedReadyResult domainReady renameMap)
    (codomainResult : IncDepRawFormationRenamedReadyResult codomainReady
      (renameMap.lift domain))
    (pairResult : IncDepRawTypingRenamedReadyResult pairReady renameMap) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.firstRule domainReady codomainReady pairReady)
      renameMap where
  renamedTyping := IncDepRawHasType.firstRule pairResult.renamedTyping
  renamedReady := IncDepRawTypingSemanticReady.firstRule domainResult.renamedReady
    codomainResult.renamedReady pairResult.renamedReady

def IncDepRawTypingRenamedReadyResult.refl
    {source target : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm} {termTyping : IncDepRawHasType source term type}
    {typeFormation : IncDepRawWellFormed source type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {termReady : IncDepRawTypingSemanticReady termTyping}
    (renameMap : IncDepRawRenaming source target)
    (typeResult : IncDepRawFormationRenamedReadyResult typeReady renameMap)
    (termResult : IncDepRawTypingRenamedReadyResult termReady renameMap) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.reflRule typeReady termReady) renameMap where
  renamedTyping := IncDepRawHasType.reflRule termResult.renamedTyping
  renamedReady := IncDepRawTypingSemanticReady.reflRule typeResult.renamedReady
    termResult.renamedReady

noncomputable def IncDepRawTypingRenamedReadyResult.apply
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {functionTyping : IncDepRawHasType source function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType source argument domain}
    {domainFormation : IncDepRawWellFormed source domain}
    {codomainFormation : IncDepRawWellFormed (domain :: source) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {functionReady : IncDepRawTypingSemanticReady functionTyping}
    {argumentReady : IncDepRawTypingSemanticReady argumentTyping}
    (renameMap : IncDepRawRenaming source target)
    (domainResult : IncDepRawFormationRenamedReadyResult domainReady renameMap)
    (codomainResult : IncDepRawFormationRenamedReadyResult codomainReady
      (renameMap.lift domain))
    (functionResult : IncDepRawTypingRenamedReadyResult functionReady renameMap)
    (argumentResult : IncDepRawTypingRenamedReadyResult argumentReady renameMap) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.applyRule domainReady codomainReady
        functionReady argumentReady) renameMap := by
  let renamedTyping := IncDepRawHasType.applyRule functionResult.renamedTyping
    argumentResult.renamedTyping
  let packaged : Sigma fun typing : IncDepRawHasType target
      ((function.rename renameMap.index).apply
        (argument.rename renameMap.index))
      ((codomain.rename (IncDepRawTerm.liftRename renameMap.index)).instantiate
        (argument.rename renameMap.index)) =>
      IncDepRawTypingSemanticReady typing :=
    ⟨renamedTyping, IncDepRawTypingSemanticReady.applyRule
      domainResult.renamedReady codomainResult.renamedReady
      functionResult.renamedReady argumentResult.renamedReady⟩
  rw [← IncDepRawType.instantiate_rename] at packaged
  exact ⟨packaged.1, packaged.2⟩

noncomputable def IncDepRawTypingRenamedReadyResult.pair
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {firstTyping : IncDepRawHasType source first domain}
    {secondTyping : IncDepRawHasType source second (codomain.instantiate first)}
    {domainFormation : IncDepRawWellFormed source domain}
    {codomainFormation : IncDepRawWellFormed (domain :: source) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {firstReady : IncDepRawTypingSemanticReady firstTyping}
    {secondReady : IncDepRawTypingSemanticReady secondTyping}
    (renameMap : IncDepRawRenaming source target)
    (domainResult : IncDepRawFormationRenamedReadyResult domainReady renameMap)
    (codomainResult : IncDepRawFormationRenamedReadyResult codomainReady
      (renameMap.lift domain))
    (firstResult : IncDepRawTypingRenamedReadyResult firstReady renameMap)
    (secondResult : IncDepRawTypingRenamedReadyResult secondReady renameMap) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.pairRule domainReady codomainReady
        firstReady secondReady) renameMap := by
  let packagedSecond : Sigma fun typing : IncDepRawHasType target
      (second.rename renameMap.index)
      ((codomain.instantiate first).rename renameMap.index) =>
      IncDepRawTypingSemanticReady typing :=
    ⟨secondResult.renamedTyping, secondResult.renamedReady⟩
  rw [IncDepRawType.instantiate_rename] at packagedSecond
  let renamedTyping := IncDepRawHasType.pairRule firstResult.renamedTyping
    packagedSecond.1
  let renamedReady := IncDepRawTypingSemanticReady.pairRule
    domainResult.renamedReady codomainResult.renamedReady
    firstResult.renamedReady packagedSecond.2
  exact ⟨renamedTyping, renamedReady⟩

noncomputable def IncDepRawTypingRenamedReadyResult.second
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {pairTyping : IncDepRawHasType source pair (.sigma domain codomain)}
    {domainFormation : IncDepRawWellFormed source domain}
    {codomainFormation : IncDepRawWellFormed (domain :: source) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {pairReady : IncDepRawTypingSemanticReady pairTyping}
    (renameMap : IncDepRawRenaming source target)
    (domainResult : IncDepRawFormationRenamedReadyResult domainReady renameMap)
    (codomainResult : IncDepRawFormationRenamedReadyResult codomainReady
      (renameMap.lift domain))
    (pairResult : IncDepRawTypingRenamedReadyResult pairReady renameMap) :
    IncDepRawTypingRenamedReadyResult
      (IncDepRawTypingSemanticReady.secondRule domainReady codomainReady pairReady)
      renameMap := by
  let renamedTyping := IncDepRawHasType.secondRule pairResult.renamedTyping
  let packaged : Sigma fun typing : IncDepRawHasType target
      (.second (pair.rename renameMap.index))
      ((codomain.rename (IncDepRawTerm.liftRename renameMap.index)).instantiate
        (.first (pair.rename renameMap.index))) =>
      IncDepRawTypingSemanticReady typing :=
    ⟨renamedTyping, IncDepRawTypingSemanticReady.secondRule
      domainResult.renamedReady codomainResult.renamedReady
      pairResult.renamedReady⟩
  have instantiation := IncDepRawType.instantiate_rename
    codomain (IncDepRawTerm.first pair) renameMap.index
  simp only [IncDepRawTerm.rename] at instantiation
  rw [← instantiation] at packaged
  exact ⟨packaged.1, packaged.2⟩

mutual
  noncomputable def IncDepRawFormationSemanticReady.renameResult
      {source target : List IncDepRawType} {type : IncDepRawType}
      {formation : IncDepRawWellFormed source type}
      (ready : IncDepRawFormationSemanticReady formation)
      (renameMap : IncDepRawRenaming source target) :
      IncDepRawFormationRenamedReadyResult ready renameMap :=
    match ready with
    | .base => IncDepRawFormationRenamedReadyResult.base renameMap
    | .unit => IncDepRawFormationRenamedReadyResult.unit renameMap
    | .pi domainReady codomainReady =>
        IncDepRawFormationRenamedReadyResult.pi renameMap
          (IncDepRawFormationSemanticReady.renameResult domainReady renameMap)
          (IncDepRawFormationSemanticReady.renameResult codomainReady (renameMap.lift _))
    | .sigma domainReady codomainReady =>
        IncDepRawFormationRenamedReadyResult.sigma renameMap
          (IncDepRawFormationSemanticReady.renameResult domainReady renameMap)
          (IncDepRawFormationSemanticReady.renameResult codomainReady (renameMap.lift _))
    | .identity typeReady leftReady rightReady =>
        IncDepRawFormationRenamedReadyResult.identity renameMap
          (IncDepRawFormationSemanticReady.renameResult typeReady renameMap)
          (IncDepRawTypingSemanticReady.renameResult leftReady renameMap)
          (IncDepRawTypingSemanticReady.renameResult rightReady renameMap)

  noncomputable def IncDepRawTypingSemanticReady.renameResult
      {source target : List IncDepRawType} {term : IncDepRawTerm}
      {type : IncDepRawType} {typing : IncDepRawHasType source term type}
      (ready : IncDepRawTypingSemanticReady typing)
      (renameMap : IncDepRawRenaming source target) :
      IncDepRawTypingRenamedReadyResult ready renameMap :=
    match ready with
    | .varRule typeReady =>
        IncDepRawTypingRenamedReadyResult.variable renameMap
          (IncDepRawFormationSemanticReady.renameResult typeReady renameMap)
    | .unitRule => IncDepRawTypingRenamedReadyResult.unit renameMap
    | .lambdaRule domainReady codomainReady bodyReady =>
        IncDepRawTypingRenamedReadyResult.lambda renameMap
          (IncDepRawFormationSemanticReady.renameResult domainReady renameMap)
          (IncDepRawFormationSemanticReady.renameResult codomainReady
            (renameMap.lift _))
          (IncDepRawTypingSemanticReady.renameResult bodyReady (renameMap.lift _))
    | .applyRule domainReady codomainReady functionReady argumentReady =>
        IncDepRawTypingRenamedReadyResult.apply renameMap
          (IncDepRawFormationSemanticReady.renameResult domainReady renameMap)
          (IncDepRawFormationSemanticReady.renameResult codomainReady
            (renameMap.lift _))
          (IncDepRawTypingSemanticReady.renameResult functionReady renameMap)
          (IncDepRawTypingSemanticReady.renameResult argumentReady renameMap)
    | .pairRule domainReady codomainReady firstReady secondReady =>
        IncDepRawTypingRenamedReadyResult.pair renameMap
          (IncDepRawFormationSemanticReady.renameResult domainReady renameMap)
          (IncDepRawFormationSemanticReady.renameResult codomainReady
            (renameMap.lift _))
          (IncDepRawTypingSemanticReady.renameResult firstReady renameMap)
          (IncDepRawTypingSemanticReady.renameResult secondReady renameMap)
    | .firstRule domainReady codomainReady pairReady =>
        IncDepRawTypingRenamedReadyResult.first renameMap
          (IncDepRawFormationSemanticReady.renameResult domainReady renameMap)
          (IncDepRawFormationSemanticReady.renameResult codomainReady
            (renameMap.lift _))
          (IncDepRawTypingSemanticReady.renameResult pairReady renameMap)
    | .secondRule domainReady codomainReady pairReady =>
        IncDepRawTypingRenamedReadyResult.second renameMap
          (IncDepRawFormationSemanticReady.renameResult domainReady renameMap)
          (IncDepRawFormationSemanticReady.renameResult codomainReady
            (renameMap.lift _))
          (IncDepRawTypingSemanticReady.renameResult pairReady renameMap)
    | .reflRule typeReady termReady =>
        IncDepRawTypingRenamedReadyResult.refl renameMap
          (IncDepRawFormationSemanticReady.renameResult typeReady renameMap)
          (IncDepRawTypingSemanticReady.renameResult termReady renameMap)
end

noncomputable def IncDepRawFormationSemanticReady.weakenResult
    {context : List IncDepRawType} {type head : IncDepRawType}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawFormationSemanticReady formation) :
    IncDepRawFormationRenamedReadyResult ready
      ((IncDepRawRenaming.identity context).weakenTarget head) :=
  ready.renameResult
    ((IncDepRawRenaming.identity context).weakenTarget head)

noncomputable def IncDepRawTypingSemanticReady.weakenResult
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type head : IncDepRawType}
    {typing : IncDepRawHasType context term type}
    (ready : IncDepRawTypingSemanticReady typing) :
    IncDepRawTypingRenamedReadyResult ready
      ((IncDepRawRenaming.identity context).weakenTarget head) :=
  ready.renameResult
    ((IncDepRawRenaming.identity context).weakenTarget head)

noncomputable def IncDepRawTypingSemanticReady.toDeeplyWellFormed
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    (ready : IncDepRawTypingSemanticReady typing) :
    IncDepRawTypingDeeplyWellFormed typing := by
  cases ready with
  | varRule typeReady =>
      exact IncDepRawTypingDeeplyWellFormed.varRule typeReady.formation
  | unitRule => exact IncDepRawTypingDeeplyWellFormed.unitRule
  | lambdaRule domainReady codomainReady bodyReady =>
      exact IncDepRawTypingDeeplyWellFormed.lambdaRule
        codomainReady.formation bodyReady.toDeeplyWellFormed
  | applyRule domainReady codomainReady functionReady argumentReady
      =>
      exact IncDepRawTypingDeeplyWellFormed.applyRule
        domainReady.formation codomainReady.formation
        functionReady.toDeeplyWellFormed argumentReady.toDeeplyWellFormed
  | pairRule domainReady codomainReady firstReady secondReady =>
      exact IncDepRawTypingDeeplyWellFormed.pairRule
        domainReady.formation codomainReady.formation
        firstReady.toDeeplyWellFormed secondReady.toDeeplyWellFormed
  | firstRule domainReady codomainReady pairReady =>
      exact IncDepRawTypingDeeplyWellFormed.firstRule
        domainReady.formation codomainReady.formation
        pairReady.toDeeplyWellFormed
  | secondRule domainReady codomainReady pairReady =>
      exact IncDepRawTypingDeeplyWellFormed.secondRule
        domainReady.formation codomainReady.formation
        pairReady.toDeeplyWellFormed
  | reflRule typeReady termReady =>
      exact IncDepRawTypingDeeplyWellFormed.reflRule
        typeReady.formation termReady.toDeeplyWellFormed

noncomputable def IncDepRawDeepCertifiedTyping.ofSemanticReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (certified : IncDepRawCertifiedTyping context term type)
    (ready : IncDepRawTypingSemanticReady certified.typing) :
    IncDepRawDeepCertifiedTyping context term type where
  toIncDepRawCertifiedTyping := certified
  deeplyWellFormed := ready.toDeeplyWellFormed

def IncDepRawCertifiedTyping.ofClosed
    {term : IncDepRawTerm} {type : IncDepRawType}
    (typeWellFormed : IncDepRawWellFormed [] type)
    (typing : IncDepRawHasType [] term type) :
    IncDepRawCertifiedTyping [] term type where
  contextWellFormed := IncDepRawContext.WellFormed.empty
  typeWellFormed := typeWellFormed
  typing := typing

noncomputable def IncDepRawCertifiedTyping.rename
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (certified : IncDepRawCertifiedTyping source term type)
    (renameMap : IncDepRawRenaming source target)
    (targetWellFormed : IncDepRawContext.WellFormed target) :
    IncDepRawCertifiedTyping target (term.rename renameMap.index)
      (type.rename renameMap.index) where
  contextWellFormed := targetWellFormed
  typeWellFormed := certified.typeWellFormed.rename renameMap
  typing := certified.typing.rename renameMap

noncomputable def IncDepRawCertifiedTyping.substitute
    {source target : List IncDepRawType}
    {term : IncDepRawTerm} {type : IncDepRawType}
    (certified : IncDepRawCertifiedTyping target term type)
    (substitution : IncDepRawSubstitution source target)
    (sourceWellFormed : IncDepRawContext.WellFormed source) :
    IncDepRawCertifiedTyping source (term.substitute substitution.term)
      (type.substitute substitution.term) where
  contextWellFormed := sourceWellFormed
  typeWellFormed := certified.typeWellFormed.substitute substitution
  typing := certified.typing.substitute substitution

def incDepRawIdentity (type : IncDepRawType) : IncDepRawTerm :=
  .lambda type (.var 0)

def incDepRawIdentity_hasType
    (type : IncDepRawType) (typeWellFormed : IncDepRawWellFormed [] type) :
    IncDepRawHasType [] (incDepRawIdentity type)
      (.pi type (type.rename Nat.succ)) := by
  exact IncDepRawHasType.lambdaRule typeWellFormed
    (IncDepRawHasType.varRule IncDepRawLookup.here)

def incDepRawRefl_hasType
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm} (typing : IncDepRawHasType context term type) :
    IncDepRawHasType context (.refl term) (.identity type term term) :=
  IncDepRawHasType.reflRule typing

def incDepRawDependentRefl : IncDepRawTerm :=
  .lambda .unit (.refl (.var 0))

def incDepRawDependentRefl_hasType :
    IncDepRawHasType [] incDepRawDependentRefl
      (.pi .unit (.identity .unit (.var 0) (.var 0))) := by
  exact IncDepRawHasType.lambdaRule IncDepRawWellFormed.unit
    (IncDepRawHasType.reflRule
      (IncDepRawHasType.varRule IncDepRawLookup.here))

def incDepRawDependentRefl_typeWellFormed :
    IncDepRawWellFormed []
      (.pi .unit (.identity .unit (.var 0) (.var 0))) := by
  exact IncDepRawWellFormed.pi IncDepRawWellFormed.unit
    (IncDepRawWellFormed.identity IncDepRawWellFormed.unit
      (IncDepRawHasType.varRule IncDepRawLookup.here)
      (IncDepRawHasType.varRule IncDepRawLookup.here))

def incDepRawDependentRefl_certified :
    IncDepRawCertifiedTyping [] incDepRawDependentRefl
      (.pi .unit (.identity .unit (.var 0) (.var 0))) :=
  IncDepRawCertifiedTyping.ofClosed
    incDepRawDependentRefl_typeWellFormed incDepRawDependentRefl_hasType

def incDepRawDependentRefl_deeplyWellFormed :
    IncDepRawTypingDeeplyWellFormed incDepRawDependentRefl_hasType := by
  exact IncDepRawTypingDeeplyWellFormed.lambdaRule
    (IncDepRawWellFormed.identity IncDepRawWellFormed.unit
      (IncDepRawHasType.varRule IncDepRawLookup.here)
      (IncDepRawHasType.varRule IncDepRawLookup.here))
    (IncDepRawTypingDeeplyWellFormed.reflRule IncDepRawWellFormed.unit
      (IncDepRawTypingDeeplyWellFormed.varRule IncDepRawWellFormed.unit))

def incDepRawDependentRefl_deepCertified :
    IncDepRawDeepCertifiedTyping [] incDepRawDependentRefl
      (.pi .unit (.identity .unit (.var 0) (.var 0))) where
  toIncDepRawCertifiedTyping := incDepRawDependentRefl_certified
  deeplyWellFormed := incDepRawDependentRefl_deeplyWellFormed

def incDepRawUnitVariableTyping :
    IncDepRawHasType [IncDepRawType.unit] (.var 0) .unit :=
  IncDepRawHasType.varRule IncDepRawLookup.here

def incDepRawUnitVariableSemanticReady :
    IncDepRawTypingSemanticReady incDepRawUnitVariableTyping :=
  IncDepRawTypingSemanticReady.varRule IncDepRawFormationSemanticReady.unit

def incDepRawUnitIdentityFormation :
    IncDepRawWellFormed [IncDepRawType.unit]
      (.identity .unit (.var 0) (.var 0)) :=
  IncDepRawWellFormed.identity IncDepRawWellFormed.unit
    incDepRawUnitVariableTyping incDepRawUnitVariableTyping

def incDepRawUnitIdentitySemanticReady :
    IncDepRawFormationSemanticReady incDepRawUnitIdentityFormation :=
  IncDepRawFormationSemanticReady.identity
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitVariableSemanticReady incDepRawUnitVariableSemanticReady

def incDepRawDependentRefl_semanticReady :
    IncDepRawTypingSemanticReady incDepRawDependentRefl_hasType := by
  exact IncDepRawTypingSemanticReady.lambdaRule
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitIdentitySemanticReady
    (IncDepRawTypingSemanticReady.reflRule
      IncDepRawFormationSemanticReady.unit
      incDepRawUnitVariableSemanticReady)

def incDepRawDependentRefl_typeSemanticReady :
    IncDepRawFormationSemanticReady
      incDepRawDependentRefl_typeWellFormed := by
  exact IncDepRawFormationSemanticReady.pi
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitIdentitySemanticReady

theorem incDepRawDependentRefl_application_type :
    (IncDepRawType.identity .unit (.var 0) (.var 0)).instantiate .unit =
      .identity .unit .unit .unit := by
  rfl

def incDepRawDependentPair : IncDepRawTerm :=
  .pair .unit (.refl .unit)

def incDepRawDependentPair_hasType :
    IncDepRawHasType [] incDepRawDependentPair
      (.sigma .unit (.identity .unit (.var 0) (.var 0))) := by
  exact IncDepRawHasType.pairRule IncDepRawHasType.unitRule
    (IncDepRawHasType.reflRule IncDepRawHasType.unitRule)

def incDepRawDependentPair_typeWellFormed :
    IncDepRawWellFormed []
      (.sigma .unit (.identity .unit (.var 0) (.var 0))) := by
  exact IncDepRawWellFormed.sigma IncDepRawWellFormed.unit
    (IncDepRawWellFormed.identity IncDepRawWellFormed.unit
      (IncDepRawHasType.varRule IncDepRawLookup.here)
      (IncDepRawHasType.varRule IncDepRawLookup.here))

def incDepRawDependentPair_certified :
    IncDepRawCertifiedTyping [] incDepRawDependentPair
      (.sigma .unit (.identity .unit (.var 0) (.var 0))) :=
  IncDepRawCertifiedTyping.ofClosed
    incDepRawDependentPair_typeWellFormed incDepRawDependentPair_hasType

def incDepRawDependentPair_deeplyWellFormed :
    IncDepRawTypingDeeplyWellFormed incDepRawDependentPair_hasType := by
  exact IncDepRawTypingDeeplyWellFormed.pairRule
    IncDepRawWellFormed.unit
    (IncDepRawWellFormed.identity IncDepRawWellFormed.unit
      (IncDepRawHasType.varRule IncDepRawLookup.here)
      (IncDepRawHasType.varRule IncDepRawLookup.here))
    IncDepRawTypingDeeplyWellFormed.unitRule
    (IncDepRawTypingDeeplyWellFormed.reflRule IncDepRawWellFormed.unit
      IncDepRawTypingDeeplyWellFormed.unitRule)

def incDepRawDependentPair_deepCertified :
    IncDepRawDeepCertifiedTyping [] incDepRawDependentPair
      (.sigma .unit (.identity .unit (.var 0) (.var 0))) where
  toIncDepRawCertifiedTyping := incDepRawDependentPair_certified
  deeplyWellFormed := incDepRawDependentPair_deeplyWellFormed

def incDepRawDependentPair_semanticReady :
    IncDepRawTypingSemanticReady incDepRawDependentPair_hasType := by
  exact IncDepRawTypingSemanticReady.pairRule
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitIdentitySemanticReady
    IncDepRawTypingSemanticReady.unitRule
    (IncDepRawTypingSemanticReady.reflRule
      IncDepRawFormationSemanticReady.unit
      IncDepRawTypingSemanticReady.unitRule)

def incDepRawDependentPair_typeSemanticReady :
    IncDepRawFormationSemanticReady
      incDepRawDependentPair_typeWellFormed := by
  exact IncDepRawFormationSemanticReady.sigma
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitIdentitySemanticReady

def incDepRawDependentPair_first_hasType :
    IncDepRawHasType [] (.first incDepRawDependentPair) .unit :=
  IncDepRawHasType.firstRule incDepRawDependentPair_hasType

def incDepRawDependentPair_second_hasType :
    IncDepRawHasType [] (.second incDepRawDependentPair)
      (.identity .unit (.first incDepRawDependentPair)
        (.first incDepRawDependentPair)) :=
  IncDepRawHasType.secondRule incDepRawDependentPair_hasType

def incDepRawDependentPair_first_semanticReady :
    IncDepRawTypingSemanticReady
      incDepRawDependentPair_first_hasType := by
  exact IncDepRawTypingSemanticReady.firstRule
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitIdentitySemanticReady
    incDepRawDependentPair_semanticReady

def incDepRawDependentPair_second_semanticReady :
    IncDepRawTypingSemanticReady
      incDepRawDependentPair_second_hasType := by
  exact IncDepRawTypingSemanticReady.secondRule
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitIdentitySemanticReady
    incDepRawDependentPair_semanticReady

def IncDepRawTerm.instantiate (body argument : IncDepRawTerm) : IncDepRawTerm :=
  body.substitute fun index => match index with
    | 0 => argument
    | next + 1 => .var next

theorem IncDepRawTerm.instantiate_substitute
    (body argument : IncDepRawTerm)
    (replacement : Nat → IncDepRawTerm) :
    (body.instantiate argument).substitute replacement =
      (body.substitute (IncDepRawTerm.liftReplacement replacement)).instantiate
        (argument.substitute replacement) := by
  simp only [IncDepRawTerm.instantiate]
  rw [IncDepRawTerm.substitute_comp, IncDepRawTerm.substitute_comp]
  congr 1
  funext index
  cases index with
  | zero => rfl
  | succ next =>
      simp only [IncDepRawTerm.liftReplacement, IncDepRawTerm.substitute]
      rw [IncDepRawTerm.rename_substitute]
      have mapIdentity :
          ((fun index => match index with
            | 0 => argument.substitute replacement
            | next + 1 => .var next) ∘ Nat.succ) = IncDepRawTerm.var := by
        funext index
        rfl
      rw [mapIdentity, IncDepRawTerm.substitute_identity]

theorem IncDepRawTerm.instantiate_rename
    (body argument : IncDepRawTerm) (renameMap : Nat → Nat) :
    (body.instantiate argument).rename renameMap =
      (body.rename (IncDepRawTerm.liftRename renameMap)).instantiate
        (argument.rename renameMap) := by
  simp only [IncDepRawTerm.instantiate]
  rw [IncDepRawTerm.substitute_rename,
    IncDepRawTerm.rename_substitute]
  congr 1
  funext index
  cases index <;> rfl

inductive IncDepRawStep : IncDepRawTerm → IncDepRawTerm → Prop
  | piBeta {domain body argument} :
      IncDepRawStep (.apply (.lambda domain body) argument)
        (body.instantiate argument)
  | sigmaFirstBeta {first second} :
      IncDepRawStep (.first (.pair first second)) first
  | sigmaSecondBeta {first second} :
      IncDepRawStep (.second (.pair first second)) second
  | applyFunction {function function' argument} :
      IncDepRawStep function function' →
      IncDepRawStep (.apply function argument) (.apply function' argument)
  | applyArgument {function argument argument'} :
      IncDepRawStep argument argument' →
      IncDepRawStep (.apply function argument) (.apply function argument')
  | pairFirst {first first' second} :
      IncDepRawStep first first' →
      IncDepRawStep (.pair first second) (.pair first' second)
  | pairSecond {first second second'} :
      IncDepRawStep second second' →
      IncDepRawStep (.pair first second) (.pair first second')
  | underFirst {pair pair'} :
      IncDepRawStep pair pair' →
      IncDepRawStep (.first pair) (.first pair')
  | underSecond {pair pair'} :
      IncDepRawStep pair pair' →
      IncDepRawStep (.second pair) (.second pair')

theorem IncDepRawStep.substitute
    {first second : IncDepRawTerm} (step : IncDepRawStep first second)
    (replacement : Nat → IncDepRawTerm) :
    IncDepRawStep (first.substitute replacement)
      (second.substitute replacement) := by
  induction step with
  | piBeta =>
      rw [IncDepRawTerm.instantiate_substitute]
      exact IncDepRawStep.piBeta
  | sigmaFirstBeta => exact IncDepRawStep.sigmaFirstBeta
  | sigmaSecondBeta => exact IncDepRawStep.sigmaSecondBeta
  | applyFunction _ ih => exact IncDepRawStep.applyFunction ih
  | applyArgument _ ih => exact IncDepRawStep.applyArgument ih
  | pairFirst _ ih => exact IncDepRawStep.pairFirst ih
  | pairSecond _ ih => exact IncDepRawStep.pairSecond ih
  | underFirst _ ih => exact IncDepRawStep.underFirst ih
  | underSecond _ ih => exact IncDepRawStep.underSecond ih

theorem IncDepRawStep.rename
    {first second : IncDepRawTerm} (step : IncDepRawStep first second)
    (renameMap : Nat → Nat) :
    IncDepRawStep (first.rename renameMap) (second.rename renameMap) := by
  induction step with
  | piBeta =>
      rw [IncDepRawTerm.instantiate_rename]
      exact IncDepRawStep.piBeta
  | sigmaFirstBeta => exact IncDepRawStep.sigmaFirstBeta
  | sigmaSecondBeta => exact IncDepRawStep.sigmaSecondBeta
  | applyFunction _ ih => exact IncDepRawStep.applyFunction ih
  | applyArgument _ ih => exact IncDepRawStep.applyArgument ih
  | pairFirst _ ih => exact IncDepRawStep.pairFirst ih
  | pairSecond _ ih => exact IncDepRawStep.pairSecond ih
  | underFirst _ ih => exact IncDepRawStep.underFirst ih
  | underSecond _ ih => exact IncDepRawStep.underSecond ih

inductive IncDepRawSteps : IncDepRawTerm → IncDepRawTerm → Prop
  | refl (term) : IncDepRawSteps term term
  | tail {first second third} :
      IncDepRawStep first second → IncDepRawSteps second third →
      IncDepRawSteps first third

theorem IncDepRawSteps.trans
    {first second third : IncDepRawTerm} :
    IncDepRawSteps first second → IncDepRawSteps second third →
      IncDepRawSteps first third := by
  intro firstSteps secondSteps
  induction firstSteps with
  | refl => exact secondSteps
  | tail step _ ih => exact IncDepRawSteps.tail step (ih secondSteps)

theorem IncDepRawSteps.rename
    {first second : IncDepRawTerm} (steps : IncDepRawSteps first second)
    (renameMap : Nat → Nat) :
    IncDepRawSteps (first.rename renameMap) (second.rename renameMap) := by
  induction steps with
  | refl => exact IncDepRawSteps.refl _
  | tail step _ ih =>
      exact IncDepRawSteps.tail (step.rename renameMap) ih

theorem IncDepRawSteps.substitute
    {first second : IncDepRawTerm} (steps : IncDepRawSteps first second)
    (replacement : Nat → IncDepRawTerm) :
    IncDepRawSteps (first.substitute replacement)
      (second.substitute replacement) := by
  induction steps with
  | refl => exact IncDepRawSteps.refl _
  | tail step _ ih =>
      exact IncDepRawSteps.tail (step.substitute replacement) ih

inductive IncDepRawDefEq : IncDepRawTerm → IncDepRawTerm → Prop
  | refl (term) : IncDepRawDefEq term term
  | ofStep {first second} :
      IncDepRawStep first second → IncDepRawDefEq first second
  | symm {first second} :
      IncDepRawDefEq first second → IncDepRawDefEq second first
  | trans {first second third} :
      IncDepRawDefEq first second → IncDepRawDefEq second third →
      IncDepRawDefEq first third

inductive IncDepRawTypeDefEq : IncDepRawType → IncDepRawType → Prop
  | refl (type) : IncDepRawTypeDefEq type type
  | symm {first second} :
      IncDepRawTypeDefEq first second → IncDepRawTypeDefEq second first
  | trans {first second third} :
      IncDepRawTypeDefEq first second →
      IncDepRawTypeDefEq second third →
      IncDepRawTypeDefEq first third
  | pi {firstDomain secondDomain firstCodomain secondCodomain} :
      IncDepRawTypeDefEq firstDomain secondDomain →
      IncDepRawTypeDefEq firstCodomain secondCodomain →
      IncDepRawTypeDefEq (.pi firstDomain firstCodomain)
        (.pi secondDomain secondCodomain)
  | sigma {firstDomain secondDomain firstCodomain secondCodomain} :
      IncDepRawTypeDefEq firstDomain secondDomain →
      IncDepRawTypeDefEq firstCodomain secondCodomain →
      IncDepRawTypeDefEq (.sigma firstDomain firstCodomain)
        (.sigma secondDomain secondCodomain)
  | identity {firstType secondType firstLeft secondLeft firstRight secondRight} :
      IncDepRawTypeDefEq firstType secondType →
      IncDepRawDefEq firstLeft secondLeft →
      IncDepRawDefEq firstRight secondRight →
      IncDepRawTypeDefEq (.identity firstType firstLeft firstRight)
        (.identity secondType secondLeft secondRight)

inductive IncDepRawHasTypeConversion
    (context : List IncDepRawType) : IncDepRawTerm → IncDepRawType → Prop
  | typed {term type} :
      IncDepRawHasType context term type →
      IncDepRawHasTypeConversion context term type
  | termConversion {first second type} :
      IncDepRawHasTypeConversion context first type →
      IncDepRawDefEq first second →
      IncDepRawHasTypeConversion context second type
  | typeConversion {term firstType secondType} :
      IncDepRawHasTypeConversion context term firstType →
      IncDepRawTypeDefEq firstType secondType →
      IncDepRawHasTypeConversion context term secondType

theorem IncDepRawStep.subject_reduction
    {context : List IncDepRawType} {first second : IncDepRawTerm}
    {type : IncDepRawType} (typing : IncDepRawHasType context first type)
    (step : IncDepRawStep first second) :
    IncDepRawHasTypeConversion context second type :=
  IncDepRawHasTypeConversion.termConversion
    (IncDepRawHasTypeConversion.typed typing)
    (IncDepRawDefEq.ofStep step)

theorem IncDepRawSteps.toDefEq
    {first second : IncDepRawTerm} :
    IncDepRawSteps first second → IncDepRawDefEq first second := by
  intro steps
  induction steps with
  | refl => exact IncDepRawDefEq.refl _
  | tail step _ ih =>
      exact IncDepRawDefEq.trans (IncDepRawDefEq.ofStep step) ih

theorem IncDepRawSteps.subject_reduction
    {context : List IncDepRawType} {first second : IncDepRawTerm}
    {type : IncDepRawType} (typing : IncDepRawHasType context first type)
    (steps : IncDepRawSteps first second) :
    IncDepRawHasTypeConversion context second type :=
  IncDepRawHasTypeConversion.termConversion
    (IncDepRawHasTypeConversion.typed typing) steps.toDefEq

def incDepRawDefEqSetoid : Setoid IncDepRawTerm where
  r := IncDepRawDefEq
  iseqv := ⟨IncDepRawDefEq.refl, IncDepRawDefEq.symm,
    IncDepRawDefEq.trans⟩

abbrev IncDepRawComputation := Quotient incDepRawDefEqSetoid

def IncDepRawTerm.compute (term : IncDepRawTerm) : IncDepRawComputation :=
  Quotient.mk incDepRawDefEqSetoid term

theorem IncDepRawDefEq.compute_eq
    {first second : IncDepRawTerm} (equal : IncDepRawDefEq first second) :
    first.compute = second.compute :=
  Quotient.sound equal

theorem IncDepRawStep.compute_sound
    {first second : IncDepRawTerm} (step : IncDepRawStep first second) :
    first.compute = second.compute :=
  (IncDepRawDefEq.ofStep step).compute_eq

theorem IncDepRawSteps.compute_sound
    {first second : IncDepRawTerm} (steps : IncDepRawSteps first second) :
    first.compute = second.compute :=
  steps.toDefEq.compute_eq

theorem IncDepRawSteps.evaluator_sound
    {carrier : Type u} (evaluate : IncDepRawTerm → carrier)
    (stepSound : ∀ {first second}, IncDepRawStep first second →
      evaluate first = evaluate second)
    {first second : IncDepRawTerm} (steps : IncDepRawSteps first second) :
    evaluate first = evaluate second := by
  induction steps with
  | refl => rfl
  | tail step _ ih => exact Eq.trans (stepSound step) ih

theorem IncDepRawDefEq.evaluator_sound
    {carrier : Type u} (evaluate : IncDepRawTerm → carrier)
    (stepSound : ∀ {first second}, IncDepRawStep first second →
      evaluate first = evaluate second)
    {first second : IncDepRawTerm} (equal : IncDepRawDefEq first second) :
    evaluate first = evaluate second := by
  induction equal with
  | refl => rfl
  | ofStep step => exact stepSound step
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact Eq.trans firstIH secondIH

theorem incDepRawCompute_evaluator_sound
    {first second : IncDepRawTerm} (steps : IncDepRawSteps first second) :
    first.compute = second.compute :=
  steps.evaluator_sound IncDepRawTerm.compute
    (fun step => step.compute_sound)

structure IncDepRawSoundEvaluator where
  Carrier : Type u
  evaluate : IncDepRawTerm → Carrier
  stepSound : ∀ {first second}, IncDepRawStep first second →
    evaluate first = evaluate second

theorem IncDepRawSoundEvaluator.stepsSound
    (model : IncDepRawSoundEvaluator.{u})
    {first second : IncDepRawTerm} (steps : IncDepRawSteps first second) :
    model.evaluate first = model.evaluate second :=
  steps.evaluator_sound model.evaluate model.stepSound

theorem IncDepRawSoundEvaluator.defEqSound
    (model : IncDepRawSoundEvaluator.{u})
    {first second : IncDepRawTerm} (equal : IncDepRawDefEq first second) :
    model.evaluate first = model.evaluate second :=
  equal.evaluator_sound model.evaluate model.stepSound

def incDepRawComputationSoundEvaluator : IncDepRawSoundEvaluator where
  Carrier := IncDepRawComputation
  evaluate := IncDepRawTerm.compute
  stepSound := IncDepRawStep.compute_sound

theorem incDepRawComputationSoundEvaluator_agrees (term : IncDepRawTerm) :
    incDepRawComputationSoundEvaluator.evaluate term = term.compute := by
  rfl

theorem incDepRawDependentRefl_betaStep :
    IncDepRawStep (.apply incDepRawDependentRefl .unit) (.refl .unit) := by
  exact IncDepRawStep.piBeta

theorem incDepRawDependentPair_first_betaStep :
    IncDepRawStep (.first incDepRawDependentPair) .unit := by
  exact IncDepRawStep.sigmaFirstBeta

theorem incDepRawDependentPair_second_betaStep :
    IncDepRawStep (.second incDepRawDependentPair) (.refl .unit) := by
  exact IncDepRawStep.sigmaSecondBeta

theorem incDepRawDependentRefl_compute_sound :
    (IncDepRawTerm.apply incDepRawDependentRefl .unit).compute =
      (IncDepRawTerm.refl .unit).compute :=
  incDepRawDependentRefl_betaStep.compute_sound

theorem incDepRawDependentPair_compute_sound :
    (IncDepRawTerm.first incDepRawDependentPair).compute =
      IncDepRawTerm.unit.compute ∧
    (IncDepRawTerm.second incDepRawDependentPair).compute =
      (IncDepRawTerm.refl .unit).compute :=
  ⟨incDepRawDependentPair_first_betaStep.compute_sound,
    incDepRawDependentPair_second_betaStep.compute_sound⟩

def incDepRawDependentRefl_application_hasType :
    IncDepRawHasType [] (.apply incDepRawDependentRefl .unit)
      (.identity .unit .unit .unit) :=
  IncDepRawHasType.applyRule incDepRawDependentRefl_hasType
    IncDepRawHasType.unitRule

def incDepRawDependentRefl_application_semanticReady :
    IncDepRawTypingSemanticReady
      incDepRawDependentRefl_application_hasType := by
  exact IncDepRawTypingSemanticReady.applyRule
    IncDepRawFormationSemanticReady.unit
    incDepRawUnitIdentitySemanticReady
    incDepRawDependentRefl_semanticReady
    IncDepRawTypingSemanticReady.unitRule

theorem incDepRawDependentRefl_subjectReduction :
    IncDepRawHasTypeConversion [] (.refl .unit)
      (.identity .unit .unit .unit) :=
  incDepRawDependentRefl_betaStep.subject_reduction
    incDepRawDependentRefl_application_hasType

theorem incDepRawDependentPair_first_subjectReduction :
    IncDepRawHasTypeConversion [] .unit .unit :=
  incDepRawDependentPair_first_betaStep.subject_reduction
    incDepRawDependentPair_first_hasType

theorem incDepRawDependentPair_second_subjectReduction :
    IncDepRawHasTypeConversion [] (.refl .unit)
      (.identity .unit (.first incDepRawDependentPair)
        (.first incDepRawDependentPair)) :=
  incDepRawDependentPair_second_betaStep.subject_reduction
    incDepRawDependentPair_second_hasType

structure IncContext where
  Assignment : Type u

def IncContext.empty : IncContext.{u} :=
  ⟨ULift.{u} Unit⟩

def IncContext.extend (context : IncContext.{u})
    (family : context.Assignment → Type u) : IncContext :=
  ⟨Sigma family⟩

abbrev IncContext.Substitution (source target : IncContext.{u}) : Type u :=
  source.Assignment → target.Assignment

def IncContext.Substitution.identity (context : IncContext.{u}) :
    context.Substitution context :=
  id

def IncContext.Substitution.comp
    {first second third : IncContext.{u}}
    (after : second.Substitution third)
    (before : first.Substitution second) :
    first.Substitution third :=
  after ∘ before

theorem IncContext.Substitution.identity_comp
    {source target : IncContext.{u}}
    (substitution : source.Substitution target) :
    (IncContext.Substitution.identity target).comp substitution = substitution := by
  rfl

theorem IncContext.Substitution.comp_identity
    {source target : IncContext.{u}}
    (substitution : source.Substitution target) :
    substitution.comp (IncContext.Substitution.identity source) = substitution := by
  rfl

theorem IncContext.Substitution.comp_assoc
    {first second third fourth : IncContext.{u}}
    (thirdMap : third.Substitution fourth)
    (secondMap : second.Substitution third)
    (firstMap : first.Substitution second) :
    (thirdMap.comp secondMap).comp firstMap =
      thirdMap.comp (secondMap.comp firstMap) := by
  rfl

abbrev IncTypeInContext (context : IncContext.{u}) : Type (u + 1) :=
  context.Assignment → Type u

abbrev IncTerm {context : IncContext.{u}}
    (type : IncTypeInContext context) : Type u :=
  ∀ assignment, type assignment

def IncTypeInContext.reindex
    {source target : IncContext.{u}}
    (type : IncTypeInContext target)
    (substitution : source.Substitution target) :
    IncTypeInContext source :=
  fun assignment => type (substitution assignment)

def IncTerm.substitute
    {source target : IncContext.{u}}
    {type : IncTypeInContext target}
    (term : IncTerm type)
    (substitution : source.Substitution target) :
    IncTerm (type.reindex substitution) :=
  fun assignment => term (substitution assignment)

theorem IncTypeInContext.reindex_identity
    {context : IncContext.{u}} (type : IncTypeInContext context) :
    type.reindex (IncContext.Substitution.identity context) = type := by
  rfl

theorem IncTypeInContext.reindex_comp
    {first second third : IncContext.{u}}
    (type : IncTypeInContext third)
    (after : second.Substitution third)
    (before : first.Substitution second) :
    type.reindex (after.comp before) =
      (type.reindex after).reindex before := by
  rfl

structure IncFiberEquiv (source target : Type u) where
  forward : source → target
  backward : target → source
  backward_forward : ∀ value, backward (forward value) = value
  forward_backward : ∀ value, forward (backward value) = value

def IncFiberEquiv.ofEq {source target : Type u}
    (coherence : source = target) : IncFiberEquiv source target := by
  cases coherence
  exact
    { forward := id
      backward := id
      backward_forward := fun _ => rfl
      forward_backward := fun _ => rfl }

theorem IncFiberEquiv.ofEq_forward {source target : Type u}
    (coherence : source = target) (value : source) :
    (IncFiberEquiv.ofEq coherence).forward value = Eq.mp coherence value := by
  cases coherence
  rfl

def IncFiberEquiv.trans {first second third : Type u}
    (firstEquivalence : IncFiberEquiv first second)
    (secondEquivalence : IncFiberEquiv second third) :
    IncFiberEquiv first third where
  forward := secondEquivalence.forward ∘ firstEquivalence.forward
  backward := firstEquivalence.backward ∘ secondEquivalence.backward
  backward_forward := fun value => by
    simp only [Function.comp_apply, secondEquivalence.backward_forward,
      firstEquivalence.backward_forward]
  forward_backward := fun value => by
    simp only [Function.comp_apply, firstEquivalence.forward_backward,
      secondEquivalence.forward_backward]

def IncFiberEquiv.mapEquality
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {left right : source} (equality : left = right) :
    equivalence.forward left = equivalence.forward right :=
  congrArg equivalence.forward equality

theorem IncFiberEquiv.mapEquality_refl
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    (value : source) :
    equivalence.mapEquality (Eq.refl value) = Eq.refl (equivalence.forward value) := by
  rfl

theorem IncFiberEquiv.mapEquality_trans
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {first second third : source}
    (firstEquality : first = second) (secondEquality : second = third) :
    equivalence.mapEquality (firstEquality.trans secondEquality) =
      (equivalence.mapEquality firstEquality).trans
        (equivalence.mapEquality secondEquality) := by
  cases firstEquality
  cases secondEquality
  rfl

theorem IncFiberEquiv.mapEquality_symm
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {left right : source} (equality : left = right) :
    equivalence.mapEquality equality.symm =
      (equivalence.mapEquality equality).symm := by
  cases equality
  rfl

def IncFiberEquiv.mapEqualityBackward
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {left right : target} (equality : left = right) :
    equivalence.backward left = equivalence.backward right :=
  congrArg equivalence.backward equality

theorem IncFiberEquiv.mapEqualityBackward_refl
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    (value : target) :
    equivalence.mapEqualityBackward (Eq.refl value) =
      Eq.refl (equivalence.backward value) := by
  rfl

theorem IncFiberEquiv.mapEqualityBackward_trans
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {first second third : target}
    (firstEquality : first = second) (secondEquality : second = third) :
    equivalence.mapEqualityBackward (firstEquality.trans secondEquality) =
      (equivalence.mapEqualityBackward firstEquality).trans
        (equivalence.mapEqualityBackward secondEquality) := by
  cases firstEquality
  cases secondEquality
  rfl

theorem IncFiberEquiv.mapEqualityBackward_symm
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {left right : target} (equality : left = right) :
    equivalence.mapEqualityBackward equality.symm =
      (equivalence.mapEqualityBackward equality).symm := by
  cases equality
  rfl

structure IncTypeInContext.FiberEquiv
    {context : IncContext.{u}}
    (source target : IncTypeInContext context) where
  fiberEquiv : ∀ assignment,
    IncFiberEquiv (source assignment) (target assignment)

def IncTypeInContext.FiberEquiv.refl
    {context : IncContext.{u}} (family : IncTypeInContext context) :
    IncTypeInContext.FiberEquiv family family where
  fiberEquiv := fun _ =>
    { forward := id, backward := id
      backward_forward := fun _ => rfl
      forward_backward := fun _ => rfl }

def IncTypeInContext.FiberEquiv.ofEq
    {context : IncContext.{u}} {source target : IncTypeInContext context}
    (coherence : source = target) : IncTypeInContext.FiberEquiv source target := by
  cases coherence
  exact IncTypeInContext.FiberEquiv.refl source

def IncTypeInContext.FiberEquiv.symm
    {context : IncContext.{u}} {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target) :
    IncTypeInContext.FiberEquiv target source where
  fiberEquiv := fun assignment =>
    { forward := (equivalence.fiberEquiv assignment).backward
      backward := (equivalence.fiberEquiv assignment).forward
      backward_forward := (equivalence.fiberEquiv assignment).forward_backward
      forward_backward := (equivalence.fiberEquiv assignment).backward_forward }

def IncTypeInContext.FiberEquiv.trans
    {context : IncContext.{u}} {first second third : IncTypeInContext context}
    (firstEquivalence : IncTypeInContext.FiberEquiv first second)
    (secondEquivalence : IncTypeInContext.FiberEquiv second third) :
    IncTypeInContext.FiberEquiv first third where
  fiberEquiv := fun assignment =>
    { forward := (secondEquivalence.fiberEquiv assignment).forward ∘
        (firstEquivalence.fiberEquiv assignment).forward
      backward := (firstEquivalence.fiberEquiv assignment).backward ∘
        (secondEquivalence.fiberEquiv assignment).backward
      backward_forward := by
        intro value
        simp only [Function.comp_apply,
          (secondEquivalence.fiberEquiv assignment).backward_forward,
          (firstEquivalence.fiberEquiv assignment).backward_forward]
      forward_backward := by
        intro value
        simp only [Function.comp_apply,
          (firstEquivalence.fiberEquiv assignment).forward_backward,
          (secondEquivalence.fiberEquiv assignment).forward_backward] }

def IncTypeInContext.FiberEquiv.reindex
    {sourceContext targetContext : IncContext.{u}}
    {source target : IncTypeInContext targetContext}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (substitution : sourceContext.Substitution targetContext) :
    IncTypeInContext.FiberEquiv (source.reindex substitution)
      (target.reindex substitution) where
  fiberEquiv := fun assignment =>
    equivalence.fiberEquiv (substitution assignment)

def IncTypeInContext.FiberEquiv.transport
    {context : IncContext.{u}} {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (term : IncTerm source) : IncTerm target :=
  fun assignment => (equivalence.fiberEquiv assignment).forward (term assignment)

theorem IncTypeInContext.FiberEquiv.ofEq_forward
    {context : IncContext.{u}} {source target : IncTypeInContext context}
    (coherence : source = target)
    (assignment : context.Assignment) (value : source assignment) :
    ((IncTypeInContext.FiberEquiv.ofEq coherence).fiberEquiv assignment).forward
        value =
      Eq.mp (congrFun coherence assignment) value := by
  cases coherence
  rfl

theorem IncTypeInContext.FiberEquiv.ofEq_transport_apply
    {context : IncContext.{u}} {source target : IncTypeInContext context}
    (coherence : source = target) (term : IncTerm source)
    (assignment : context.Assignment) :
    (IncTypeInContext.FiberEquiv.ofEq coherence).transport term assignment =
      Eq.mp (congrFun coherence assignment) (term assignment) := by
  exact IncTypeInContext.FiberEquiv.ofEq_forward coherence assignment
    (term assignment)

theorem IncTypeInContext.FiberEquiv.reindex_transport
    {sourceContext targetContext : IncContext.{u}}
    {source target : IncTypeInContext targetContext}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (substitution : sourceContext.Substitution targetContext)
    (term : IncTerm source) :
    (equivalence.reindex substitution).transport
        (term.substitute substitution) =
      (equivalence.transport term).substitute substitution := by
  rfl

theorem IncTypeInContext.FiberEquiv.transport_symm
    {context : IncContext.{u}} {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (term : IncTerm source) :
    equivalence.symm.transport (equivalence.transport term) = term := by
  funext assignment
  exact (equivalence.fiberEquiv assignment).backward_forward (term assignment)

theorem IncTypeInContext.FiberEquiv.symm_transport
    {context : IncContext.{u}} {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (term : IncTerm target) :
    equivalence.transport (equivalence.symm.transport term) = term := by
  funext assignment
  exact (equivalence.fiberEquiv assignment).forward_backward (term assignment)

structure IncDependentFiberEquiv
    {sourceDomain targetDomain : Type u}
    (domainEquiv : IncFiberEquiv sourceDomain targetDomain)
    (sourceCodomain : sourceDomain → Type u)
    (targetCodomain : targetDomain → Type u) where
  codomainEquiv : ∀ sourceValue,
    IncFiberEquiv (sourceCodomain sourceValue)
      (targetCodomain (domainEquiv.forward sourceValue))

def IncDependentFiberEquiv.piForward
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (sourceFunction : ∀ value, sourceCodomain value) :
    ∀ value, targetCodomain value :=
  fun targetValue =>
    Eq.mp (congrArg targetCodomain
      (domainEquiv.forward_backward targetValue))
      ((dependentEquiv.codomainEquiv
        (domainEquiv.backward targetValue)).forward
          (sourceFunction (domainEquiv.backward targetValue)))

def IncDependentFiberEquiv.piBackward
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (targetFunction : ∀ value, targetCodomain value) :
    ∀ value, sourceCodomain value :=
  fun sourceValue =>
    (dependentEquiv.codomainEquiv sourceValue).backward
      (targetFunction (domainEquiv.forward sourceValue))

theorem IncDependentFiberEquiv.piForward_apply
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (sourceFunction : ∀ value, sourceCodomain value)
    (targetValue : targetDomain) :
    dependentEquiv.piForward sourceFunction targetValue =
      Eq.mp (congrArg targetCodomain
        (domainEquiv.forward_backward targetValue))
        ((dependentEquiv.codomainEquiv
          (domainEquiv.backward targetValue)).forward
            (sourceFunction (domainEquiv.backward targetValue))) := by
  rfl

theorem IncDependentFiberEquiv.piBackward_apply
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (targetFunction : ∀ value, targetCodomain value)
    (sourceValue : sourceDomain) :
    dependentEquiv.piBackward targetFunction sourceValue =
      (dependentEquiv.codomainEquiv sourceValue).backward
      (targetFunction (domainEquiv.forward sourceValue)) := by
  rfl

theorem IncDependentFiberEquiv.piForward_eq_of_pointwise
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (sourceFunction : ∀ value, sourceCodomain value)
    (targetFunction : ∀ value, targetCodomain value)
    (pointwise : ∀ sourceValue,
      (dependentEquiv.codomainEquiv sourceValue).forward
          (sourceFunction sourceValue) =
        targetFunction (domainEquiv.forward sourceValue)) :
    dependentEquiv.piForward sourceFunction = targetFunction := by
  funext targetValue
  rw [dependentEquiv.piForward_apply, pointwise]
  have transport_section {first second : targetDomain}
      (coherence : first = second) :
      Eq.mp (congrArg targetCodomain coherence) (targetFunction first) =
        targetFunction second := by
    cases coherence
    rfl
  exact transport_section (domainEquiv.forward_backward targetValue)

theorem IncDependentFiberEquiv.piForward_apply_transport
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (sourceFunction : ∀ value, sourceCodomain value)
    (targetFunction : ∀ value, targetCodomain value)
    (sourceArgument : sourceDomain) (targetArgument : targetDomain)
    (forwardApply :
      (dependentEquiv.codomainEquiv sourceArgument).forward
          (sourceFunction sourceArgument) =
        dependentEquiv.piForward sourceFunction
          (domainEquiv.forward sourceArgument))
    (functionCoherence : dependentEquiv.piForward sourceFunction = targetFunction)
    (argumentCoherence : domainEquiv.forward sourceArgument = targetArgument) :
    Eq.mp (congrArg targetCodomain argumentCoherence)
        ((dependentEquiv.codomainEquiv sourceArgument).forward
          (sourceFunction sourceArgument)) =
      targetFunction targetArgument := by
  rw [forwardApply, congrFun functionCoherence]
  have transport_section {first second : targetDomain}
      (coherence : first = second) :
      Eq.mp (congrArg targetCodomain coherence) (targetFunction first) =
        targetFunction second := by
    cases coherence
    rfl
  exact transport_section argumentCoherence

structure IncDependentPiFiberEquiv
    {sourceDomain targetDomain : Type u}
    (domainEquiv : IncFiberEquiv sourceDomain targetDomain)
    (sourceCodomain : sourceDomain → Type u)
    (targetCodomain : targetDomain → Type u) where
  dependentEquiv : IncDependentFiberEquiv domainEquiv
    sourceCodomain targetCodomain
  backward_forward : ∀ function,
    dependentEquiv.piBackward (dependentEquiv.piForward function) = function
  forward_backward : ∀ function,
    dependentEquiv.piForward (dependentEquiv.piBackward function) = function

def IncDependentPiFiberEquiv.toFiberEquiv
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (equivalence : IncDependentPiFiberEquiv domainEquiv
      sourceCodomain targetCodomain) :
    IncFiberEquiv ((value : sourceDomain) → sourceCodomain value)
      ((value : targetDomain) → targetCodomain value) where
  forward := equivalence.dependentEquiv.piForward
  backward := equivalence.dependentEquiv.piBackward
  backward_forward := equivalence.backward_forward
  forward_backward := equivalence.forward_backward

structure IncDependentPiApplicationFiberEquiv
    {sourceDomain targetDomain : Type u}
    (domainEquiv : IncFiberEquiv sourceDomain targetDomain)
    (sourceCodomain : sourceDomain → Type u)
    (targetCodomain : targetDomain → Type u)
    extends IncDependentPiFiberEquiv domainEquiv sourceCodomain targetCodomain where
  forward_apply : ∀ sourceFunction sourceArgument,
    (dependentEquiv.codomainEquiv sourceArgument).forward
        (sourceFunction sourceArgument) =
      dependentEquiv.piForward sourceFunction
        (domainEquiv.forward sourceArgument)

def IncDependentPiApplicationFiberEquiv.toPiFiberEquiv
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (equivalence : IncDependentPiApplicationFiberEquiv domainEquiv
      sourceCodomain targetCodomain) :
    IncDependentPiFiberEquiv domainEquiv sourceCodomain targetCodomain :=
  equivalence.toIncDependentPiFiberEquiv

def IncDependentFiberEquiv.sigmaForward
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain) :
    (Sigma sourceCodomain) → Sigma targetCodomain :=
  fun value => ⟨domainEquiv.forward value.1,
    (dependentEquiv.codomainEquiv value.1).forward value.2⟩

def IncDependentFiberEquiv.sigmaBackward
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain) :
    (Sigma targetCodomain) → Sigma sourceCodomain :=
  fun value =>
    let sourceValue := domainEquiv.backward value.1
    ⟨sourceValue, (dependentEquiv.codomainEquiv sourceValue).backward
      (Eq.mp (congrArg targetCodomain
        (domainEquiv.forward_backward value.1).symm) value.2)⟩

theorem IncDependentFiberEquiv.sigmaForward_pair
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (first : sourceDomain) (second : sourceCodomain first) :
    dependentEquiv.sigmaForward ⟨first, second⟩ =
      ⟨domainEquiv.forward first,
        (dependentEquiv.codomainEquiv first).forward second⟩ := by
  rfl

theorem IncDependentFiberEquiv.sigmaForward_first
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (value : Sigma sourceCodomain) :
    (dependentEquiv.sigmaForward value).1 = domainEquiv.forward value.1 := by
  rfl

theorem IncDependentFiberEquiv.sigmaForward_second
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (value : Sigma sourceCodomain) :
    (dependentEquiv.sigmaForward value).2 =
      (dependentEquiv.codomainEquiv value.1).forward value.2 := by
  rfl

theorem IncDependentFiberEquiv.sigmaForward_second_eq_of_eq
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (sourceValue : Sigma sourceCodomain)
    (targetValue : Sigma targetCodomain)
    (coherence : dependentEquiv.sigmaForward sourceValue = targetValue) :
    Eq.mp (congrArg targetCodomain (congrArg Sigma.fst coherence))
        ((dependentEquiv.codomainEquiv sourceValue.1).forward sourceValue.2) =
      targetValue.2 := by
  cases coherence
  rfl

theorem IncDependentFiberEquiv.sigmaForward_eq_of_components
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (dependentEquiv : IncDependentFiberEquiv domainEquiv
      sourceCodomain targetCodomain)
    (sourceValue : Sigma sourceCodomain)
    (targetValue : Sigma targetCodomain)
    (firstCoherence : domainEquiv.forward sourceValue.1 = targetValue.1)
    (secondCoherence :
      Eq.mp (congrArg targetCodomain firstCoherence)
          ((dependentEquiv.codomainEquiv sourceValue.1).forward sourceValue.2) =
        targetValue.2) :
    dependentEquiv.sigmaForward sourceValue = targetValue := by
  cases sourceValue with
  | mk sourceFirst sourceSecond =>
    cases targetValue with
    | mk targetFirst targetSecond =>
      cases firstCoherence
      cases secondCoherence
      rfl

structure IncDependentSigmaFiberEquiv
    {sourceDomain targetDomain : Type u}
    (domainEquiv : IncFiberEquiv sourceDomain targetDomain)
    (sourceCodomain : sourceDomain → Type u)
    (targetCodomain : targetDomain → Type u) where
  dependentEquiv : IncDependentFiberEquiv domainEquiv
    sourceCodomain targetCodomain
  backward_forward : ∀ value,
    dependentEquiv.sigmaBackward (dependentEquiv.sigmaForward value) = value
  forward_backward : ∀ value,
    dependentEquiv.sigmaForward (dependentEquiv.sigmaBackward value) = value

def IncDependentSigmaFiberEquiv.toFiberEquiv
    {sourceDomain targetDomain : Type u}
    {domainEquiv : IncFiberEquiv sourceDomain targetDomain}
    {sourceCodomain : sourceDomain → Type u}
    {targetCodomain : targetDomain → Type u}
    (equivalence : IncDependentSigmaFiberEquiv domainEquiv
      sourceCodomain targetCodomain) :
    IncFiberEquiv (Sigma sourceCodomain) (Sigma targetCodomain) where
  forward := equivalence.dependentEquiv.sigmaForward
  backward := equivalence.dependentEquiv.sigmaBackward
  backward_forward := equivalence.backward_forward
  forward_backward := equivalence.forward_backward

theorem IncTerm.substitute_identity
    {context : IncContext.{u}} {type : IncTypeInContext context}
    (term : IncTerm type) :
    term.substitute (IncContext.Substitution.identity context) = term := by
  rfl

theorem IncTerm.substitute_comp
    {first second third : IncContext.{u}}
    {type : IncTypeInContext third}
    (term : IncTerm type)
    (after : second.Substitution third)
    (before : first.Substitution second) :
    term.substitute (after.comp before) =
      (term.substitute after).substitute before := by
  rfl

def IncContext.extendProjection
    (context : IncContext.{u}) (family : IncTypeInContext context) :
    (context.extend family).Substitution context :=
  Sigma.fst

def IncContext.extendVariable
    (context : IncContext.{u}) (family : IncTypeInContext context) :
    IncTerm (family.reindex (context.extendProjection family)) :=
  Sigma.snd

def IncContext.Substitution.extend
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (family : IncTypeInContext target)
    (term : IncTerm (family.reindex substitution)) :
    source.Substitution (target.extend family) :=
  fun assignment => ⟨substitution assignment, term assignment⟩

theorem IncContext.Substitution.extend_projection
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (family : IncTypeInContext target)
    (term : IncTerm (family.reindex substitution)) :
    (target.extendProjection family).comp
        (substitution.extend family term) = substitution := by
  rfl

theorem IncContext.Substitution.extend_variable
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (family : IncTypeInContext target)
    (term : IncTerm (family.reindex substitution)) :
    (target.extendVariable family).substitute
        (substitution.extend family term) = term := by
  rfl

def IncContext.Substitution.instantiate
    {context : IncContext.{u}}
    (family : IncTypeInContext context)
    (argument : IncTerm family) :
    context.Substitution (context.extend family) :=
  (IncContext.Substitution.identity context).extend family argument

theorem IncContext.Substitution.instantiate_projection
    {context : IncContext.{u}}
    (family : IncTypeInContext context)
    (argument : IncTerm family) :
    (context.extendProjection family).comp
        (IncContext.Substitution.instantiate family argument) =
      IncContext.Substitution.identity context := by
  rfl

theorem IncContext.Substitution.instantiate_variable
    {context : IncContext.{u}}
    (family : IncTypeInContext context)
    (argument : IncTerm family) :
    (context.extendVariable family).substitute
        (IncContext.Substitution.instantiate family argument) = argument := by
  rfl

def IncTypeInContext.instantiateFiber
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    (codomain : IncTypeInContext (context.extend domain))
    (argument : IncTerm domain) : IncTypeInContext context :=
  codomain.reindex (IncContext.Substitution.instantiate domain argument)

theorem IncTypeInContext.instantiateFiber_apply
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    (codomain : IncTypeInContext (context.extend domain))
    (argument : IncTerm domain) :
    IncTypeInContext.instantiateFiber codomain argument =
      fun assignment => codomain ⟨assignment, argument assignment⟩ := by
  rfl

def IncTerm.instantiateFiber
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (body : IncTerm codomain) (argument : IncTerm domain) :
    IncTerm (IncTypeInContext.instantiateFiber codomain argument) :=
  body.substitute (IncContext.Substitution.instantiate domain argument)

theorem IncTerm.instantiateFiber_apply
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (body : IncTerm codomain) (argument : IncTerm domain) :
    IncTerm.instantiateFiber body argument =
      fun assignment => body ⟨assignment, argument assignment⟩ := by
  rfl

def IncPiType
    {context : IncContext.{u}}
    (domain : IncTypeInContext context)
    (codomain : IncTypeInContext (context.extend domain)) :
    IncTypeInContext context :=
  fun assignment => ∀ value : domain assignment,
    codomain ⟨assignment, value⟩

def IncContext.Substitution.liftDependent
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (domain : IncTypeInContext target) :
    (source.extend (domain.reindex substitution)).Substitution
      (target.extend domain) :=
  fun extended => ⟨substitution extended.1, extended.2⟩

theorem IncContext.Substitution.liftDependent_projection
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (domain : IncTypeInContext target) :
    (target.extendProjection domain).comp
        (substitution.liftDependent domain) =
      substitution.comp
        (source.extendProjection (domain.reindex substitution)) := by
  rfl

theorem IncContext.Substitution.liftDependent_variable
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (domain : IncTypeInContext target) :
    (target.extendVariable domain).substitute
        (substitution.liftDependent domain) =
      source.extendVariable (domain.reindex substitution) := by
  rfl

theorem IncPiType.reindex
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (domain : IncTypeInContext target)
    (codomain : IncTypeInContext (target.extend domain)) :
    (IncPiType domain codomain).reindex substitution =
      IncPiType (domain.reindex substitution)
        (codomain.reindex (substitution.liftDependent domain)) := by
  rfl

structure IncDependentPiTypeInContextFiberEquiv
    {context : IncContext.{u}}
    {sourceDomain targetDomain : IncTypeInContext context}
    (domainEquiv : IncTypeInContext.FiberEquiv sourceDomain targetDomain)
    (sourceCodomain : IncTypeInContext (context.extend sourceDomain))
    (targetCodomain : IncTypeInContext (context.extend targetDomain)) where
  fiberEquiv : ∀ assignment,
    IncDependentPiFiberEquiv (domainEquiv.fiberEquiv assignment)
      (fun value => sourceCodomain ⟨assignment, value⟩)
      (fun value => targetCodomain ⟨assignment, value⟩)

def IncDependentPiTypeInContextFiberEquiv.piFiberEquivalence
    {context : IncContext.{u}}
    {sourceDomain targetDomain : IncTypeInContext context}
    {domainEquiv : IncTypeInContext.FiberEquiv sourceDomain targetDomain}
    {sourceCodomain : IncTypeInContext (context.extend sourceDomain)}
    {targetCodomain : IncTypeInContext (context.extend targetDomain)}
    (equivalence : IncDependentPiTypeInContextFiberEquiv domainEquiv
      sourceCodomain targetCodomain) :
    IncTypeInContext.FiberEquiv
      (IncPiType sourceDomain sourceCodomain)
      (IncPiType targetDomain targetCodomain) where
  fiberEquiv := fun assignment =>
    (equivalence.fiberEquiv assignment).toFiberEquiv

def IncPiTerm.lambda
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (body : IncTerm codomain) :
    IncTerm (IncPiType domain codomain) :=
  fun assignment value => body ⟨assignment, value⟩

def IncPiTerm.apply
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (function : IncTerm (IncPiType domain codomain))
    (argument : IncTerm domain) :
    IncTerm (fun assignment => codomain ⟨assignment, argument assignment⟩) :=
  fun assignment => function assignment (argument assignment)

theorem IncPiTerm.beta
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (body : IncTerm codomain) (argument : IncTerm domain) :
    IncPiTerm.apply (IncPiTerm.lambda body) argument =
      fun assignment => body ⟨assignment, argument assignment⟩ := by
  rfl

theorem IncPiTerm.eta
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (function : IncTerm (IncPiType domain codomain)) :
    IncPiTerm.lambda
      (fun extended => function extended.1 extended.2) = function := by
  rfl

theorem IncPiTerm.lambda_substitute
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    {domain : IncTypeInContext target}
    {codomain : IncTypeInContext (target.extend domain)}
    (body : IncTerm codomain) :
    (IncPiTerm.lambda body).substitute substitution =
      IncPiTerm.lambda
        (body.substitute (substitution.liftDependent domain)) := by
  rfl

theorem IncPiTerm.apply_substitute
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    {domain : IncTypeInContext target}
    {codomain : IncTypeInContext (target.extend domain)}
    (function : IncTerm (IncPiType domain codomain))
    (argument : IncTerm domain) :
    ∀ assignment,
      (IncPiTerm.apply function argument).substitute substitution assignment =
        function (substitution assignment)
          (argument (substitution assignment)) := by
  intro assignment
  rfl

def IncSigmaType
    {context : IncContext.{u}}
    (domain : IncTypeInContext context)
    (codomain : IncTypeInContext (context.extend domain)) :
    IncTypeInContext context :=
  fun assignment => Sigma fun value : domain assignment =>
    codomain ⟨assignment, value⟩

theorem IncSigmaType.reindex
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (domain : IncTypeInContext target)
    (codomain : IncTypeInContext (target.extend domain)) :
    (IncSigmaType domain codomain).reindex substitution =
      IncSigmaType (domain.reindex substitution)
        (codomain.reindex (substitution.liftDependent domain)) := by
  rfl

def IncSigmaTerm.pair
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (first : IncTerm domain)
    (second : IncTerm (fun assignment =>
      codomain ⟨assignment, first assignment⟩)) :
    IncTerm (IncSigmaType domain codomain) :=
  fun assignment => ⟨first assignment, second assignment⟩

def IncSigmaTerm.first
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (pair : IncTerm (IncSigmaType domain codomain)) :
    IncTerm domain :=
  fun assignment => (pair assignment).1

def IncSigmaTerm.second
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (pair : IncTerm (IncSigmaType domain codomain)) :
    IncTerm (fun assignment =>
      codomain ⟨assignment, (pair assignment).1⟩) :=
  fun assignment => (pair assignment).2

theorem IncSigmaTerm.first_beta
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (first : IncTerm domain)
    (second : IncTerm (fun assignment =>
      codomain ⟨assignment, first assignment⟩)) :
    IncSigmaTerm.first (IncSigmaTerm.pair first second) = first := by
  rfl

theorem IncSigmaTerm.second_beta
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (first : IncTerm domain)
    (second : IncTerm (fun assignment =>
      codomain ⟨assignment, first assignment⟩)) :
    IncSigmaTerm.second (IncSigmaTerm.pair first second) = second := by
  rfl

theorem IncSigmaTerm.eta
    {context : IncContext.{u}}
    {domain : IncTypeInContext context}
    {codomain : IncTypeInContext (context.extend domain)}
    (pair : IncTerm (IncSigmaType domain codomain)) :
    IncSigmaTerm.pair (IncSigmaTerm.first pair) (IncSigmaTerm.second pair) = pair := by
  funext assignment
  change ⟨(pair assignment).1, (pair assignment).2⟩ = pair assignment
  generalize valueEq : pair assignment = value
  cases value
  rfl

theorem IncSigmaTerm.pair_substitute
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    {domain : IncTypeInContext target}
    {codomain : IncTypeInContext (target.extend domain)}
    (first : IncTerm domain)
    (second : IncTerm (fun assignment =>
      codomain ⟨assignment, first assignment⟩)) :
    ∀ assignment,
      (IncSigmaTerm.pair first second).substitute substitution assignment =
        ⟨first (substitution assignment),
          second (substitution assignment)⟩ := by
  intro assignment
  rfl

theorem IncSigmaTerm.first_substitute
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    {domain : IncTypeInContext target}
    {codomain : IncTypeInContext (target.extend domain)}
    (pair : IncTerm (IncSigmaType domain codomain)) :
    (IncSigmaTerm.first pair).substitute substitution =
      fun assignment => (pair (substitution assignment)).1 := by
  rfl

theorem IncSigmaTerm.second_substitute
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    {domain : IncTypeInContext target}
    {codomain : IncTypeInContext (target.extend domain)}
    (pair : IncTerm (IncSigmaType domain codomain)) :
    ∀ assignment,
      (IncSigmaTerm.second pair).substitute substitution assignment =
        (pair (substitution assignment)).2 := by
  intro assignment
  rfl

def IncIdentityType
    {context : IncContext.{u}}
    (type : IncTypeInContext context)
    (left right : IncTerm type) :
    IncTypeInContext context :=
  fun assignment =>
    ULift.{u} (PLift (left assignment = right assignment))

theorem IncIdentityType.witness_irrel
    {carrier : Sort v} {left right : carrier}
    (first second : ULift.{u} (PLift (left = right))) :
    first = second := by
  cases first with
  | up firstLifted =>
      cases firstLifted with
      | up firstPath =>
          cases second with
          | up secondLifted =>
              cases secondLifted with
              | up secondPath => congr

def IncFiberEquiv.mapIdentityWitness
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {left right : source}
    (witness : ULift.{u} (PLift (left = right))) :
    ULift.{u} (PLift
      (equivalence.forward left = equivalence.forward right)) :=
  ⟨⟨equivalence.mapEquality witness.down.down⟩⟩

def IncFiberEquiv.mapIdentityWitnessBackward
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    {left right : target}
    (witness : ULift.{u} (PLift (left = right))) :
    ULift.{u} (PLift
      (equivalence.backward left = equivalence.backward right)) :=
  ⟨⟨equivalence.mapEqualityBackward witness.down.down⟩⟩

theorem IncFiberEquiv.mapIdentityWitness_refl
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    (value : source) :
    equivalence.mapIdentityWitness
        (left := value) (right := value) ⟨⟨rfl⟩⟩ =
      (⟨⟨rfl⟩⟩ : ULift.{u} (PLift
        (equivalence.forward value = equivalence.forward value))) := by
  rfl

theorem IncFiberEquiv.mapIdentityWitnessBackward_refl
    {source target : Type u} (equivalence : IncFiberEquiv source target)
    (value : target) :
    equivalence.mapIdentityWitnessBackward
        (left := value) (right := value) ⟨⟨rfl⟩⟩ =
      (⟨⟨rfl⟩⟩ : ULift.{u} (PLift
        (equivalence.backward value = equivalence.backward value))) := by
  rfl

def IncIdentityTerm.map
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    {left right : IncTerm source}
    (equal : IncTerm (IncIdentityType source left right)) :
    IncTerm (IncIdentityType target
      (equivalence.transport left) (equivalence.transport right)) :=
  fun assignment =>
    (equivalence.fiberEquiv assignment).mapIdentityWitness (equal assignment)

def IncIdentityTerm.mapBackward
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    {left right : IncTerm target}
    (equal : IncTerm (IncIdentityType target left right)) :
    IncTerm (IncIdentityType source
      (equivalence.symm.transport left) (equivalence.symm.transport right)) :=
  fun assignment =>
    (equivalence.fiberEquiv assignment).mapIdentityWitnessBackward
      (equal assignment)

def IncIdentityType.fiberEquivalence
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    {sourceLeft sourceRight : IncTerm source}
    {targetLeft targetRight : IncTerm target}
    (leftCoherence : equivalence.transport sourceLeft = targetLeft)
    (rightCoherence : equivalence.transport sourceRight = targetRight) :
    IncTypeInContext.FiberEquiv
      (IncIdentityType source sourceLeft sourceRight)
      (IncIdentityType target targetLeft targetRight) where
  fiberEquiv := fun assignment =>
    let fiber := equivalence.fiberEquiv assignment
    let leftEq := congrFun leftCoherence assignment
    let rightEq := congrFun rightCoherence assignment
    { forward := fun witness =>
        ⟨⟨leftEq.symm.trans
          ((fiber.mapEquality witness.down.down).trans rightEq)⟩⟩
      backward := fun witness =>
        ⟨⟨(fiber.backward_forward (sourceLeft assignment)).symm.trans
          ((congrArg fiber.backward leftEq).trans
            ((fiber.mapEqualityBackward witness.down.down).trans
              ((congrArg fiber.backward rightEq).symm.trans
                (fiber.backward_forward (sourceRight assignment)))))⟩⟩
      backward_forward := by
        intro witness
        cases witness with
        | up lifted =>
          cases lifted with
          | up path => congr
      forward_backward := by
        intro witness
        cases witness with
        | up lifted =>
          cases lifted with
          | up path => congr }

theorem IncIdentityType.fiberEquivalence_forward
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    {sourceLeft sourceRight : IncTerm source}
    {targetLeft targetRight : IncTerm target}
    (leftCoherence : equivalence.transport sourceLeft = targetLeft)
    (rightCoherence : equivalence.transport sourceRight = targetRight)
    (assignment) (witness : IncIdentityType source sourceLeft sourceRight assignment) :
    ((IncIdentityType.fiberEquivalence equivalence leftCoherence rightCoherence).fiberEquiv
        assignment).forward witness =
      ⟨⟨(congrFun leftCoherence assignment).symm.trans
        (((equivalence.fiberEquiv assignment).mapEquality witness.down.down).trans
          (congrFun rightCoherence assignment))⟩⟩ := by
  rfl

def IncIdentityTerm.refl
    {context : IncContext.{u}}
    {type : IncTypeInContext context}
    (term : IncTerm type) :
    IncTerm (IncIdentityType type term term) :=
  fun _ => ⟨⟨rfl⟩⟩

theorem IncIdentityTerm.map_refl
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (term : IncTerm source) :
    IncIdentityTerm.map equivalence (IncIdentityTerm.refl term) =
      IncIdentityTerm.refl (equivalence.transport term) := by
  rfl

theorem IncIdentityTerm.mapBackward_refl
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (term : IncTerm target) :
    IncIdentityTerm.mapBackward equivalence (IncIdentityTerm.refl term) =
      IncIdentityTerm.refl (equivalence.symm.transport term) := by
  rfl

def IncIdentityTerm.transport
    {context : IncContext.{u}}
    {type : IncTypeInContext context}
    {left right : IncTerm type}
    (family : ∀ assignment, type assignment → Type u)
    (equal : IncTerm (IncIdentityType type left right))
    (value : ∀ assignment, family assignment (left assignment)) :
    ∀ assignment, family assignment (right assignment) := by
  intro assignment
  have pointEqual := (equal assignment).down.down
  rw [← pointEqual]
  exact value assignment

def IncIdentityTerm.J
    {context : IncContext.{u}}
    {type : IncTypeInContext context}
    (motive : ∀ assignment (_left _right : type assignment), Type u)
    (reflCase : ∀ assignment value,
      motive assignment value value)
    {left right : IncTerm type}
    (equal : IncTerm (IncIdentityType type left right)) :
    ∀ assignment,
      motive assignment (left assignment) (right assignment) := by
  intro assignment
  exact (equal assignment).down.down ▸
    reflCase assignment (left assignment)

theorem IncIdentityTerm.transport_refl
    {context : IncContext.{u}}
    {type : IncTypeInContext context}
    (family : ∀ assignment, type assignment → Type u)
    (term : IncTerm type)
    (value : ∀ assignment, family assignment (term assignment)) :
    IncIdentityTerm.transport family (IncIdentityTerm.refl term) value = value := by
  rfl

theorem IncIdentityTerm.J_beta
    {context : IncContext.{u}}
    {type : IncTypeInContext context}
    (motive : ∀ assignment (_left _right : type assignment), Type u)
    (reflCase : ∀ assignment value,
      motive assignment value value)
    (term : IncTerm type) :
    IncIdentityTerm.J motive reflCase (IncIdentityTerm.refl term) =
      fun assignment => reflCase assignment (term assignment) := by
  funext assignment
  simp [IncIdentityTerm.J]

structure IncIdentityJMap
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (sourceMotive : ∀ assignment (_left _right : source assignment), Type u)
    (targetMotive : ∀ assignment (_left _right : target assignment), Type u)
    (sourceRefl : ∀ assignment value,
      sourceMotive assignment value value)
    (targetRefl : ∀ assignment value,
      targetMotive assignment value value) where
  mapMotive : ∀ assignment left right,
    sourceMotive assignment left right →
      targetMotive assignment
        ((equivalence.fiberEquiv assignment).forward left)
        ((equivalence.fiberEquiv assignment).forward right)
  mapRefl : ∀ assignment value,
    mapMotive assignment value value (sourceRefl assignment value) =
      targetRefl assignment
        ((equivalence.fiberEquiv assignment).forward value)

theorem IncIdentityJMap.eliminate
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    {equivalence : IncTypeInContext.FiberEquiv source target}
    {sourceMotive : ∀ assignment (_left _right : source assignment), Type u}
    {targetMotive : ∀ assignment (_left _right : target assignment), Type u}
    {sourceRefl : ∀ assignment value,
      sourceMotive assignment value value}
    {targetRefl : ∀ assignment value,
      targetMotive assignment value value}
    (motiveMap : IncIdentityJMap equivalence sourceMotive targetMotive
      sourceRefl targetRefl)
    (assignment) {left right : source assignment}
    (path : left = right) :
    (equivalence.fiberEquiv assignment).mapEquality path ▸
        targetRefl assignment
          ((equivalence.fiberEquiv assignment).forward left) =
      motiveMap.mapMotive assignment left right
        (path ▸ sourceRefl assignment left) := by
  cases path
  exact (motiveMap.mapRefl assignment left).symm

theorem IncIdentityTerm.J_map
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (sourceMotive : ∀ assignment (_left _right : source assignment), Type u)
    (targetMotive : ∀ assignment (_left _right : target assignment), Type u)
    (sourceRefl : ∀ assignment value,
      sourceMotive assignment value value)
    (targetRefl : ∀ assignment value,
      targetMotive assignment value value)
    (motiveMap : IncIdentityJMap equivalence sourceMotive targetMotive
      sourceRefl targetRefl)
    {left right : IncTerm source}
    (equal : IncTerm (IncIdentityType source left right)) :
    IncIdentityTerm.J targetMotive targetRefl
        (IncIdentityTerm.map equivalence equal) =
      fun assignment => motiveMap.mapMotive assignment
        (left assignment) (right assignment)
        (IncIdentityTerm.J sourceMotive sourceRefl equal assignment) := by
  funext assignment
  exact motiveMap.eliminate assignment (equal assignment).down.down

theorem IncIdentityTerm.J_map_refl
    {context : IncContext.{u}}
    {source target : IncTypeInContext context}
    (equivalence : IncTypeInContext.FiberEquiv source target)
    (motive : ∀ assignment (_left _right : target assignment), Type u)
    (reflCase : ∀ assignment value, motive assignment value value)
    (term : IncTerm source) :
    IncIdentityTerm.J motive reflCase
        (IncIdentityTerm.map equivalence (IncIdentityTerm.refl term)) =
      fun assignment => reflCase assignment
        (equivalence.transport term assignment) := by
  rw [IncIdentityTerm.map_refl]
  exact IncIdentityTerm.J_beta motive reflCase (equivalence.transport term)

theorem IncIdentityType.reindex
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    (type : IncTypeInContext target)
    (left right : IncTerm type) :
    (IncIdentityType type left right).reindex substitution =
      IncIdentityType (type.reindex substitution)
        (left.substitute substitution) (right.substitute substitution) := by
  rfl

theorem IncIdentityTerm.refl_substitute
    {source target : IncContext.{u}}
    (substitution : source.Substitution target)
    {type : IncTypeInContext target}
    (term : IncTerm type) :
    (IncIdentityTerm.refl term).substitute substitution =
      IncIdentityTerm.refl (term.substitute substitution) := by
  rfl

def incDepUnitType : IncTypeInContext IncContext.empty :=
  fun _ => ULift Unit

def incDepUnitTerm : IncTerm incDepUnitType :=
  fun _ => ⟨()⟩

def incDepRawDependentReflSemanticCodomain :
    IncTypeInContext (IncContext.empty.extend incDepUnitType) :=
  IncIdentityType
    (incDepUnitType.reindex
      (IncContext.empty.extendProjection incDepUnitType))
    (IncContext.empty.extendVariable incDepUnitType)
    (IncContext.empty.extendVariable incDepUnitType)

def incDepRawDependentReflSemantic :
    IncTerm (IncPiType incDepUnitType
      incDepRawDependentReflSemanticCodomain) :=
  IncPiTerm.lambda
    (IncIdentityTerm.refl
      (IncContext.empty.extendVariable incDepUnitType))

theorem incDepRawDependentReflSemantic_beta :
    IncPiTerm.apply incDepRawDependentReflSemantic incDepUnitTerm =
      IncIdentityTerm.refl incDepUnitTerm := by
  rfl

def incDepRawDependentPairSemantic :
    IncTerm (IncSigmaType incDepUnitType
      incDepRawDependentReflSemanticCodomain) :=
  IncSigmaTerm.pair incDepUnitTerm
    (IncIdentityTerm.refl incDepUnitTerm)

theorem incDepRawDependentPairSemantic_first_beta :
    IncSigmaTerm.first incDepRawDependentPairSemantic = incDepUnitTerm := by
  rfl

theorem incDepRawDependentPairSemantic_second_beta :
    IncSigmaTerm.second incDepRawDependentPairSemantic =
      IncIdentityTerm.refl incDepUnitTerm := by
  rfl

theorem incDepRawDependentRefl_reductionSound :
    IncDepRawDefEq (.apply incDepRawDependentRefl .unit) (.refl .unit) ∧
    IncPiTerm.apply incDepRawDependentReflSemantic incDepUnitTerm =
      IncIdentityTerm.refl incDepUnitTerm := by
  exact ⟨IncDepRawDefEq.ofStep incDepRawDependentRefl_betaStep,
    incDepRawDependentReflSemantic_beta⟩

theorem incDepRawDependentPair_first_reductionSound :
    IncDepRawDefEq (.first incDepRawDependentPair) .unit ∧
    IncSigmaTerm.first incDepRawDependentPairSemantic = incDepUnitTerm := by
  exact ⟨IncDepRawDefEq.ofStep incDepRawDependentPair_first_betaStep,
    incDepRawDependentPairSemantic_first_beta⟩

theorem incDepRawDependentPair_second_reductionSound :
    IncDepRawDefEq (.second incDepRawDependentPair) (.refl .unit) ∧
    IncSigmaTerm.second incDepRawDependentPairSemantic =
      IncIdentityTerm.refl incDepUnitTerm := by
  exact ⟨IncDepRawDefEq.ofStep incDepRawDependentPair_second_betaStep,
    incDepRawDependentPairSemantic_second_beta⟩

structure IncDepRawClosedSemanticResult
    {term : IncDepRawTerm} {type : IncDepRawType}
    (certified : IncDepRawCertifiedTyping [] term type) where
  semanticType : IncTypeInContext IncContext.empty
  semanticTerm : IncTerm semanticType

structure IncDepRawContextSemanticResult
    {context : List IncDepRawType}
    (wellFormed : IncDepRawContext.WellFormed context) where
  semanticContext : IncContext

def incDepRawEmptyContextSemantic :
    IncDepRawContextSemanticResult IncDepRawContext.WellFormed.empty where
  semanticContext := IncContext.empty

def IncDepRawContextSemanticResult.extend
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed)
    {typeWellFormed : IncDepRawWellFormed context type}
    (semanticType : IncTypeInContext contextResult.semanticContext) :
    IncDepRawContextSemanticResult
      (IncDepRawContext.WellFormed.extend contextWellFormed typeWellFormed) where
  semanticContext := contextResult.semanticContext.extend semanticType

structure IncDepRawSemanticResult
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    (certified : IncDepRawCertifiedTyping context term type)
    (contextResult : IncDepRawContextSemanticResult
      certified.contextWellFormed) where
  semanticType : IncTypeInContext contextResult.semanticContext
  semanticTerm : IncTerm semanticType

structure IncDepRawFormationSemanticResult
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (formation : IncDepRawWellFormed context type)
    (contextResult : IncDepRawContextSemanticResult contextWellFormed) where
  semanticType : IncTypeInContext contextResult.semanticContext

def IncDepRawFormationSemanticResult.base
    {context : List IncDepRawType} {index : Nat}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed)
    (baseModel : Nat → Type u) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.base (context := context) (index := index))
      contextResult where
  semanticType := fun _ => baseModel index

def IncDepRawFormationSemanticResult.unit
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.unit (context := context)) contextResult where
  semanticType := fun _ => ULift Unit

def IncDepRawFormationSemanticResult.pi
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (domainResult : IncDepRawFormationSemanticResult
      domainFormation contextResult)
    (codomainResult : IncDepRawFormationSemanticResult codomainFormation
      (contextResult.extend (typeWellFormed := domainFormation)
        domainResult.semanticType)) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.pi domainFormation codomainFormation)
      contextResult where
  semanticType := IncPiType domainResult.semanticType codomainResult.semanticType

def IncDepRawFormationSemanticResult.sigma
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (domainResult : IncDepRawFormationSemanticResult
      domainFormation contextResult)
    (codomainResult : IncDepRawFormationSemanticResult codomainFormation
      (contextResult.extend (typeWellFormed := domainFormation)
        domainResult.semanticType)) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.sigma domainFormation codomainFormation)
      contextResult where
  semanticType := IncSigmaType domainResult.semanticType codomainResult.semanticType

def IncDepRawFormationSemanticResult.identity
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (typeResult : IncDepRawFormationSemanticResult typeFormation contextResult)
    (leftSemantic rightSemantic : IncTerm typeResult.semanticType) :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.identity typeFormation leftTyping rightTyping)
      contextResult where
  semanticType := IncIdentityType typeResult.semanticType
    leftSemantic rightSemantic

noncomputable def IncDepRawFormationSemanticResult.weaken
    {context : List IncDepRawType} {type head : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (typeFormation : IncDepRawWellFormed context type)
    (typeResult : IncDepRawFormationSemanticResult typeFormation contextResult)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    IncDepRawFormationSemanticResult
      (typeFormation.rename
        ((IncDepRawRenaming.identity context).weakenTarget head))
      (contextResult.extend (typeWellFormed := headWellFormed)
        headResult.semanticType) where
  semanticType := typeResult.semanticType.reindex
    (contextResult.semanticContext.extendProjection headResult.semanticType)

theorem IncDepRawFormationSemanticResult.weaken_semanticType
    {context : List IncDepRawType} {type head : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (typeFormation : IncDepRawWellFormed context type)
    (typeResult : IncDepRawFormationSemanticResult typeFormation contextResult)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    (IncDepRawFormationSemanticResult.weaken typeFormation typeResult
      headResult).semanticType =
      typeResult.semanticType.reindex
        (contextResult.semanticContext.extendProjection headResult.semanticType) := by
  rfl

structure IncDepRawSubstitutionSemanticResult
    {source target : List IncDepRawType}
    (substitution : IncDepRawSubstitution source target)
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    (sourceResult : IncDepRawContextSemanticResult sourceWellFormed)
    (targetResult : IncDepRawContextSemanticResult targetWellFormed) where
  semanticSubstitution : sourceResult.semanticContext.Substitution
    targetResult.semanticContext

def IncDepRawSubstitutionSemanticResult.identity
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed) :
    IncDepRawSubstitutionSemanticResult
      (IncDepRawSubstitution.identity context) contextResult contextResult where
  semanticSubstitution := IncContext.Substitution.identity
    contextResult.semanticContext

noncomputable def IncDepRawSubstitutionSemanticResult.lift
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution) :
    IncDepRawSubstitutionSemanticResult (substitution.lift domain)
      (sourceResult.extend (typeWellFormed := substitutedDomainFormation)
        sourceDomain.semanticType)
      (targetResult.extend (typeWellFormed := domainFormation)
        targetDomain.semanticType) where
  semanticSubstitution := fun extended =>
    ⟨substitutionResult.semanticSubstitution extended.1,
      Eq.mp (congrFun coherence extended.1) extended.2⟩

noncomputable def IncDepRawSubstitutionSemanticResult.liftFiber
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (domainEquivalence : IncTypeInContext.FiberEquiv
      sourceDomain.semanticType
      (targetDomain.semanticType.reindex
        substitutionResult.semanticSubstitution)) :
    IncDepRawSubstitutionSemanticResult (substitution.lift domain)
      (sourceResult.extend (typeWellFormed := substitutedDomainFormation)
        sourceDomain.semanticType)
      (targetResult.extend (typeWellFormed := domainFormation)
        targetDomain.semanticType) where
  semanticSubstitution := fun extended =>
    ⟨substitutionResult.semanticSubstitution extended.1,
      (domainEquivalence.fiberEquiv extended.1).forward extended.2⟩

theorem IncDepRawSubstitutionSemanticResult.liftFiber_projection
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (domainEquivalence : IncTypeInContext.FiberEquiv
      sourceDomain.semanticType
      (targetDomain.semanticType.reindex
        substitutionResult.semanticSubstitution)) :
    (targetResult.semanticContext.extendProjection targetDomain.semanticType).comp
        (IncDepRawSubstitutionSemanticResult.liftFiber substitutionResult
          targetDomain sourceDomain domainEquivalence).semanticSubstitution =
      substitutionResult.semanticSubstitution.comp
        (sourceResult.semanticContext.extendProjection sourceDomain.semanticType) := by
  rfl

theorem IncDepRawSubstitutionSemanticResult.liftFiber_variable
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (domainEquivalence : IncTypeInContext.FiberEquiv
      sourceDomain.semanticType
      (targetDomain.semanticType.reindex
        substitutionResult.semanticSubstitution))
    (assignment : sourceResult.semanticContext.Assignment)
    (value : sourceDomain.semanticType assignment) :
    (targetResult.semanticContext.extendVariable targetDomain.semanticType)
      ((IncDepRawSubstitutionSemanticResult.liftFiber substitutionResult
        targetDomain sourceDomain domainEquivalence).semanticSubstitution
          ⟨assignment, value⟩) =
      (domainEquivalence.fiberEquiv assignment).forward value := by
  rfl

theorem IncDepRawSubstitutionSemanticResult.liftFiber_ofEq
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType =
      targetDomain.semanticType.reindex substitutionResult.semanticSubstitution) :
    (IncDepRawSubstitutionSemanticResult.liftFiber substitutionResult
      targetDomain sourceDomain
      (IncTypeInContext.FiberEquiv.ofEq coherence)).semanticSubstitution =
    (IncDepRawSubstitutionSemanticResult.lift substitutionResult
      targetDomain sourceDomain coherence).semanticSubstitution := by
  funext extended
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (IncTypeInContext.FiberEquiv.ofEq_forward coherence
      extended.1 extended.2)

theorem IncDepRawSubstitutionSemanticResult.identity_apply
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed)
    (assignment : contextResult.semanticContext.Assignment) :
    (IncDepRawSubstitutionSemanticResult.identity contextResult).semanticSubstitution
      assignment = assignment := by
  rfl

theorem IncDepRawSubstitutionSemanticResult.lift_projection
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution) :
    (targetResult.semanticContext.extendProjection targetDomain.semanticType).comp
        (IncDepRawSubstitutionSemanticResult.lift substitutionResult
          targetDomain sourceDomain coherence).semanticSubstitution =
      substitutionResult.semanticSubstitution.comp
        (sourceResult.semanticContext.extendProjection sourceDomain.semanticType) := by
  rfl

theorem IncDepRawSubstitutionSemanticResult.lift_variable
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution)
    (assignment : sourceResult.semanticContext.Assignment)
    (value : sourceDomain.semanticType assignment) :
    (targetResult.semanticContext.extendVariable targetDomain.semanticType)
      ((IncDepRawSubstitutionSemanticResult.lift substitutionResult
        targetDomain sourceDomain coherence).semanticSubstitution
          ⟨assignment, value⟩) =
      Eq.mp (congrFun coherence assignment) value := by
  rfl

theorem IncDepRawSubstitutionSemanticResult.lift_variable_fiber
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution)
    (assignment : sourceResult.semanticContext.Assignment)
    (value : sourceDomain.semanticType assignment) :
    ((IncTypeInContext.FiberEquiv.ofEq coherence).fiberEquiv assignment).forward
        value =
      (targetResult.semanticContext.extendVariable targetDomain.semanticType)
        ((IncDepRawSubstitutionSemanticResult.lift substitutionResult
          targetDomain sourceDomain coherence).semanticSubstitution
            ⟨assignment, value⟩) := by
  rw [IncTypeInContext.FiberEquiv.ofEq_forward]
  exact (IncDepRawSubstitutionSemanticResult.lift_variable substitutionResult
    targetDomain sourceDomain coherence assignment value).symm

theorem IncDepRawSubstitutionSemanticResult.lift_older_transport
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (domainCoherence : sourceDomain.semanticType =
      targetDomain.semanticType.reindex substitutionResult.semanticSubstitution)
    {sourceFamily : IncTypeInContext sourceResult.semanticContext}
    {targetFamily : IncTypeInContext targetResult.semanticContext}
    (familyEquivalence : IncTypeInContext.FiberEquiv sourceFamily
      (targetFamily.reindex substitutionResult.semanticSubstitution))
    (sourceTerm : IncTerm sourceFamily) (targetTerm : IncTerm targetFamily)
    (termCoherence : familyEquivalence.transport sourceTerm =
      targetTerm.substitute substitutionResult.semanticSubstitution) :
    (familyEquivalence.reindex
      (sourceResult.semanticContext.extendProjection sourceDomain.semanticType)).transport
        (sourceTerm.substitute
          (sourceResult.semanticContext.extendProjection sourceDomain.semanticType)) =
      (targetTerm.substitute
        (targetResult.semanticContext.extendProjection targetDomain.semanticType)).substitute
          (IncDepRawSubstitutionSemanticResult.lift substitutionResult
            targetDomain sourceDomain domainCoherence).semanticSubstitution := by
  rw [IncTypeInContext.FiberEquiv.reindex_transport, termCoherence]
  rfl

theorem IncDepRawSubstitutionSemanticResult.liftFiber_older_transport
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (domainEquivalence : IncTypeInContext.FiberEquiv
      sourceDomain.semanticType
      (targetDomain.semanticType.reindex substitutionResult.semanticSubstitution))
    {sourceFamily : IncTypeInContext sourceResult.semanticContext}
    {targetFamily : IncTypeInContext targetResult.semanticContext}
    (familyEquivalence : IncTypeInContext.FiberEquiv sourceFamily
      (targetFamily.reindex substitutionResult.semanticSubstitution))
    (sourceTerm : IncTerm sourceFamily) (targetTerm : IncTerm targetFamily)
    (termCoherence : familyEquivalence.transport sourceTerm =
      targetTerm.substitute substitutionResult.semanticSubstitution) :
    (familyEquivalence.reindex
      (sourceResult.semanticContext.extendProjection sourceDomain.semanticType)).transport
        (sourceTerm.substitute
          (sourceResult.semanticContext.extendProjection sourceDomain.semanticType)) =
      (targetTerm.substitute
        (targetResult.semanticContext.extendProjection targetDomain.semanticType)).substitute
          (IncDepRawSubstitutionSemanticResult.liftFiber substitutionResult
            targetDomain sourceDomain domainEquivalence).semanticSubstitution := by
  rw [IncTypeInContext.FiberEquiv.reindex_transport, termCoherence]
  rfl

structure IncDepRawFormationSubstitutionSemanticResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  targetFormationResult : IncDepRawFormationSemanticResult targetFormation
    targetResult
  sourceFormationResult : IncDepRawFormationSemanticResult
    (targetFormation.substitute substitution) sourceResult
  semanticType_coherence : sourceFormationResult.semanticType =
    targetFormationResult.semanticType.reindex
      substitutionResult.semanticSubstitution

def IncDepRawFormationSubstitutionSemanticResult.fiberEquivalence
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawFormationSubstitutionSemanticResult
      (targetFormation := targetFormation) substitutionResult) :
    IncTypeInContext.FiberEquiv result.sourceFormationResult.semanticType
      (result.targetFormationResult.semanticType.reindex
        substitutionResult.semanticSubstitution) :=
  IncTypeInContext.FiberEquiv.ofEq result.semanticType_coherence

structure IncDepRawFormationSubstitutionFiberResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  targetFormationResult : IncDepRawFormationSemanticResult targetFormation
    targetResult
  sourceFormationResult : IncDepRawFormationSemanticResult
    (targetFormation.substitute substitution) sourceResult
  semanticFiberEquivalence : IncTypeInContext.FiberEquiv
    sourceFormationResult.semanticType
    (targetFormationResult.semanticType.reindex
      substitutionResult.semanticSubstitution)

def IncDepRawFormationSubstitutionSemanticResult.toFiberResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawFormationSubstitutionSemanticResult
      (targetFormation := targetFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult where
  targetFormationResult := result.targetFormationResult
  sourceFormationResult := result.sourceFormationResult
  semanticFiberEquivalence := result.fiberEquivalence

def IncDepRawFormationSubstitutionSemanticResult.base
    {source target : List IncDepRawType} {index : Nat}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (baseModel : Nat → Type u) :
    IncDepRawFormationSubstitutionSemanticResult
      (targetFormation := IncDepRawWellFormed.base (index := index))
      substitutionResult where
  targetFormationResult := IncDepRawFormationSemanticResult.base
    targetResult baseModel
  sourceFormationResult := IncDepRawFormationSemanticResult.base
    sourceResult baseModel
  semanticType_coherence := rfl

def IncDepRawFormationSubstitutionSemanticResult.unit
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawFormationSubstitutionSemanticResult
      (targetFormation := IncDepRawWellFormed.unit) substitutionResult where
  targetFormationResult := IncDepRawFormationSemanticResult.unit targetResult
  sourceFormationResult := IncDepRawFormationSemanticResult.unit sourceResult
  semanticType_coherence := rfl

def IncDepRawFormationSubstitutionFiberResult.base
    {source target : List IncDepRawType} {index : Nat}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (baseModel : Nat → Type u) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.base (index := index))
      substitutionResult :=
  (IncDepRawFormationSubstitutionSemanticResult.base
    substitutionResult baseModel).toFiberResult

def IncDepRawFormationSubstitutionFiberResult.unit
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.unit) substitutionResult :=
  (IncDepRawFormationSubstitutionSemanticResult.unit
    substitutionResult).toFiberResult

noncomputable def IncDepRawFormationSubstitutionFiberResult.liftSubstitution
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult) :
    IncDepRawSubstitutionSemanticResult (substitution.lift domain)
      (sourceResult.extend
        (typeWellFormed := domainFormation.substitute substitution)
        domainResult.sourceFormationResult.semanticType)
      (targetResult.extend (typeWellFormed := domainFormation)
        domainResult.targetFormationResult.semanticType) :=
  IncDepRawSubstitutionSemanticResult.liftFiber substitutionResult
    domainResult.targetFormationResult domainResult.sourceFormationResult
    domainResult.semanticFiberEquivalence

noncomputable def IncDepRawFormationSubstitutionFiberResult.instantiateFiberEquivalence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (sourceTerm : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetTerm : IncTerm domainResult.targetFormationResult.semanticType)
    (termCoherence : domainResult.semanticFiberEquivalence.transport sourceTerm =
      targetTerm.substitute substitutionResult.semanticSubstitution) :
    IncTypeInContext.FiberEquiv
      (IncTypeInContext.instantiateFiber
        codomainResult.sourceFormationResult.semanticType sourceTerm)
      ((IncTypeInContext.instantiateFiber
        codomainResult.targetFormationResult.semanticType targetTerm).reindex
          substitutionResult.semanticSubstitution) where
  fiberEquiv := fun assignment =>
    let codomainEquivalence :=
      codomainResult.semanticFiberEquivalence.fiberEquiv
        ⟨assignment, sourceTerm assignment⟩
    let endpointCoherence :
        (domainResult.semanticFiberEquivalence.fiberEquiv assignment).forward
            (sourceTerm assignment) =
          targetTerm (substitutionResult.semanticSubstitution assignment) :=
      congrFun termCoherence assignment
    codomainEquivalence.trans (IncFiberEquiv.ofEq
      (congrArg
        (fun value => codomainResult.targetFormationResult.semanticType
          ⟨substitutionResult.semanticSubstitution assignment, value⟩)
        endpointCoherence))

theorem IncDepRawFormationSubstitutionFiberResult.instantiateFiberEquivalence_forward
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (sourceTerm : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetTerm : IncTerm domainResult.targetFormationResult.semanticType)
    (termCoherence : domainResult.semanticFiberEquivalence.transport sourceTerm =
      targetTerm.substitute substitutionResult.semanticSubstitution)
    (assignment : sourceResult.semanticContext.Assignment)
    (value : codomainResult.sourceFormationResult.semanticType
      ⟨assignment, sourceTerm assignment⟩) :
    ((domainResult.instantiateFiberEquivalence codomainResult sourceTerm
      targetTerm termCoherence).fiberEquiv assignment).forward value =
      Eq.mp (congrArg
        (fun endpoint => codomainResult.targetFormationResult.semanticType
          ⟨substitutionResult.semanticSubstitution assignment, endpoint⟩)
        (congrFun termCoherence assignment))
        ((codomainResult.semanticFiberEquivalence.fiberEquiv
          ⟨assignment, sourceTerm assignment⟩).forward value) := by
  simp [IncDepRawFormationSubstitutionFiberResult.instantiateFiberEquivalence,
    IncFiberEquiv.trans, IncFiberEquiv.ofEq_forward]

structure IncDepRawAlignedFormationSubstitutionFiberResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  targetFormationResult : IncDepRawFormationSemanticResult targetFormation
    targetResult
  sourceFormationResult : IncDepRawFormationSemanticResult
    (targetFormation.substitute substitution) sourceResult
  sourceCanonical : IncTypeInContext sourceResult.semanticContext
  targetCanonical : IncTypeInContext targetResult.semanticContext
  sourceAlignment : sourceFormationResult.semanticType = sourceCanonical
  targetAlignment : targetFormationResult.semanticType = targetCanonical
  canonicalEquivalence : IncTypeInContext.FiberEquiv sourceCanonical
    (targetCanonical.reindex substitutionResult.semanticSubstitution)

noncomputable def IncDepRawAlignedFormationSubstitutionFiberResult.toFormationFiberResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult where
  targetFormationResult := result.targetFormationResult
  sourceFormationResult := result.sourceFormationResult
  semanticFiberEquivalence :=
    (IncTypeInContext.FiberEquiv.ofEq result.sourceAlignment).trans
      (result.canonicalEquivalence.trans
        (IncTypeInContext.FiberEquiv.ofEq
          (congrArg
            (fun family => family.reindex
              substitutionResult.semanticSubstitution)
            result.targetAlignment.symm)))

noncomputable def IncDepRawAlignedFormationSubstitutionFiberResult.instantiate
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution)
    (targetInstantiatedResult : IncDepRawFormationSemanticResult
      instantiatedFormation targetResult)
    (sourceInstantiatedResult : IncDepRawFormationSemanticResult
      (instantiatedFormation.substitute substitution) sourceResult)
    (sourceAlignment : sourceInstantiatedResult.semanticType =
      IncTypeInContext.instantiateFiber
        codomainResult.sourceFormationResult.semanticType sourceArgument)
    (targetAlignment : targetInstantiatedResult.semanticType =
      IncTypeInContext.instantiateFiber
        codomainResult.targetFormationResult.semanticType targetArgument) :
    IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult where
  targetFormationResult := targetInstantiatedResult
  sourceFormationResult := sourceInstantiatedResult
  sourceCanonical := IncTypeInContext.instantiateFiber
    codomainResult.sourceFormationResult.semanticType sourceArgument
  targetCanonical := IncTypeInContext.instantiateFiber
    codomainResult.targetFormationResult.semanticType targetArgument
  sourceAlignment := sourceAlignment
  targetAlignment := targetAlignment
  canonicalEquivalence := domainResult.instantiateFiberEquivalence
    codomainResult sourceArgument targetArgument argumentCoherence

noncomputable def IncDepRawFormationSubstitutionFiberResult.instantiate
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution)
    (targetInstantiatedResult : IncDepRawFormationSemanticResult
      instantiatedFormation targetResult)
    (sourceInstantiatedResult : IncDepRawFormationSemanticResult
      (instantiatedFormation.substitute substitution) sourceResult)
    (sourceAlignment : sourceInstantiatedResult.semanticType =
      IncTypeInContext.instantiateFiber
        codomainResult.sourceFormationResult.semanticType sourceArgument)
    (targetAlignment : targetInstantiatedResult.semanticType =
      IncTypeInContext.instantiateFiber
        codomainResult.targetFormationResult.semanticType targetArgument) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult :=
  (IncDepRawAlignedFormationSubstitutionFiberResult.instantiate
    domainResult codomainResult sourceArgument targetArgument argumentCoherence
    targetInstantiatedResult sourceInstantiatedResult sourceAlignment
    targetAlignment).toFormationFiberResult

noncomputable def IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult where
  targetFormationResult :=
    { semanticType := IncTypeInContext.instantiateFiber
        codomainResult.targetFormationResult.semanticType targetArgument }
  sourceFormationResult :=
    { semanticType := IncTypeInContext.instantiateFiber
        codomainResult.sourceFormationResult.semanticType sourceArgument }
  semanticFiberEquivalence := domainResult.instantiateFiberEquivalence
    codomainResult sourceArgument targetArgument argumentCoherence

structure IncDepRawPiFormationSubstitutionFiberResult
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  domainResult : IncDepRawFormationSubstitutionFiberResult
    (targetFormation := domainFormation) substitutionResult
  targetCodomainResult : IncDepRawFormationSemanticResult codomainFormation
    (targetResult.extend (typeWellFormed := domainFormation)
      domainResult.targetFormationResult.semanticType)
  sourceCodomainResult : IncDepRawFormationSemanticResult
    (codomainFormation.substitute (substitution.lift domain))
    (sourceResult.extend
      (typeWellFormed := domainFormation.substitute substitution)
      domainResult.sourceFormationResult.semanticType)
  fiberEquiv : ∀ assignment,
    IncDependentPiFiberEquiv
      (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
      (fun value => sourceCodomainResult.semanticType ⟨assignment, value⟩)
      (fun value => targetCodomainResult.semanticType
        ⟨substitutionResult.semanticSubstitution assignment, value⟩)

noncomputable def IncDepRawPiFormationSubstitutionFiberResult.ofCodomainResult
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (fiberEquiv : ∀ assignment,
      IncDependentPiFiberEquiv
        (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
        (fun value => codomainResult.sourceFormationResult.semanticType
          ⟨assignment, value⟩)
        (fun value => codomainResult.targetFormationResult.semanticType
          ⟨substitutionResult.semanticSubstitution assignment, value⟩)) :
    IncDepRawPiFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult where
  domainResult := domainResult
  targetCodomainResult := codomainResult.targetFormationResult
  sourceCodomainResult := codomainResult.sourceFormationResult
  fiberEquiv := fiberEquiv

noncomputable def IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (assignment : sourceResult.semanticContext.Assignment) :
    IncDependentFiberEquiv
      (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
      (fun value => codomainResult.sourceFormationResult.semanticType
        ⟨assignment, value⟩)
      (fun value => codomainResult.targetFormationResult.semanticType
        ⟨substitutionResult.semanticSubstitution assignment, value⟩) where
  codomainEquiv := fun value =>
    codomainResult.semanticFiberEquivalence.fiberEquiv ⟨assignment, value⟩

structure IncDepRawPiSubstitutionCoherence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution) where
  backward_forward : ∀ assignment function,
    (IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
      domainResult codomainResult assignment).piBackward
      ((IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).piForward function) = function
  forward_backward : ∀ assignment function,
    (IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
      domainResult codomainResult assignment).piForward
      ((IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).piBackward function) = function
  forward_apply : ∀ assignment sourceFunction sourceArgument,
    ((IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
      domainResult codomainResult assignment).codomainEquiv
        sourceArgument).forward (sourceFunction sourceArgument) =
    (IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
      domainResult codomainResult assignment).piForward sourceFunction
        ((domainResult.semanticFiberEquivalence.fiberEquiv assignment).forward
          sourceArgument)

noncomputable def IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawPiSubstitutionCoherence domainResult codomainResult) :
    IncDepRawPiFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult :=
  IncDepRawPiFormationSubstitutionFiberResult.ofCodomainResult
    domainResult codomainResult (fun assignment =>
      { dependentEquiv :=
          IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
            domainResult codomainResult assignment
        backward_forward := coherence.backward_forward assignment
        forward_backward := coherence.forward_backward assignment })

noncomputable def IncDepRawPiFormationSubstitutionFiberResult.ofCodomainCoherence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (backward_forward : ∀ assignment function,
      (IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).piBackward
        ((IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
          domainResult codomainResult assignment).piForward function) = function)
    (forward_backward : ∀ assignment function,
      (IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).piForward
        ((IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
          domainResult codomainResult assignment).piBackward function) = function) :
    IncDepRawPiFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult :=
  IncDepRawPiFormationSubstitutionFiberResult.ofCodomainResult
    domainResult codomainResult (fun assignment =>
      { dependentEquiv :=
          IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
            domainResult codomainResult assignment
        backward_forward := backward_forward assignment
        forward_backward := forward_backward assignment })

noncomputable def IncDepRawPiFormationSubstitutionFiberResult.piFiberEquivalence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawPiFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult) :
    IncTypeInContext.FiberEquiv
      (IncPiType result.domainResult.sourceFormationResult.semanticType
        result.sourceCodomainResult.semanticType)
      ((IncPiType result.domainResult.targetFormationResult.semanticType
        result.targetCodomainResult.semanticType).reindex
          substitutionResult.semanticSubstitution) where
  fiberEquiv := fun assignment => (result.fiberEquiv assignment).toFiberEquiv

noncomputable def IncDepRawPiFormationSubstitutionFiberResult.toFormationFiberResult
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawPiFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.pi domainFormation codomainFormation)
      substitutionResult where
  targetFormationResult := IncDepRawFormationSemanticResult.pi
    result.domainResult.targetFormationResult result.targetCodomainResult
  sourceFormationResult := IncDepRawFormationSemanticResult.pi
    result.domainResult.sourceFormationResult result.sourceCodomainResult
  semanticFiberEquivalence := result.piFiberEquivalence

noncomputable def IncDepRawFormationSubstitutionFiberResult.pi
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (fiberEquiv : ∀ assignment,
      IncDependentPiFiberEquiv
        (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
        (fun value => codomainResult.sourceFormationResult.semanticType
          ⟨assignment, value⟩)
        (fun value => codomainResult.targetFormationResult.semanticType
          ⟨substitutionResult.semanticSubstitution assignment, value⟩)) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.pi domainFormation codomainFormation)
      substitutionResult :=
  (IncDepRawPiFormationSubstitutionFiberResult.ofCodomainResult
    domainResult codomainResult fiberEquiv).toFormationFiberResult

noncomputable def IncDepRawFormationSubstitutionFiberResult.piCoherent
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawPiSubstitutionCoherence domainResult codomainResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.pi domainFormation codomainFormation)
      substitutionResult :=
  (IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
    domainResult codomainResult coherence).toFormationFiberResult

structure IncDepRawSigmaFormationSubstitutionFiberResult
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  domainResult : IncDepRawFormationSubstitutionFiberResult
    (targetFormation := domainFormation) substitutionResult
  targetCodomainResult : IncDepRawFormationSemanticResult codomainFormation
    (targetResult.extend (typeWellFormed := domainFormation)
      domainResult.targetFormationResult.semanticType)
  sourceCodomainResult : IncDepRawFormationSemanticResult
    (codomainFormation.substitute (substitution.lift domain))
    (sourceResult.extend
      (typeWellFormed := domainFormation.substitute substitution)
      domainResult.sourceFormationResult.semanticType)
  fiberEquiv : ∀ assignment,
    IncDependentSigmaFiberEquiv
      (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
      (fun value => sourceCodomainResult.semanticType ⟨assignment, value⟩)
      (fun value => targetCodomainResult.semanticType
        ⟨substitutionResult.semanticSubstitution assignment, value⟩)

noncomputable def IncDepRawSigmaFormationSubstitutionFiberResult.ofCodomainResult
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (fiberEquiv : ∀ assignment,
      IncDependentSigmaFiberEquiv
        (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
        (fun value => codomainResult.sourceFormationResult.semanticType
          ⟨assignment, value⟩)
        (fun value => codomainResult.targetFormationResult.semanticType
          ⟨substitutionResult.semanticSubstitution assignment, value⟩)) :
    IncDepRawSigmaFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult where
  domainResult := domainResult
  targetCodomainResult := codomainResult.targetFormationResult
  sourceCodomainResult := codomainResult.sourceFormationResult
  fiberEquiv := fiberEquiv

noncomputable def IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (assignment : sourceResult.semanticContext.Assignment) :
    IncDependentFiberEquiv
      (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
      (fun value => codomainResult.sourceFormationResult.semanticType
        ⟨assignment, value⟩)
      (fun value => codomainResult.targetFormationResult.semanticType
        ⟨substitutionResult.semanticSubstitution assignment, value⟩) where
  codomainEquiv := fun value =>
    codomainResult.semanticFiberEquivalence.fiberEquiv ⟨assignment, value⟩

structure IncDepRawSigmaSubstitutionCoherence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution) where
  backward_forward : ∀ assignment value,
    (IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
      domainResult codomainResult assignment).sigmaBackward
      ((IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).sigmaForward value) = value
  forward_backward : ∀ assignment value,
    (IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
      domainResult codomainResult assignment).sigmaForward
      ((IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).sigmaBackward value) = value

noncomputable def IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawSigmaSubstitutionCoherence domainResult codomainResult) :
    IncDepRawSigmaFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult :=
  IncDepRawSigmaFormationSubstitutionFiberResult.ofCodomainResult
    domainResult codomainResult (fun assignment =>
      { dependentEquiv :=
          IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
            domainResult codomainResult assignment
        backward_forward := coherence.backward_forward assignment
        forward_backward := coherence.forward_backward assignment })

structure IncDepRawSubstitutionFiberModel where
  baseModel : Nat → Type u
  typingFormation : ∀
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type},
    IncDepRawTypingSemanticReady typing →
      Sigma fun formation : IncDepRawWellFormed context type =>
        IncDepRawFormationSemanticReady formation
  piCoherence : ∀
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution),
    IncDepRawPiSubstitutionCoherence domainResult codomainResult
  sigmaCoherence : ∀
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution),
    IncDepRawSigmaSubstitutionCoherence domainResult codomainResult

def IncDepRawSubstitutionFiberModel.formationForTyping
    (model : IncDepRawSubstitutionFiberModel.{u})
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    (ready : IncDepRawTypingSemanticReady typing) :
    Sigma fun formation : IncDepRawWellFormed context type =>
      IncDepRawFormationSemanticReady formation :=
  model.typingFormation ready

def IncDepRawSubstitutionFiberModel.base
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {index : Nat}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.base (index := index))
      substitutionResult :=
  IncDepRawFormationSubstitutionFiberResult.base substitutionResult model.baseModel

def IncDepRawSubstitutionFiberModel.unit
    (_model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.unit) substitutionResult :=
  IncDepRawFormationSubstitutionFiberResult.unit substitutionResult

noncomputable def IncDepRawSubstitutionFiberModel.pi
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.pi domainFormation codomainFormation)
      substitutionResult :=
  (IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
    domainResult codomainResult (model.piCoherence domainResult codomainResult))
      |>.toFormationFiberResult

noncomputable def IncDepRawSigmaFormationSubstitutionFiberResult.ofCodomainCoherence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (backward_forward : ∀ assignment value,
      (IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).sigmaBackward
        ((IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
          domainResult codomainResult assignment).sigmaForward value) = value)
    (forward_backward : ∀ assignment value,
      (IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
        domainResult codomainResult assignment).sigmaForward
        ((IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
          domainResult codomainResult assignment).sigmaBackward value) = value) :
    IncDepRawSigmaFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult :=
  IncDepRawSigmaFormationSubstitutionFiberResult.ofCodomainResult
    domainResult codomainResult (fun assignment =>
      { dependentEquiv :=
          IncDepRawSigmaFormationSubstitutionFiberResult.dependentEquiv
            domainResult codomainResult assignment
        backward_forward := backward_forward assignment
        forward_backward := forward_backward assignment })

noncomputable def IncDepRawSigmaFormationSubstitutionFiberResult.sigmaFiberEquivalence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawSigmaFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult) :
    IncTypeInContext.FiberEquiv
      (IncSigmaType result.domainResult.sourceFormationResult.semanticType
        result.sourceCodomainResult.semanticType)
      ((IncSigmaType result.domainResult.targetFormationResult.semanticType
        result.targetCodomainResult.semanticType).reindex
          substitutionResult.semanticSubstitution) where
  fiberEquiv := fun assignment => (result.fiberEquiv assignment).toFiberEquiv

noncomputable def IncDepRawSigmaFormationSubstitutionFiberResult.toFormationFiberResult
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawSigmaFormationSubstitutionFiberResult
      (domainFormation := domainFormation)
      (codomainFormation := codomainFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.sigma domainFormation codomainFormation)
      substitutionResult where
  targetFormationResult := IncDepRawFormationSemanticResult.sigma
    result.domainResult.targetFormationResult result.targetCodomainResult
  sourceFormationResult := IncDepRawFormationSemanticResult.sigma
    result.domainResult.sourceFormationResult result.sourceCodomainResult
  semanticFiberEquivalence := result.sigmaFiberEquivalence

noncomputable def IncDepRawFormationSubstitutionFiberResult.sigma
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (fiberEquiv : ∀ assignment,
      IncDependentSigmaFiberEquiv
        (domainResult.semanticFiberEquivalence.fiberEquiv assignment)
        (fun value => codomainResult.sourceFormationResult.semanticType
          ⟨assignment, value⟩)
        (fun value => codomainResult.targetFormationResult.semanticType
          ⟨substitutionResult.semanticSubstitution assignment, value⟩)) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.sigma domainFormation codomainFormation)
      substitutionResult :=
  (IncDepRawSigmaFormationSubstitutionFiberResult.ofCodomainResult
    domainResult codomainResult fiberEquiv).toFormationFiberResult

noncomputable def IncDepRawFormationSubstitutionFiberResult.sigmaCoherent
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawSigmaSubstitutionCoherence domainResult codomainResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.sigma domainFormation codomainFormation)
      substitutionResult :=
  (IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
    domainResult codomainResult coherence).toFormationFiberResult

noncomputable def IncDepRawSubstitutionFiberModel.sigma
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.sigma domainFormation codomainFormation)
      substitutionResult :=
  IncDepRawFormationSubstitutionFiberResult.sigmaCoherent domainResult
    codomainResult (model.sigmaCoherence domainResult codomainResult)

inductive IncDepRawNonIdentityFormationReady :
    {context : List IncDepRawType} → {type : IncDepRawType} →
    IncDepRawWellFormed context type → Type
  | base {context index} :
      IncDepRawNonIdentityFormationReady
        (IncDepRawWellFormed.base (context := context) (index := index))
  | unit {context} :
      IncDepRawNonIdentityFormationReady
        (IncDepRawWellFormed.unit (context := context))
  | pi {context domain codomain}
      {domainFormation : IncDepRawWellFormed context domain}
      {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
      IncDepRawNonIdentityFormationReady domainFormation →
      IncDepRawNonIdentityFormationReady codomainFormation →
      IncDepRawNonIdentityFormationReady
        (IncDepRawWellFormed.pi domainFormation codomainFormation)
  | sigma {context domain codomain}
      {domainFormation : IncDepRawWellFormed context domain}
      {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
      IncDepRawNonIdentityFormationReady domainFormation →
      IncDepRawNonIdentityFormationReady codomainFormation →
      IncDepRawNonIdentityFormationReady
        (IncDepRawWellFormed.sigma domainFormation codomainFormation)

mutual
  inductive IncDepRawFormationDispatchReady :
      {context : List IncDepRawType} → {type : IncDepRawType} →
      IncDepRawWellFormed context type → Type
    | base {context index} : IncDepRawFormationDispatchReady
        (IncDepRawWellFormed.base (context := context) (index := index))
    | unit {context} : IncDepRawFormationDispatchReady
        (IncDepRawWellFormed.unit (context := context))
    | pi {context domain codomain}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationDispatchReady domainFormation →
        IncDepRawFormationDispatchReady codomainFormation →
        IncDepRawFormationDispatchReady
          (IncDepRawWellFormed.pi domainFormation codomainFormation)
    | sigma {context domain codomain}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain} :
        IncDepRawFormationDispatchReady domainFormation →
        IncDepRawFormationDispatchReady codomainFormation →
        IncDepRawFormationDispatchReady
          (IncDepRawWellFormed.sigma domainFormation codomainFormation)
    | identity {context type left right}
        {typeFormation : IncDepRawWellFormed context type}
        {leftTyping : IncDepRawHasType context left type}
        {rightTyping : IncDepRawHasType context right type} :
        IncDepRawFormationDispatchReady typeFormation →
        IncDepRawTypingDispatchReady leftTyping →
        IncDepRawTypingDispatchReady rightTyping →
        IncDepRawFormationDispatchReady
          (IncDepRawWellFormed.identity typeFormation leftTyping rightTyping)

  inductive IncDepRawTypingDispatchReady :
      {context : List IncDepRawType} → {term : IncDepRawTerm} →
      {type : IncDepRawType} → IncDepRawHasType context term type → Type
    | varRule {context position type}
        {lookup : IncDepRawLookup context position type}
        {typeFormation : IncDepRawWellFormed context type} :
        IncDepRawFormationDispatchReady typeFormation →
        IncDepRawTypingDispatchReady (IncDepRawHasType.varRule lookup)
    | unitRule {context} : IncDepRawTypingDispatchReady
        (IncDepRawHasType.unitRule (context := context))
    | lambdaRule {context domain codomain body}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {bodyTyping : IncDepRawHasType (domain :: context) body codomain} :
        IncDepRawFormationDispatchReady domainFormation →
        IncDepRawFormationDispatchReady codomainFormation →
        IncDepRawTypingDispatchReady bodyTyping →
        IncDepRawTypingDispatchReady
          (IncDepRawHasType.lambdaRule domainFormation bodyTyping)
    | applyRule {context domain codomain function argument}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {functionTyping : IncDepRawHasType context function (.pi domain codomain)}
        {argumentTyping : IncDepRawHasType context argument domain}
        {resultFormation : IncDepRawWellFormed context
          (codomain.instantiate argument)} :
        IncDepRawFormationDispatchReady domainFormation →
        IncDepRawFormationDispatchReady codomainFormation →
        IncDepRawFormationDispatchReady resultFormation →
        IncDepRawTypingDispatchReady functionTyping →
        IncDepRawTypingDispatchReady argumentTyping →
        IncDepRawTypingDispatchReady
          (IncDepRawHasType.applyRule functionTyping argumentTyping)
    | pairRule {context domain codomain first second}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {firstTyping : IncDepRawHasType context first domain}
        {secondTyping : IncDepRawHasType context second
          (codomain.instantiate first)}
        {resultFormation : IncDepRawWellFormed context
          (codomain.instantiate first)} :
        IncDepRawFormationDispatchReady domainFormation →
        IncDepRawFormationDispatchReady codomainFormation →
        IncDepRawFormationDispatchReady resultFormation →
        IncDepRawTypingDispatchReady firstTyping →
        IncDepRawTypingDispatchReady secondTyping →
        IncDepRawTypingDispatchReady
          (IncDepRawHasType.pairRule firstTyping secondTyping)
    | firstRule {context domain codomain pair}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)} :
        IncDepRawFormationDispatchReady domainFormation →
        IncDepRawFormationDispatchReady codomainFormation →
        IncDepRawTypingDispatchReady pairTyping →
        IncDepRawTypingDispatchReady (IncDepRawHasType.firstRule pairTyping)
    | secondRule {context domain codomain pair}
        {domainFormation : IncDepRawWellFormed context domain}
        {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
        {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
        {resultFormation : IncDepRawWellFormed context
          (codomain.instantiate (.first pair))} :
        IncDepRawFormationDispatchReady domainFormation →
        IncDepRawFormationDispatchReady codomainFormation →
        IncDepRawFormationDispatchReady resultFormation →
        IncDepRawTypingDispatchReady pairTyping →
        IncDepRawTypingDispatchReady (IncDepRawHasType.secondRule pairTyping)
    | reflRule {context type term}
        {typeFormation : IncDepRawWellFormed context type}
        {termTyping : IncDepRawHasType context term type} :
        IncDepRawFormationDispatchReady typeFormation →
        IncDepRawTypingDispatchReady termTyping →
        IncDepRawTypingDispatchReady (IncDepRawHasType.reflRule termTyping)
end

mutual
  def IncDepRawCoherentFormationDispatchReady.toDispatchReady
      {context : List IncDepRawType} {type : IncDepRawType}
      {formation : IncDepRawWellFormed context type}
      (ready : IncDepRawCoherentFormationDispatchReady formation) :
      IncDepRawFormationDispatchReady formation :=
    match ready with
    | .base => .base
    | .unit => .unit
    | .pi domainReady codomainReady =>
        .pi domainReady.toDispatchReady codomainReady.toDispatchReady
    | .sigma domainReady codomainReady =>
        .sigma domainReady.toDispatchReady codomainReady.toDispatchReady
    | .identity typeReady leftReady rightReady =>
        .identity typeReady.toDispatchReady leftReady.toDispatchPair.1
          rightReady.toDispatchPair.1

  def IncDepRawCoherentTypingDispatchReady.toDispatchPair
      {context : List IncDepRawType} {term : IncDepRawTerm}
      {type : IncDepRawType} {typing : IncDepRawHasType context term type}
      {formation : IncDepRawWellFormed context type}
      (ready : IncDepRawCoherentTypingDispatchReady typing formation) :
      IncDepRawTypingDispatchReady typing ×
        IncDepRawFormationDispatchReady formation :=
    match ready with
    | .varRule typeReady =>
        ⟨.varRule typeReady.toDispatchReady, typeReady.toDispatchReady⟩
    | .unitRule => ⟨.unitRule, .unit⟩
    | .lambdaRule domainReady bodyReady =>
        let bodyPair := bodyReady.toDispatchPair
        ⟨.lambdaRule domainReady.toDispatchReady bodyPair.2 bodyPair.1,
          .pi domainReady.toDispatchReady bodyPair.2⟩
    | .applyRule domainReady codomainReady resultReady functionReady
        argumentReady =>
        ⟨.applyRule domainReady.toDispatchReady codomainReady.toDispatchReady
          resultReady.toDispatchReady functionReady.toDispatchPair.1
          argumentReady.toDispatchPair.1,
          resultReady.toDispatchReady⟩
    | .pairRule domainReady codomainReady resultReady firstReady secondReady =>
        ⟨.pairRule domainReady.toDispatchReady codomainReady.toDispatchReady
          resultReady.toDispatchReady firstReady.toDispatchPair.1
          secondReady.toDispatchPair.1,
          .sigma domainReady.toDispatchReady codomainReady.toDispatchReady⟩
    | .firstRule domainReady codomainReady pairReady =>
        ⟨.firstRule domainReady.toDispatchReady codomainReady.toDispatchReady
          pairReady.toDispatchPair.1,
          domainReady.toDispatchReady⟩
    | .secondRule domainReady codomainReady resultReady pairReady =>
        ⟨.secondRule domainReady.toDispatchReady codomainReady.toDispatchReady
          resultReady.toDispatchReady pairReady.toDispatchPair.1,
          resultReady.toDispatchReady⟩
    | .reflRule typeReady termReady =>
        ⟨.reflRule typeReady.toDispatchReady termReady.toDispatchPair.1,
          .identity typeReady.toDispatchReady termReady.toDispatchPair.1
            termReady.toDispatchPair.1⟩
end

def IncDepRawCoherentTypingDispatchReady.toDispatchReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation) :
    IncDepRawTypingDispatchReady typing :=
  ready.toDispatchPair.1

def IncDepRawCoherentTypingDispatchReady.formationDispatchReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation) :
    IncDepRawFormationDispatchReady formation :=
  ready.toDispatchPair.2

def IncDepRawCoherentTypingDispatchReady.formationReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation) :
    IncDepRawCoherentFormationDispatchReady formation :=
  match ready with
  | .varRule typeReady => typeReady
  | .unitRule => .unit
  | .lambdaRule domainReady bodyReady => .pi domainReady bodyReady.formationReady
  | .applyRule _ _ resultReady _ _ => resultReady
  | .pairRule domainReady codomainReady _ _ _ => .sigma domainReady codomainReady
  | .firstRule domainReady _ _ => domainReady
  | .secondRule _ _ resultReady _ => resultReady
  | .reflRule typeReady termReady => .identity typeReady termReady termReady

structure IncDepRawStrictTypingDispatchReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} (typing : IncDepRawHasType context term type)
    {formation : IncDepRawWellFormed context type}
    (formationReady : IncDepRawCoherentFormationDispatchReady formation) where
  ready : IncDepRawCoherentTypingDispatchReady typing formation
  formationReady_eq : ready.formationReady = formationReady

def IncDepRawStrictTypingDispatchReady.ofCoherent
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawCoherentTypingDispatchReady typing formation) :
    IncDepRawStrictTypingDispatchReady typing ready.formationReady where
  ready := ready
  formationReady_eq := rfl

def IncDepRawStrictTypingDispatchReady.toCoherent
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    {formationReady : IncDepRawCoherentFormationDispatchReady formation}
    (ready : IncDepRawStrictTypingDispatchReady typing formationReady) :
    IncDepRawCoherentTypingDispatchReady typing formation :=
  ready.ready

def IncDepRawStrictTypingDispatchReady.toDispatchReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    {formationReady : IncDepRawCoherentFormationDispatchReady formation}
    (ready : IncDepRawStrictTypingDispatchReady typing formationReady) :
    IncDepRawTypingDispatchReady typing :=
  ready.ready.toDispatchReady

def IncDepRawStrictTypingDispatchReady.formationDispatchReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    {formationReady : IncDepRawCoherentFormationDispatchReady formation}
    (_ready : IncDepRawStrictTypingDispatchReady typing formationReady) :
    IncDepRawFormationDispatchReady formation :=
  formationReady.toDispatchReady

def IncDepRawStrictTypingDispatchReady.castFormationReady
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {formation : IncDepRawWellFormed context type}
    {firstReady secondReady : IncDepRawCoherentFormationDispatchReady formation}
    (ready : IncDepRawStrictTypingDispatchReady typing firstReady)
    (readinessEq : firstReady = secondReady) :
    IncDepRawStrictTypingDispatchReady typing secondReady := by
  cases readinessEq
  exact ready

def IncDepRawCoherentFormationDispatchReady.identityStrict
    {context : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {leftTyping : IncDepRawHasType context left type}
    {rightTyping : IncDepRawHasType context right type}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (leftReady : IncDepRawStrictTypingDispatchReady leftTyping typeReady)
    (rightReady : IncDepRawStrictTypingDispatchReady rightTyping typeReady) :
    IncDepRawCoherentFormationDispatchReady
      (IncDepRawWellFormed.identity typeFormation leftTyping rightTyping) :=
  IncDepRawCoherentFormationDispatchReady.identity typeReady leftReady.ready
    rightReady.ready

def IncDepRawStrictTypingDispatchReady.varRule
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation) :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.varRule lookup) typeReady where
  ready := IncDepRawCoherentTypingDispatchReady.varRule typeReady
  formationReady_eq := rfl

def IncDepRawStrictTypingDispatchReady.unitRule
    {context : List IncDepRawType} :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.unitRule (context := context))
      (IncDepRawCoherentFormationDispatchReady.unit (context := context)) where
  ready := IncDepRawCoherentTypingDispatchReady.unitRule
  formationReady_eq := rfl

def IncDepRawStrictTypingDispatchReady.lambdaRule
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (bodyReady : IncDepRawStrictTypingDispatchReady bodyTyping codomainReady) :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.lambdaRule domainFormation bodyTyping)
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady) := by
  cases bodyReady with
  | mk ready readinessEq =>
      cases readinessEq
      exact
        { ready := IncDepRawCoherentTypingDispatchReady.lambdaRule
            domainReady ready
          formationReady_eq := rfl }

def IncDepRawStrictTypingDispatchReady.applyRule
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {resultFormation : IncDepRawWellFormed context
      (codomain.instantiate argument)}
    {functionTyping : IncDepRawHasType context function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType context argument domain}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (resultReady : IncDepRawCoherentFormationDispatchReady resultFormation)
    (functionReady : IncDepRawStrictTypingDispatchReady functionTyping
      (IncDepRawCoherentFormationDispatchReady.pi domainReady codomainReady))
    (argumentReady : IncDepRawStrictTypingDispatchReady argumentTyping
      domainReady) :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.applyRule functionTyping argumentTyping) resultReady where
  ready := IncDepRawCoherentTypingDispatchReady.applyRule domainReady
    codomainReady resultReady functionReady.ready argumentReady.ready
  formationReady_eq := rfl

def IncDepRawStrictTypingDispatchReady.pairRule
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {resultFormation : IncDepRawWellFormed context
      (codomain.instantiate first)}
    {firstTyping : IncDepRawHasType context first domain}
    {secondTyping : IncDepRawHasType context second (codomain.instantiate first)}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (resultReady : IncDepRawCoherentFormationDispatchReady resultFormation)
    (firstReady : IncDepRawStrictTypingDispatchReady firstTyping domainReady)
    (secondReady : IncDepRawStrictTypingDispatchReady secondTyping resultReady) :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.pairRule firstTyping secondTyping)
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady) where
  ready := IncDepRawCoherentTypingDispatchReady.pairRule domainReady
    codomainReady resultReady firstReady.ready secondReady.ready
  formationReady_eq := rfl

def IncDepRawStrictTypingDispatchReady.firstRule
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (pairReady : IncDepRawStrictTypingDispatchReady pairTyping
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady)) :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.firstRule pairTyping) domainReady where
  ready := IncDepRawCoherentTypingDispatchReady.firstRule domainReady
    codomainReady pairReady.ready
  formationReady_eq := rfl

def IncDepRawStrictTypingDispatchReady.secondRule
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {resultFormation : IncDepRawWellFormed context
      (codomain.instantiate (.first pair))}
    {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (resultReady : IncDepRawCoherentFormationDispatchReady resultFormation)
    (pairReady : IncDepRawStrictTypingDispatchReady pairTyping
      (IncDepRawCoherentFormationDispatchReady.sigma domainReady codomainReady)) :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.secondRule pairTyping) resultReady where
  ready := IncDepRawCoherentTypingDispatchReady.secondRule domainReady
    codomainReady resultReady pairReady.ready
  formationReady_eq := rfl

def IncDepRawStrictTypingDispatchReady.reflRule
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm}
    {typeFormation : IncDepRawWellFormed context type}
    {termTyping : IncDepRawHasType context term type}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (termReady : IncDepRawStrictTypingDispatchReady termTyping typeReady) :
    IncDepRawStrictTypingDispatchReady
      (IncDepRawHasType.reflRule termTyping)
      (IncDepRawCoherentFormationDispatchReady.identityStrict typeReady
        termReady termReady) where
  ready := IncDepRawCoherentTypingDispatchReady.reflRule typeReady
    termReady.ready
  formationReady_eq := rfl

mutual
  noncomputable def IncDepRawFormationDispatchReady.toSemanticReady
      {context : List IncDepRawType} {type : IncDepRawType}
      {formation : IncDepRawWellFormed context type}
      (ready : IncDepRawFormationDispatchReady formation) :
      IncDepRawFormationSemanticReady formation :=
    match ready with
    | .base => .base
    | .unit => .unit
    | .pi domainReady codomainReady =>
        .pi domainReady.toSemanticReady codomainReady.toSemanticReady
    | .sigma domainReady codomainReady =>
        .sigma domainReady.toSemanticReady codomainReady.toSemanticReady
    | .identity typeReady leftReady rightReady =>
        .identity typeReady.toSemanticReady leftReady.toSemanticReady
          rightReady.toSemanticReady

  noncomputable def IncDepRawTypingDispatchReady.toSemanticReady
      {context : List IncDepRawType} {term : IncDepRawTerm}
      {type : IncDepRawType} {typing : IncDepRawHasType context term type}
      (ready : IncDepRawTypingDispatchReady typing) :
      IncDepRawTypingSemanticReady typing :=
    match ready with
    | .varRule typeReady => .varRule typeReady.toSemanticReady
    | .unitRule => .unitRule
    | .lambdaRule domainReady codomainReady bodyReady =>
        .lambdaRule domainReady.toSemanticReady codomainReady.toSemanticReady
          bodyReady.toSemanticReady
    | .applyRule domainReady codomainReady _ functionReady argumentReady =>
        .applyRule domainReady.toSemanticReady codomainReady.toSemanticReady
          functionReady.toSemanticReady argumentReady.toSemanticReady
    | .pairRule domainReady codomainReady _ firstReady secondReady =>
        .pairRule domainReady.toSemanticReady codomainReady.toSemanticReady
          firstReady.toSemanticReady secondReady.toSemanticReady
    | .firstRule domainReady codomainReady pairReady =>
        .firstRule domainReady.toSemanticReady codomainReady.toSemanticReady
          pairReady.toSemanticReady
    | .secondRule domainReady codomainReady _ pairReady =>
        .secondRule domainReady.toSemanticReady codomainReady.toSemanticReady
          pairReady.toSemanticReady
    | .reflRule typeReady termReady =>
        .reflRule typeReady.toSemanticReady termReady.toSemanticReady
end

noncomputable def IncDepRawNonIdentityFormationReady.toSemanticReady
    {context : List IncDepRawType} {type : IncDepRawType}
    {formation : IncDepRawWellFormed context type}
    (ready : IncDepRawNonIdentityFormationReady formation) :
    IncDepRawFormationSemanticReady formation := by
  induction ready with
  | base => exact IncDepRawFormationSemanticReady.base
  | unit => exact IncDepRawFormationSemanticReady.unit
  | pi _ _ domainIH codomainIH =>
      exact IncDepRawFormationSemanticReady.pi domainIH codomainIH
  | sigma _ _ domainIH codomainIH =>
      exact IncDepRawFormationSemanticReady.sigma domainIH codomainIH

noncomputable def IncDepRawNonIdentityFormationReady.dispatchSubstitution
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (model : IncDepRawSubstitutionFiberModel.{u})
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (ready : IncDepRawNonIdentityFormationReady targetFormation) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult := by
  induction ready generalizing source sourceWellFormed sourceResult with
  | base => exact model.base substitutionResult
  | unit => exact model.unit substitutionResult
  | pi domainReady codomainReady domainIH codomainIH =>
      let domainResult := domainIH substitutionResult
      let codomainResult := codomainIH domainResult.liftSubstitution
      exact model.pi domainResult codomainResult
  | sigma domainReady codomainReady domainIH codomainIH =>
      let domainResult := domainIH substitutionResult
      let codomainResult := codomainIH domainResult.liftSubstitution
      exact model.sigma domainResult codomainResult

inductive IncDepRawContextSemanticTree :
    {context : List IncDepRawType} →
    {wellFormed : IncDepRawContext.WellFormed context} →
    (result : IncDepRawContextSemanticResult.{u} wellFormed) → Type (u + 2)
  | empty : IncDepRawContextSemanticTree incDepRawEmptyContextSemantic
  | extend {context : List IncDepRawType} {type : IncDepRawType}
      {contextWellFormed : IncDepRawContext.WellFormed context}
      {typeWellFormed : IncDepRawWellFormed context type}
      {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
      (tail : IncDepRawContextSemanticTree contextResult)
      (head : IncDepRawFormationSemanticResult.{u} typeWellFormed contextResult) :
      IncDepRawContextSemanticTree
        (contextResult.extend (typeWellFormed := typeWellFormed)
          head.semanticType)

def incDepRawEmptyContextSemanticTree :
    IncDepRawContextSemanticTree incDepRawEmptyContextSemantic :=
  IncDepRawContextSemanticTree.empty

structure IncDepRawTypingSemanticResult
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} (typing : IncDepRawHasType context term type)
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed)
    (semanticType : IncTypeInContext contextResult.semanticContext) where
  semanticTerm : IncTerm semanticType

structure IncDepRawIdentityFormationSubstitutionFiberResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  typeResult : IncDepRawFormationSubstitutionFiberResult
    (targetFormation := typeFormation) substitutionResult
  targetLeft : IncDepRawTypingSemanticResult leftTyping targetResult
    typeResult.targetFormationResult.semanticType
  targetRight : IncDepRawTypingSemanticResult rightTyping targetResult
    typeResult.targetFormationResult.semanticType
  sourceLeft : IncDepRawTypingSemanticResult
    (leftTyping.substitute substitution) sourceResult
    typeResult.sourceFormationResult.semanticType
  sourceRight : IncDepRawTypingSemanticResult
    (rightTyping.substitute substitution) sourceResult
    typeResult.sourceFormationResult.semanticType
  leftCoherence : typeResult.semanticFiberEquivalence.transport sourceLeft.semanticTerm =
    targetLeft.semanticTerm.substitute substitutionResult.semanticSubstitution
  rightCoherence : typeResult.semanticFiberEquivalence.transport sourceRight.semanticTerm =
    targetRight.semanticTerm.substitute substitutionResult.semanticSubstitution

def IncDepRawIdentityFormationSubstitutionFiberResult.identityFiberEquivalence
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawIdentityFormationSubstitutionFiberResult
      (typeFormation := typeFormation) (leftTyping := leftTyping)
      (rightTyping := rightTyping) substitutionResult) :
    IncTypeInContext.FiberEquiv
      (IncIdentityType result.typeResult.sourceFormationResult.semanticType
        result.sourceLeft.semanticTerm result.sourceRight.semanticTerm)
      ((IncIdentityType result.typeResult.targetFormationResult.semanticType
        result.targetLeft.semanticTerm result.targetRight.semanticTerm).reindex
          substitutionResult.semanticSubstitution) := by
  rw [IncIdentityType.reindex]
  exact IncIdentityType.fiberEquivalence result.typeResult.semanticFiberEquivalence
    result.leftCoherence result.rightCoherence

noncomputable def IncDepRawIdentityFormationSubstitutionFiberResult.toFormationFiberResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawIdentityFormationSubstitutionFiberResult
      (typeFormation := typeFormation) (leftTyping := leftTyping)
      (rightTyping := rightTyping) substitutionResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.identity
        typeFormation leftTyping rightTyping) substitutionResult where
  targetFormationResult := IncDepRawFormationSemanticResult.identity
    result.typeResult.targetFormationResult
    result.targetLeft.semanticTerm result.targetRight.semanticTerm
  sourceFormationResult := IncDepRawFormationSemanticResult.identity
    result.typeResult.sourceFormationResult
    result.sourceLeft.semanticTerm result.sourceRight.semanticTerm
  semanticFiberEquivalence := result.identityFiberEquivalence

structure IncDepRawTypingSubstitutionFiberResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult) where
  targetTermResult : IncDepRawTypingSemanticResult targetTyping targetResult
    typeResult.targetFormationResult.semanticType
  sourceTermResult : IncDepRawTypingSemanticResult
    (targetTyping.substitute substitution) sourceResult
    typeResult.sourceFormationResult.semanticType
  semanticTerm_coherence :
    typeResult.semanticFiberEquivalence.transport sourceTermResult.semanticTerm =
      targetTermResult.semanticTerm.substitute
        substitutionResult.semanticSubstitution

structure IncDepRawFormationSubstitutionFiberRebase
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (left right : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult) where
  sourceEquivalence : IncTypeInContext.FiberEquiv
    left.sourceFormationResult.semanticType
    right.sourceFormationResult.semanticType
  targetEquivalence : IncTypeInContext.FiberEquiv
    left.targetFormationResult.semanticType
    right.targetFormationResult.semanticType
  naturality : ∀ term : IncTerm left.sourceFormationResult.semanticType,
    right.semanticFiberEquivalence.transport
        (sourceEquivalence.transport term) =
      (targetEquivalence.reindex
        substitutionResult.semanticSubstitution).transport
          (left.semanticFiberEquivalence.transport term)

def IncDepRawAlignedFormationSubstitutionFiberResult.canonicalFiberResult
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult where
  targetFormationResult := { semanticType := result.targetCanonical }
  sourceFormationResult := { semanticType := result.sourceCanonical }
  semanticFiberEquivalence := result.canonicalEquivalence

noncomputable def IncDepRawAlignedFormationSubstitutionFiberResult.toCanonicalRebase
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberRebase result.toFormationFiberResult
      result.canonicalFiberResult := by
  cases result with
  | mk targetFormationResult sourceFormationResult sourceCanonical
      targetCanonical sourceAlignment targetAlignment canonicalEquivalence =>
      cases sourceAlignment
      cases targetAlignment
      exact
        { sourceEquivalence := IncTypeInContext.FiberEquiv.refl _
          targetEquivalence := IncTypeInContext.FiberEquiv.refl _
          naturality := by intro term; rfl }

noncomputable def IncDepRawAlignedFormationSubstitutionFiberResult.fromCanonicalRebase
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberRebase result.canonicalFiberResult
      result.toFormationFiberResult := by
  cases result with
  | mk targetFormationResult sourceFormationResult sourceCanonical
      targetCanonical sourceAlignment targetAlignment canonicalEquivalence =>
      cases sourceAlignment
      cases targetAlignment
      exact
        { sourceEquivalence := IncTypeInContext.FiberEquiv.refl _
          targetEquivalence := IncTypeInContext.FiberEquiv.refl _
          naturality := by intro term; rfl }

structure IncDepRawInstantiateFormationAlignment
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult) where
  sourceAlignment : structuralResult.sourceFormationResult.semanticType =
    IncTypeInContext.instantiateFiber
      codomainResult.sourceFormationResult.semanticType sourceArgument
  targetAlignment : structuralResult.targetFormationResult.semanticType =
    IncTypeInContext.instantiateFiber
      codomainResult.targetFormationResult.semanticType targetArgument

def IncDepRawInstantiateFormationAlignment.canonical
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution) :
    IncDepRawInstantiateFormationAlignment domainResult codomainResult
      sourceArgument targetArgument
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult sourceArgument
        targetArgument argumentCoherence) where
  sourceAlignment := rfl
  targetAlignment := rfl

noncomputable def IncDepRawInstantiateFormationAlignment.toAlignedResult
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult}
    {codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution}
    {sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType}
    {targetArgument : IncTerm domainResult.targetFormationResult.semanticType}
    {structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult}
    (alignment : IncDepRawInstantiateFormationAlignment domainResult
      codomainResult sourceArgument targetArgument structuralResult)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution) :
    IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult :=
  IncDepRawAlignedFormationSubstitutionFiberResult.instantiate
    domainResult codomainResult sourceArgument targetArgument argumentCoherence
    structuralResult.targetFormationResult structuralResult.sourceFormationResult
    alignment.sourceAlignment alignment.targetAlignment

structure IncDepRawInstantiateFormationCoherence
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult) where
  alignment : IncDepRawInstantiateFormationAlignment domainResult codomainResult
    sourceArgument targetArgument structuralResult
  structuralRebase :
    let aligned := alignment.toAlignedResult argumentCoherence
    IncDepRawFormationSubstitutionFiberRebase structuralResult
      aligned.toFormationFiberResult

noncomputable def IncDepRawInstantiateFormationCoherence.canonical
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution) :
    IncDepRawInstantiateFormationCoherence domainResult codomainResult
      sourceArgument targetArgument argumentCoherence
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult sourceArgument
        targetArgument argumentCoherence) := by
  let alignment := IncDepRawInstantiateFormationAlignment.canonical
    instantiatedFormation domainResult codomainResult sourceArgument targetArgument
    argumentCoherence
  exact
    { alignment := alignment
      structuralRebase :=
        { sourceEquivalence := IncTypeInContext.FiberEquiv.refl _
          targetEquivalence := IncTypeInContext.FiberEquiv.refl _
          naturality := by intro term; rfl } }

structure IncDepRawInstantiateFormationCoherenceProvider where
  provide : ∀
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult),
    IncDepRawInstantiateFormationCoherence domainResult codomainResult
      sourceArgument targetArgument argumentCoherence structuralResult

noncomputable def IncDepRawInstantiateFormationCoherenceProvider.dispatch
    (provider : IncDepRawInstantiateFormationCoherenceProvider)
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (sourceArgument : IncTerm domainResult.sourceFormationResult.semanticType)
    (targetArgument : IncTerm domainResult.targetFormationResult.semanticType)
    (argumentCoherence :
      domainResult.semanticFiberEquivalence.transport sourceArgument =
        targetArgument.substitute substitutionResult.semanticSubstitution)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult) :
    IncDepRawInstantiateFormationCoherence domainResult codomainResult
      sourceArgument targetArgument argumentCoherence structuralResult :=
  provider.provide domainResult codomainResult sourceArgument targetArgument
    argumentCoherence structuralResult

def IncDepRawFormationSubstitutionFiberRebase.refl
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult) :
    IncDepRawFormationSubstitutionFiberRebase result result where
  sourceEquivalence := IncTypeInContext.FiberEquiv.refl _
  targetEquivalence := IncTypeInContext.FiberEquiv.refl _
  naturality := by intro term; rfl

def IncDepRawFormationSubstitutionFiberRebase.trans
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {first second third : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (firstRebase : IncDepRawFormationSubstitutionFiberRebase first second)
    (secondRebase : IncDepRawFormationSubstitutionFiberRebase second third) :
    IncDepRawFormationSubstitutionFiberRebase first third where
  sourceEquivalence := firstRebase.sourceEquivalence.trans
    secondRebase.sourceEquivalence
  targetEquivalence := firstRebase.targetEquivalence.trans
    secondRebase.targetEquivalence
  naturality := by
    intro term
    change third.semanticFiberEquivalence.transport
        (secondRebase.sourceEquivalence.transport
          (firstRebase.sourceEquivalence.transport term)) =
      (secondRebase.targetEquivalence.reindex
        substitutionResult.semanticSubstitution).transport
        ((firstRebase.targetEquivalence.reindex
          substitutionResult.semanticSubstitution).transport
          (first.semanticFiberEquivalence.transport term))
    rw [secondRebase.naturality
        (firstRebase.sourceEquivalence.transport term),
      firstRebase.naturality term]

def IncDepRawFormationSubstitutionFiberRebase.symm
    {source target : List IncDepRawType} {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {left right : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (rebase : IncDepRawFormationSubstitutionFiberRebase left right) :
    IncDepRawFormationSubstitutionFiberRebase right left where
  sourceEquivalence := rebase.sourceEquivalence.symm
  targetEquivalence := rebase.targetEquivalence.symm
  naturality := by
    intro term
    have forward := rebase.naturality
      (rebase.sourceEquivalence.symm.transport term)
    rw [rebase.sourceEquivalence.symm_transport] at forward
    have backward := congrArg
      (fun transported =>
        (rebase.targetEquivalence.reindex
          substitutionResult.semanticSubstitution).symm.transport transported)
      forward
    change (rebase.targetEquivalence.reindex
        substitutionResult.semanticSubstitution).symm.transport
          (right.semanticFiberEquivalence.transport term) =
      (rebase.targetEquivalence.reindex
        substitutionResult.semanticSubstitution).symm.transport
          ((rebase.targetEquivalence.reindex
            substitutionResult.semanticSubstitution).transport
            (left.semanticFiberEquivalence.transport
              (rebase.sourceEquivalence.symm.transport term))) at backward
    rw [(rebase.targetEquivalence.reindex
      substitutionResult.semanticSubstitution).transport_symm] at backward
    exact backward.symm

noncomputable def IncDepRawTypingSubstitutionFiberResult.rebase
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {left right : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) left)
    (rebase : IncDepRawFormationSubstitutionFiberRebase left right) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) right where
  targetTermResult :=
    { semanticTerm := rebase.targetEquivalence.transport
        result.targetTermResult.semanticTerm }
  sourceTermResult :=
    { semanticTerm := rebase.sourceEquivalence.transport
        result.sourceTermResult.semanticTerm }
  semanticTerm_coherence := by
    rw [rebase.naturality result.sourceTermResult.semanticTerm,
      result.semanticTerm_coherence,
      IncTypeInContext.FiberEquiv.reindex_transport]

noncomputable def IncDepRawTypingSubstitutionFiberResult.rebaseSymm
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {left right : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) right)
    (rebase : IncDepRawFormationSubstitutionFiberRebase left right) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) left :=
  result.rebase rebase.symm

noncomputable def IncDepRawTypingSubstitutionFiberResult.rebaseToCanonical
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {aligned : IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) aligned.toFormationFiberResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) aligned.canonicalFiberResult :=
  result.rebase aligned.toCanonicalRebase

noncomputable def IncDepRawTypingSubstitutionFiberResult.rebaseFromCanonical
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {aligned : IncDepRawAlignedFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) aligned.canonicalFiberResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) aligned.toFormationFiberResult :=
  result.rebase aligned.fromCanonicalRebase

structure IncDepRawVariableSubstitutionFiberResult
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult) where
  targetVariable : IncTerm typeResult.targetFormationResult.semanticType
  sourceReplacement : IncDepRawTypingSemanticResult
    (substitution.preserves lookup) sourceResult
    typeResult.sourceFormationResult.semanticType
  variableCoherence :
    typeResult.semanticFiberEquivalence.transport
        sourceReplacement.semanticTerm =
      targetVariable.substitute substitutionResult.semanticSubstitution

structure IncDepRawSubstitutionReplacementSemanticResult
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  replacement : ∀ {position type}
    (lookup : IncDepRawLookup target position type),
    Sigma fun semanticType : IncTypeInContext sourceResult.semanticContext =>
      IncDepRawTypingSemanticResult (substitution.preserves lookup)
        sourceResult semanticType

def IncDepRawSubstitutionReplacementSemanticResult.semanticType
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawSubstitutionReplacementSemanticResult substitutionResult)
    {position type} (lookup : IncDepRawLookup target position type) :
    IncTypeInContext sourceResult.semanticContext :=
  (result.replacement lookup).1

def IncDepRawSubstitutionReplacementSemanticResult.typingResult
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawSubstitutionReplacementSemanticResult substitutionResult)
    {position type} (lookup : IncDepRawLookup target position type) :
    IncDepRawTypingSemanticResult (substitution.preserves lookup) sourceResult
      (result.semanticType lookup) :=
  (result.replacement lookup).2

def IncDepRawTypingSubstitutionFiberResult.identityFormation
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (leftResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := leftTyping) typeResult)
    (rightResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := rightTyping) typeResult) :
    IncDepRawIdentityFormationSubstitutionFiberResult
      (typeFormation := typeFormation) (leftTyping := leftTyping)
      (rightTyping := rightTyping) substitutionResult where
  typeResult := typeResult
  targetLeft := leftResult.targetTermResult
  targetRight := rightResult.targetTermResult
  sourceLeft := leftResult.sourceTermResult
  sourceRight := rightResult.sourceTermResult
  leftCoherence := leftResult.semanticTerm_coherence
  rightCoherence := rightResult.semanticTerm_coherence

noncomputable def IncDepRawFormationSubstitutionFiberResult.identity
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (leftResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := leftTyping) typeResult)
    (rightResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := rightTyping) typeResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.identity
        typeFormation leftTyping rightTyping) substitutionResult :=
  (IncDepRawTypingSubstitutionFiberResult.identityFormation
    typeResult leftResult rightResult).toFormationFiberResult

noncomputable def IncDepRawSubstitutionFiberModel.identity
    (_model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (leftResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := leftTyping) typeResult)
    (rightResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := rightTyping) typeResult) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.identity
        typeFormation leftTyping rightTyping) substitutionResult :=
  IncDepRawFormationSubstitutionFiberResult.identity
    typeResult leftResult rightResult

noncomputable def IncDepRawNonIdentityFormationReady.dispatchIdentitySubstitution
    {source target : List IncDepRawType} {type : IncDepRawType}
    {left right : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {typeFormation : IncDepRawWellFormed target type}
    {leftTyping : IncDepRawHasType target left type}
    {rightTyping : IncDepRawHasType target right type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (model : IncDepRawSubstitutionFiberModel.{u})
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (typeReady : IncDepRawNonIdentityFormationReady typeFormation)
    (leftResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := leftTyping)
      (typeReady.dispatchSubstitution model substitutionResult))
    (rightResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := rightTyping)
      (typeReady.dispatchSubstitution model substitutionResult)) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := IncDepRawWellFormed.identity
        typeFormation leftTyping rightTyping) substitutionResult :=
  model.identity (typeReady.dispatchSubstitution model substitutionResult)
    leftResult rightResult

def IncDepRawTypingSemanticResult.castType
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {source target : IncTypeInContext contextResult.semanticContext}
    (result : IncDepRawTypingSemanticResult typing contextResult source)
    (coherence : source = target) :
    IncDepRawTypingSemanticResult typing contextResult target := by
  cases coherence
  exact result

def IncDepRawTypingSemanticResult.castTyping
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {sourceTyping targetTyping : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (result : IncDepRawTypingSemanticResult sourceTyping contextResult semanticType)
    (coherence : sourceTyping = targetTyping) :
    IncDepRawTypingSemanticResult targetTyping contextResult semanticType := by
  cases coherence
  exact result

def IncDepRawSubstitutionReplacementSemanticResult.typingResultAligned
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawSubstitutionReplacementSemanticResult substitutionResult)
    {position type} (lookup : IncDepRawLookup target position type)
    (semanticType : IncTypeInContext sourceResult.semanticContext)
    (coherence : result.semanticType lookup = semanticType) :
    IncDepRawTypingSemanticResult (substitution.preserves lookup) sourceResult
      semanticType :=
  (result.typingResult lookup).castType coherence

noncomputable def IncDepRawTypingSemanticResult.weaken
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type head : IncDepRawType}
    {typing : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (typingResult : IncDepRawTypingSemanticResult typing contextResult semanticType)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    IncDepRawTypingSemanticResult
      (typing.rename ((IncDepRawRenaming.identity context).weakenTarget head))
      (contextResult.extend (typeWellFormed := headWellFormed)
        headResult.semanticType)
      (semanticType.reindex
        (contextResult.semanticContext.extendProjection headResult.semanticType)) where
  semanticTerm := typingResult.semanticTerm.substitute
    (contextResult.semanticContext.extendProjection headResult.semanticType)

theorem IncDepRawTypingSemanticResult.weaken_semanticTerm
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type head : IncDepRawType}
    {typing : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (typingResult : IncDepRawTypingSemanticResult typing contextResult semanticType)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    (IncDepRawTypingSemanticResult.weaken typingResult headResult).semanticTerm =
      typingResult.semanticTerm.substitute
        (contextResult.semanticContext.extendProjection headResult.semanticType) := by
  rfl

noncomputable def IncDepRawFormationRenamedReadyResult.weakenSemantic
    {context : List IncDepRawType} {type head : IncDepRawType}
    {formation : IncDepRawWellFormed context type}
    {ready : IncDepRawFormationSemanticReady formation}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (renamed : IncDepRawFormationRenamedReadyResult ready
      ((IncDepRawRenaming.identity context).weakenTarget head))
    (typeResult : IncDepRawFormationSemanticResult formation contextResult)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    IncDepRawFormationSemanticResult renamed.renamedFormation
      (contextResult.extend (typeWellFormed := headWellFormed)
        headResult.semanticType) where
  semanticType := typeResult.semanticType.reindex
    (contextResult.semanticContext.extendProjection headResult.semanticType)

noncomputable def IncDepRawTypingRenamedReadyResult.weakenSemantic
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type head : IncDepRawType}
    {typing : IncDepRawHasType context term type}
    {ready : IncDepRawTypingSemanticReady typing}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (renamed : IncDepRawTypingRenamedReadyResult ready
      ((IncDepRawRenaming.identity context).weakenTarget head))
    (typingResult : IncDepRawTypingSemanticResult typing contextResult semanticType)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    IncDepRawTypingSemanticResult renamed.renamedTyping
      (contextResult.extend (typeWellFormed := headWellFormed)
        headResult.semanticType)
      (semanticType.reindex
        (contextResult.semanticContext.extendProjection headResult.semanticType)) where
  semanticTerm := typingResult.semanticTerm.substitute
    (contextResult.semanticContext.extendProjection headResult.semanticType)

theorem IncDepRawTypingRenamedReadyResult.weakenSemantic_term
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type head : IncDepRawType}
    {typing : IncDepRawHasType context term type}
    {ready : IncDepRawTypingSemanticReady typing}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (renamed : IncDepRawTypingRenamedReadyResult ready
      ((IncDepRawRenaming.identity context).weakenTarget head))
    (typingResult : IncDepRawTypingSemanticResult typing contextResult semanticType)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    (renamed.weakenSemantic typingResult headResult).semanticTerm =
      typingResult.semanticTerm.substitute
        (contextResult.semanticContext.extendProjection headResult.semanticType) := by
  rfl

structure IncDepRawTypingFormationSemanticResult
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {typeFormation : IncDepRawWellFormed context type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed) where
  formationResult : IncDepRawFormationSemanticResult typeFormation contextResult
  typingResult : IncDepRawTypingSemanticResult typing contextResult
    formationResult.semanticType

def IncDepRawTypingFormationSemanticResult.align
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {typeFormation : IncDepRawWellFormed context type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (formationResult : IncDepRawFormationSemanticResult typeFormation contextResult)
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (typingResult : IncDepRawTypingSemanticResult typing contextResult semanticType)
    (coherence : semanticType = formationResult.semanticType) :
    IncDepRawTypingFormationSemanticResult
      (typing := typing) (typeFormation := typeFormation) contextResult where
  formationResult := formationResult
  typingResult := typingResult.castType coherence

structure IncDepRawLookupSemanticResult
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    (lookup : IncDepRawLookup context position type)
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed) where
  semanticType : IncTypeInContext contextResult.semanticContext
  semanticTerm : IncTerm semanticType

def IncDepRawLookupSemanticResult.here
    {context : List IncDepRawType} {type : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {typeWellFormed : IncDepRawWellFormed context type}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (semanticType : IncTypeInContext contextResult.semanticContext) :
    IncDepRawLookupSemanticResult
      (IncDepRawLookup.here (context := context) (type := type))
      (contextResult.extend (typeWellFormed := typeWellFormed) semanticType) where
  semanticType := semanticType.reindex
    (contextResult.semanticContext.extendProjection semanticType)
  semanticTerm := contextResult.semanticContext.extendVariable semanticType

def IncDepRawLookupSemanticResult.there
    {context : List IncDepRawType} {position : Nat} {type head : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (lookupResult : IncDepRawLookupSemanticResult lookup contextResult)
    (semanticHead : IncTypeInContext contextResult.semanticContext) :
    IncDepRawLookupSemanticResult
      (IncDepRawLookup.there (head := head) lookup)
      (contextResult.extend (typeWellFormed := headWellFormed) semanticHead) where
  semanticType := lookupResult.semanticType.reindex
    (contextResult.semanticContext.extendProjection semanticHead)
  semanticTerm := lookupResult.semanticTerm.substitute
    (contextResult.semanticContext.extendProjection semanticHead)

def IncDepRawTypingSemanticResult.variable
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (semanticVariable : IncTerm semanticType) :
    IncDepRawTypingSemanticResult (IncDepRawHasType.varRule lookup)
      contextResult semanticType where
  semanticTerm := semanticVariable

def IncDepRawVariableSubstitutionFiberResult.toTyping
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult}
    (result : IncDepRawVariableSubstitutionFiberResult
      (lookup := lookup) typeResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.varRule lookup) typeResult where
  targetTermResult := IncDepRawTypingSemanticResult.variable result.targetVariable
  sourceTermResult := result.sourceReplacement
  semanticTerm_coherence := result.variableCoherence

def IncDepRawLookupSemanticResult.toTyping
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (lookupResult : IncDepRawLookupSemanticResult lookup contextResult) :
    IncDepRawTypingSemanticResult (IncDepRawHasType.varRule lookup)
      contextResult lookupResult.semanticType :=
  IncDepRawTypingSemanticResult.variable lookupResult.semanticTerm

noncomputable def IncDepRawContextSemanticTree.interpretLookup
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    (tree : IncDepRawContextSemanticTree contextResult)
    {position : Nat} {type : IncDepRawType}
    (lookup : IncDepRawLookup context position type) :
    IncDepRawLookupSemanticResult lookup contextResult := by
  induction tree generalizing position type with
  | empty => cases lookup
  | extend tail head ih =>
      cases lookup with
      | here =>
          exact IncDepRawLookupSemanticResult.here head.semanticType
      | there previous =>
          exact IncDepRawLookupSemanticResult.there (ih previous)
            head.semanticType

noncomputable def IncDepRawContextSemanticTree.interpretVariable
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    (tree : IncDepRawContextSemanticTree contextResult)
    {position : Nat} {type : IncDepRawType}
    (lookup : IncDepRawLookup context position type) :
    IncDepRawTypingSemanticResult (IncDepRawHasType.varRule lookup)
      contextResult (tree.interpretLookup lookup).semanticType :=
  (tree.interpretLookup lookup).toTyping

noncomputable def IncDepRawSubstitutionReplacementSemanticResult.identity
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (contextTree : IncDepRawContextSemanticTree contextResult) :
    IncDepRawSubstitutionReplacementSemanticResult
      (IncDepRawSubstitutionSemanticResult.identity contextResult) where
  replacement := by
    intro position type lookup
    let lookupResult := contextTree.interpretLookup lookup
    exact ⟨lookupResult.semanticType,
      { semanticTerm := lookupResult.semanticTerm }⟩

theorem IncDepRawSubstitutionReplacementSemanticResult.identity_term
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (contextTree : IncDepRawContextSemanticTree contextResult)
    {position type} (lookup : IncDepRawLookup context position type) :
    ((IncDepRawSubstitutionReplacementSemanticResult.identity contextTree).typingResult
      lookup).semanticTerm =
      (contextTree.interpretLookup lookup).semanticTerm := by
  rfl

noncomputable def IncDepRawSubstitutionReplacementSemanticResult.lift
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution) :
    IncDepRawSubstitutionReplacementSemanticResult
      (IncDepRawSubstitutionSemanticResult.lift substitutionResult
        targetDomain sourceDomain coherence) where
  replacement := by
    intro position type lookup
    cases lookup with
    | here =>
        exact ⟨sourceDomain.semanticType.reindex
            (sourceResult.semanticContext.extendProjection sourceDomain.semanticType),
          { semanticTerm :=
              sourceResult.semanticContext.extendVariable sourceDomain.semanticType }⟩
    | there previous =>
        let previousResult := replacements.replacement previous
        exact ⟨previousResult.1.reindex
            (sourceResult.semanticContext.extendProjection sourceDomain.semanticType),
          { semanticTerm := previousResult.2.semanticTerm.substitute
              (sourceResult.semanticContext.extendProjection sourceDomain.semanticType) }⟩

noncomputable def IncDepRawSubstitutionReplacementSemanticResult.liftFiber
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (domainEquivalence : IncTypeInContext.FiberEquiv
      sourceDomain.semanticType
      (targetDomain.semanticType.reindex
        substitutionResult.semanticSubstitution)) :
    IncDepRawSubstitutionReplacementSemanticResult
      (IncDepRawSubstitutionSemanticResult.liftFiber substitutionResult
        targetDomain sourceDomain domainEquivalence) where
  replacement := by
    intro position type lookup
    cases lookup with
    | here =>
        exact ⟨sourceDomain.semanticType.reindex
            (sourceResult.semanticContext.extendProjection sourceDomain.semanticType),
          { semanticTerm :=
              sourceResult.semanticContext.extendVariable sourceDomain.semanticType }⟩
    | there previous =>
        let previousResult := replacements.replacement previous
        exact ⟨previousResult.1.reindex
            (sourceResult.semanticContext.extendProjection sourceDomain.semanticType),
          { semanticTerm := previousResult.2.semanticTerm.substitute
              (sourceResult.semanticContext.extendProjection sourceDomain.semanticType) }⟩

noncomputable def IncDepRawSubstitutionReplacementSemanticResult.liftResult
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult) :
    IncDepRawSubstitutionReplacementSemanticResult domainResult.liftSubstitution :=
  IncDepRawSubstitutionReplacementSemanticResult.liftFiber substitutionResult
    replacements domainResult.targetFormationResult
    domainResult.sourceFormationResult domainResult.semanticFiberEquivalence

theorem IncDepRawSubstitutionReplacementSemanticResult.liftResult_here_term
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult) :
    ((replacements.liftResult domainResult).typingResult
      (IncDepRawLookup.here (context := target) (type := domain))).semanticTerm =
    sourceResult.semanticContext.extendVariable
      domainResult.sourceFormationResult.semanticType := by
  rfl

theorem IncDepRawSubstitutionReplacementSemanticResult.liftResult_there_term
    {source target : List IncDepRawType} {domain type : IncDepRawType}
    {position : Nat}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (lookup : IncDepRawLookup target position type) :
    ((replacements.liftResult domainResult).typingResult
      (IncDepRawLookup.there (head := domain) lookup)).semanticTerm =
    (replacements.typingResult lookup).semanticTerm.substitute
      (sourceResult.semanticContext.extendProjection
        domainResult.sourceFormationResult.semanticType) := by
  rfl

theorem IncDepRawSubstitutionReplacementSemanticResult.liftResult_here_fiber
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (assignment : sourceResult.semanticContext.Assignment)
    (value : domainResult.sourceFormationResult.semanticType assignment) :
    (domainResult.semanticFiberEquivalence.fiberEquiv assignment).forward
        (((replacements.liftResult domainResult).typingResult
          (IncDepRawLookup.here (context := target) (type := domain))).semanticTerm
            ⟨assignment, value⟩) =
      (targetResult.semanticContext.extendVariable
        domainResult.targetFormationResult.semanticType)
        (domainResult.liftSubstitution.semanticSubstitution
          ⟨assignment, value⟩) := by
  exact IncDepRawSubstitutionSemanticResult.liftFiber_variable
    substitutionResult domainResult.targetFormationResult
    domainResult.sourceFormationResult domainResult.semanticFiberEquivalence
    assignment value

theorem IncDepRawSubstitutionReplacementSemanticResult.liftResult_there_fiber
    {source target : List IncDepRawType} {domain type : IncDepRawType}
    {position : Nat}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (lookup : IncDepRawLookup target position type)
    {targetFamily : IncTypeInContext targetResult.semanticContext}
    (familyEquivalence : IncTypeInContext.FiberEquiv
      (replacements.semanticType lookup)
      (targetFamily.reindex substitutionResult.semanticSubstitution))
    (targetTerm : IncTerm targetFamily)
    (termCoherence : familyEquivalence.transport
        (replacements.typingResult lookup).semanticTerm =
      targetTerm.substitute substitutionResult.semanticSubstitution) :
    (familyEquivalence.reindex
      (sourceResult.semanticContext.extendProjection
        domainResult.sourceFormationResult.semanticType)).transport
        (((replacements.liftResult domainResult).typingResult
          (IncDepRawLookup.there (head := domain) lookup)).semanticTerm) =
      (targetTerm.substitute
        (targetResult.semanticContext.extendProjection
          domainResult.targetFormationResult.semanticType)).substitute
          domainResult.liftSubstitution.semanticSubstitution := by
  exact IncDepRawSubstitutionSemanticResult.liftFiber_older_transport
    substitutionResult domainResult.targetFormationResult
    domainResult.sourceFormationResult domainResult.semanticFiberEquivalence
    familyEquivalence (replacements.typingResult lookup).semanticTerm
    targetTerm termCoherence

theorem IncDepRawSubstitutionReplacementSemanticResult.lift_here_term
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution) :
    ((IncDepRawSubstitutionReplacementSemanticResult.lift substitutionResult
      replacements targetDomain sourceDomain coherence).typingResult
        (IncDepRawLookup.here (context := target) (type := domain))).semanticTerm =
      sourceResult.semanticContext.extendVariable sourceDomain.semanticType := by
  rfl

theorem IncDepRawSubstitutionReplacementSemanticResult.lift_there_term
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution)
    {position type} (lookup : IncDepRawLookup target position type) :
    ((IncDepRawSubstitutionReplacementSemanticResult.lift substitutionResult
      replacements targetDomain sourceDomain coherence).typingResult
        (IncDepRawLookup.there (head := domain) lookup)).semanticTerm =
      (replacements.typingResult lookup).semanticTerm.substitute
        (sourceResult.semanticContext.extendProjection sourceDomain.semanticType) := by
  rfl

theorem IncDepRawSubstitutionReplacementSemanticResult.lift_here_fiber
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (coherence : sourceDomain.semanticType = targetDomain.semanticType.reindex
      substitutionResult.semanticSubstitution)
    (assignment : sourceResult.semanticContext.Assignment)
    (value : sourceDomain.semanticType assignment) :
    ((IncTypeInContext.FiberEquiv.ofEq coherence).fiberEquiv assignment).forward
        (((IncDepRawSubstitutionReplacementSemanticResult.lift
          substitutionResult replacements targetDomain sourceDomain coherence).typingResult
              (IncDepRawLookup.here (context := target) (type := domain))).semanticTerm
                ⟨assignment, value⟩) =
      (targetResult.semanticContext.extendVariable targetDomain.semanticType)
        ((IncDepRawSubstitutionSemanticResult.lift substitutionResult
          targetDomain sourceDomain coherence).semanticSubstitution
            ⟨assignment, value⟩) := by
  exact IncDepRawSubstitutionSemanticResult.lift_variable_fiber
    substitutionResult targetDomain sourceDomain coherence assignment value

theorem IncDepRawSubstitutionReplacementSemanticResult.lift_there_fiber
    {source target : List IncDepRawType} {domain : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    {domainFormation : IncDepRawWellFormed target domain}
    {substitutedDomainFormation : IncDepRawWellFormed source
      (domain.substitute substitution.term)}
    (targetDomain : IncDepRawFormationSemanticResult domainFormation targetResult)
    (sourceDomain : IncDepRawFormationSemanticResult
      substitutedDomainFormation sourceResult)
    (domainCoherence : sourceDomain.semanticType =
      targetDomain.semanticType.reindex substitutionResult.semanticSubstitution)
    {position type} (lookup : IncDepRawLookup target position type)
    {targetFamily : IncTypeInContext targetResult.semanticContext}
    (familyEquivalence : IncTypeInContext.FiberEquiv
      (replacements.semanticType lookup)
      (targetFamily.reindex substitutionResult.semanticSubstitution))
    (targetTerm : IncTerm targetFamily)
    (termCoherence : familyEquivalence.transport
        (replacements.typingResult lookup).semanticTerm =
      targetTerm.substitute substitutionResult.semanticSubstitution) :
    (familyEquivalence.reindex
      (sourceResult.semanticContext.extendProjection sourceDomain.semanticType)).transport
        (((IncDepRawSubstitutionReplacementSemanticResult.lift
          substitutionResult replacements targetDomain sourceDomain
            domainCoherence).typingResult
              (IncDepRawLookup.there (head := domain) lookup)).semanticTerm) =
      (targetTerm.substitute
        (targetResult.semanticContext.extendProjection targetDomain.semanticType)).substitute
          (IncDepRawSubstitutionSemanticResult.lift substitutionResult
            targetDomain sourceDomain domainCoherence).semanticSubstitution := by
  exact IncDepRawSubstitutionSemanticResult.lift_older_transport
    substitutionResult targetDomain sourceDomain domainCoherence
    familyEquivalence (replacements.typingResult lookup).semanticTerm
    targetTerm termCoherence

def IncDepRawContextSemanticTree.interpretUnit
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    (_tree : IncDepRawContextSemanticTree contextResult) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.unitRule (context := context)) contextResult
      (fun _ => ULift Unit) :=
  ⟨fun _ => ⟨()⟩⟩

def incDepRawOneUnitContextWellFormed :
    IncDepRawContext.WellFormed [IncDepRawType.unit] :=
  IncDepRawContext.WellFormed.extend IncDepRawContext.WellFormed.empty
    IncDepRawWellFormed.unit

def incDepRawEmptyUnitFormationSemantic :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.unit (context := []))
      incDepRawEmptyContextSemantic :=
  IncDepRawFormationSemanticResult.unit incDepRawEmptyContextSemantic

def incDepRawOneUnitContextSemantic :=
  incDepRawEmptyContextSemantic.extend
    (typeWellFormed := IncDepRawWellFormed.unit)
    incDepRawEmptyUnitFormationSemantic.semanticType

def incDepRawOneUnitContextSemanticTree :
    IncDepRawContextSemanticTree incDepRawOneUnitContextSemantic :=
  IncDepRawContextSemanticTree.extend incDepRawEmptyContextSemanticTree
    incDepRawEmptyUnitFormationSemantic

def incDepRawOneUnitFormationSemantic :
    IncDepRawFormationSemanticResult
      (IncDepRawWellFormed.unit (context := [IncDepRawType.unit]))
      incDepRawOneUnitContextSemantic :=
  IncDepRawFormationSemanticResult.unit incDepRawOneUnitContextSemantic

def incDepRawTwoUnitContextSemantic :=
  incDepRawOneUnitContextSemantic.extend
    (typeWellFormed := IncDepRawWellFormed.unit)
    incDepRawOneUnitFormationSemantic.semanticType

def incDepRawTwoUnitContextSemanticTree :
    IncDepRawContextSemanticTree incDepRawTwoUnitContextSemantic :=
  IncDepRawContextSemanticTree.extend incDepRawOneUnitContextSemanticTree
    incDepRawOneUnitFormationSemantic

noncomputable def incDepRawTwoUnitNewestLookupSemantic :=
  incDepRawTwoUnitContextSemanticTree.interpretLookup
    (IncDepRawLookup.here (context := [IncDepRawType.unit])
      (type := IncDepRawType.unit))

noncomputable def incDepRawTwoUnitOlderLookupSemantic :=
  incDepRawTwoUnitContextSemanticTree.interpretLookup
    (IncDepRawLookup.there (head := IncDepRawType.unit)
      (IncDepRawLookup.here (context := []) (type := IncDepRawType.unit)))

noncomputable def incDepRawTwoUnitNewestTypingSemantic :=
  incDepRawTwoUnitContextSemanticTree.interpretVariable
    (IncDepRawLookup.here (context := [IncDepRawType.unit])
      (type := IncDepRawType.unit))

noncomputable def incDepRawTwoUnitOlderTypingSemantic :=
  incDepRawTwoUnitContextSemanticTree.interpretVariable
    (IncDepRawLookup.there (head := IncDepRawType.unit)
      (IncDepRawLookup.here (context := []) (type := IncDepRawType.unit)))

def incDepRawTwoUnitUnitTypingSemantic :=
  incDepRawTwoUnitContextSemanticTree.interpretUnit

theorem incDepRawTwoUnitNewestLookupSemantic_value
    (assignment : incDepRawTwoUnitContextSemantic.semanticContext.Assignment) :
    incDepRawTwoUnitNewestLookupSemantic.semanticTerm assignment = assignment.2 := by
  rfl

theorem incDepRawTwoUnitOlderLookupSemantic_value
    (assignment : incDepRawTwoUnitContextSemantic.semanticContext.Assignment) :
    incDepRawTwoUnitOlderLookupSemantic.semanticTerm assignment = assignment.1.2 := by
  rfl

theorem incDepRawTwoUnitNewestTypingSemantic_value
    (assignment : incDepRawTwoUnitContextSemantic.semanticContext.Assignment) :
    incDepRawTwoUnitNewestTypingSemantic.semanticTerm assignment = assignment.2 := by
  rfl

theorem incDepRawTwoUnitOlderTypingSemantic_value
    (assignment : incDepRawTwoUnitContextSemantic.semanticContext.Assignment) :
    incDepRawTwoUnitOlderTypingSemantic.semanticTerm assignment = assignment.1.2 := by
  rfl

def IncDepRawTypingSemanticResult.unit
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.unitRule (context := context)) contextResult
      (fun _ => ULift Unit) where
  semanticTerm := fun _ => ⟨()⟩

def IncDepRawTypingSubstitutionFiberResult.unit
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.unitRule)
      (IncDepRawFormationSubstitutionSemanticResult.toFiberResult
        (IncDepRawFormationSubstitutionSemanticResult.unit substitutionResult)) where
  targetTermResult := IncDepRawTypingSemanticResult.unit targetResult
  sourceTermResult := IncDepRawTypingSemanticResult.unit sourceResult
  semanticTerm_coherence := rfl

def IncDepRawSubstitutionFiberModel.typingUnit
    (_model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.unitRule)
      (IncDepRawFormationSubstitutionFiberResult.unit substitutionResult) :=
  IncDepRawTypingSubstitutionFiberResult.unit substitutionResult

theorem IncDepRawTypingSubstitutionFiberResult.unit_apply
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    (assignment : sourceResult.semanticContext.Assignment) :
    (IncDepRawTypingSubstitutionFiberResult.unit substitutionResult).targetTermResult.semanticTerm
        (substitutionResult.semanticSubstitution assignment) =
      (IncDepRawTypingSubstitutionFiberResult.unit substitutionResult).sourceTermResult.semanticTerm
        assignment := by
  rfl

def IncDepRawTypingSemanticResult.lambda
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {domainFormation : IncDepRawWellFormed context domain}
    {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (bodyResult : IncDepRawTypingSemanticResult bodyTyping
      (contextResult.extend (typeWellFormed := domainFormation) semanticDomain)
      semanticCodomain) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.lambdaRule domainFormation bodyTyping) contextResult
      (IncPiType semanticDomain semanticCodomain) where
  semanticTerm := IncPiTerm.lambda bodyResult.semanticTerm

def IncDepRawTypingSemanticResult.apply
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {functionTyping : IncDepRawHasType context function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType context argument domain}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (functionResult : IncDepRawTypingSemanticResult functionTyping contextResult
      (IncPiType semanticDomain semanticCodomain))
    (argumentResult : IncDepRawTypingSemanticResult argumentTyping contextResult
      semanticDomain) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.applyRule functionTyping argumentTyping) contextResult
      (IncTypeInContext.instantiateFiber semanticCodomain
        argumentResult.semanticTerm) where
  semanticTerm := IncPiTerm.apply functionResult.semanticTerm
    argumentResult.semanticTerm

def IncDepRawTypingSemanticResult.pair
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {firstTyping : IncDepRawHasType context first domain}
    {secondTyping : IncDepRawHasType context second (codomain.instantiate first)}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (firstResult : IncDepRawTypingSemanticResult firstTyping contextResult
      semanticDomain)
    (secondResult : IncDepRawTypingSemanticResult secondTyping contextResult
      (IncTypeInContext.instantiateFiber semanticCodomain
        firstResult.semanticTerm)) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.pairRule firstTyping secondTyping) contextResult
      (IncSigmaType semanticDomain semanticCodomain) where
  semanticTerm := IncSigmaTerm.pair firstResult.semanticTerm
    secondResult.semanticTerm

def IncDepRawTypingSemanticResult.first
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (pairResult : IncDepRawTypingSemanticResult pairTyping contextResult
      (IncSigmaType semanticDomain semanticCodomain)) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.firstRule pairTyping) contextResult semanticDomain where
  semanticTerm := IncSigmaTerm.first pairResult.semanticTerm

def IncDepRawTypingSemanticResult.second
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (pairResult : IncDepRawTypingSemanticResult pairTyping contextResult
      (IncSigmaType semanticDomain semanticCodomain)) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.secondRule pairTyping) contextResult
      (IncTypeInContext.instantiateFiber semanticCodomain
        (IncSigmaTerm.first pairResult.semanticTerm)) where
  semanticTerm := IncSigmaTerm.second pairResult.semanticTerm

def IncDepRawTypingSemanticResult.refl
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm} {termTyping : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (termResult : IncDepRawTypingSemanticResult termTyping contextResult
      semanticType) :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.reflRule termTyping) contextResult
      (IncIdentityType semanticType termResult.semanticTerm
        termResult.semanticTerm) where
  semanticTerm := IncIdentityTerm.refl termResult.semanticTerm

noncomputable def IncDepRawTypingSubstitutionFiberResult.refl
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {termTyping : IncDepRawHasType target term type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (termResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := termTyping) typeResult) :
    let identityResult :=
      IncDepRawTypingSubstitutionFiberResult.identityFormation
        typeResult termResult termResult
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.reflRule termTyping)
      identityResult.toFormationFiberResult := by
  dsimp
  let identityResult :=
    IncDepRawTypingSubstitutionFiberResult.identityFormation
      typeResult termResult termResult
  refine
    { targetTermResult := IncDepRawTypingSemanticResult.refl
        termResult.targetTermResult
      sourceTermResult := IncDepRawTypingSemanticResult.refl
        termResult.sourceTermResult
      semanticTerm_coherence := ?_ }
  funext assignment
  apply IncIdentityType.witness_irrel

noncomputable def IncDepRawSubstitutionFiberModel.refl
    (_model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {termTyping : IncDepRawHasType target term type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (termResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := termTyping) typeResult) :
    let identityResult :=
      IncDepRawTypingSubstitutionFiberResult.identityFormation
        typeResult termResult termResult
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.reflRule termTyping)
      identityResult.toFormationFiberResult :=
  IncDepRawTypingSubstitutionFiberResult.refl typeResult termResult

noncomputable def IncDepRawTypingSubstitutionFiberResult.lambda
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {bodyTyping : IncDepRawHasType (domain :: target) body codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawPiSubstitutionCoherence domainResult codomainResult)
    (bodyResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := bodyTyping) codomainResult) :
    let piResult :=
      IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
        domainResult codomainResult coherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.lambdaRule domainFormation bodyTyping)
      piResult.toFormationFiberResult := by
  dsimp
  let piResult :=
    IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
      domainResult codomainResult coherence
  refine
    { targetTermResult := IncDepRawTypingSemanticResult.lambda
        bodyResult.targetTermResult
      sourceTermResult := IncDepRawTypingSemanticResult.lambda
        bodyResult.sourceTermResult
      semanticTerm_coherence := ?_ }
  funext assignment
  exact
    (piResult.fiberEquiv assignment).dependentEquiv.piForward_eq_of_pointwise
      (fun value => bodyResult.sourceTermResult.semanticTerm
        ⟨assignment, value⟩)
      (fun value => bodyResult.targetTermResult.semanticTerm
        ⟨substitutionResult.semanticSubstitution assignment, value⟩)
      (fun sourceValue => congrFun bodyResult.semanticTerm_coherence
        ⟨assignment, sourceValue⟩)

noncomputable def IncDepRawSubstitutionFiberModel.lambda
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {bodyTyping : IncDepRawHasType (domain :: target) body codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (bodyResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := bodyTyping) codomainResult) :
    let coherence := model.piCoherence domainResult codomainResult
    let piResult :=
      IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
        domainResult codomainResult coherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.lambdaRule domainFormation bodyTyping)
      piResult.toFormationFiberResult :=
  IncDepRawTypingSubstitutionFiberResult.lambda domainResult codomainResult
    (model.piCoherence domainResult codomainResult) bodyResult

noncomputable def IncDepRawTypingSubstitutionFiberResult.apply
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawPiSubstitutionCoherence domainResult codomainResult)
    (functionResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := functionTyping)
      (IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
        domainResult codomainResult coherence).toFormationFiberResult)
    (argumentResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := argumentTyping) domainResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.applyRule functionTyping argumentTyping)
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        argumentResult.sourceTermResult.semanticTerm
        argumentResult.targetTermResult.semanticTerm
        argumentResult.semanticTerm_coherence) := by
  refine
    { targetTermResult := IncDepRawTypingSemanticResult.apply
        functionResult.targetTermResult argumentResult.targetTermResult
      sourceTermResult :=
        { semanticTerm := IncPiTerm.apply
            functionResult.sourceTermResult.semanticTerm
            argumentResult.sourceTermResult.semanticTerm }
      semanticTerm_coherence := ?_ }
  funext assignment
  change ((domainResult.instantiateFiberEquivalence codomainResult
      argumentResult.sourceTermResult.semanticTerm
      argumentResult.targetTermResult.semanticTerm
      argumentResult.semanticTerm_coherence).fiberEquiv assignment).forward
        (functionResult.sourceTermResult.semanticTerm assignment
          (argumentResult.sourceTermResult.semanticTerm assignment)) =
    functionResult.targetTermResult.semanticTerm
      (substitutionResult.semanticSubstitution assignment)
      (argumentResult.targetTermResult.semanticTerm
        (substitutionResult.semanticSubstitution assignment))
  rw [IncDepRawFormationSubstitutionFiberResult.instantiateFiberEquivalence_forward]
  exact (IncDepRawPiFormationSubstitutionFiberResult.dependentEquiv
      domainResult codomainResult assignment).piForward_apply_transport
    (functionResult.sourceTermResult.semanticTerm assignment)
    (functionResult.targetTermResult.semanticTerm
      (substitutionResult.semanticSubstitution assignment))
    (argumentResult.sourceTermResult.semanticTerm assignment)
    (argumentResult.targetTermResult.semanticTerm
      (substitutionResult.semanticSubstitution assignment))
    (coherence.forward_apply assignment _ _)
    (congrFun functionResult.semanticTerm_coherence assignment)
    (congrFun argumentResult.semanticTerm_coherence assignment)

noncomputable def IncDepRawSubstitutionFiberModel.apply
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := functionTyping)
      (IncDepRawPiFormationSubstitutionFiberResult.ofApplicationCoherence
        domainResult codomainResult
        (model.piCoherence domainResult codomainResult)).toFormationFiberResult)
    (argumentResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := argumentTyping) domainResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.applyRule functionTyping argumentTyping)
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        argumentResult.sourceTermResult.semanticTerm
        argumentResult.targetTermResult.semanticTerm
        argumentResult.semanticTerm_coherence) :=
  IncDepRawTypingSubstitutionFiberResult.apply instantiatedFormation
    domainResult codomainResult (model.piCoherence domainResult codomainResult)
    functionResult argumentResult

noncomputable def IncDepRawSubstitutionFiberModel.applyRebased
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := functionTyping) (model.pi domainResult codomainResult))
    (argumentResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := argumentTyping) domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (alignment : IncDepRawInstantiateFormationAlignment domainResult
      codomainResult argumentResult.sourceTermResult.semanticTerm
      argumentResult.targetTermResult.semanticTerm structuralResult) :
    let aligned := alignment.toAlignedResult argumentResult.semanticTerm_coherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.applyRule functionTyping argumentTyping)
      aligned.toFormationFiberResult := by
  dsimp
  let aligned := alignment.toAlignedResult argumentResult.semanticTerm_coherence
  let canonical := model.apply instantiatedFormation domainResult codomainResult
    functionResult argumentResult
  exact canonical.rebaseFromCanonical (aligned := aligned)

noncomputable def IncDepRawSubstitutionFiberModel.applyCoherent
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := functionTyping) (model.pi domainResult codomainResult))
    (argumentResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := argumentTyping) domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (coherence : IncDepRawInstantiateFormationCoherence domainResult
      codomainResult argumentResult.sourceTermResult.semanticTerm
      argumentResult.targetTermResult.semanticTerm
      argumentResult.semanticTerm_coherence structuralResult) :
    let aligned := coherence.alignment.toAlignedResult
      argumentResult.semanticTerm_coherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.applyRule functionTyping argumentTyping)
      aligned.toFormationFiberResult :=
  model.applyRebased instantiatedFormation domainResult codomainResult
    functionResult argumentResult structuralResult coherence.alignment

noncomputable def IncDepRawSubstitutionFiberModel.applyStructuralExact
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := functionTyping) (model.pi domainResult codomainResult))
    (argumentResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := argumentTyping) domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (coherence : IncDepRawInstantiateFormationCoherence domainResult
      codomainResult argumentResult.sourceTermResult.semanticTerm
      argumentResult.targetTermResult.semanticTerm
      argumentResult.semanticTerm_coherence structuralResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.applyRule functionTyping argumentTyping)
      structuralResult := by
  let alignedResult := model.applyCoherent instantiatedFormation domainResult
    codomainResult functionResult argumentResult structuralResult coherence
  exact alignedResult.rebaseSymm coherence.structuralRebase

noncomputable def IncDepRawTypingSubstitutionFiberResult.pair
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {firstTyping : IncDepRawHasType target first domain}
    {secondTyping : IncDepRawHasType target second (codomain.instantiate first)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate first))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawSigmaSubstitutionCoherence domainResult codomainResult)
    (firstResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := firstTyping) domainResult)
    (secondResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := secondTyping)
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        firstResult.sourceTermResult.semanticTerm
        firstResult.targetTermResult.semanticTerm
        firstResult.semanticTerm_coherence)) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.pairRule firstTyping secondTyping)
      (IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
        domainResult codomainResult coherence).toFormationFiberResult := by
  let sigmaResult :=
    IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
      domainResult codomainResult coherence
  refine
    { targetTermResult := IncDepRawTypingSemanticResult.pair
        firstResult.targetTermResult secondResult.targetTermResult
      sourceTermResult :=
        { semanticTerm := IncSigmaTerm.pair
            firstResult.sourceTermResult.semanticTerm
            secondResult.sourceTermResult.semanticTerm }
      semanticTerm_coherence := ?_ }
  funext assignment
  let firstCoherence := congrFun firstResult.semanticTerm_coherence assignment
  have secondCoherence := congrFun secondResult.semanticTerm_coherence assignment
  change ((domainResult.instantiateFiberEquivalence codomainResult
      firstResult.sourceTermResult.semanticTerm
      firstResult.targetTermResult.semanticTerm
      firstResult.semanticTerm_coherence).fiberEquiv assignment).forward
        (secondResult.sourceTermResult.semanticTerm assignment) =
      secondResult.targetTermResult.semanticTerm
        (substitutionResult.semanticSubstitution assignment) at secondCoherence
  rw [IncDepRawFormationSubstitutionFiberResult.instantiateFiberEquivalence_forward]
    at secondCoherence
  exact (sigmaResult.fiberEquiv assignment).dependentEquiv
    |>.sigmaForward_eq_of_components
      ⟨firstResult.sourceTermResult.semanticTerm assignment,
        secondResult.sourceTermResult.semanticTerm assignment⟩
      ⟨firstResult.targetTermResult.semanticTerm
          (substitutionResult.semanticSubstitution assignment),
        secondResult.targetTermResult.semanticTerm
          (substitutionResult.semanticSubstitution assignment)⟩
      firstCoherence secondCoherence

noncomputable def IncDepRawSubstitutionFiberModel.pair
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {firstTyping : IncDepRawHasType target first domain}
    {secondTyping : IncDepRawHasType target second (codomain.instantiate first)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate first))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (firstResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := firstTyping) domainResult)
    (secondResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := secondTyping)
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        firstResult.sourceTermResult.semanticTerm
        firstResult.targetTermResult.semanticTerm
        firstResult.semanticTerm_coherence)) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.pairRule firstTyping secondTyping)
      (IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
        domainResult codomainResult
        (model.sigmaCoherence domainResult codomainResult)).toFormationFiberResult :=
  IncDepRawTypingSubstitutionFiberResult.pair instantiatedFormation
    domainResult codomainResult (model.sigmaCoherence domainResult codomainResult)
    firstResult secondResult

noncomputable def IncDepRawSubstitutionFiberModel.pairRebased
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {firstTyping : IncDepRawHasType target first domain}
    {secondTyping : IncDepRawHasType target second (codomain.instantiate first)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate first))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (firstResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := firstTyping) domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (secondResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := secondTyping) structuralResult)
    (alignment : IncDepRawInstantiateFormationAlignment domainResult
      codomainResult firstResult.sourceTermResult.semanticTerm
      firstResult.targetTermResult.semanticTerm structuralResult)
    (structuralRebase :
      let aligned := alignment.toAlignedResult firstResult.semanticTerm_coherence
      IncDepRawFormationSubstitutionFiberRebase structuralResult
        aligned.toFormationFiberResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.pairRule firstTyping secondTyping)
      (model.sigma domainResult codomainResult) := by
  let aligned := alignment.toAlignedResult firstResult.semanticTerm_coherence
  let alignedSecond := secondResult.rebase structuralRebase
  let canonicalSecond := alignedSecond.rebaseToCanonical (aligned := aligned)
  exact model.pair instantiatedFormation domainResult codomainResult firstResult
    canonicalSecond

noncomputable def IncDepRawSubstitutionFiberModel.pairCoherent
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {firstTyping : IncDepRawHasType target first domain}
    {secondTyping : IncDepRawHasType target second (codomain.instantiate first)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate first))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (firstResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := firstTyping) domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (secondResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := secondTyping) structuralResult)
    (coherence : IncDepRawInstantiateFormationCoherence domainResult
      codomainResult firstResult.sourceTermResult.semanticTerm
      firstResult.targetTermResult.semanticTerm firstResult.semanticTerm_coherence
      structuralResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.pairRule firstTyping secondTyping)
      (model.sigma domainResult codomainResult) :=
  model.pairRebased instantiatedFormation domainResult codomainResult firstResult
    structuralResult secondResult coherence.alignment coherence.structuralRebase

noncomputable def IncDepRawTypingSubstitutionFiberResult.first
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawSigmaSubstitutionCoherence domainResult codomainResult)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping)
      (IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
        domainResult codomainResult coherence).toFormationFiberResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.firstRule pairTyping) domainResult where
  targetTermResult := IncDepRawTypingSemanticResult.first
    pairResult.targetTermResult
  sourceTermResult := IncDepRawTypingSemanticResult.first
    pairResult.sourceTermResult
  semanticTerm_coherence := by
    funext assignment
    have pairCoherence := congrFun pairResult.semanticTerm_coherence assignment
    have firstCoherence := congrArg Sigma.fst pairCoherence
    exact firstCoherence

noncomputable def IncDepRawSubstitutionFiberModel.first
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping)
      (IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
        domainResult codomainResult
        (model.sigmaCoherence domainResult codomainResult)).toFormationFiberResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.firstRule pairTyping) domainResult :=
  IncDepRawTypingSubstitutionFiberResult.first domainResult codomainResult
    (model.sigmaCoherence domainResult codomainResult) pairResult

noncomputable def IncDepRawTypingSubstitutionFiberResult.second
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (coherence : IncDepRawSigmaSubstitutionCoherence domainResult codomainResult)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping)
      (IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
        domainResult codomainResult coherence).toFormationFiberResult) :
    let firstCoherence :
        domainResult.semanticFiberEquivalence.transport
            (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm) =
          (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm).substitute
            substitutionResult.semanticSubstitution := by
      funext assignment
      exact congrArg Sigma.fst
        (congrFun pairResult.semanticTerm_coherence assignment)
    let instantiatedResult :=
      IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
        (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
        firstCoherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.secondRule pairTyping)
      instantiatedResult := by
  dsimp
  let sigmaResult :=
    IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
      domainResult codomainResult coherence
  let firstCoherence :
      domainResult.semanticFiberEquivalence.transport
          (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm) =
        (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm).substitute
          substitutionResult.semanticSubstitution := by
    funext assignment
    exact congrArg Sigma.fst
      (congrFun pairResult.semanticTerm_coherence assignment)
  let instantiatedResult :=
    IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
      instantiatedFormation domainResult codomainResult
      (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
      (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
      firstCoherence
  refine
    { targetTermResult := IncDepRawTypingSemanticResult.second
        pairResult.targetTermResult
      sourceTermResult :=
        { semanticTerm := IncSigmaTerm.second
            pairResult.sourceTermResult.semanticTerm }
      semanticTerm_coherence := ?_ }
  funext assignment
  change ((domainResult.instantiateFiberEquivalence codomainResult
      (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
      (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
      firstCoherence).fiberEquiv assignment).forward
        (IncSigmaTerm.second pairResult.sourceTermResult.semanticTerm assignment) =
    IncSigmaTerm.second pairResult.targetTermResult.semanticTerm
      (substitutionResult.semanticSubstitution assignment)
  rw [IncDepRawFormationSubstitutionFiberResult.instantiateFiberEquivalence_forward]
  exact (sigmaResult.fiberEquiv assignment).dependentEquiv
    |>.sigmaForward_second_eq_of_eq
      (pairResult.sourceTermResult.semanticTerm assignment)
      (pairResult.targetTermResult.semanticTerm
        (substitutionResult.semanticSubstitution assignment))
      (congrFun pairResult.semanticTerm_coherence assignment)

noncomputable def IncDepRawSubstitutionFiberModel.second
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation)
      domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping)
      (IncDepRawSigmaFormationSubstitutionFiberResult.ofCoherence
        domainResult codomainResult
        (model.sigmaCoherence domainResult codomainResult)).toFormationFiberResult) :
    let firstCoherence :
        domainResult.semanticFiberEquivalence.transport
            (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm) =
          (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm).substitute
            substitutionResult.semanticSubstitution := by
      funext assignment
      exact congrArg Sigma.fst
        (congrFun pairResult.semanticTerm_coherence assignment)
    let instantiatedResult :=
      IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
        (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
        firstCoherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.secondRule pairTyping)
      instantiatedResult :=
  IncDepRawTypingSubstitutionFiberResult.second instantiatedFormation
    domainResult codomainResult (model.sigmaCoherence domainResult codomainResult)
    pairResult

noncomputable def IncDepRawSubstitutionFiberModel.secondRebased
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping) (model.sigma domainResult codomainResult))
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (alignment : IncDepRawInstantiateFormationAlignment domainResult
      codomainResult
      (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
      (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
      structuralResult) :
    let firstCoherence :
        domainResult.semanticFiberEquivalence.transport
            (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm) =
          (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm).substitute
            substitutionResult.semanticSubstitution := by
      funext assignment
      exact congrArg Sigma.fst
        (congrFun pairResult.semanticTerm_coherence assignment)
    let aligned := alignment.toAlignedResult firstCoherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.secondRule pairTyping)
      aligned.toFormationFiberResult := by
  dsimp
  let firstCoherence :
      domainResult.semanticFiberEquivalence.transport
          (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm) =
        (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm).substitute
          substitutionResult.semanticSubstitution := by
    funext assignment
    exact congrArg Sigma.fst
      (congrFun pairResult.semanticTerm_coherence assignment)
  let aligned := alignment.toAlignedResult firstCoherence
  let canonical := model.second instantiatedFormation domainResult codomainResult
    pairResult
  exact canonical.rebaseFromCanonical (aligned := aligned)

noncomputable def IncDepRawSubstitutionFiberModel.secondCoherent
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping) (model.sigma domainResult codomainResult))
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (coherence : IncDepRawInstantiateFormationCoherence domainResult
      codomainResult
      (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
      (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
      (by
        funext assignment
        exact congrArg Sigma.fst
          (congrFun pairResult.semanticTerm_coherence assignment))
      structuralResult) :
    let firstCoherence :
        domainResult.semanticFiberEquivalence.transport
            (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm) =
          (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm).substitute
            substitutionResult.semanticSubstitution := by
      funext assignment
      exact congrArg Sigma.fst
        (congrFun pairResult.semanticTerm_coherence assignment)
    let aligned := coherence.alignment.toAlignedResult firstCoherence
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.secondRule pairTyping)
      aligned.toFormationFiberResult :=
  model.secondRebased instantiatedFormation domainResult codomainResult pairResult
    structuralResult coherence.alignment

noncomputable def IncDepRawSubstitutionFiberModel.secondStructuralExact
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping) (model.sigma domainResult codomainResult))
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (coherence : IncDepRawInstantiateFormationCoherence domainResult
      codomainResult
      (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
      (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
      (by
        funext assignment
        exact congrArg Sigma.fst
          (congrFun pairResult.semanticTerm_coherence assignment))
      structuralResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.secondRule pairTyping)
      structuralResult := by
  let alignedResult := model.secondCoherent instantiatedFormation domainResult
    codomainResult pairResult structuralResult coherence
  exact alignedResult.rebaseSymm coherence.structuralRebase

def IncDepRawTypingFormationSemanticResult.unit
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    (contextResult : IncDepRawContextSemanticResult contextWellFormed) :
    IncDepRawTypingFormationSemanticResult
      (typing := IncDepRawHasType.unitRule (context := context))
      (typeFormation := IncDepRawWellFormed.unit) contextResult where
  formationResult := IncDepRawFormationSemanticResult.unit contextResult
  typingResult := IncDepRawTypingSemanticResult.unit contextResult

def IncDepRawTypingFormationSemanticResult.refl
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm} {termTyping : IncDepRawHasType context term type}
    {typeFormation : IncDepRawWellFormed context type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (termResult : IncDepRawTypingFormationSemanticResult
      (typing := termTyping) (typeFormation := typeFormation) contextResult) :
    IncDepRawTypingFormationSemanticResult
      (typing := IncDepRawHasType.reflRule termTyping)
      (typeFormation := IncDepRawWellFormed.identity typeFormation
        termTyping termTyping) contextResult where
  formationResult := IncDepRawFormationSemanticResult.identity
    termResult.formationResult termResult.typingResult.semanticTerm
      termResult.typingResult.semanticTerm
  typingResult := IncDepRawTypingSemanticResult.refl termResult.typingResult

noncomputable def incDepRawOneUnitVariableTypingSemantic :=
  incDepRawOneUnitContextSemanticTree.interpretVariable
    (IncDepRawLookup.here (context := []) (type := IncDepRawType.unit))

noncomputable def incDepRawOneUnitReflTypingSemantic :=
  IncDepRawTypingSemanticResult.refl
    incDepRawOneUnitVariableTypingSemantic

noncomputable def incDepRawDependentReflTypingSemantic :=
  IncDepRawTypingSemanticResult.lambda
    incDepRawOneUnitReflTypingSemantic

noncomputable def incDepRawClosedUnitTypingSemantic :=
  incDepRawEmptyContextSemanticTree.interpretUnit

noncomputable def incDepRawDependentReflApplicationTypingSemantic :=
  IncDepRawTypingSemanticResult.apply
    incDepRawDependentReflTypingSemantic
    incDepRawClosedUnitTypingSemantic

theorem incDepRawDependentReflTypingSemantic_beta :
    incDepRawDependentReflApplicationTypingSemantic.semanticTerm =
      IncIdentityTerm.refl incDepUnitTerm := by
  rfl

noncomputable def incDepRawClosedUnitReflTypingSemantic :=
  IncDepRawTypingSemanticResult.refl incDepRawClosedUnitTypingSemantic

noncomputable def incDepRawClosedUnitReflFiberTypingSemantic :
    IncDepRawTypingSemanticResult
      (IncDepRawHasType.reflRule
        (IncDepRawHasType.unitRule (context := [])))
      incDepRawEmptyContextSemantic
      (fun assignment => incDepRawDependentReflSemanticCodomain
        ⟨assignment, incDepRawClosedUnitTypingSemantic.semanticTerm assignment⟩) where
  semanticTerm := fun _ => ⟨⟨rfl⟩⟩

noncomputable def incDepRawDependentPairTypingSemantic :=
  IncDepRawTypingSemanticResult.pair
    (domain := IncDepRawType.unit)
    (codomain := .identity .unit (.var 0) (.var 0))
    (first := IncDepRawTerm.unit) (second := .refl .unit)
    (firstTyping := IncDepRawHasType.unitRule)
    (secondTyping := IncDepRawHasType.reflRule IncDepRawHasType.unitRule)
    (semanticCodomain := incDepRawDependentReflSemanticCodomain)
    incDepRawClosedUnitTypingSemantic incDepRawClosedUnitReflFiberTypingSemantic

noncomputable def incDepRawDependentPairFirstTypingSemantic :=
  IncDepRawTypingSemanticResult.first incDepRawDependentPairTypingSemantic

noncomputable def incDepRawDependentPairSecondTypingSemantic :=
  IncDepRawTypingSemanticResult.second incDepRawDependentPairTypingSemantic

theorem incDepRawDependentPairFirstTypingSemantic_beta :
    incDepRawDependentPairFirstTypingSemantic.semanticTerm = incDepUnitTerm := by
  rfl

theorem incDepRawDependentPairSecondTypingSemantic_beta :
    incDepRawDependentPairSecondTypingSemantic.semanticTerm =
      IncIdentityTerm.refl incDepUnitTerm := by
  rfl

structure IncDepRawReadyTypingSemanticResult
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    (ready : IncDepRawTypingSemanticReady typing)
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (contextTree : IncDepRawContextSemanticTree contextResult) where
  semanticType : IncTypeInContext contextResult.semanticContext
  typingResult : IncDepRawTypingSemanticResult typing contextResult semanticType

structure IncDepRawReadyVariableFormationSemanticResult
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    (typeReady : IncDepRawFormationSemanticReady typeFormation)
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (contextTree : IncDepRawContextSemanticTree contextResult) where
  formationResult : IncDepRawFormationSemanticResult typeFormation contextResult
  lookupType_coherence :
    (contextTree.interpretLookup lookup).semanticType =
      formationResult.semanticType

noncomputable def IncDepRawReadyVariableFormationSemanticResult.here
    {context : List IncDepRawType} {head : IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {headReady : IncDepRawFormationSemanticReady headWellFormed}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    (contextTree : IncDepRawContextSemanticTree contextResult)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    let renamed := headReady.weakenResult (head := head)
    let extendedTree := IncDepRawContextSemanticTree.extend contextTree headResult
    IncDepRawReadyVariableFormationSemanticResult
      (lookup := IncDepRawLookup.here (context := context) (type := head))
      renamed.renamedReady extendedTree := by
  dsimp
  let renamed := headReady.weakenResult (head := head)
  refine
    { formationResult := renamed.weakenSemantic headResult headResult
      lookupType_coherence := rfl }

noncomputable def IncDepRawReadyVariableFormationSemanticResult.there
    {context : List IncDepRawType} {position : Nat} {type head : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {headWellFormed : IncDepRawWellFormed context head}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    (previous : IncDepRawReadyVariableFormationSemanticResult
      (lookup := lookup) typeReady contextTree)
    (headResult : IncDepRawFormationSemanticResult headWellFormed contextResult) :
    let renamed := typeReady.weakenResult (head := head)
    let extendedTree := IncDepRawContextSemanticTree.extend contextTree headResult
    IncDepRawReadyVariableFormationSemanticResult
      (lookup := IncDepRawLookup.there (head := head) lookup)
      renamed.renamedReady extendedTree := by
  dsimp
  let renamed := typeReady.weakenResult (head := head)
  let extendedTree := IncDepRawContextSemanticTree.extend contextTree headResult
  refine
    { formationResult := renamed.weakenSemantic previous.formationResult headResult
      lookupType_coherence := ?_ }
  exact congrArg (fun family => family.reindex
    (contextResult.semanticContext.extendProjection headResult.semanticType))
    previous.lookupType_coherence

noncomputable def IncDepRawReadyVariableFormationSemanticResult.toTypingFormation
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    (result : IncDepRawReadyVariableFormationSemanticResult
      (lookup := lookup) typeReady contextTree) :
    IncDepRawTypingFormationSemanticResult
      (typing := IncDepRawHasType.varRule lookup)
      (typeFormation := typeFormation) contextResult :=
  IncDepRawTypingFormationSemanticResult.align result.formationResult
    (contextTree.interpretVariable lookup) result.lookupType_coherence

noncomputable def IncDepRawReadyVariableFormationSemanticResult.toVariableSubstitution
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {targetTree : IncDepRawContextSemanticTree targetResult}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetAlignment : IncDepRawReadyVariableFormationSemanticResult
      (lookup := lookup) typeReady targetTree)
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (sourceReplacement : IncDepRawTypingSemanticResult
      (substitution.preserves lookup) sourceResult
      typeResult.sourceFormationResult.semanticType)
    (targetFormationCoherence :
      typeResult.targetFormationResult.semanticType =
        targetAlignment.formationResult.semanticType)
    (variableCoherence :
      typeResult.semanticFiberEquivalence.transport
          sourceReplacement.semanticTerm =
        (targetAlignment.toTypingFormation.typingResult.castType
          targetFormationCoherence.symm).semanticTerm.substitute
            substitutionResult.semanticSubstitution) :
    IncDepRawVariableSubstitutionFiberResult
      (lookup := lookup) typeResult where
  targetVariable :=
    (targetAlignment.toTypingFormation.typingResult.castType
      targetFormationCoherence.symm).semanticTerm
  sourceReplacement := sourceReplacement
  variableCoherence := variableCoherence

noncomputable def IncDepRawReadyVariableFormationSemanticResult.toTypingSubstitution
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {targetTree : IncDepRawContextSemanticTree targetResult}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetAlignment : IncDepRawReadyVariableFormationSemanticResult
      (lookup := lookup) typeReady targetTree)
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    (sourceFormationCoherence : replacements.semanticType lookup =
      typeResult.sourceFormationResult.semanticType)
    (targetFormationCoherence :
      typeResult.targetFormationResult.semanticType =
        targetAlignment.formationResult.semanticType)
    (variableCoherence :
      typeResult.semanticFiberEquivalence.transport
          (replacements.typingResultAligned lookup
            typeResult.sourceFormationResult.semanticType
            sourceFormationCoherence).semanticTerm =
        (targetAlignment.toTypingFormation.typingResult.castType
          targetFormationCoherence.symm).semanticTerm.substitute
            substitutionResult.semanticSubstitution) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.varRule lookup) typeResult :=
  (targetAlignment.toVariableSubstitution typeResult
    (replacements.typingResultAligned lookup
      typeResult.sourceFormationResult.semanticType sourceFormationCoherence)
    targetFormationCoherence variableCoherence).toTyping

noncomputable def IncDepRawSubstitutionFiberModel.variable
    (_model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {targetTree : IncDepRawContextSemanticTree targetResult}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (targetAlignment : IncDepRawReadyVariableFormationSemanticResult
      (lookup := lookup) typeReady targetTree)
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult)
    (sourceFormationCoherence : replacements.semanticType lookup =
      typeResult.sourceFormationResult.semanticType)
    (targetFormationCoherence :
      typeResult.targetFormationResult.semanticType =
        targetAlignment.formationResult.semanticType)
    (variableCoherence :
      typeResult.semanticFiberEquivalence.transport
          (replacements.typingResultAligned lookup
            typeResult.sourceFormationResult.semanticType
            sourceFormationCoherence).semanticTerm =
        (targetAlignment.toTypingFormation.typingResult.castType
          targetFormationCoherence.symm).semanticTerm.substitute
            substitutionResult.semanticSubstitution) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.varRule lookup) typeResult :=
  targetAlignment.toTypingSubstitution typeResult replacements
    sourceFormationCoherence targetFormationCoherence variableCoherence

structure IncDepRawVariableSubstitutionProvider where
  dispatchVariable : ∀
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult},
    (typeReady : IncDepRawFormationDispatchReady typeFormation) →
    (targetTree : IncDepRawContextSemanticTree targetResult) →
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult) →
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) →
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.varRule lookup) typeResult

structure IncDepRawTypingSubstitutionDispatchResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    (targetTyping : IncDepRawHasType target term type)
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  typeFormation : IncDepRawWellFormed target type
  typeReady : IncDepRawFormationDispatchReady typeFormation
  formationResult : IncDepRawFormationSubstitutionFiberResult
    (targetFormation := typeFormation) substitutionResult
  typingResult : IncDepRawTypingSubstitutionFiberResult
    (targetTyping := targetTyping) formationResult

structure IncDepRawStrictTypingSubstitutionDispatchResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {targetFormationReady :
      IncDepRawCoherentFormationDispatchReady targetFormation}
    (targetReady : IncDepRawStrictTypingDispatchReady targetTyping
      targetFormationReady)
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) where
  formationResult : IncDepRawFormationSubstitutionFiberResult
    (targetFormation := targetFormation) substitutionResult
  typingResult : IncDepRawTypingSubstitutionFiberResult
    (targetTyping := targetTyping) formationResult

def IncDepRawStrictTypingSubstitutionDispatchResult.toDispatchResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {targetFormation : IncDepRawWellFormed target type}
    {targetFormationReady :
      IncDepRawCoherentFormationDispatchReady targetFormation}
    {targetReady : IncDepRawStrictTypingDispatchReady targetTyping
      targetFormationReady}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawStrictTypingSubstitutionDispatchResult targetReady
      substitutionResult) :
    IncDepRawTypingSubstitutionDispatchResult targetTyping substitutionResult where
  typeFormation := targetFormation
  typeReady := targetReady.formationDispatchReady
  formationResult := result.formationResult
  typingResult := result.typingResult

def IncDepRawTypingSubstitutionDispatchResult.semanticTargetType
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult) : IncTypeInContext targetResult.semanticContext :=
  result.formationResult.targetFormationResult.semanticType

def IncDepRawTypingSubstitutionDispatchResult.semanticSourceType
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult) : IncTypeInContext sourceResult.semanticContext :=
  result.formationResult.sourceFormationResult.semanticType

def IncDepRawTypingSubstitutionFiberResult.castFormation
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {targetFormation : IncDepRawWellFormed target type}
    {left right : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := targetFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) left)
    (alignment : left = right) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) right := by
  cases alignment
  exact result

def IncDepRawTypingSubstitutionDispatchResult.typingResultAligned
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult)
    (expected : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := result.typeFormation) substitutionResult)
    (alignment : result.formationResult = expected) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) expected :=
  result.typingResult.castFormation alignment

def IncDepRawTypingSubstitutionDispatchResult.typingResultAlignedAcross
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult)
    {expectedFormation : IncDepRawWellFormed target type}
    (formationAlignment : result.typeFormation = expectedFormation)
    (expected : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := expectedFormation) substitutionResult)
    (alignment : HEq result.formationResult expected) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) expected := by
  cases formationAlignment
  exact result.typingResult.castFormation (eq_of_heq alignment)

structure IncDepRawTypingSubstitutionDispatchAlignment
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult)
    {expectedFormation : IncDepRawWellFormed target type}
    (expectedResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := expectedFormation) substitutionResult) where
  formationAlignment : result.typeFormation = expectedFormation
  resultAlignment : HEq result.formationResult expectedResult

structure IncDepRawTypingSubstitutionAlignedDispatchResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    (targetTyping : IncDepRawHasType target term type)
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult)
    {expectedFormation : IncDepRawWellFormed target type}
    (expectedResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := expectedFormation) substitutionResult) where
  dispatchResult : IncDepRawTypingSubstitutionDispatchResult targetTyping
    substitutionResult
  alignment : IncDepRawTypingSubstitutionDispatchAlignment dispatchResult
    expectedResult

def IncDepRawTypingSubstitutionAlignedDispatchResult.typingResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {expectedFormation : IncDepRawWellFormed target type}
    {expectedResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := expectedFormation) substitutionResult}
    (result : IncDepRawTypingSubstitutionAlignedDispatchResult targetTyping
      substitutionResult expectedResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) expectedResult :=
  result.dispatchResult.typingResultAlignedAcross
    result.alignment.formationAlignment expectedResult
    result.alignment.resultAlignment

def IncDepRawTypingSubstitutionDispatchAlignment.exact
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult) :
    IncDepRawTypingSubstitutionDispatchAlignment result result.formationResult where
  formationAlignment := rfl
  resultAlignment := HEq.rfl

def IncDepRawTypingSubstitutionAlignedDispatchResult.exact
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult) :
    IncDepRawTypingSubstitutionAlignedDispatchResult targetTyping
      substitutionResult result.formationResult where
  dispatchResult := result
  alignment := IncDepRawTypingSubstitutionDispatchAlignment.exact result

theorem IncDepRawTypingSubstitutionAlignedDispatchResult.exact_typingResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult) :
    (IncDepRawTypingSubstitutionAlignedDispatchResult.exact result).typingResult =
      result.typingResult := by
  rfl

def IncDepRawTypingSubstitutionDispatchAlignment.typingResult
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {targetTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    {result : IncDepRawTypingSubstitutionDispatchResult targetTyping
      substitutionResult}
    {expectedFormation : IncDepRawWellFormed target type}
    {expectedResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := expectedFormation) substitutionResult}
    (alignment : IncDepRawTypingSubstitutionDispatchAlignment result
      expectedResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := targetTyping) expectedResult :=
  result.typingResultAlignedAcross alignment.formationAlignment expectedResult
    alignment.resultAlignment

noncomputable def IncDepRawVariableSubstitutionProvider.dispatch
    (provider : IncDepRawVariableSubstitutionProvider)
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawFormationDispatchReady typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    IncDepRawTypingSubstitutionFiberResult
      (targetTyping := IncDepRawHasType.varRule lookup) typeResult :=
  provider.dispatchVariable typeReady targetTree typeResult replacements

def IncDepRawSubstitutionFiberModel.dispatchTypingUnit
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.unitRule (context := target)) substitutionResult where
  typeFormation := IncDepRawWellFormed.unit
  typeReady := IncDepRawFormationDispatchReady.unit
  formationResult := model.unit substitutionResult
  typingResult := model.typingUnit substitutionResult

def IncDepRawSubstitutionFiberModel.dispatchStrictUnit
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    (substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult) :
    IncDepRawStrictTypingSubstitutionDispatchResult
      (IncDepRawStrictTypingDispatchReady.unitRule (context := target))
      substitutionResult where
  formationResult := model.unit substitutionResult
  typingResult := model.typingUnit substitutionResult

noncomputable def IncDepRawVariableSubstitutionProvider.dispatchResult
    (provider : IncDepRawVariableSubstitutionProvider)
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawFormationDispatchReady typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.varRule lookup) substitutionResult where
  typeFormation := typeFormation
  typeReady := typeReady
  formationResult := typeResult
  typingResult := provider.dispatch typeReady targetTree typeResult replacements

noncomputable def IncDepRawVariableSubstitutionProvider.dispatchStrictVariable
    (provider : IncDepRawVariableSubstitutionProvider)
    {source target : List IncDepRawType} {position : Nat}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {lookup : IncDepRawLookup target position type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (targetTree : IncDepRawContextSemanticTree targetResult)
    (typeResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := typeFormation) substitutionResult)
    (replacements : IncDepRawSubstitutionReplacementSemanticResult
      substitutionResult) :
    IncDepRawStrictTypingSubstitutionDispatchResult
      (IncDepRawStrictTypingDispatchReady.varRule
        (lookup := lookup) typeReady) substitutionResult where
  formationResult := typeResult
  typingResult := provider.dispatch typeReady.toDispatchReady targetTree typeResult
    replacements

noncomputable def IncDepRawSubstitutionFiberModel.dispatchRefl
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {termTyping : IncDepRawHasType target term type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (termReady : IncDepRawTypingDispatchReady termTyping)
    (termResult : IncDepRawTypingSubstitutionDispatchResult termTyping
      substitutionResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.reflRule termTyping) substitutionResult where
  typeFormation := IncDepRawWellFormed.identity termResult.typeFormation
    termTyping termTyping
  typeReady := IncDepRawFormationDispatchReady.identity
    termResult.typeReady termReady termReady
  formationResult := model.identity termResult.formationResult
    termResult.typingResult termResult.typingResult
  typingResult := model.refl termResult.formationResult termResult.typingResult

noncomputable def IncDepRawSubstitutionFiberModel.dispatchStrictRefl
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType}
    {substitution : IncDepRawSubstitution source target}
    {termTyping : IncDepRawHasType target term type}
    {typeFormation : IncDepRawWellFormed target type}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (typeReady : IncDepRawCoherentFormationDispatchReady typeFormation)
    (termReady : IncDepRawStrictTypingDispatchReady termTyping typeReady)
    (termResult : IncDepRawStrictTypingSubstitutionDispatchResult termReady
      substitutionResult) :
    IncDepRawStrictTypingSubstitutionDispatchResult
      (IncDepRawStrictTypingDispatchReady.reflRule typeReady termReady)
      substitutionResult where
  formationResult := model.identity termResult.formationResult
    termResult.typingResult termResult.typingResult
  typingResult := model.refl termResult.formationResult termResult.typingResult

noncomputable def IncDepRawSubstitutionFiberModel.dispatchLambda
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {bodyTyping : IncDepRawHasType (domain :: target) body codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawFormationDispatchReady domainFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (bodyResult : IncDepRawTypingSubstitutionDispatchResult bodyTyping
      domainResult.liftSubstitution) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.lambdaRule domainFormation bodyTyping)
      substitutionResult where
  typeFormation := IncDepRawWellFormed.pi domainFormation
    bodyResult.typeFormation
  typeReady := IncDepRawFormationDispatchReady.pi domainReady
    bodyResult.typeReady
  formationResult := model.pi domainResult bodyResult.formationResult
  typingResult := model.lambda domainResult bodyResult.formationResult
    bodyResult.typingResult

noncomputable def IncDepRawSubstitutionFiberModel.dispatchStrictLambda
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {bodyTyping : IncDepRawHasType (domain :: target) body codomain}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawCoherentFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawCoherentFormationDispatchReady codomainFormation)
    (bodyReady : IncDepRawStrictTypingDispatchReady bodyTyping codomainReady)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (bodyResult : IncDepRawStrictTypingSubstitutionDispatchResult bodyReady
      domainResult.liftSubstitution) :
    IncDepRawStrictTypingSubstitutionDispatchResult
      (IncDepRawStrictTypingDispatchReady.lambdaRule domainReady codomainReady
        bodyReady) substitutionResult where
  formationResult := model.pi domainResult bodyResult.formationResult
  typingResult := model.lambda domainResult bodyResult.formationResult
    bodyResult.typingResult

noncomputable def IncDepRawSubstitutionFiberModel.dispatchFirst
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawFormationDispatchReady domainFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionDispatchResult pairTyping
      substitutionResult)
    (pairAlignment : IncDepRawTypingSubstitutionDispatchAlignment pairResult
      (model.sigma domainResult codomainResult)) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.firstRule pairTyping) substitutionResult where
  typeFormation := domainFormation
  typeReady := domainReady
  formationResult := domainResult
  typingResult := model.first domainResult codomainResult
    pairAlignment.typingResult

noncomputable def IncDepRawSubstitutionFiberModel.dispatchFirstAligned
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawFormationDispatchReady domainFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionDispatchResult pairTyping
      substitutionResult)
    (pairAlignment : IncDepRawTypingSubstitutionDispatchAlignment pairResult
      (model.sigma domainResult codomainResult)) :
    IncDepRawTypingSubstitutionAlignedDispatchResult
      (IncDepRawHasType.firstRule pairTyping) substitutionResult domainResult := by
  let result := model.dispatchFirst domainReady domainResult codomainResult
    pairResult pairAlignment
  exact
    { dispatchResult := result
      alignment :=
        { formationAlignment := rfl
          resultAlignment := HEq.rfl } }

noncomputable def IncDepRawSubstitutionFiberModel.secondCanonical
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionFiberResult
      (targetTyping := pairTyping)
      (model.sigma domainResult codomainResult)) :
    IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult :=
  IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
    instantiatedFormation domainResult codomainResult
    (IncSigmaTerm.first pairResult.sourceTermResult.semanticTerm)
    (IncSigmaTerm.first pairResult.targetTermResult.semanticTerm)
    (by
      funext assignment
      exact congrArg Sigma.fst
        (congrFun pairResult.semanticTerm_coherence assignment))

noncomputable def IncDepRawSubstitutionFiberModel.dispatchSecond
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionDispatchResult pairTyping
      substitutionResult)
    (pairAlignment : IncDepRawTypingSubstitutionDispatchAlignment pairResult
      (model.sigma domainResult codomainResult)) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.secondRule pairTyping) substitutionResult := by
  let alignedPair := pairAlignment.typingResult
  let instantiatedResult := model.secondCanonical instantiatedFormation
    domainResult codomainResult alignedPair
  exact
    { typeFormation := instantiatedFormation
      typeReady := resultReady
      formationResult := instantiatedResult
      typingResult := model.second instantiatedFormation domainResult
        codomainResult alignedPair }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchSecondAligned
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionDispatchResult pairTyping
      substitutionResult)
    (pairAlignment : IncDepRawTypingSubstitutionDispatchAlignment pairResult
      (model.sigma domainResult codomainResult)) :
    IncDepRawTypingSubstitutionAlignedDispatchResult
      (IncDepRawHasType.secondRule pairTyping) substitutionResult
      (model.secondCanonical instantiatedFormation domainResult codomainResult
        pairAlignment.typingResult) := by
  let result := model.dispatchSecond instantiatedFormation resultReady domainResult
    codomainResult pairResult pairAlignment
  exact
    { dispatchResult := result
      alignment :=
        { formationAlignment := rfl
          resultAlignment := HEq.rfl } }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchSecondStructural
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionDispatchResult pairTyping
      substitutionResult)
    (pairAlignment : IncDepRawTypingSubstitutionDispatchAlignment pairResult
      (model.sigma domainResult codomainResult))
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (instantiateAlignment : IncDepRawInstantiateFormationAlignment domainResult
      codomainResult
      (IncSigmaTerm.first
        pairAlignment.typingResult.sourceTermResult.semanticTerm)
      (IncSigmaTerm.first
        pairAlignment.typingResult.targetTermResult.semanticTerm)
      structuralResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.secondRule pairTyping) substitutionResult := by
  let alignedPair := pairAlignment.typingResult
  let firstCoherence :
      domainResult.semanticFiberEquivalence.transport
          (IncSigmaTerm.first alignedPair.sourceTermResult.semanticTerm) =
        (IncSigmaTerm.first alignedPair.targetTermResult.semanticTerm).substitute
          substitutionResult.semanticSubstitution := by
    funext assignment
    exact congrArg Sigma.fst
      (congrFun alignedPair.semanticTerm_coherence assignment)
  let alignedFormation := instantiateAlignment.toAlignedResult firstCoherence
  exact
    { typeFormation := instantiatedFormation
      typeReady := resultReady
      formationResult := alignedFormation.toFormationFiberResult
      typingResult := model.secondRebased instantiatedFormation domainResult
        codomainResult alignedPair structuralResult instantiateAlignment }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchSecondCoherent
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {pairTyping : IncDepRawHasType target pair (.sigma domain codomain)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate (.first pair)))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (pairResult : IncDepRawTypingSubstitutionDispatchResult pairTyping
      substitutionResult)
    (pairAlignment : IncDepRawTypingSubstitutionDispatchAlignment pairResult
      (model.sigma domainResult codomainResult))
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (coherence : IncDepRawInstantiateFormationCoherence domainResult
      codomainResult
      (IncSigmaTerm.first
        pairAlignment.typingResult.sourceTermResult.semanticTerm)
      (IncSigmaTerm.first
        pairAlignment.typingResult.targetTermResult.semanticTerm)
      (by
        funext assignment
        exact congrArg Sigma.fst
          (congrFun pairAlignment.typingResult.semanticTerm_coherence assignment))
      structuralResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.secondRule pairTyping) substitutionResult :=
  let alignedPair := pairAlignment.typingResult
  { typeFormation := instantiatedFormation
    typeReady := resultReady
    formationResult := structuralResult
    typingResult := model.secondStructuralExact instantiatedFormation domainResult
      codomainResult alignedPair structuralResult coherence }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchApply
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionDispatchResult functionTyping
      substitutionResult)
    (argumentResult : IncDepRawTypingSubstitutionDispatchResult argumentTyping
      substitutionResult)
    (functionAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      functionResult (model.pi domainResult codomainResult))
    (argumentAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      argumentResult domainResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.applyRule functionTyping argumentTyping)
      substitutionResult := by
  let alignedFunction := functionAlignment.typingResult
  let alignedArgument := argumentAlignment.typingResult
  let instantiatedResult :=
    IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
      instantiatedFormation domainResult codomainResult
      alignedArgument.sourceTermResult.semanticTerm
      alignedArgument.targetTermResult.semanticTerm
      alignedArgument.semanticTerm_coherence
  exact
    { typeFormation := instantiatedFormation
      typeReady := resultReady
      formationResult := instantiatedResult
      typingResult := model.apply instantiatedFormation domainResult
        codomainResult alignedFunction alignedArgument }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchApplyAligned
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionDispatchResult functionTyping
      substitutionResult)
    (argumentResult : IncDepRawTypingSubstitutionDispatchResult argumentTyping
      substitutionResult)
    (functionAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      functionResult (model.pi domainResult codomainResult))
    (argumentAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      argumentResult domainResult) :
    IncDepRawTypingSubstitutionAlignedDispatchResult
      (IncDepRawHasType.applyRule functionTyping argumentTyping)
      substitutionResult
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        argumentAlignment.typingResult.sourceTermResult.semanticTerm
        argumentAlignment.typingResult.targetTermResult.semanticTerm
        argumentAlignment.typingResult.semanticTerm_coherence) := by
  let result := model.dispatchApply instantiatedFormation resultReady domainResult
    codomainResult functionResult argumentResult functionAlignment
    argumentAlignment
  exact
    { dispatchResult := result
      alignment :=
        { formationAlignment := rfl
          resultAlignment := HEq.rfl } }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchApplyStructural
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionDispatchResult functionTyping
      substitutionResult)
    (argumentResult : IncDepRawTypingSubstitutionDispatchResult argumentTyping
      substitutionResult)
    (functionAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      functionResult (model.pi domainResult codomainResult))
    (argumentAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      argumentResult domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (instantiateAlignment : IncDepRawInstantiateFormationAlignment domainResult
      codomainResult
      argumentAlignment.typingResult.sourceTermResult.semanticTerm
      argumentAlignment.typingResult.targetTermResult.semanticTerm
      structuralResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.applyRule functionTyping argumentTyping)
      substitutionResult := by
  let alignedFunction := functionAlignment.typingResult
  let alignedArgument := argumentAlignment.typingResult
  let alignedFormation := instantiateAlignment.toAlignedResult
    alignedArgument.semanticTerm_coherence
  exact
    { typeFormation := instantiatedFormation
      typeReady := resultReady
      formationResult := alignedFormation.toFormationFiberResult
      typingResult := model.applyRebased instantiatedFormation domainResult
        codomainResult alignedFunction alignedArgument structuralResult
        instantiateAlignment }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchApplyCoherent
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {functionTyping : IncDepRawHasType target function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType target argument domain}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate argument))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (resultReady : IncDepRawFormationDispatchReady instantiatedFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (functionResult : IncDepRawTypingSubstitutionDispatchResult functionTyping
      substitutionResult)
    (argumentResult : IncDepRawTypingSubstitutionDispatchResult argumentTyping
      substitutionResult)
    (functionAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      functionResult (model.pi domainResult codomainResult))
    (argumentAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      argumentResult domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (coherence : IncDepRawInstantiateFormationCoherence domainResult
      codomainResult
      argumentAlignment.typingResult.sourceTermResult.semanticTerm
      argumentAlignment.typingResult.targetTermResult.semanticTerm
      argumentAlignment.typingResult.semanticTerm_coherence structuralResult) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.applyRule functionTyping argumentTyping)
      substitutionResult :=
  let alignedFunction := functionAlignment.typingResult
  let alignedArgument := argumentAlignment.typingResult
  { typeFormation := instantiatedFormation
    typeReady := resultReady
    formationResult := structuralResult
    typingResult := model.applyStructuralExact instantiatedFormation domainResult
      codomainResult alignedFunction alignedArgument structuralResult coherence }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchPair
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {firstTyping : IncDepRawHasType target first domain}
    {secondTyping : IncDepRawHasType target second (codomain.instantiate first)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate first))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawFormationDispatchReady codomainFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (firstResult : IncDepRawTypingSubstitutionDispatchResult firstTyping
      substitutionResult)
    (secondResult : IncDepRawTypingSubstitutionDispatchResult secondTyping
      substitutionResult)
    (firstAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      firstResult domainResult)
    (secondAlignment : IncDepRawTypingSubstitutionDispatchAlignment secondResult
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        firstAlignment.typingResult.sourceTermResult.semanticTerm
        firstAlignment.typingResult.targetTermResult.semanticTerm
        firstAlignment.typingResult.semanticTerm_coherence)) :
    IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.pairRule firstTyping secondTyping)
      substitutionResult := by
  let alignedFirst := firstAlignment.typingResult
  let instantiatedResult :=
    IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
      instantiatedFormation domainResult codomainResult
      alignedFirst.sourceTermResult.semanticTerm
      alignedFirst.targetTermResult.semanticTerm
      alignedFirst.semanticTerm_coherence
  let alignedSecond := secondAlignment.typingResult
  exact
    { typeFormation := IncDepRawWellFormed.sigma domainFormation codomainFormation
      typeReady := IncDepRawFormationDispatchReady.sigma domainReady codomainReady
      formationResult := model.sigma domainResult codomainResult
      typingResult := model.pair instantiatedFormation domainResult codomainResult
        alignedFirst alignedSecond }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchPairAligned
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {firstTyping : IncDepRawHasType target first domain}
    {secondTyping : IncDepRawHasType target second (codomain.instantiate first)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate first))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawFormationDispatchReady codomainFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (firstResult : IncDepRawTypingSubstitutionDispatchResult firstTyping
      substitutionResult)
    (secondResult : IncDepRawTypingSubstitutionDispatchResult secondTyping
      substitutionResult)
    (firstAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      firstResult domainResult)
    (secondAlignment : IncDepRawTypingSubstitutionDispatchAlignment secondResult
      (IncDepRawFormationSubstitutionFiberResult.instantiateCanonical
        instantiatedFormation domainResult codomainResult
        firstAlignment.typingResult.sourceTermResult.semanticTerm
        firstAlignment.typingResult.targetTermResult.semanticTerm
        firstAlignment.typingResult.semanticTerm_coherence)) :
    IncDepRawTypingSubstitutionAlignedDispatchResult
      (IncDepRawHasType.pairRule firstTyping secondTyping) substitutionResult
      (model.sigma domainResult codomainResult) := by
  let result := model.dispatchPair instantiatedFormation domainReady codomainReady
    domainResult codomainResult firstResult secondResult firstAlignment
    secondAlignment
  exact
    { dispatchResult := result
      alignment :=
        { formationAlignment := rfl
          resultAlignment := HEq.rfl } }

noncomputable def IncDepRawSubstitutionFiberModel.dispatchPairStructural
    (model : IncDepRawSubstitutionFiberModel.{u})
    {source target : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {substitution : IncDepRawSubstitution source target}
    {domainFormation : IncDepRawWellFormed target domain}
    {codomainFormation : IncDepRawWellFormed (domain :: target) codomain}
    {firstTyping : IncDepRawHasType target first domain}
    {secondTyping : IncDepRawHasType target second (codomain.instantiate first)}
    (instantiatedFormation : IncDepRawWellFormed target
      (codomain.instantiate first))
    {sourceWellFormed : IncDepRawContext.WellFormed source}
    {targetWellFormed : IncDepRawContext.WellFormed target}
    {sourceResult : IncDepRawContextSemanticResult sourceWellFormed}
    {targetResult : IncDepRawContextSemanticResult targetWellFormed}
    {substitutionResult : IncDepRawSubstitutionSemanticResult substitution
      sourceResult targetResult}
    (domainReady : IncDepRawFormationDispatchReady domainFormation)
    (codomainReady : IncDepRawFormationDispatchReady codomainFormation)
    (domainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := domainFormation) substitutionResult)
    (codomainResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := codomainFormation) domainResult.liftSubstitution)
    (firstResult : IncDepRawTypingSubstitutionDispatchResult firstTyping
      substitutionResult)
    (secondResult : IncDepRawTypingSubstitutionDispatchResult secondTyping
      substitutionResult)
    (firstAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      firstResult domainResult)
    (structuralResult : IncDepRawFormationSubstitutionFiberResult
      (targetFormation := instantiatedFormation) substitutionResult)
    (secondAlignment : IncDepRawTypingSubstitutionDispatchAlignment
      secondResult structuralResult)
    (instantiateAlignment : IncDepRawInstantiateFormationAlignment domainResult
      codomainResult firstAlignment.typingResult.sourceTermResult.semanticTerm
      firstAlignment.typingResult.targetTermResult.semanticTerm structuralResult)
    (structuralRebase :
      let aligned := instantiateAlignment.toAlignedResult
        firstAlignment.typingResult.semanticTerm_coherence
      IncDepRawFormationSubstitutionFiberRebase structuralResult
        aligned.toFormationFiberResult) :
    IncDepRawTypingSubstitutionAlignedDispatchResult
      (IncDepRawHasType.pairRule firstTyping secondTyping) substitutionResult
      (model.sigma domainResult codomainResult) := by
  let alignedFirst := firstAlignment.typingResult
  let alignedSecond := secondAlignment.typingResult
  let typingResult := model.pairRebased instantiatedFormation domainResult
    codomainResult alignedFirst structuralResult alignedSecond
    instantiateAlignment structuralRebase
  let result : IncDepRawTypingSubstitutionDispatchResult
      (IncDepRawHasType.pairRule firstTyping secondTyping) substitutionResult :=
    { typeFormation := IncDepRawWellFormed.sigma domainFormation codomainFormation
      typeReady := IncDepRawFormationDispatchReady.sigma domainReady codomainReady
      formationResult := model.sigma domainResult codomainResult
      typingResult := typingResult }
  exact
    { dispatchResult := result
      alignment :=
        { formationAlignment := rfl
          resultAlignment := HEq.rfl } }

noncomputable def IncDepRawReadyTypingSemanticResult.variable
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    (contextTree : IncDepRawContextSemanticTree contextResult) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.varRule (lookup := lookup) typeReady)
      contextTree where
  semanticType := (contextTree.interpretLookup lookup).semanticType
  typingResult := contextTree.interpretVariable lookup

noncomputable def IncDepRawReadyTypingSemanticResult.variableAligned
    {context : List IncDepRawType} {position : Nat} {type : IncDepRawType}
    {lookup : IncDepRawLookup context position type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    (formation : IncDepRawReadyVariableFormationSemanticResult
      (lookup := lookup) typeReady contextTree) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.varRule (lookup := lookup) typeReady)
      contextTree where
  semanticType := formation.formationResult.semanticType
  typingResult := formation.toTypingFormation.typingResult

def IncDepRawReadyTypingSemanticResult.unit
    {context : List IncDepRawType}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    (contextTree : IncDepRawContextSemanticTree contextResult) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.unitRule (context := context)) contextTree where
  semanticType := fun _ => ULift Unit
  typingResult := contextTree.interpretUnit

noncomputable def IncDepRawReadyTypingSemanticResult.refl
    {context : List IncDepRawType} {type : IncDepRawType}
    {term : IncDepRawTerm} {termTyping : IncDepRawHasType context term type}
    {typeFormation : IncDepRawWellFormed context type}
    {typeReady : IncDepRawFormationSemanticReady typeFormation}
    {termReady : IncDepRawTypingSemanticReady termTyping}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    (termResult : IncDepRawReadyTypingSemanticResult termReady contextTree) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.reflRule typeReady termReady) contextTree where
  semanticType := IncIdentityType termResult.semanticType
    termResult.typingResult.semanticTerm termResult.typingResult.semanticTerm
  typingResult := IncDepRawTypingSemanticResult.refl termResult.typingResult

noncomputable def IncDepRawReadyTypingSemanticResult.lambda
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {body : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {bodyReady : IncDepRawTypingSemanticReady bodyTyping}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    (domainResult : IncDepRawFormationSemanticResult domainFormation contextResult)
    {extendedTree : IncDepRawContextSemanticTree
      (contextResult.extend (typeWellFormed := domainFormation)
        domainResult.semanticType)}
    (bodyResult : IncDepRawReadyTypingSemanticResult bodyReady extendedTree) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.lambdaRule domainReady codomainReady bodyReady)
      contextTree where
  semanticType := IncPiType domainResult.semanticType bodyResult.semanticType
  typingResult := IncDepRawTypingSemanticResult.lambda bodyResult.typingResult

noncomputable def IncDepRawReadyTypingSemanticResult.apply
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {function argument : IncDepRawTerm}
    {functionTyping : IncDepRawHasType context function (.pi domain codomain)}
    {argumentTyping : IncDepRawHasType context argument domain}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {functionReady : IncDepRawTypingSemanticReady functionTyping}
    {argumentReady : IncDepRawTypingSemanticReady argumentTyping}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (functionResult : IncDepRawTypingSemanticResult functionTyping contextResult
      (IncPiType semanticDomain semanticCodomain))
    (argumentResult : IncDepRawTypingSemanticResult argumentTyping contextResult
      semanticDomain) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.applyRule domainReady codomainReady
        functionReady argumentReady) contextTree where
  semanticType := IncTypeInContext.instantiateFiber semanticCodomain
    argumentResult.semanticTerm
  typingResult := IncDepRawTypingSemanticResult.apply
    functionResult argumentResult

noncomputable def IncDepRawReadyTypingSemanticResult.pair
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {firstTyping : IncDepRawHasType context first domain}
    {secondTyping : IncDepRawHasType context second (codomain.instantiate first)}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {firstReady : IncDepRawTypingSemanticReady firstTyping}
    {secondReady : IncDepRawTypingSemanticReady secondTyping}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (firstResult : IncDepRawTypingSemanticResult firstTyping contextResult
      semanticDomain)
    (secondResult : IncDepRawTypingSemanticResult secondTyping contextResult
      (IncTypeInContext.instantiateFiber semanticCodomain
        firstResult.semanticTerm)) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.pairRule domainReady codomainReady
        firstReady secondReady) contextTree where
  semanticType := IncSigmaType semanticDomain semanticCodomain
  typingResult := IncDepRawTypingSemanticResult.pair firstResult secondResult

noncomputable def IncDepRawReadyTypingSemanticResult.first
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {pairReady : IncDepRawTypingSemanticReady pairTyping}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (pairResult : IncDepRawTypingSemanticResult pairTyping contextResult
      (IncSigmaType semanticDomain semanticCodomain)) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.firstRule domainReady codomainReady pairReady)
      contextTree where
  semanticType := semanticDomain
  typingResult := IncDepRawTypingSemanticResult.first pairResult

noncomputable def IncDepRawReadyTypingSemanticResult.second
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {pair : IncDepRawTerm}
    {pairTyping : IncDepRawHasType context pair (.sigma domain codomain)}
    {domainFormation : IncDepRawWellFormed context domain}
    {codomainFormation : IncDepRawWellFormed (domain :: context) codomain}
    {domainReady : IncDepRawFormationSemanticReady domainFormation}
    {codomainReady : IncDepRawFormationSemanticReady codomainFormation}
    {pairReady : IncDepRawTypingSemanticReady pairTyping}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {contextTree : IncDepRawContextSemanticTree contextResult}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (pairResult : IncDepRawTypingSemanticResult pairTyping contextResult
      (IncSigmaType semanticDomain semanticCodomain)) :
    IncDepRawReadyTypingSemanticResult
      (IncDepRawTypingSemanticReady.secondRule domainReady codomainReady pairReady)
      contextTree where
  semanticType := IncTypeInContext.instantiateFiber semanticCodomain
    (IncSigmaTerm.first pairResult.semanticTerm)
  typingResult := IncDepRawTypingSemanticResult.second pairResult

theorem IncDepRawTypingSemanticResult.pi_beta
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {body argument : IncDepRawTerm}
    {domainFormation : IncDepRawWellFormed context domain}
    {bodyTyping : IncDepRawHasType (domain :: context) body codomain}
    {argumentTyping : IncDepRawHasType context argument domain}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (bodyResult : IncDepRawTypingSemanticResult bodyTyping
      (contextResult.extend (typeWellFormed := domainFormation) semanticDomain)
      semanticCodomain)
    (argumentResult : IncDepRawTypingSemanticResult argumentTyping contextResult
      semanticDomain) :
    IncPiTerm.apply
      (IncPiTerm.lambda bodyResult.semanticTerm) argumentResult.semanticTerm =
      fun assignment => bodyResult.semanticTerm
        ⟨assignment, argumentResult.semanticTerm assignment⟩ := by
  rfl

theorem IncDepRawTypingSemanticResult.sigma_first_beta
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {firstTyping : IncDepRawHasType context first domain}
    {secondTyping : IncDepRawHasType context second (codomain.instantiate first)}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (firstResult : IncDepRawTypingSemanticResult firstTyping contextResult
      semanticDomain)
    (secondResult : IncDepRawTypingSemanticResult secondTyping contextResult
      (IncTypeInContext.instantiateFiber semanticCodomain
        firstResult.semanticTerm)) :
    IncSigmaTerm.first
      (IncSigmaTerm.pair firstResult.semanticTerm secondResult.semanticTerm) =
      firstResult.semanticTerm := by
  rfl

theorem IncDepRawTypingSemanticResult.sigma_second_beta
    {context : List IncDepRawType} {domain codomain : IncDepRawType}
    {first second : IncDepRawTerm}
    {firstTyping : IncDepRawHasType context first domain}
    {secondTyping : IncDepRawHasType context second (codomain.instantiate first)}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (firstResult : IncDepRawTypingSemanticResult firstTyping contextResult
      semanticDomain)
    (secondResult : IncDepRawTypingSemanticResult secondTyping contextResult
      (IncTypeInContext.instantiateFiber semanticCodomain
        firstResult.semanticTerm)) :
    IncSigmaTerm.second
      (IncSigmaTerm.pair firstResult.semanticTerm secondResult.semanticTerm) =
      secondResult.semanticTerm := by
  rfl

theorem IncDepRawTypingSemanticResult.pi_eta
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (termResult : IncDepRawTypingSemanticResult typing contextResult
      (IncPiType semanticDomain semanticCodomain)) :
    IncPiTerm.lambda (fun extended =>
      termResult.semanticTerm extended.1 extended.2) =
      termResult.semanticTerm := by
  rfl

theorem IncDepRawTypingSemanticResult.sigma_eta
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {semanticDomain : IncTypeInContext contextResult.semanticContext}
    {semanticCodomain : IncTypeInContext
      (contextResult.semanticContext.extend semanticDomain)}
    (termResult : IncDepRawTypingSemanticResult typing contextResult
      (IncSigmaType semanticDomain semanticCodomain)) :
    IncSigmaTerm.pair (IncSigmaTerm.first termResult.semanticTerm)
      (IncSigmaTerm.second termResult.semanticTerm) =
      termResult.semanticTerm := by
  rfl

theorem IncDepRawTypingSemanticResult.identity_J_beta
    {context : List IncDepRawType} {term : IncDepRawTerm}
    {type : IncDepRawType} {typing : IncDepRawHasType context term type}
    {contextWellFormed : IncDepRawContext.WellFormed context}
    {contextResult : IncDepRawContextSemanticResult.{u} contextWellFormed}
    {semanticType : IncTypeInContext contextResult.semanticContext}
    (termResult : IncDepRawTypingSemanticResult typing contextResult semanticType)
    (motive : ∀ assignment
      (_left _right : semanticType assignment), Type u)
    (reflCase : ∀ assignment value,
      motive assignment value value) :
    IncIdentityTerm.J motive reflCase
      (IncIdentityTerm.refl termResult.semanticTerm) =
      fun assignment => reflCase assignment
        (termResult.semanticTerm assignment) := by
  exact IncIdentityTerm.J_beta motive reflCase termResult.semanticTerm

noncomputable def incDepRawDependentRefl_readySemanticResult :
    IncDepRawReadyTypingSemanticResult incDepRawDependentRefl_semanticReady
      incDepRawEmptyContextSemanticTree where
  semanticType := _
  typingResult := incDepRawDependentReflTypingSemantic

noncomputable def incDepRawDependentReflApplication_readySemanticResult :
    IncDepRawReadyTypingSemanticResult
      incDepRawDependentRefl_application_semanticReady
      incDepRawEmptyContextSemanticTree where
  semanticType := _
  typingResult := incDepRawDependentReflApplicationTypingSemantic

noncomputable def incDepRawDependentPair_readySemanticResult :
    IncDepRawReadyTypingSemanticResult incDepRawDependentPair_semanticReady
      incDepRawEmptyContextSemanticTree where
  semanticType := _
  typingResult := incDepRawDependentPairTypingSemantic

noncomputable def incDepRawDependentPairFirst_readySemanticResult :
    IncDepRawReadyTypingSemanticResult
      incDepRawDependentPair_first_semanticReady
      incDepRawEmptyContextSemanticTree where
  semanticType := _
  typingResult := incDepRawDependentPairFirstTypingSemantic

noncomputable def incDepRawDependentPairSecond_readySemanticResult :
    IncDepRawReadyTypingSemanticResult
      incDepRawDependentPair_second_semanticReady
      incDepRawEmptyContextSemanticTree where
  semanticType := _
  typingResult := incDepRawDependentPairSecondTypingSemantic

def incDepRawClosedContextSemantic
    {term : IncDepRawTerm} {type : IncDepRawType}
    (certified : IncDepRawCertifiedTyping [] term type) :
    IncDepRawContextSemanticResult certified.contextWellFormed := by
  cases certified.contextWellFormed
  exact incDepRawEmptyContextSemantic

def IncDepRawClosedSemanticResult.toGeneral
    {term : IncDepRawTerm} {type : IncDepRawType}
    {certified : IncDepRawCertifiedTyping [] term type}
    (closed : IncDepRawClosedSemanticResult certified) :
    IncDepRawSemanticResult certified
      (incDepRawClosedContextSemantic certified) := by
  cases certified with
  | mk contextWellFormed typeWellFormed typing =>
      cases contextWellFormed
      exact ⟨closed.semanticType, closed.semanticTerm⟩

def incDepRawDependentRefl_interpretation :
    IncDepRawClosedSemanticResult incDepRawDependentRefl_certified where
  semanticType := IncPiType incDepUnitType
    incDepRawDependentReflSemanticCodomain
  semanticTerm := incDepRawDependentReflSemantic

def incDepRawDependentPair_interpretation :
    IncDepRawClosedSemanticResult incDepRawDependentPair_certified where
  semanticType := IncSigmaType incDepUnitType
    incDepRawDependentReflSemanticCodomain
  semanticTerm := incDepRawDependentPairSemantic

def incDepRawDependentRefl_generalInterpretation :
    IncDepRawSemanticResult incDepRawDependentRefl_certified
      (incDepRawClosedContextSemantic incDepRawDependentRefl_certified) :=
  incDepRawDependentRefl_interpretation.toGeneral

def incDepRawDependentPair_generalInterpretation :
    IncDepRawSemanticResult incDepRawDependentPair_certified
      (incDepRawClosedContextSemantic incDepRawDependentPair_certified) :=
  incDepRawDependentPair_interpretation.toGeneral

structure IncDepRawClosedReductionResult
    {first second : IncDepRawTerm} (steps : IncDepRawSteps first second) where
  semanticType : IncTypeInContext IncContext.empty
  firstSemantic : IncTerm semanticType
  secondSemantic : IncTerm semanticType
  sound : firstSemantic = secondSemantic

def incDepRawDependentRefl_reductionInterpretation :
    IncDepRawClosedReductionResult
      (IncDepRawSteps.tail incDepRawDependentRefl_betaStep
        (IncDepRawSteps.refl _)) where
  semanticType := IncIdentityType incDepUnitType incDepUnitTerm incDepUnitTerm
  firstSemantic := IncPiTerm.apply incDepRawDependentReflSemantic incDepUnitTerm
  secondSemantic := IncIdentityTerm.refl incDepUnitTerm
  sound := incDepRawDependentReflSemantic_beta

def incDepRawDependentPair_first_reductionInterpretation :
    IncDepRawClosedReductionResult
      (IncDepRawSteps.tail incDepRawDependentPair_first_betaStep
        (IncDepRawSteps.refl _)) where
  semanticType := incDepUnitType
  firstSemantic := IncSigmaTerm.first incDepRawDependentPairSemantic
  secondSemantic := incDepUnitTerm
  sound := incDepRawDependentPairSemantic_first_beta

def incDepRawDependentPair_second_reductionInterpretation :
    IncDepRawClosedReductionResult
      (IncDepRawSteps.tail incDepRawDependentPair_second_betaStep
        (IncDepRawSteps.refl _)) where
  semanticType := IncIdentityType incDepUnitType incDepUnitTerm incDepUnitTerm
  firstSemantic := IncSigmaTerm.second incDepRawDependentPairSemantic
  secondSemantic := IncIdentityTerm.refl incDepUnitTerm
  sound := incDepRawDependentPairSemantic_second_beta

def IncIdentityFamily
    {I R T : Type u} [DecidableEq (I × I)]
    (pairIncidence : Incidence (I × I) R T) :
    IncDependentFamily pairIncidence where
  fiber := fun pair => ULift.{u} (PLift (pair.1 = pair.2))

def IncIdentityFamily.refl
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} (index : I) :
    (IncIdentityFamily pairIncidence).fiber (index, index) :=
  ⟨⟨rfl⟩⟩

def IncIdentityFamily.symm
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left right : I} :
    (IncIdentityFamily pairIncidence).fiber (left, right) →
      (IncIdentityFamily pairIncidence).fiber (right, left) :=
  fun equal => ⟨⟨equal.down.down.symm⟩⟩

def IncIdentityFamily.trans
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left middle right : I} :
    (IncIdentityFamily pairIncidence).fiber (left, middle) →
      (IncIdentityFamily pairIncidence).fiber (middle, right) →
        (IncIdentityFamily pairIncidence).fiber (left, right) :=
  fun first second => ⟨⟨first.down.down.trans second.down.down⟩⟩

def IncIdentityFamily.transport
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (family : I → Type u) {left right : I} :
    (IncIdentityFamily pairIncidence).fiber (left, right) →
      family left → family right := by
  intro equal value
  have indicesEqual : left = right := equal.down.down
  subst right
  exact value

def IncIdentityFamily.J
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (motive : ∀ left right : I, left = right → Type u)
    (reflCase : ∀ index, motive index index (Eq.refl index))
    {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    motive left right equal.down.down := by
  have proof := equal.down.down
  cases proof
  exact reflCase left

theorem IncIdentityFamily.transport_refl
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (family : I → Type u) (index : I) (value : family index) :
    IncIdentityFamily.transport (pairIncidence := pairIncidence) family
      (IncIdentityFamily.refl index) value = value := by
  simp [IncIdentityFamily.transport]

theorem IncIdentityFamily.transport_trans
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (family : I → Type u) {left middle right : I}
    (first : (IncIdentityFamily pairIncidence).fiber (left, middle))
    (second : (IncIdentityFamily pairIncidence).fiber (middle, right))
    (value : family left) :
    IncIdentityFamily.transport (pairIncidence := pairIncidence) family
        (IncIdentityFamily.trans first second) value =
      IncIdentityFamily.transport (pairIncidence := pairIncidence) family second
        (IncIdentityFamily.transport (pairIncidence := pairIncidence) family first value) := by
  have firstEq : left = middle := first.down.down
  have secondEq : middle = right := second.down.down
  subst middle
  subst right
  simp [IncIdentityFamily.transport]

theorem IncIdentityFamily.J_beta
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    (motive : ∀ left right : I, left = right → Type u)
    (reflCase : ∀ index, motive index index (Eq.refl index))
    (index : I) :
    IncIdentityFamily.J (pairIncidence := pairIncidence) motive reflCase
        (IncIdentityFamily.refl (pairIncidence := pairIncidence) index) =
      reflCase index := by
  simp [IncIdentityFamily.J]

def natIncIdentityFamily :
    IncDependentFamily (incidenceProd natIncidence natIncidence) :=
  IncIdentityFamily (incidenceProd natIncidence natIncidence)

def natIncIdentity_zero_refl : natIncIdentityFamily.fiber (0, 0) :=
  IncIdentityFamily.refl (pairIncidence := incidenceProd natIncidence natIncidence) 0

theorem natIncIdentity_zero_one_empty :
    ¬ Nonempty (natIncIdentityFamily.fiber (0, 1)) := by
  rintro ⟨witness⟩
  exact Nat.zero_ne_one witness.down.down

def IncIdentityFamily.congrArg
    {I J R T R' T' : Type u}
    [DecidableEq (I × I)] [DecidableEq (J × J)]
    {sourcePairs : Incidence (I × I) R T}
    {targetPairs : Incidence (J × J) R' T'}
    (map : I → J) {left right : I} :
    (IncIdentityFamily sourcePairs).fiber (left, right) →
      (IncIdentityFamily targetPairs).fiber (map left, map right) :=
  fun equal => ⟨⟨_root_.congrArg map equal.down.down⟩⟩

theorem IncIdentityFamily.witness_unique
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left right : I}
    (first second : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    first = second := by
  rcases first with ⟨⟨firstProof⟩⟩
  rcases second with ⟨⟨secondProof⟩⟩
  have proofsEqual : firstProof = secondProof := Subsingleton.elim _ _
  exact _root_.congrArg
    (fun proof => (⟨⟨proof⟩⟩ : (IncIdentityFamily pairIncidence).fiber (left, right)))
    proofsEqual

theorem IncIdentityFamily.congrArg_id
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T}
    {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    IncIdentityFamily.congrArg (sourcePairs := pairIncidence)
      (targetPairs := pairIncidence) id equal = equal := by
  exact IncIdentityFamily.witness_unique _ _

theorem IncIdentityFamily.congrArg_comp
    {I J K R T R' T' R'' T'' : Type u}
    [DecidableEq (I × I)] [DecidableEq (J × J)] [DecidableEq (K × K)]
    {sourcePairs : Incidence (I × I) R T}
    {middlePairs : Incidence (J × J) R' T'}
    {targetPairs : Incidence (K × K) R'' T''}
    (second : J → K) (first : I → J) {left right : I}
    (equal : (IncIdentityFamily sourcePairs).fiber (left, right)) :
    IncIdentityFamily.congrArg (sourcePairs := sourcePairs)
        (targetPairs := targetPairs) (second ∘ first) equal =
      IncIdentityFamily.congrArg (sourcePairs := middlePairs)
        (targetPairs := targetPairs) second
        (IncIdentityFamily.congrArg (sourcePairs := sourcePairs)
          (targetPairs := middlePairs) first equal) := by
  exact IncIdentityFamily.witness_unique _ _

theorem IncIdentityFamily.transport_morphism_naturality
    {I R T Rb Tb : Type u} [DecidableEq I] [DecidableEq (I × I)]
    {baseIncidence : Incidence I Rb Tb}
    {pairIncidence : Incidence (I × I) R T}
    {source target : IncDependentFamily baseIncidence}
    (morphism : IncDependentFamilyMorphism source target)
    {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right))
    (value : source.fiber left) :
    morphism.app right
        (IncIdentityFamily.transport source.fiber equal value) =
      IncIdentityFamily.transport target.fiber equal
        (morphism.app left value) := by
  have indicesEqual : left = right := equal.down.down
  subst right
  rfl

theorem IncIdentityFamily.symm_symm
    {I R T : Type u} [DecidableEq (I × I)]
    {pairIncidence : Incidence (I × I) R T} {left right : I}
    (equal : (IncIdentityFamily pairIncidence).fiber (left, right)) :
    IncIdentityFamily.symm (pairIncidence := pairIncidence)
        (IncIdentityFamily.symm (pairIncidence := pairIncidence) equal) = equal := by
  exact IncIdentityFamily.witness_unique _ _

def IncDependentFamily.pullbackAlongBoundaryEmbedding
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (family : IncDependentFamily target)
    (embedding : IncidenceBoundaryObservationEmbedding source target) :
    IncDependentFamily source where
  fiber := fun index => family.fiber (embedding.map index)

def IncDependentFamily.pullbackSumToTarget
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (family : IncDependentFamily target)
    (embedding : IncidenceBoundaryObservationEmbedding source target) :
    IncDependentSum (family.pullbackAlongBoundaryEmbedding embedding) →
      IncDependentSum family
  | ⟨index, value⟩ => ⟨embedding.map index, value⟩

def IncDependentFamily.pullbackProduct
    {I I' R T R' T' : Type u} [DecidableEq I] [DecidableEq I']
    {source : Incidence I R T} {target : Incidence I' R' T'}
    (family : IncDependentFamily target)
    (embedding : IncidenceBoundaryObservationEmbedding source target)
    (term : IncDependentProduct family) :
    IncDependentProduct (family.pullbackAlongBoundaryEmbedding embedding) :=
  fun index => term (embedding.map index)

theorem IncDependentFamily.pullbackProduct_comp
    {I I' I'' R T R' T' R'' T'' : Type u}
    [DecidableEq I] [DecidableEq I'] [DecidableEq I'']
    {source : Incidence I R T} {middle : Incidence I' R' T'}
    {target : Incidence I'' R'' T''}
    (family : IncDependentFamily target)
    (second : IncidenceBoundaryObservationEmbedding middle target)
    (first : IncidenceBoundaryObservationEmbedding source middle)
    (term : IncDependentProduct family) :
    family.pullbackProduct (second.comp first) term =
      (family.pullbackAlongBoundaryEmbedding second).pullbackProduct first
        (family.pullbackProduct second term) := by
  rfl

theorem IncDependentFamily.pullbackSumToTarget_comp
    {I I' I'' R T R' T' R'' T'' : Type u}
    [DecidableEq I] [DecidableEq I'] [DecidableEq I'']
    {source : Incidence I R T} {middle : Incidence I' R' T'}
    {target : Incidence I'' R'' T''}
    (family : IncDependentFamily target)
    (second : IncidenceBoundaryObservationEmbedding middle target)
    (first : IncidenceBoundaryObservationEmbedding source middle) :
    family.pullbackSumToTarget (second.comp first) =
      family.pullbackSumToTarget second ∘
        (family.pullbackAlongBoundaryEmbedding second).pullbackSumToTarget first := by
  funext total
  rcases total with ⟨index, value⟩
  rfl

/- Positive: `PairId.atom` is a boundary-natural embedding -- its
   boundary is exactly `natIncidence`'s, transported through `atom`
   pointwise (with `PeanoRole.pred` relabeled to `PairRole.chain`,
   which is definitionally how `pairBoundaryChained`'s atom case was
   built in the first place). -/
theorem atom_boundary_natural (n : Nat) :
  pairIncidenceChained.boundary (PairId.atom n) =
    (natIncidence.boundary n).map (fun e =>
      ({ i := PairId.atom e.i, role := PairRole.chain, sign := e.sign, mult := e.mult,
         mult_pos := e.mult_pos }
        : Endpoint PairId PairRole)) := by
  cases n with
  | zero => simp [natIncidence, peanoBoundary, pairIncidenceChained, pairBoundaryChained]
  | succ k => simp [natIncidence, peanoBoundary, pairIncidenceChained, pairBoundaryChained]

/- Positive: `PairId.atom` preserves the unit element. -/
theorem atom_unit_natural :
  PairId.atom natIncidence.unit = pairIncidenceChained.unit := by
  simp [natIncidence, pairIncidenceChained]

/- Negative, and the interesting part: `PairId.atom` does NOT preserve
   `glue`. `natIncidence.glue` is addition; `pairIncidenceChained.glue`
   is left-biased selection -- structurally unrelated operations.
   Concrete witness: `atom 2 `glue` atom 3` would have to be `atom 5` for
   the embedding to be glue-natural, but it's `atom 2` (left-biased,
   `atom 2 ≠ atom 0`). -/
theorem atom_glue_not_natural :
  ¬ (∀ m n, pairIncidenceChained.glue (PairId.atom m) (PairId.atom n) =
       some (PairId.atom (m + n))) := by
  intro h
  have h23 := h 2 3
  simp [pairIncidenceChained] at h23

/- Consistency corollary: since `atom` is boundary/unit-natural (and
   injective, for free from the carrier's own constructor injectivity),
   `≈`-agreement on atoms inside `pairIncidenceChained` coincides exactly
   with `≈`-agreement in `natIncidence` itself -- the embedding is
   faithful at the level cycles 1-5 actually established (boundary,
   hence `≈`), even though it fails to be a `glue`-homomorphism. -/
theorem atom_approxBisim_iff (m n : Nat) :
  approxBisim pairIncidenceChained (PairId.atom m) (PairId.atom n) ↔
  approxBisim natIncidence m n := by
  rw [pairIncidenceChained_approxBisim_iff, natIncidence_approxBisim_iff]
  exact ⟨fun h => by injection h, fun h => by rw [h]⟩

/- Research cycle 7 (see RESEARCH_LOG.md): cycle 6 flagged a circularity
   risk for testing "pair-up"-style compatibility with `natIncidence.glue`
   -- defining a new count function specifically so it works would prove
   nothing. Sidestepped that by testing `sizeOf` instead: it already
   exists (used for `well_founded` proofs since cycle 3), wasn't defined
   for this purpose, and its exact formula (`PairId.pair.sizeOf_spec`) is
   whatever Lean's deriving mechanism happened to produce -- so whatever
   relationship it has to `glue` is discovered, not designed.

   Finding: `sizeOf` is *not* a strict `glue`-homomorphism (confirms
   cycle 6's finding via an independent route), but it IS one up to a
   precise, constant "cost" of 1 per `pair` node -- not just "doesn't
   match", but "matches exactly once you account for the pairing
   operation's own cost". A cleaner, quantified negative than cycle 6's
   qualitative one. -/
theorem sizeOf_pair_eq_succ_glue (a b : PairId) :
  sizeOf (PairId.pair a b) = 1 + (natIncidence.glue (sizeOf a) (sizeOf b)).getD 0 := by
  rw [PairId.pair.sizeOf_spec]
  simp [natIncidence]
  omega

theorem sizeOf_pair_ne_glue (a b : PairId) :
  some (sizeOf (PairId.pair a b)) ≠ natIncidence.glue (sizeOf a) (sizeOf b) := by
  simp [natIncidence, PairId.pair.sizeOf_spec]

/- Research cycle 15 (see RESEARCH_LOG.md): cycle 14 fixed
   `pathIncidenceChained`'s collapse (cycle 13) the same way cycle 3 fixed
   `pairIncidenceChained`'s (a role-tagged predecessor chain), and asked
   the queued question: does `PathId.node : Nat → PathId` -- the obvious
   embedding into a *second*, independently-built chain-shaped instance
   -- reproduce cycle 6's exact mixed result (boundary/unit natural, glue
   not), or does something different happen now that source and target
   are both single-link `Nat`-indexed chains with near-identical shape
   (unlike `PairId`, a richer nested type)?

   Finding: the SAME qualitative outcome, term for term. `node`
   preserves `boundary` (up to the same `pred → chain` role-relabeling
   pattern as `atom`) and `unit`, but not `glue` --
   `pathIncidenceChained.glue` is the same left-biased-selection
   placeholder as `pairIncidenceChained.glue`, still structurally
   unrelated to `natIncidence.glue` (addition). This is a genuine
   confirmation, not a foregone conclusion: it shows the boundary/glue
   split from cycle 6 isn't an artifact of `PairId`'s richer shape --
   it persists even between two *maximally similar* chain instances,
   because the real cause is the algebraic *kind* of `glue` (addition
   vs. selection), not any structural dissimilarity between the carrier
   types. -/
theorem node_boundary_natural (n : Nat) :
  pathIncidenceChained.boundary (PathId.node n) =
    (natIncidence.boundary n).map (fun e =>
      ({ i := PathId.node e.i, role := PathRole.chain, sign := e.sign, mult := e.mult,
         mult_pos := e.mult_pos }
        : Endpoint PathId PathRole)) := by
  cases n with
  | zero => simp [natIncidence, peanoBoundary, pathIncidenceChained, pathBoundaryChained]
  | succ k => simp [natIncidence, peanoBoundary, pathIncidenceChained, pathBoundaryChained]

def natToPathBoundaryObservationEmbedding :
    IncidenceBoundaryObservationEmbedding natIncidence pathIncidenceChained where
  map := PathId.node
  boundary_iff := by
    intro n
    cases n with
    | zero =>
      simp [IncidenceBoundaryValuation, natIncidence, peanoBoundary,
        pathIncidenceChained, pathBoundaryChained]
    | succ n =>
      simp [IncidenceBoundaryValuation, natIncidence, peanoBoundary,
        pathIncidenceChained, pathBoundaryChained]

theorem natToPath_boundaryLogic_satisfies_iff (formula : Formula Nat) :
    IncidenceBoundarySatisfies pathIncidenceChained
        (formula.map PathId.node) ↔
      IncidenceBoundarySatisfies natIncidence formula :=
  natToPathBoundaryObservationEmbedding.satisfies_iff formula

theorem natToPath_boundaryLogic_entails_iff
    (context : List (Formula Nat)) (formula : Formula Nat) :
    IncidenceBoundaryEntails pathIncidenceChained
        (Formula.mapContext PathId.node context) (formula.map PathId.node) ↔
      IncidenceBoundaryEntails natIncidence context formula :=
  natToPathBoundaryObservationEmbedding.entails_iff context formula

theorem natToPath_leafLogic_satisfies_iff (formula : Formula Nat) :
    IncidenceLeafSatisfies pathIncidenceChained (formula.map PathId.node) ↔
      IncidenceLeafSatisfies natIncidence formula :=
  natToPathBoundaryObservationEmbedding.leafSatisfies_iff formula

theorem natToPath_leafLogic_context_iff (context : List (Formula Nat)) :
    IncidenceLeafContextSatisfies pathIncidenceChained
        (Formula.mapContext PathId.node context) ↔
      IncidenceLeafContextSatisfies natIncidence context :=
  natToPathBoundaryObservationEmbedding.leafContextSatisfies_iff context

theorem natToPath_leafLogic_entails_iff
    (context : List (Formula Nat)) (formula : Formula Nat) :
    IncidenceLeafEntails pathIncidenceChained
        (Formula.mapContext PathId.node context) (formula.map PathId.node) ↔
      IncidenceLeafEntails natIncidence context formula :=
  natToPathBoundaryObservationEmbedding.leafEntails_iff context formula

theorem node_unit_natural :
  PathId.node natIncidence.unit = pathIncidenceChained.unit := by
  simp [natIncidence, pathIncidenceChained]

/- Concrete witness, same shape as `atom_glue_not_natural`: `node 2`
   `glue` `node 3` would have to be `node 5` for glue-naturality, but
   it's `node 2` (left-biased, `node 2 ≠ node 0`). -/
theorem node_glue_not_natural :
  ¬ (∀ m n, pathIncidenceChained.glue (PathId.node m) (PathId.node n) =
       some (PathId.node (m + n))) := by
  intro h
  have h23 := h 2 3
  simp [pathIncidenceChained] at h23

theorem node_approxBisim_iff (m n : Nat) :
  approxBisim pathIncidenceChained (PathId.node m) (PathId.node n) ↔
  approxBisim natIncidence m n := by
  rw [pathIncidenceChained_approxBisim_iff, natIncidence_approxBisim_iff]
  exact ⟨fun h => by injection h, fun h => by rw [h]⟩

end IncidenceCore
