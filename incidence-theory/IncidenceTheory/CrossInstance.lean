import IncidenceTheory.Peano
import IncidenceTheory.Pairs
import IncidenceTheory.PathComplex
import IncidenceTheory.Product

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

theorem incDepRawDependentRefl_application_type :
    (IncDepRawType.identity .unit (.var 0) (.var 0)).instantiate .unit =
      .identity .unit .unit .unit := by
  rfl

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

def IncIdentityTerm.refl
    {context : IncContext.{u}}
    {type : IncTypeInContext context}
    (term : IncTerm type) :
    IncTerm (IncIdentityType type term term) :=
  fun _ => ⟨⟨rfl⟩⟩

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
