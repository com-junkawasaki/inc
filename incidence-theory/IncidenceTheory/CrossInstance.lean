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

noncomputable def IncRawHasType.weaken
    {context : List IncRawType} {term : IncRawTerm} {type : IncRawType}
    (typing : IncRawHasType context term type) (head : IncRawType) :
    IncRawHasType (head :: context)
      (term.rename Nat.succ) type :=
  typing.rename (IncRawRenaming.weaken context head)

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
