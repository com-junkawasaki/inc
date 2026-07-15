import Mathlib.Order.Zorn
import IncidenceTheory.ReferenceFoundationEncoding

/-! Target-avoiding Lindenbaum extensions, the order-theoretic core of the
prime/Henkin counterworld construction. -/

namespace IncidenceCore.ReferenceFoundation

open Set

def SetDerives (infinity : InfinitySchema) (theory : Set Formula)
    (formula : Formula) : Prop :=
  ∃ context : Context, (∀ item ∈ context, item ∈ theory) ∧
    Derives infinity context formula

theorem SetDerives.mono {infinity : InfinitySchema} {smaller larger : Set Formula}
    {formula : Formula} (included : smaller ⊆ larger)
    (proof : SetDerives infinity smaller formula) :
    SetDerives infinity larger formula := by
  rcases proof with ⟨context, contextIn, derivation⟩
  exact ⟨context, fun item member => included (contextIn item member), derivation⟩

theorem SetDerives.of_mem {infinity : InfinitySchema} {theory : Set Formula}
    {formula : Formula} (member : formula ∈ theory) :
    SetDerives infinity theory formula :=
  ⟨[formula], by simpa, Derives.assumption (by simp)⟩

theorem SetDerives.eliminate_insert {infinity : InfinitySchema}
    {theory : Set Formula} {assumption result : Formula}
    (assumptionProof : SetDerives infinity theory assumption)
    (resultProof : SetDerives infinity (insert assumption theory) result) :
    SetDerives infinity theory result := by
  classical
  rcases assumptionProof with ⟨assumptionContext, assumptionIn, derivesAssumption⟩
  rcases resultProof with ⟨resultContext, resultIn, derivesResult⟩
  let remainder := resultContext.filter (fun item => item != assumption)
  let combined := assumptionContext ++ remainder
  have resultToHead : ∀ {item}, item ∈ resultContext →
      item ∈ assumption :: remainder := by
    intro item member
    by_cases equal : item = assumption
    · exact List.mem_cons.mpr (Or.inl equal)
    · exact List.mem_cons.mpr (Or.inr
        (List.mem_filter.mpr ⟨member, by simp [equal]⟩))
  have derivesFromHead : Derives infinity (assumption :: remainder) result :=
    derivesResult.weaken resultToHead
  have headToCombined : ∀ {item}, item ∈ assumption :: remainder →
      item ∈ assumption :: combined := by
    intro item member
    simp only [List.mem_cons] at member ⊢
    exact member.elim Or.inl (fun tail => Or.inr
      (List.mem_append_right assumptionContext tail))
  have body : Derives infinity (assumption :: combined) result :=
    derivesFromHead.weaken headToCombined
  have cutProof : Derives infinity combined assumption :=
    derivesAssumption.weaken (fun member =>
      List.mem_append_left remainder member)
  refine ⟨combined, ?_, Derives.cut cutProof body⟩
  intro item member
  rcases List.mem_append.mp member with inAssumption | inRemainder
  · exact assumptionIn item inAssumption
  · have filtered := List.mem_filter.mp inRemainder
    have inInserted := resultIn item filtered.1
    rcases inInserted with equal | inTheory
    · have notEqual : item ≠ assumption := by simpa using filtered.2
      exact False.elim (notEqual equal)
    · exact inTheory

theorem SetDerives.strip_insert {infinity : InfinitySchema}
    {theory : Set Formula} {assumption result : Formula}
    {context : Context}
    (contextIn : ∀ item ∈ context, item ∈ insert assumption theory)
    (proof : Derives infinity context result) :
    let remainder := context.filter (fun item => item != assumption)
    Derives infinity (assumption :: remainder) result ∧
      (∀ item ∈ remainder, item ∈ theory) := by
  classical
  let remainder := context.filter (fun item => item != assumption)
  constructor
  · apply proof.weaken
    intro item member
    by_cases equal : item = assumption
    · exact List.mem_cons.mpr (Or.inl equal)
    · exact List.mem_cons.mpr (Or.inr
        (List.mem_filter.mpr ⟨member, by simp [equal]⟩))
  · intro item member
    have filtered := List.mem_filter.mp member
    rcases contextIn item filtered.1 with equal | inTheory
    · have notEqual : item ≠ assumption := by simpa using filtered.2
      exact False.elim (notEqual equal)
    · exact inTheory

theorem SetDerives.orElim_insert {infinity : InfinitySchema}
    {theory : Set Formula} {left right result : Formula}
    (disjunction : SetDerives infinity theory (.or left right))
    (leftBranch : SetDerives infinity (insert left theory) result)
    (rightBranch : SetDerives infinity (insert right theory) result) :
    SetDerives infinity theory result := by
  classical
  rcases disjunction with ⟨orContext, orIn, derivesOr⟩
  rcases leftBranch with ⟨leftContext, leftIn, derivesLeft⟩
  rcases rightBranch with ⟨rightContext, rightIn, derivesRight⟩
  rcases SetDerives.strip_insert leftIn derivesLeft with
    ⟨leftStripped, leftRemainderIn⟩
  rcases SetDerives.strip_insert rightIn derivesRight with
    ⟨rightStripped, rightRemainderIn⟩
  let leftRemainder := leftContext.filter (fun item => item != left)
  let rightRemainder := rightContext.filter (fun item => item != right)
  let combined := orContext ++ leftRemainder ++ rightRemainder
  have orCombined : Derives infinity combined (.or left right) :=
    derivesOr.weaken (fun member => List.mem_append_left rightRemainder
      (List.mem_append_left leftRemainder member))
  have leftCombined : Derives infinity (left :: combined) result :=
    leftStripped.weaken (by
      intro item member
      simp only [List.mem_cons] at member ⊢
      exact member.elim Or.inl (fun tail => Or.inr
        (List.mem_append_left rightRemainder
          (List.mem_append_right orContext tail))))
  have rightCombined : Derives infinity (right :: combined) result :=
    rightStripped.weaken (by
      intro item member
      simp only [List.mem_cons] at member ⊢
      exact member.elim Or.inl (fun tail => Or.inr
        (List.mem_append_right (orContext ++ leftRemainder) tail)))
  refine ⟨combined, ?_, Derives.orElim orCombined leftCombined rightCombined⟩
  intro item member
  rcases List.mem_append.mp member with inFirst | inRight
  · rcases List.mem_append.mp inFirst with inOr | inLeft
    · exact orIn item inOr
    · exact leftRemainderIn item inLeft
  · exact rightRemainderIn item inRight

theorem SetDerives.andIntro {infinity : InfinitySchema}
    {theory : Set Formula} {left right : Formula}
    (leftProof : SetDerives infinity theory left)
    (rightProof : SetDerives infinity theory right) :
    SetDerives infinity theory (.and left right) := by
  rcases leftProof with ⟨leftContext, leftIn, derivesLeft⟩
  rcases rightProof with ⟨rightContext, rightIn, derivesRight⟩
  refine ⟨leftContext ++ rightContext, ?_,
    Derives.andIntro
      (derivesLeft.weaken (fun member => List.mem_append_left _ member))
      (derivesRight.weaken (fun member => List.mem_append_right _ member))⟩
  intro item member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact leftIn item inLeft
  · exact rightIn item inRight

theorem SetDerives.impElim {infinity : InfinitySchema}
    {theory : Set Formula} {left right : Formula}
    (implication : SetDerives infinity theory (.imp left right))
    (premise : SetDerives infinity theory left) :
    SetDerives infinity theory right := by
  rcases implication with ⟨impContext, impIn, derivesImp⟩
  rcases premise with ⟨premiseContext, premiseIn, derivesPremise⟩
  refine ⟨impContext ++ premiseContext, ?_,
    Derives.impElim
      (derivesImp.weaken (fun member => List.mem_append_left _ member))
      (derivesPremise.weaken (fun member => List.mem_append_right _ member))⟩
  intro item member
  rcases List.mem_append.mp member with inImp | inPremise
  · exact impIn item inImp
  · exact premiseIn item inPremise

theorem SetDerives.impIntro_insert {infinity : InfinitySchema}
    {theory : Set Formula} {left right : Formula}
    (body : SetDerives infinity (insert left theory) right) :
    SetDerives infinity theory (.imp left right) := by
  rcases body with ⟨context, contextIn, derivation⟩
  rcases SetDerives.strip_insert contextIn derivation with
    ⟨stripped, remainderIn⟩
  exact ⟨context.filter (fun item => item != left), remainderIn,
    Derives.impIntro stripped⟩

theorem SetDerives.botElim {infinity : InfinitySchema}
    {theory : Set Formula} {formula : Formula}
    (contradiction : SetDerives infinity theory .bot) :
    SetDerives infinity theory formula := by
  rcases contradiction with ⟨context, contextIn, proof⟩
  exact ⟨context, contextIn, Derives.botElim proof⟩

theorem chain_contains_context {chain : Set (Set Formula)}
    (nonempty : chain.Nonempty)
    (ordered : IsChain (fun left right : Set Formula => left ⊆ right) chain)
    {context : Context}
    (inUnion : ∀ item ∈ context, item ∈ ⋃₀ chain) :
    ∃ theory ∈ chain, ∀ item ∈ context, item ∈ theory := by
  induction context with
  | nil =>
      rcases nonempty with ⟨theory, theoryIn⟩
      exact ⟨theory, theoryIn, by simp⟩
  | cons head tail ih =>
      rcases mem_sUnion.mp (inUnion head (by simp)) with
        ⟨headTheory, headIn, headMember⟩
      rcases ih (fun item member => inUnion item (by simp [member])) with
        ⟨tailTheory, tailIn, tailContains⟩
      rcases ordered.total headIn tailIn with
        headTail | tailHead
      · exact ⟨tailTheory, tailIn, by
          intro item member
          simp only [List.mem_cons] at member
          exact member.elim (fun equal => equal ▸ headTail headMember)
            (tailContains item)⟩
      · exact ⟨headTheory, headIn, by
          intro item member
          simp only [List.mem_cons] at member
          exact member.elim (fun equal => equal ▸ headMember)
            (fun tailMember => tailHead (tailContains item tailMember))⟩

def Avoids (infinity : InfinitySchema) (base : Set Formula)
    (target : Formula) (theory : Set Formula) : Prop :=
  base ⊆ theory ∧ ¬ SetDerives infinity theory target

structure MaximalAvoiding (infinity : InfinitySchema)
    (base : Set Formula) (target : Formula) where
  theory : Set Formula
  base_subset : base ⊆ theory
  avoids : ¬ SetDerives infinity theory target
  maximal : ∀ {larger : Set Formula}, theory ⊆ larger →
    base ⊆ larger → ¬ SetDerives infinity larger target → larger ⊆ theory

theorem MaximalAvoiding.mem_of_derives {infinity : InfinitySchema}
    {base : Set Formula} {target formula : Formula}
    (maximalTheory : MaximalAvoiding infinity base target)
    (proof : SetDerives infinity maximalTheory.theory formula) :
    formula ∈ maximalTheory.theory := by
  have insertedAvoids : ¬ SetDerives infinity
      (insert formula maximalTheory.theory) target := by
    intro derivesTarget
    exact maximalTheory.avoids (proof.eliminate_insert derivesTarget)
  exact maximalTheory.maximal (subset_insert _ _)
    (Subset.trans maximalTheory.base_subset (subset_insert _ _))
    insertedAvoids (mem_insert formula _)

theorem MaximalAvoiding.derives_iff_mem {infinity : InfinitySchema}
    {base : Set Formula} {target formula : Formula}
    (maximalTheory : MaximalAvoiding infinity base target) :
    SetDerives infinity maximalTheory.theory formula ↔
      formula ∈ maximalTheory.theory :=
  ⟨maximalTheory.mem_of_derives, SetDerives.of_mem⟩

theorem MaximalAvoiding.or_iff {infinity : InfinitySchema}
    {base : Set Formula} {target left right : Formula}
    (maximalTheory : MaximalAvoiding infinity base target) :
    (.or left right) ∈ maximalTheory.theory ↔
      left ∈ maximalTheory.theory ∨ right ∈ maximalTheory.theory := by
  constructor
  · intro disjunction
    by_contra neither
    simp only [not_or] at neither
    have leftTarget : SetDerives infinity
        (insert left maximalTheory.theory) target := by
      by_contra avoidsInsert
      have insertedSubset := maximalTheory.maximal (subset_insert _ _)
        (Subset.trans maximalTheory.base_subset (subset_insert _ _))
        avoidsInsert
      exact neither.1 (insertedSubset (mem_insert left _))
    have rightTarget : SetDerives infinity
        (insert right maximalTheory.theory) target := by
      by_contra avoidsInsert
      have insertedSubset := maximalTheory.maximal (subset_insert _ _)
        (Subset.trans maximalTheory.base_subset (subset_insert _ _))
        avoidsInsert
      exact neither.2 (insertedSubset (mem_insert right _))
    exact maximalTheory.avoids
      (SetDerives.orElim_insert (SetDerives.of_mem disjunction)
        leftTarget rightTarget)
  · intro disjunct
    apply maximalTheory.mem_of_derives
    rcases disjunct with leftMember | rightMember
    · rcases SetDerives.of_mem (infinity := infinity) leftMember with
        ⟨context, contextIn, proof⟩
      exact ⟨context, contextIn, Derives.orIntroLeft proof⟩
    · rcases SetDerives.of_mem (infinity := infinity) rightMember with
        ⟨context, contextIn, proof⟩
      exact ⟨context, contextIn, Derives.orIntroRight proof⟩

theorem MaximalAvoiding.bot_iff {infinity : InfinitySchema}
    {base : Set Formula} {target : Formula}
    (maximalTheory : MaximalAvoiding infinity base target) :
    Formula.bot ∈ maximalTheory.theory ↔ False := by
  constructor
  · intro member
    exact maximalTheory.avoids
      (SetDerives.botElim (SetDerives.of_mem member))
  · exact False.elim

theorem MaximalAvoiding.and_iff {infinity : InfinitySchema}
    {base : Set Formula} {target left right : Formula}
    (maximalTheory : MaximalAvoiding infinity base target) :
    (.and left right) ∈ maximalTheory.theory ↔
      left ∈ maximalTheory.theory ∧ right ∈ maximalTheory.theory := by
  constructor
  · intro conjunction
    have proof := SetDerives.of_mem (infinity := infinity) conjunction
    rcases proof with ⟨context, contextIn, derivation⟩
    exact ⟨maximalTheory.mem_of_derives
      ⟨context, contextIn, Derives.andElimLeft derivation⟩,
      maximalTheory.mem_of_derives
      ⟨context, contextIn, Derives.andElimRight derivation⟩⟩
  · rintro ⟨leftMember, rightMember⟩
    exact maximalTheory.mem_of_derives
      (SetDerives.andIntro (SetDerives.of_mem leftMember)
        (SetDerives.of_mem rightMember))

structure PrimeTheory (infinity : InfinitySchema) where
  theory : Set Formula
  closed : ∀ {formula}, SetDerives infinity theory formula → formula ∈ theory
  consistent : Formula.bot ∉ theory
  primeOr : ∀ left right, (.or left right) ∈ theory ↔
    left ∈ theory ∨ right ∈ theory
  axioms : ∀ {formula}, Axiom infinity formula → formula ∈ theory

def MaximalAvoiding.toPrimeTheory {infinity : InfinitySchema}
    {base : Set Formula} {target : Formula}
    (maximalTheory : MaximalAvoiding infinity base target) :
    PrimeTheory infinity where
  theory := maximalTheory.theory
  closed := maximalTheory.mem_of_derives
  consistent := fun member => (maximalTheory.bot_iff.mp member)
  primeOr := fun left right => maximalTheory.or_iff
  axioms := fun valid => maximalTheory.mem_of_derives
    ⟨[], by simp, Derives.axiom valid⟩

theorem PrimeTheory.imp_forward {infinity : InfinitySchema}
    {current future : PrimeTheory infinity} {left right : Formula}
    (included : current.theory ⊆ future.theory)
    (implication : (.imp left right) ∈ current.theory)
    (premise : left ∈ future.theory) : right ∈ future.theory := by
  apply future.closed
  exact SetDerives.impElim
    (SetDerives.of_mem (included implication)) (SetDerives.of_mem premise)

theorem exists_maximalAvoiding {infinity : InfinitySchema}
    {base : Set Formula} {target : Formula}
    (baseAvoids : ¬ SetDerives infinity base target) :
    Nonempty (MaximalAvoiding infinity base target) := by
  let candidates : Set (Set Formula) :=
    {theory | Avoids infinity base target theory}
  have baseCandidate : base ∈ candidates := ⟨Subset.rfl, baseAvoids⟩
  rcases zorn_subset_nonempty candidates (by
      intro chain chainCandidates ordered nonempty
      refine ⟨⋃₀ chain, ?_, ?_⟩
      · constructor
        · intro item itemBase
          rcases nonempty with ⟨theory, theoryIn⟩
          exact mem_sUnion.mpr
            ⟨theory, theoryIn, (chainCandidates theoryIn).1 itemBase⟩
        · intro derivesTarget
          rcases derivesTarget with ⟨context, contextUnion, derivation⟩
          rcases chain_contains_context nonempty ordered
              (fun item member => contextUnion item member) with
            ⟨theory, theoryIn, contextTheory⟩
          exact (chainCandidates theoryIn).2
            ⟨context, contextTheory, derivation⟩
      · intro theory theoryIn
        exact subset_sUnion_of_mem theoryIn)
    base baseCandidate with ⟨maximalTheory, baseIncluded, maximalTheoryMaximal⟩
  refine ⟨{
    theory := maximalTheory
    base_subset := (show Avoids infinity base target maximalTheory from
      maximalTheoryMaximal.1).1
    avoids := (show Avoids infinity base target maximalTheory from
      maximalTheoryMaximal.1).2
    maximal := ?_ }⟩
  intro larger included baseLarger avoidsLarger
  exact maximalTheoryMaximal.2 ⟨baseLarger, avoidsLarger⟩ included

theorem PrimeTheory.future_counterexample_of_imp_not_mem
    {infinity : InfinitySchema} (current : PrimeTheory infinity)
    {left right : Formula} (missing : (.imp left right) ∉ current.theory) :
    ∃ future : PrimeTheory infinity,
      current.theory ⊆ future.theory ∧
      left ∈ future.theory ∧ right ∉ future.theory := by
  have baseAvoids : ¬ SetDerives infinity (insert left current.theory) right := by
    intro derivesRight
    exact missing (current.closed (SetDerives.impIntro_insert derivesRight))
  let maximal := Classical.choice (exists_maximalAvoiding baseAvoids)
  refine ⟨maximal.toPrimeTheory, ?_, ?_, ?_⟩
  · exact Subset.trans (subset_insert _ _) maximal.base_subset
  · exact maximal.base_subset (mem_insert left _)
  · intro rightMember
    exact maximal.avoids (SetDerives.of_mem rightMember)

theorem PrimeTheory.imp_iff {infinity : InfinitySchema}
    (current : PrimeTheory infinity) (left right : Formula) :
    (.imp left right) ∈ current.theory ↔
      ∀ future : PrimeTheory infinity, current.theory ⊆ future.theory →
        left ∈ future.theory → right ∈ future.theory := by
  constructor
  · intro implication future included premise
    exact PrimeTheory.imp_forward included implication premise
  · intro futureProperty
    by_contra missing
    rcases current.future_counterexample_of_imp_not_mem missing with
      ⟨future, included, leftMember, rightMissing⟩
    exact rightMissing (futureProperty future included leftMember)

end IncidenceCore.ReferenceFoundation
