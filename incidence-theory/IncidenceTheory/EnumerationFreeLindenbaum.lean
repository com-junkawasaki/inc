import IncidenceTheory.ResonanceLawStrongCompleteness
import Mathlib.Order.Zorn

namespace IncidenceCore

universe u

structure FinitaryTheoryExtension {Atom : Type u}
    (base : DeductivelyClosedTheory Atom) (forbidden : Formula Atom)
    (carrier : Set (Formula Atom)) : Prop where
  contains_base : ∀ formula, base.contains formula → formula ∈ carrier
  avoids : ∀ context : List (Formula Atom),
    (∀ formula, formula ∈ context → formula ∈ carrier) →
      ¬ Derives context forbidden

theorem chain_finite_context_bound {Atom : Type u}
    (chain : Set (Set (Formula Atom)))
    (ordered : IsChain (fun left right => left ⊆ right) chain)
    (nonempty : chain.Nonempty)
    (context : List (Formula Atom))
    (contained : ∀ formula, formula ∈ context → formula ∈ ⋃₀ chain) :
    ∃ carrier ∈ chain,
      ∀ formula, formula ∈ context → formula ∈ carrier := by
  induction context with
  | nil =>
      rcases nonempty with ⟨carrier, member⟩
      exact ⟨carrier, member, by simp⟩
  | cons head tail ih =>
      rcases Set.mem_sUnion.mp (contained head (by simp)) with
        ⟨headCarrier, headMember, headContains⟩
      rcases ih (by
        intro formula member
        exact contained formula (List.mem_cons_of_mem _ member)) with
        ⟨tailCarrier, tailMember, tailContains⟩
      rcases ordered.total headMember tailMember with subset | subset
      · refine ⟨tailCarrier, tailMember, ?_⟩
        intro formula member
        rcases List.mem_cons.mp member with rfl | tailFormula
        · exact subset headContains
        · exact tailContains formula tailFormula
      · refine ⟨headCarrier, headMember, ?_⟩
        intro formula member
        rcases List.mem_cons.mp member with rfl | tailFormula
        · exact headContains
        · exact subset (tailContains formula tailFormula)

theorem finitaryTheoryExtension_sUnion
    {Atom : Type u} (base : DeductivelyClosedTheory Atom)
    (forbidden : Formula Atom)
    (chain : Set (Set (Formula Atom)))
    (members : chain ⊆ { carrier |
      FinitaryTheoryExtension base forbidden carrier })
    (ordered : IsChain (fun left right => left ⊆ right) chain)
    (nonempty : chain.Nonempty) :
    FinitaryTheoryExtension base forbidden (⋃₀ chain) := by
  refine
    { contains_base := ?_
      avoids := ?_ }
  · intro formula baseContains
    rcases nonempty with ⟨carrier, carrierMember⟩
    exact Set.mem_sUnion.mpr
      ⟨carrier, carrierMember,
        (members carrierMember).contains_base formula baseContains⟩
  · intro context contained derives
    rcases chain_finite_context_bound chain ordered nonempty context contained with
      ⟨carrier, carrierMember, carrierContains⟩
    exact (members carrierMember).avoids context carrierContains derives

theorem baseCarrier_finitaryTheoryExtension
    {Atom : Type u} (base : DeductivelyClosedTheory Atom)
    (forbidden : Formula Atom) (avoids : ¬ base.contains forbidden) :
    FinitaryTheoryExtension base forbidden { formula | base.contains formula } := by
  refine
    { contains_base := fun _ contains => contains
      avoids := ?_ }
  intro context contained derives
  exact avoids (base.closed contained derives)

theorem exists_maximal_finitaryTheoryExtension
    {Atom : Type u} (base : DeductivelyClosedTheory Atom)
    (forbidden : Formula Atom) (avoids : ¬ base.contains forbidden) :
    ∃ carrier : Set (Formula Atom),
      { formula | base.contains formula } ⊆ carrier ∧
        Maximal (fun candidate =>
          FinitaryTheoryExtension base forbidden candidate) carrier := by
  apply zorn_subset_nonempty
    { carrier | FinitaryTheoryExtension base forbidden carrier }
  · intro chain members ordered nonempty
    exact ⟨⋃₀ chain,
      finitaryTheoryExtension_sUnion base forbidden chain members ordered nonempty,
      fun carrier member => Set.subset_sUnion_of_mem member⟩
  · exact baseCarrier_finitaryTheoryExtension base forbidden avoids

theorem finitaryTheoryExtension_forbidden_not_mem
    {Atom : Type u} {base : DeductivelyClosedTheory Atom}
    {forbidden : Formula Atom} {carrier : Set (Formula Atom)}
    (extension : FinitaryTheoryExtension base forbidden carrier) :
    forbidden ∉ carrier := by
  intro member
  exact extension.avoids [forbidden] (by simpa using member)
    (Derives.ax (by simp))

theorem maximal_finitaryTheoryExtension_closed
    {Atom : Type u} {base : DeductivelyClosedTheory Atom}
    {forbidden : Formula Atom} {carrier : Set (Formula Atom)}
    (maximal : Maximal
      (fun candidate => FinitaryTheoryExtension base forbidden candidate)
      carrier)
    {context : List (Formula Atom)} {formula : Formula Atom}
    (contained : ∀ assumption, assumption ∈ context → assumption ∈ carrier)
    (derivation : Derives context formula) : formula ∈ carrier := by
  classical
  let enlarged : Set (Formula Atom) := Set.insert formula carrier
  have enlargedExtension : FinitaryTheoryExtension base forbidden enlarged := by
    refine
      { contains_base := fun assumption baseContains =>
          Set.mem_insert_iff.mpr (Or.inr
            (maximal.1.contains_base assumption baseContains))
        avoids := ?_ }
    intro assumptions assumptionsContained derivesForbidden
    let reduced := assumptions.filter (fun assumption => assumption ∈ carrier)
    have reducedContained : ∀ assumption, assumption ∈ reduced →
        assumption ∈ carrier := by
      intro assumption member
      exact of_decide_eq_true (List.mem_filter.mp member).2
    apply maximal.1.avoids (context ++ reduced)
    · intro assumption member
      rcases List.mem_append.mp member with contextMember | reducedMember
      · exact contained assumption contextMember
      · exact reducedContained assumption reducedMember
    · apply derives_substitute (source := assumptions)
      · intro assumption member
        rcases Set.mem_insert_iff.mp (assumptionsContained assumption member) with
          rfl | carrierMember
        · apply derives_weaken (source := context)
          · exact fun item itemMember =>
              List.mem_append.mpr (Or.inl itemMember)
          · exact derivation
        · exact Derives.ax (List.mem_append.mpr (Or.inr
            (List.mem_filter.mpr ⟨member, decide_eq_true carrierMember⟩)))
      · exact derivesForbidden
  have enlargedSubset : enlarged ⊆ carrier :=
    maximal.2 enlargedExtension (fun _ member =>
      Set.mem_insert_iff.mpr (Or.inr member))
  exact enlargedSubset (Set.mem_insert formula carrier)

theorem maximal_finitaryTheoryExtension_imp_of_insert_fails
    {Atom : Type u} {base : DeductivelyClosedTheory Atom}
    {forbidden : Formula Atom} {carrier : Set (Formula Atom)}
    (maximal : Maximal
      (fun candidate => FinitaryTheoryExtension base forbidden candidate)
      carrier)
    (premise : Formula Atom)
    (fails : ¬ FinitaryTheoryExtension base forbidden
      (Set.insert premise carrier)) :
    Formula.imp premise forbidden ∈ carrier := by
  classical
  have notAvoids : ¬ ∀ context : List (Formula Atom),
      (∀ formula, formula ∈ context →
        formula ∈ Set.insert premise carrier) →
      ¬ Derives context forbidden := by
    intro avoids
    apply fails
    exact
      { contains_base := fun formula contains =>
          Set.mem_insert_iff.mpr (Or.inr
            (maximal.1.contains_base formula contains))
        avoids := avoids }
  rcases Classical.not_forall.mp notAvoids with ⟨context, notContext⟩
  rcases Classical.not_imp.mp notContext with ⟨contained, notNotDerives⟩
  have derivesForbidden : Derives context forbidden :=
    Classical.byContradiction notNotDerives
  let reduced := context.filter (fun formula => formula ∈ carrier)
  have derivesFromReduced : Derives (premise :: reduced) forbidden := by
    apply derives_substitute (source := context)
    · intro assumption member
      rcases Set.mem_insert_iff.mp (contained assumption member) with
        rfl | carrierMember
      · exact Derives.ax List.mem_cons_self
      · exact Derives.ax (List.mem_cons_of_mem _
          (List.mem_filter.mpr ⟨member, decide_eq_true carrierMember⟩))
    · exact derivesForbidden
  apply maximal_finitaryTheoryExtension_closed maximal
    (context := reduced)
  · intro assumption member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · exact Derives.impI derivesFromReduced

theorem maximal_finitaryTheoryExtension_prime
    {Atom : Type u} {base : DeductivelyClosedTheory Atom}
    {forbidden : Formula Atom} {carrier : Set (Formula Atom)}
    (maximal : Maximal
      (fun candidate => FinitaryTheoryExtension base forbidden candidate)
      carrier)
    {left right : Formula Atom} (disjunction : Formula.or left right ∈ carrier) :
    left ∈ carrier ∨ right ∈ carrier := by
  classical
  by_cases leftMember : left ∈ carrier
  · exact Or.inl leftMember
  by_cases rightMember : right ∈ carrier
  · exact Or.inr rightMember
  exfalso
  have leftFails : ¬ FinitaryTheoryExtension base forbidden
      (Set.insert left carrier) := by
    intro extension
    have subset : Set.insert left carrier ⊆ carrier :=
      maximal.2 extension (fun _ member => Set.mem_insert_iff.mpr (Or.inr member))
    exact leftMember (subset (Set.mem_insert left carrier))
  have rightFails : ¬ FinitaryTheoryExtension base forbidden
      (Set.insert right carrier) := by
    intro extension
    have subset : Set.insert right carrier ⊆ carrier :=
      maximal.2 extension (fun _ member => Set.mem_insert_iff.mpr (Or.inr member))
    exact rightMember (subset (Set.mem_insert right carrier))
  have leftImp := maximal_finitaryTheoryExtension_imp_of_insert_fails
    maximal left leftFails
  have rightImp := maximal_finitaryTheoryExtension_imp_of_insert_fails
    maximal right rightFails
  have forbiddenMember : forbidden ∈ carrier := by
    apply maximal_finitaryTheoryExtension_closed maximal
      (context := [.or left right, .imp left forbidden, .imp right forbidden])
    · intro assumption member
      rcases List.mem_cons.mp member with rfl | member
      · exact disjunction
      rcases List.mem_cons.mp member with rfl | member
      · exact leftImp
      have : assumption = .imp right forbidden := by simpa using member
      subst assumption
      exact rightImp
    · apply Derives.orE (p := left) (q := right)
      · exact Derives.ax List.mem_cons_self
      · exact Derives.impE
          (Derives.ax (p := .imp left forbidden) (by simp))
          (Derives.ax (p := left) (by simp))
      · exact Derives.impE
          (Derives.ax (p := .imp right forbidden) (by simp))
          (Derives.ax (p := right) (by simp))
  exact (finitaryTheoryExtension_forbidden_not_mem maximal.1) forbiddenMember

noncomputable def maximalFinitaryTheoryPrimeTheory
    {Atom : Type u} (base : DeductivelyClosedTheory Atom)
    (forbidden : Formula Atom) (carrier : Set (Formula Atom))
    (maximal : Maximal
      (fun candidate => FinitaryTheoryExtension base forbidden candidate)
      carrier) : PrimeTheory Atom where
  contains := fun formula => formula ∈ carrier
  closed := maximal_finitaryTheoryExtension_closed maximal
  consistent := by
    intro bottomMember
    exact maximal.1.avoids [.bot] (by simpa using bottomMember)
      (Derives.botE (Derives.ax (by simp)))
  prime := maximal_finitaryTheoryExtension_prime maximal

theorem enumerationFree_relative_prime_extension
    {Atom : Type u} (base : DeductivelyClosedTheory Atom)
    (forbidden : Formula Atom) (avoids : ¬ base.contains forbidden) :
    ∃ theory : PrimeTheory Atom,
      (∀ formula, base.contains formula → theory.contains formula) ∧
        ¬ theory.contains forbidden := by
  rcases exists_maximal_finitaryTheoryExtension base forbidden avoids with
    ⟨carrier, baseSubset, maximal⟩
  exact ⟨maximalFinitaryTheoryPrimeTheory base forbidden carrier maximal,
    fun formula contains => baseSubset contains,
    finitaryTheoryExtension_forbidden_not_mem maximal.1⟩

def primeTheoryWithPremiseClosure {Atom : Type u}
    (theory : PrimeTheory Atom) (premise : Formula Atom) :
    DeductivelyClosedTheory Atom where
  contains := theoryDerives theory [premise]
  closed := by
    intro context formula contained derivation
    exact theoryDerives_closed theory contained derivation

theorem enumerationFree_prime_implication_failure_extension
    {Atom : Type u} (theory : PrimeTheory Atom)
    (premise conclusion : Formula Atom)
    (missing : ¬ theory.contains (.imp premise conclusion)) :
    ∃ extension : PrimeTheory Atom,
      primeTheoryLe theory extension ∧ extension.contains premise ∧
        ¬ extension.contains conclusion := by
  have avoids : ¬ (primeTheoryWithPremiseClosure theory premise).contains conclusion :=
    theoryAvoids_imp_extension theory missing
  rcases enumerationFree_relative_prime_extension
    (primeTheoryWithPremiseClosure theory premise) conclusion avoids with
    ⟨extension, containsClosure, excludes⟩
  refine ⟨extension, ?_, ?_, excludes⟩
  · intro formula theoryContains
    apply containsClosure formula
    refine ⟨[formula], by simpa using theoryContains, ?_⟩
    exact Derives.ax (by simp)
  · apply containsClosure premise
    exact ⟨[], by simp, Derives.ax (by simp)⟩

def enumerationFreePrimeExtensionWitness (Atom : Type u) :
    PrimeExtensionWitness Atom where
  extend_imp_failure :=
    enumerationFree_prime_implication_failure_extension

theorem enumerationFree_canonical_truth_lemma
    {Atom : Type u} (theory : PrimeTheory Atom)
    (formula : Formula Atom) :
    KripkeForces (canonicalKripkeModel Atom) theory formula ↔
      theory.contains formula :=
  canonical_truth_lemma (enumerationFreePrimeExtensionWitness Atom) theory formula

theorem enumerationFree_relative_prime_extension_finite
    {Atom : Type u} (context : List (Formula Atom))
    (forbidden : Formula Atom) (notDerives : ¬ Derives context forbidden) :
    ∃ theory : PrimeTheory Atom,
      (∀ formula, formula ∈ context → theory.contains formula) ∧
        ¬ theory.contains forbidden := by
  have avoids : ¬ (derivationClosedTheory context).contains forbidden :=
    notDerives
  rcases enumerationFree_relative_prime_extension
    (derivationClosedTheory context) forbidden avoids with
    ⟨theory, containsClosure, excludes⟩
  exact ⟨theory,
    fun formula member => containsClosure formula (Derives.ax member), excludes⟩

theorem enumerationFree_canonical_countermodel_of_not_derives
    {Atom : Type u} {context : List (Formula Atom)}
    {formula : Formula Atom} (notDerives : ¬ Derives context formula) :
    ∃ theory : PrimeTheory Atom,
      KripkeContextForces (canonicalKripkeModel Atom) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel Atom) theory formula := by
  rcases enumerationFree_relative_prime_extension_finite
    context formula notDerives with ⟨theory, containsContext, excludes⟩
  refine ⟨theory, ?_, ?_⟩
  · intro assumption member
    exact (enumerationFree_canonical_truth_lemma theory assumption).mpr
      (containsContext assumption member)
  · intro forces
    exact excludes ((enumerationFree_canonical_truth_lemma theory formula).mp forces)

theorem enumerationFree_kripke_entails_complete
    {Atom : Type u} {context : List (Formula Atom)}
    {formula : Formula Atom} :
    KripkeEntails.{u, u} context formula → Derives context formula := by
  intro entails
  apply Classical.byContradiction
  intro notDerives
  rcases enumerationFree_canonical_countermodel_of_not_derives notDerives with
    ⟨theory, forcesContext, notForces⟩
  exact notForces (entails (canonicalKripkeModel Atom) theory forcesContext)

theorem enumerationFree_kripke_complete
    {Atom : Type u} (context : List (Formula Atom))
    (formula : Formula Atom) :
    KripkeEntails.{u, u} context formula ↔ Derives context formula := by
  constructor
  · exact enumerationFree_kripke_entails_complete
  · exact derives_kripke_entails

theorem enumerationFree_resonanceLawCanonicalCone_truth_lemma
    {Atom : Type u} (base : PrimeTheory Atom)
    (world : ResonanceLawCanonicalWorld base)
    (formula : Formula Atom) :
    KripkeForces (resonanceLawCanonicalCone base) world formula ↔
      world.theory.contains formula := by
  rw [resonanceLawCanonicalCone_forces_iff]
  exact enumerationFree_canonical_truth_lemma world.theory formula

theorem enumerationFree_resonanceLaw_canonical_countermodels
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceLawCanonicalCountermodels inc := by
  refine ⟨?_⟩
  intro formula notDerives
  rcases enumerationFree_relative_prime_extension
    (resonanceLawDeductivelyClosedTheory inc) formula notDerives with
    ⟨base, containsClosure, notContains⟩
  have containsSchema : ∀ law : ResonanceLawAxiom inc,
      base.contains law.formula := by
    intro law
    exact containsClosure law.formula (resonanceLawAxiom_mem_closedTheory law)
  let root : ResonanceLawCanonicalWorld base :=
    ⟨base, primeTheoryLe_refl base⟩
  refine ⟨resonanceLawCanonicalCone base,
    resonanceLawCanonicalCone_lawful base containsSchema, root, ?_⟩
  intro forces
  exact notContains
    ((enumerationFree_resonanceLawCanonicalCone_truth_lemma
      base root formula).mp forces)

theorem enumerationFree_resonanceLaw_strongCompleteness
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    ResonanceLawStrongCompleteness inc :=
  (resonanceLawStrongCompleteness_iff_countermodels inc).mpr
    (enumerationFree_resonanceLaw_canonical_countermodels inc)

theorem enumerationFree_resonanceLaw_kripke_complete
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T)
    (formula : Formula (ResonanceAtom I)) :
    ResonanceLawKripkeEntails inc formula ↔
      ResonanceLawDerives inc formula :=
  (enumerationFree_resonanceLaw_strongCompleteness inc).iff formula

structure EnumerationFreeResonanceLawCompletenessTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) : Prop where
  relative_prime_extension : ∀ formula : Formula (ResonanceAtom I),
    ¬ ResonanceLawDerives inc formula →
      ∃ theory : PrimeTheory (ResonanceAtom I),
        (∀ law : ResonanceLawAxiom inc, theory.contains law.formula) ∧
          ¬ theory.contains formula
  canonical_countermodels : ResonanceLawCanonicalCountermodels inc
  strong_completeness : ResonanceLawStrongCompleteness inc
  kripke_complete : ∀ formula : Formula (ResonanceAtom I),
    ResonanceLawKripkeEntails inc formula ↔
      ResonanceLawDerives inc formula

theorem enumerationFreeResonanceLawCompletenessTheorem
    {I R T : Type u} [DecidableEq I] (inc : Incidence I R T) :
    EnumerationFreeResonanceLawCompletenessTheorem inc where
  relative_prime_extension := by
    intro formula notDerives
    rcases enumerationFree_relative_prime_extension
      (resonanceLawDeductivelyClosedTheory inc) formula notDerives with
      ⟨theory, containsClosure, excludes⟩
    exact ⟨theory, fun law => containsClosure law.formula
      (resonanceLawAxiom_mem_closedTheory law), excludes⟩
  canonical_countermodels :=
    enumerationFree_resonanceLaw_canonical_countermodels inc
  strong_completeness := enumerationFree_resonanceLaw_strongCompleteness inc
  kripke_complete := enumerationFree_resonanceLaw_kripke_complete inc

end IncidenceCore
