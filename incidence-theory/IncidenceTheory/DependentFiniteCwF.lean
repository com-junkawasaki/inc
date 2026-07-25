import IncidenceTheory.DependentFiniteComprehension

namespace IncidenceCore

open CategoryTheory

/-- The dependent fiber of total typed terms lying over one well-formed type. -/
abbrev IncDepRawFiniteTerm
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) :=
  { term : IncDepRawFiniteTypedTerm context // term.finiteTypeObject = type }

theorem IncDepRawFiniteTerm.heq_of_val_eq
    {context : IncDepRawFiniteContextObject}
    {firstType secondType : IncDepRawFiniteType context}
    {first : IncDepRawFiniteTerm firstType}
    {second : IncDepRawFiniteTerm secondType}
    (valueEq : first.val = second.val) : HEq first second := by
  have typeEq : firstType = secondType := by
    rw [← first.property, ← second.property, valueEq]
  cases typeEq
  exact heq_of_eq (Subtype.ext valueEq)

noncomputable def IncDepRawFiniteTerm.reindex
    {source target : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType target}
    (term : IncDepRawFiniteTerm type) (substitution : source ⟶ target) :
    IncDepRawFiniteTerm (type.reindexFinite substitution) where
  val := term.val.reindexFinite substitution
  property := by
    rw [IncDepRawFiniteTypedTerm.finiteTypeObject_reindexFinite, term.property]

theorem IncDepRawFiniteTerm.reindex_identity
    {context : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType context}
    (term : IncDepRawFiniteTerm type) :
    HEq (term.reindex (𝟙 context)) term := by
  apply IncDepRawFiniteTerm.heq_of_val_eq
  exact IncDepRawFiniteTypedTerm.reindexFinite_identity term.val

theorem IncDepRawFiniteTerm.reindex_comp
    {first second third : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType third}
    (term : IncDepRawFiniteTerm type)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third) :
    HEq (term.reindex (firstMap ≫ secondMap))
      ((term.reindex secondMap).reindex firstMap) := by
  apply IncDepRawFiniteTerm.heq_of_val_eq
  exact IncDepRawFiniteTypedTerm.reindexFinite_comp
    term.val firstMap secondMap

theorem IncDepRawFiniteType.genericType_eq_reindex
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) :
    type.genericTerm.finiteTypeObject = type.reindexFinite type.projection := by
  apply IncDepRawExtensionalType.ext
  change type.raw.rename Nat.succ =
    type.raw.substitute (fun index => IncDepRawTerm.var (index + 1))
  have mapEq : (fun index => IncDepRawTerm.var (index + 1)) =
      IncDepRawTerm.var ∘ Nat.succ := by
    funext index
    rfl
  rw [mapEq, ← IncDepRawType.rename_substitute type.raw Nat.succ IncDepRawTerm.var,
    IncDepRawType.substitute_identity]

noncomputable def IncDepRawFiniteType.genericFiberTerm
    {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context) :
    IncDepRawFiniteTerm (type.reindexFinite type.projection) where
  val := type.genericTerm
  property := type.genericType_eq_reindex

noncomputable def IncDepRawFiniteType.pairFiber
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawFiniteTerm (type.reindexFinite substitution)) :
    source ⟶ type.extendContext := by
  have typeEq : term.val.type = (type.reindexFinite substitution).raw :=
    congrArg IncDepRawExtensionalType.raw term.property
  let typing := Classical.choice term.val.typing
  have typing' : IncDepRawHasType source.context term.val.term
      (type.reindexFinite substitution).raw := by
    rw [← typeEq]
    exact typing
  exact type.pair substitution term.val.term ⟨typing'⟩

@[simp] theorem IncDepRawFiniteType.pairFiber_projection
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawFiniteTerm (type.reindexFinite substitution)) :
    type.pairFiber substitution term ≫ type.projection = substitution := by
  unfold IncDepRawFiniteType.pairFiber
  apply IncDepRawFiniteType.pair_projection

@[simp] theorem IncDepRawFiniteType.pairFiber_generic
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawFiniteTerm (type.reindexFinite substitution)) :
    (type.pairFiber substitution term).substituteScopedTerm
        (.var 0) type.genericScope = term.val.term := by
  unfold IncDepRawFiniteType.pairFiber
  apply IncDepRawFiniteType.pair_generic

theorem IncDepRawFiniteType.pairFiber_unique
    {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawFiniteTerm (type.reindexFinite substitution))
    (candidate : source ⟶ type.extendContext)
    (projectionEq : candidate ≫ type.projection = substitution)
    (genericEq : candidate.substituteScopedTerm (.var 0) type.genericScope =
      term.val.term) :
    candidate = type.pairFiber substitution term := by
  unfold IncDepRawFiniteType.pairFiber
  apply IncDepRawFiniteType.pair_unique <;> assumption

/-- A single certificate for the split syntactic category-with-families data
    carried by finite raw contexts. -/
structure IncDepRawFiniteCwFTheorem : Prop where
  terminal : ∀ source : IncDepRawFiniteContextObject,
    ∃! map : source ⟶ incDepRawFiniteEmptyContext, map = map
  type_identity : ∀ {context : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType context), type.reindexFinite (𝟙 context) = type
  type_composition : ∀ {first second third : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType third)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third),
    type.reindexFinite (firstMap ≫ secondMap) =
      (type.reindexFinite secondMap).reindexFinite firstMap
  term_identity : ∀ {context : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType context} (term : IncDepRawFiniteTerm type),
    HEq (term.reindex (𝟙 context)) term
  term_composition : ∀ {first second third : IncDepRawFiniteContextObject}
    {type : IncDepRawFiniteType third} (term : IncDepRawFiniteTerm type)
    (firstMap : first ⟶ second) (secondMap : second ⟶ third),
    HEq (term.reindex (firstMap ≫ secondMap))
      ((term.reindex secondMap).reindex firstMap)
  comprehension : ∀ {source target : IncDepRawFiniteContextObject}
    (type : IncDepRawFiniteType target) (substitution : source ⟶ target)
    (term : IncDepRawFiniteTerm (type.reindexFinite substitution)),
    let paired := type.pairFiber substitution term
    paired ≫ type.projection = substitution ∧
      paired.substituteScopedTerm (.var 0) type.genericScope = term.val.term ∧
      ∀ candidate : source ⟶ type.extendContext,
        candidate ≫ type.projection = substitution →
        candidate.substituteScopedTerm (.var 0) type.genericScope = term.val.term →
        candidate = paired

theorem incDepRawFiniteCwFTheorem : IncDepRawFiniteCwFTheorem where
  terminal := incDepRawFiniteEmpty_terminal
  type_identity := IncDepRawFiniteType.reindexFinite_identity
  type_composition := IncDepRawFiniteType.reindexFinite_comp
  term_identity := IncDepRawFiniteTerm.reindex_identity
  term_composition := IncDepRawFiniteTerm.reindex_comp
  comprehension := by
    intro source target type substitution term
    exact ⟨type.pairFiber_projection substitution term,
      type.pairFiber_generic substitution term,
      fun candidate projectionEq genericEq =>
        type.pairFiber_unique substitution term candidate projectionEq genericEq⟩

end IncidenceCore
