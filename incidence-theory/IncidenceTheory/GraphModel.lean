import IncidenceTheory
import IncidenceTheory.FiniteSet
import IncidenceTheory.HFSets
import IncidenceTheory.Logic
import IncidenceTheory.Coherent

/- Merkle-ID: implementation.graph_model
   story.jsonnet → implementation.nodes.graph_model
   Minimal concrete models to validate API; starts with trivial model, then graph triangle. -/

namespace IncidenceCore

universe u

inductive GraphType : Type u where
  | unit

instance : Inhabited GraphType where
  default := GraphType.unit

variable {I : Type u} [Inhabited I] [DecidableEq I]

/- Merkle-ID: implementation.graph_model.trivial
   trivial incidence structure over roles = GraphRole. -/
def trivialIncidence : Incidence I GraphRole GraphType where
  boundary := fun _ => []
  typeFunc := fun _ => default
  glue     := fun i j => if i = default then some j else if j = default then some i else some i
  unit     := default
  guards   := { allow := fun _ _ => true }
  type_consistent := fun i e h => rfl
  sign_rules := fun i e h => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by simp
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = default <;> simp [h]
  type_preserve := by intro i j k _ _; rfl

/- Merkle-ID: foundation.logic
   reflexivity of bisimilarity for trivial model (from general lemma). -/
theorem approxBisim_refl_trivial (i : I) :
  approxBisim (trivialIncidence : Incidence I GraphRole GraphType) i i :=
  approxBisim_refl _ _

theorem trivial_boundary_square_zero (idx : List I) :
    boundarySquareZero (trivialIncidence : Incidence I GraphRole GraphType) idx := by
  apply empty_boundaries_square_zero
  intro i
  rfl

theorem trivial_total_isBisimulation :
    IsBisimulation (trivialIncidence : Incidence I GraphRole GraphType) (fun _ _ => True) := by
  intro i j hij
  refine ⟨rfl, ?_⟩
  simp [boundaryMatched, trivialIncidence]

theorem trivial_approxBisim_total (i j : I) :
    approxBisim (trivialIncidence : Incidence I GraphRole GraphType) i j :=
  ⟨(fun _ _ => True), trivial_total_isBisimulation, trivial⟩

def trivialLinearCompleteness (idx : List I) :
    LinearCompletenessSpec (trivialIncidence : Incidence I GraphRole GraphType) idx where
  complete := by
    intro i j h
    exact trivial_approxBisim_total i j

theorem trivial_glue_respects_approxBisim :
    GlueRespects (trivialIncidence : Incidence I GraphRole GraphType)
      (approxBisim (trivialIncidence : Incidence I GraphRole GraphType)) := by
  intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk₁ hk₂
  exact trivial_approxBisim_total k₁ k₂

end IncidenceCore

/- Merkle-ID: implementation.graph_model.simple
   A simple directed graph instance using the canonical API. -/

namespace IncidenceCore

inductive GraphRole where | src | dst
deriving DecidableEq, Repr

/- A finite, well-founded, nonempty-boundary model.  `root` has one endpoint
   (`leaf`), so this is not merely the empty-boundary model. -/
inductive FiniteIncidence where | leaf | root
deriving DecidableEq, Repr

def finiteRank : FiniteIncidence → Nat
  | .leaf => 0
  | .root => 1

def finiteBoundary : FiniteIncidence → Boundary FiniteIncidence GraphRole
  | .leaf => []
  | .root =>
      [{ i := .leaf, role := .src, sign := .pos, mult := 1, mult_pos := by omega }]

def finiteGlue : FiniteIncidence → FiniteIncidence → Option FiniteIncidence
  | .leaf, j => some j
  | .root, .leaf => some .root
  | .root, .root => some .root

theorem finiteBoundary_decreases :
    ∀ i e, e ∈ finiteBoundary i → finiteRank e.i < finiteRank i := by
  intro i e he
  cases i with
  | leaf => simp [finiteBoundary] at he
  | root =>
    simp [finiteBoundary] at he
    rcases he with rfl
    simp [finiteRank]

def finiteIncidence : Incidence FiniteIncidence GraphRole GraphType where
  boundary := finiteBoundary
  typeFunc := fun _ => GraphType.unit
  glue := finiteGlue
  unit := .leaf
  guards := Guards.permissive FiniteIncidence
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro i e he; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    intro i ⟨e, he, hei⟩
    cases i with
    | leaf => simp [finiteBoundary] at he
    | root =>
      simp [finiteBoundary] at he
      rcases he with rfl
      simp at hei
  unit_left := by intro i; cases i <;> rfl
  unit_right := by intro i; cases i <;> rfl
  type_preserve := by intro i j k hallow hglue; rfl

/- A checked, nondegenerate model certificate for the data and laws of the
   incidence core.  It records that the carrier is inhabited and that the
   model has a genuine boundary endpoint, so the witness is not the vacuous
   empty-boundary example. -/
structure FiniteIncidenceConsistencyCertificate where
  model : Incidence FiniteIncidence GraphRole GraphType
  carrier_inhabited : Nonempty FiniteIncidence
  nonempty_boundary : ∃ i, model.boundary i ≠ []

def finiteIncidenceConsistencyCertificate : FiniteIncidenceConsistencyCertificate where
  model := finiteIncidence
  carrier_inhabited := ⟨.leaf⟩
  nonempty_boundary := by
    refine ⟨.root, ?_⟩
    simp [finiteIncidence, finiteBoundary]

/- The core's constraints therefore admit a concrete two-element model. -/
theorem incidenceCore_has_nontrivial_model :
    Nonempty (Incidence FiniteIncidence GraphRole GraphType) ∧
      ∃ i, finiteIncidence.boundary i ≠ [] := by
  exact ⟨⟨finiteIncidence⟩, finiteIncidenceConsistencyCertificate.nonempty_boundary⟩

theorem finiteIncidence_root_boundary_nonempty : finiteIncidence.boundary .root ≠ [] := by
  simp [finiteIncidence, finiteBoundary]

/- The two nodes have genuinely different observable branching: `root` has a
   boundary endpoint whereas `leaf` has none.  This makes the finite model a
   useful sharp test of the coinductive quotient, rather than merely a model
   in which every node collapses. -/
theorem finiteIncidence_root_not_approxBisim_leaf :
    ¬ approxBisim finiteIncidence .root .leaf := by
  rintro ⟨rel, hrel, hrootleaf⟩
  rcases hrel .root .leaf hrootleaf with ⟨_, hmatched⟩
  let endpoint : Endpoint FiniteIncidence GraphRole :=
    { i := .leaf, role := .src, sign := .pos, mult := 1,
      mult_pos := by omega }
  have hendpoint : endpoint ∈ finiteIncidence.boundary .root := by
    simp [finiteIncidence, finiteBoundary, endpoint]
  rcases hmatched.left endpoint hendpoint with ⟨endpoint', hleaf, _, _⟩
  simp [finiteIncidence, finiteBoundary] at hleaf

theorem finiteIncidence_leaf_not_approxBisim_root :
    ¬ approxBisim finiteIncidence .leaf .root := by
  intro h
  exact finiteIncidence_root_not_approxBisim_leaf (approxBisim_symm h)

/- Bisimilarity is discrete on the two-element incidence model. -/
theorem finiteIncidence_approxBisim_iff_eq (i j : FiniteIncidence) :
    approxBisim finiteIncidence i j ↔ i = j := by
  constructor
  · intro h
    cases i <;> cases j
    · rfl
    · exact False.elim (finiteIncidence_leaf_not_approxBisim_root h)
    · exact False.elim (finiteIncidence_root_not_approxBisim_leaf h)
    · rfl
  · intro h
    subst j
    exact approxBisim_refl finiteIncidence i

theorem finiteIncidence_quotient_mk_injective {i j : FiniteIncidence} :
    (Quotient.mk (approxBisimSetoid finiteIncidence) i :
        IncidenceQuotient finiteIncidence) =
      Quotient.mk (approxBisimSetoid finiteIncidence) j → i = j := by
  intro hij
  apply (finiteIncidence_approxBisim_iff_eq i j).mp
  exact Quotient.exact hij

theorem finiteIncidence_quotient_mk_eq_iff (i j : FiniteIncidence) :
    (Quotient.mk (approxBisimSetoid finiteIncidence) i :
        IncidenceQuotient finiteIncidence) =
      Quotient.mk (approxBisimSetoid finiteIncidence) j ↔ i = j := by
  constructor
  · exact finiteIncidence_quotient_mk_injective
  · intro h
    subst j
    rfl

/- The two-point model has a discrete observational quotient, so identity is
   already a stable normal form.  This gives a concrete witness for the
   optional operational A11--A13-style interface without strengthening the
   underlying incidence data. -/
def finiteIdentityNormalizationSpec : BisimulationNormalizationSpec finiteIncidence where
  glue_respects_approx := by
    intro i₁ i₂ j₁ j₂ k₁ k₂ hi hj hk₁ hk₂
    have hiEq : i₁ = i₂ := (finiteIncidence_approxBisim_iff_eq i₁ i₂).mp hi
    have hjEq : j₁ = j₂ := (finiteIncidence_approxBisim_iff_eq j₁ j₂).mp hj
    subst i₂
    subst j₂
    rw [hk₁] at hk₂
    injection hk₂ with hresult
    subst k₂
    exact approxBisim_refl finiteIncidence k₁
  normalize := id
  normalize_sound := by
    intro i
    exact approxBisim_refl finiteIncidence i
  normalize_idempotent := by intro i; rfl

theorem finiteIdentityNormalization_is_identity (i : FiniteIncidence) :
    finiteIdentityNormalizationSpec.normalize i = i := rfl

theorem finiteIdentityNormalization_glue_congruent
    {i₁ i₂ j₁ j₂ k₁ k₂ : FiniteIncidence}
    (hi : approxBisim finiteIncidence i₁ i₂)
    (hj : approxBisim finiteIncidence j₁ j₂)
    (hk₁ : finiteIncidence.glue (finiteIdentityNormalizationSpec.normalize i₁)
      (finiteIdentityNormalizationSpec.normalize j₁) = some k₁)
    (hk₂ : finiteIncidence.glue (finiteIdentityNormalizationSpec.normalize i₂)
      (finiteIdentityNormalizationSpec.normalize j₂) = some k₂) :
    approxBisim finiteIncidence k₁ k₂ :=
  normalized_glue_congruent finiteIdentityNormalizationSpec hi hj hk₁ hk₂

theorem finiteGlue_associative (i j k : FiniteIncidence) :
    Option.bind (finiteGlue i j) (fun ij => finiteGlue ij k) =
      Option.bind (finiteGlue j k) (fun jk => finiteGlue i jk) := by
  cases i <;> cases j <;> cases k <;> rfl

/- Concrete witnesses for the layered A2/A6--A10 interfaces.  Those legacy
   interfaces use `Unit` as their endpoint-role parameter; this model is the
   role-erasure of the nonempty finite incidence model above. -/
def finiteUnitBoundary : FiniteIncidence → Boundary FiniteIncidence Unit
  | .leaf => []
  | .root =>
      [{ i := .leaf, role := (), sign := .pos, mult := 1, mult_pos := by omega }]

def finiteUnitGluing : IncidenceGluing FiniteIncidence GraphRole GraphType where
  boundary := finiteUnitBoundary
  typeFunc := fun _ => GraphType.unit
  type_consistent := by intro i e he; rfl
  glue := finiteGlue
  unit := .leaf
  unit_left := by intro i; cases i <;> rfl
  unit_right := by intro i; cases i <;> rfl
  associativity := finiteGlue_associative

def finiteUnitPreservation : IncidencePreservation FiniteIncidence GraphRole GraphType where
  toIncidenceGluing := finiteUnitGluing
  guards := Guards.permissive FiniteIncidence
  type_preserve := by intro i j k hallow hglue; rfl
  guard_preserve := by intro i j k hallow hglue; trivial

theorem finite_model_no_direct_boundary_cycle :
    ∀ i, ¬(∃ e ∈ finiteBoundary i, e.i = i) :=
  well_founded_theorem finiteBoundary finiteRank finiteBoundary_decreases

def finiteGluingSpec : GluingSpec finiteIncidence where
  unit_ok := fun i => ⟨finiteIncidence.unit_right i, finiteIncidence.unit_left i⟩
  type_preserve := fun _ _ => rfl
  assoc_when_ok := by
    intro i j k ij ijk jk _ hij _ hijk _ hjk _
    have hleft :
        Option.bind (finiteIncidence.glue i j) (fun x => finiteIncidence.glue x k) = some ijk := by
      simp [hij, hijk]
    have hright :
        Option.bind (finiteIncidence.glue j k) (fun x => finiteIncidence.glue i x) = some ijk := by
      change Option.bind (finiteGlue j k) (fun x => finiteGlue i x) = some ijk
      rw [← finiteGlue_associative i j k]
      change Option.bind (finiteGlue i j) (fun x => finiteGlue x k) = some ijk at hleft
      exact hleft
    simpa [hjk] using hright

def finiteIdx : List FiniteIncidence := [.leaf, .root]

/- The concrete two-point boundary matrix has one positive endpoint, hence
   its Gram Laplacian is the rank-one diagonal matrix `diag(1, 0)`.  Naming
   the matrices keeps the calculations below independent of the bundled
   algebraic-model record. -/
def finiteB : Matrix FiniteIncidence FiniteIncidence Int :=
  boundaryMatrix finiteIncidence finiteIdx

def finiteL : Matrix FiniteIncidence FiniteIncidence Int :=
  laplacian finiteIncidence finiteIdx

theorem finiteB_leaf_leaf : finiteB .leaf .leaf = 0 := by native_decide
theorem finiteB_leaf_root : finiteB .leaf .root = 0 := by native_decide
theorem finiteB_root_leaf : finiteB .root .leaf = 1 := by native_decide
theorem finiteB_root_root : finiteB .root .root = 0 := by native_decide

theorem finiteL_leaf_leaf : finiteL .leaf .leaf = 1 := by native_decide
theorem finiteL_leaf_root : finiteL .leaf .root = 0 := by native_decide
theorem finiteL_root_leaf : finiteL .root .leaf = 0 := by native_decide
theorem finiteL_root_root : finiteL .root .root = 0 := by native_decide

theorem finiteL_leaf_row_sum : finiteL .leaf .leaf + finiteL .leaf .root = 1 := by
  native_decide

theorem finiteL_root_row_sum : finiteL .root .leaf + finiteL .root .root = 0 := by
  native_decide

theorem finiteL_trace : finiteL .leaf .leaf + finiteL .root .root = 1 := by
  native_decide

/- Matrix application is written using the same finite index list as the
   Gram product.  The root coordinate is the kernel direction, while the
   leaf coordinate is observed exactly. -/
def finiteLApply (x : FiniteIncidence → Int) (i : FiniteIncidence) : Int :=
  finiteIdx.foldl (fun total j => total + finiteL i j * x j) 0

theorem finiteLApply_leaf (x : FiniteIncidence → Int) :
    finiteLApply x .leaf = x .leaf := by
  simp [finiteLApply, finiteIdx, finiteL, laplacian, boundaryMatrix,
    finiteIncidence, finiteBoundary]

theorem finiteLApply_root (x : FiniteIncidence → Int) :
    finiteLApply x .root = 0 := by
  simp [finiteLApply, finiteIdx, finiteL, laplacian, boundaryMatrix,
    finiteIncidence, finiteBoundary]

theorem finiteL_kernel_iff (x : FiniteIncidence → Int) :
    (∀ i, finiteLApply x i = 0) ↔ x .leaf = 0 := by
  constructor
  · intro h
    have hleaf := h .leaf
    simp [finiteLApply_leaf] at hleaf
    exact hleaf
  · intro h i
    cases i
    · simp [finiteLApply_leaf, h]
    · exact finiteLApply_root x

/- Thus this Gram Laplacian is an actual projection.  These are action-level
   statements, so no separate finite-matrix multiplication interface is
   required. -/
theorem finiteLApply_idempotent (x : FiniteIncidence → Int) (i : FiniteIncidence) :
    finiteLApply (fun j => finiteLApply x j) i = finiteLApply x i := by
  cases i
  · simp [finiteLApply_leaf]
  · simp [finiteLApply_root]

theorem finiteLApply_comp_self (x : FiniteIncidence → Int) :
    (fun i => finiteLApply (fun j => finiteLApply x j) i) = finiteLApply x := by
  funext i
  exact finiteLApply_idempotent x i

def finiteLeafBasis : FiniteIncidence → Int
  | .leaf => 1
  | .root => 0

def finiteRootBasis : FiniteIncidence → Int
  | .leaf => 0
  | .root => 1

theorem finiteLApply_leafBasis (i : FiniteIncidence) :
    finiteLApply finiteLeafBasis i = finiteLeafBasis i := by
  cases i <;> simp [finiteLApply_leaf, finiteLApply_root, finiteLeafBasis]

theorem finiteLApply_rootBasis (i : FiniteIncidence) :
    finiteLApply finiteRootBasis i = 0 := by
  cases i <;> simp [finiteLApply_leaf, finiteLApply_root, finiteRootBasis]

theorem finiteLApply_basis_decomposition (x : FiniteIncidence → Int) (i : FiniteIncidence) :
    finiteLApply x i = x .leaf * finiteLeafBasis i := by
  cases i
  · simp [finiteLApply_leaf, finiteLeafBasis]
  · simp [finiteLApply_root, finiteLeafBasis]

theorem finite_basis_decomposition (x : FiniteIncidence → Int) :
    x = fun i => x .leaf * finiteLeafBasis i + x .root * finiteRootBasis i := by
  funext i
  cases i <;> simp [finiteLeafBasis, finiteRootBasis]

theorem finiteLApply_fixed_iff (x : FiniteIncidence → Int) :
    (∀ i, finiteLApply x i = x i) ↔ x .root = 0 := by
  constructor
  · intro h
    have hroot := h .root
    have : 0 = x .root := by
      simpa [finiteLApply_root] using hroot
    exact this.symm
  · intro h i
    cases i
    · exact finiteLApply_leaf x
    · simp [finiteLApply_root, h]

/- The complementary component is visibly killed by the projection.  In this
   two-point model this gives a direct-sum decomposition of every potential
   into its image and kernel parts. -/
def finiteLKernelComponent (x : FiniteIncidence → Int) : FiniteIncidence → Int :=
  fun i => x i - finiteLApply x i

theorem finiteL_kernelComponent_in_kernel (x : FiniteIncidence → Int) :
    ∀ i, finiteLApply (finiteLKernelComponent x) i = 0 := by
  apply (finiteL_kernel_iff (finiteLKernelComponent x)).mpr
  simp [finiteLKernelComponent, finiteLApply_leaf]

theorem finiteL_image_plus_kernel (x : FiniteIncidence → Int) (i : FiniteIncidence) :
    finiteLApply x i + finiteLKernelComponent x i = x i := by
  unfold finiteLKernelComponent
  omega

theorem finiteL_image_kernel_decomposition (x : FiniteIncidence → Int) :
    x = fun i => finiteLApply x i + finiteLKernelComponent x i := by
  funext i
  exact (finiteL_image_plus_kernel x i).symm

theorem finiteL_image_kernel_unique (x y z : FiniteIncidence → Int)
    (hdecomp : ∀ i, x i = y i + z i)
    (hyimage : ∀ i, finiteLApply y i = y i)
    (hzkernel : ∀ i, finiteLApply z i = 0) :
    y = finiteLApply x ∧ z = finiteLKernelComponent x := by
  have hzleaf : z .leaf = 0 := (finiteL_kernel_iff z).mp hzkernel
  have hyroot : y .root = 0 := by
    have hroot := hyimage .root
    have : 0 = y .root := by simpa [finiteLApply_root] using hroot
    exact this.symm
  constructor
  · funext i
    cases i
    · have hleaf := hdecomp .leaf
      simp [hzleaf] at hleaf
      simpa [finiteLApply_leaf] using hleaf.symm
    · simpa [finiteLApply_root] using hyroot
  · funext i
    cases i
    · simp [finiteLKernelComponent, finiteLApply_leaf, hzleaf]
    · have hroot := hdecomp .root
      simp [hyroot] at hroot
      simpa [finiteLKernelComponent, finiteLApply_root] using hroot.symm

def finiteAlgebraicModel : IncidenceAlgebraic FiniteIncidence GraphRole GraphType where
  toIncidencePreservation := finiteUnitPreservation
  boundaryMatrix := boundaryMatrix finiteIncidence finiteIdx
  laplacian := laplacian finiteIncidence finiteIdx

theorem finiteAlgebraic_boundaryMatrix :
    finiteAlgebraicModel.boundaryMatrix = boundaryMatrix finiteIncidence finiteIdx := rfl

theorem finiteAlgebraic_laplacian :
    finiteAlgebraicModel.laplacian = laplacian finiteIncidence finiteIdx := rfl

/- The public structures are intentionally layered: `Incidence` carries the
   core data, `GluingSpec` supplies the guarded associativity law, and the
   historical A2--A10 interfaces erase endpoint roles to `Unit`.  This
   certificate puts the concrete witnesses together without identifying the
   role-sensitive boundary of the core model with that erased presentation.
   The current A11--A15 files do not expose corresponding fields, so they are
   deliberately not claimed here. -/
structure FiniteIncidenceLayerCertificate where
  core : Incidence FiniteIncidence GraphRole GraphType
  core_eq : core = finiteIncidence
  nonempty_boundary : ∃ i, core.boundary i ≠ []
  gluing : GluingSpec finiteIncidence
  erased_gluing : IncidenceGluing FiniteIncidence GraphRole GraphType
  erased_preservation : IncidencePreservation FiniteIncidence GraphRole GraphType
  algebraic : IncidenceAlgebraic FiniteIncidence GraphRole GraphType
  erased_gluing_eq : erased_gluing = finiteUnitGluing
  erased_preservation_eq : erased_preservation = finiteUnitPreservation
  algebraic_eq : algebraic = finiteAlgebraicModel
  glue_total : ∀ i j, ∃ k, finiteIncidence.glue i j = some k
  laplacian_symmetric : ∀ i j,
    algebraic.laplacian i j = algebraic.laplacian j i
  laplacian_diagonal_nonnegative : ∀ i,
    0 ≤ algebraic.laplacian i i

def finiteIncidenceLayerCertificate : FiniteIncidenceLayerCertificate where
  core := finiteIncidence
  core_eq := rfl
  nonempty_boundary := ⟨.root, finiteIncidence_root_boundary_nonempty⟩
  gluing := finiteGluingSpec
  erased_gluing := finiteUnitGluing
  erased_preservation := finiteUnitPreservation
  algebraic := finiteAlgebraicModel
  erased_gluing_eq := rfl
  erased_preservation_eq := rfl
  algebraic_eq := rfl
  glue_total := by
    intro i j
    cases i <;> cases j <;> first | exact ⟨.leaf, rfl⟩ | exact ⟨.root, rfl⟩
  laplacian_symmetric := by
    intro i j
    exact laplacian_symmetric finiteIncidence finiteIdx i j
  laplacian_diagonal_nonnegative := by
    intro i
    exact laplacian_diagonal_nonnegative finiteIncidence finiteIdx i

/- The following projections are the directly usable consequences of the
   interfaces currently formalized in `Axioms.lean`: core A1--A5, gluing
   A6--A8, preservation A9--A10, and derived linear data A16--A17. -/
theorem finiteIncidence_available_layers :
    Nonempty (Incidence FiniteIncidence GraphRole GraphType.{0}) ∧
      Nonempty (GluingSpec finiteIncidence) ∧
      Nonempty (IncidenceGluing.{0, 0} FiniteIncidence GraphRole GraphType.{0}) ∧
      Nonempty (IncidencePreservation.{0, 0} FiniteIncidence GraphRole GraphType.{0}) ∧
      Nonempty (IncidenceAlgebraic.{0, 0} FiniteIncidence GraphRole GraphType.{0}) := by
  exact ⟨⟨finiteIncidenceLayerCertificate.core⟩,
    ⟨finiteIncidenceLayerCertificate.gluing⟩,
    ⟨finiteIncidenceLayerCertificate.erased_gluing⟩,
    ⟨finiteIncidenceLayerCertificate.erased_preservation⟩,
    ⟨finiteIncidenceLayerCertificate.algebraic⟩⟩

theorem finiteIncidence_glue_total (i j : FiniteIncidence) :
    ∃ k, finiteIncidence.glue i j = some k :=
  finiteIncidenceLayerCertificate.glue_total i j

theorem finiteIncidence_laplacian_symmetric (i j : FiniteIncidence) :
    finiteAlgebraicModel.laplacian i j = finiteAlgebraicModel.laplacian j i :=
  finiteIncidenceLayerCertificate.laplacian_symmetric i j

theorem finiteIncidence_laplacian_diagonal_nonnegative (i : FiniteIncidence) :
    0 ≤ finiteAlgebraicModel.laplacian i i :=
  finiteIncidenceLayerCertificate.laplacian_diagonal_nonnegative i

/- The nonempty finite model witnesses that observing the `root` row really
   adds positive linear energy at `leaf`; strict extension is therefore not a
   vacuous consequence of the general theorem. -/
theorem finite_root_leaf_laplacian :
    laplacian finiteIncidence [.root] .leaf .leaf = 1 := by
  native_decide

theorem finite_leaf_energy_strict_extension :
    laplacian finiteIncidence [] .leaf .leaf <
      laplacian finiteIncidence ([] ++ [.root]) .leaf .leaf := by
  apply laplacian_diagonal_strict_monotone_append finiteIncidence [] [.root] .leaf
  rw [finite_root_leaf_laplacian]
  decide

theorem finite_leaf_energy_increment :
    laplacian finiteIncidence ([] ++ [.root]) .leaf .leaf -
      laplacian finiteIncidence [] .leaf .leaf = 1 := by
  rw [laplacian_diagonal_increment_append]
  exact finite_root_leaf_laplacian

theorem finite_model_boundary_square_zero : boundarySquareZero finiteIncidence finiteIdx := by
  intro i k hi hk
  simp [finiteIdx] at hi hk
  rcases hi with rfl | rfl <;> rcases hk with rfl | rfl <;> native_decide

def finiteLinearCompleteness : LinearCompletenessSpec finiteIncidence finiteIdx where
  complete := by
    intro i j h
    cases i <;> cases j
    · exact approxBisim_refl finiteIncidence .leaf
    · have hsep := (h .leaf (by simp [finiteIdx])).left
      simp [boundaryMatrix, finiteIncidence, finiteBoundary] at hsep
    · have hsep := (h .leaf (by simp [finiteIdx])).left
      simp [boundaryMatrix, finiteIncidence, finiteBoundary] at hsep
    · exact approxBisim_refl finiteIncidence .root

theorem finite_linear_completeness {i j : FiniteIncidence}
    (h : sameLinearObservations finiteIncidence finiteIdx i j) :
    approxBisim finiteIncidence i j :=
  linear_completeness finiteLinearCompleteness h

def finiteLogicContext : List (IncidenceFormula FiniteIncidence) :=
  [.atom .root, .imp (.atom .root) (.atom .leaf)]

def finiteLogicDerivation : Derives finiteLogicContext (.atom .leaf) :=
  Derives.impE (p := Formula.atom FiniteIncidence.root)
    (q := Formula.atom FiniteIncidence.leaf)
    (Derives.ax (by simp [finiteLogicContext]))
    (Derives.ax (by simp [finiteLogicContext]))

theorem finiteLogic_modus_ponens_sound (valuation : FiniteIncidence → Prop)
    (holds : ContextSatisfies valuation finiteLogicContext) : valuation .leaf :=
  derives_sound finiteLogicDerivation holds

/-! ### Complete internal logic for the concrete finite incidence language

The two incidence nodes are exactly the two Boolean atoms used by the concrete
enumeration in `Logic`.  Transporting that enumeration, rather than postulating
one for this model, makes canonical Kripke completeness directly available to
clients which use `leaf` and `root` as their atoms. -/

def finiteIncidenceToBool : FiniteIncidence → Bool
  | .leaf => false
  | .root => true

def boolToFiniteIncidence : Bool → FiniteIncidence
  | false => .leaf
  | true => .root

theorem boolToFiniteIncidence_finiteIncidenceToBool (node : FiniteIncidence) :
    boolToFiniteIncidence (finiteIncidenceToBool node) = node := by
  cases node <;> rfl

theorem finiteIncidenceToBool_boolToFiniteIncidence (bit : Bool) :
    finiteIncidenceToBool (boolToFiniteIncidence bit) = bit := by
  cases bit <;> rfl

noncomputable def finiteIncidenceFormulaDecode : Nat → Formula FiniteIncidence :=
  fun code => (boolFormulaDecode code).map boolToFiniteIncidence

noncomputable def finiteIncidenceFormulaCode : Formula FiniteIncidence → Nat :=
  fun formula => boolFormulaCode (formula.map finiteIncidenceToBool)

theorem finiteIncidenceFormulaDecode_code (formula : Formula FiniteIncidence) :
    finiteIncidenceFormulaDecode (finiteIncidenceFormulaCode formula) = formula := by
  unfold finiteIncidenceFormulaDecode finiteIncidenceFormulaCode
  rw [boolFormulaDecode_code]
  exact Formula.map_leftInverse finiteIncidenceToBool boolToFiniteIncidence
    boolToFiniteIncidence_finiteIncidenceToBool formula

noncomputable def finiteIncidenceFormulaEnumeration : FormulaEnumeration FiniteIncidence where
  enumerate := finiteIncidenceFormulaDecode
  exhaustive := fun formula => ⟨finiteIncidenceFormulaCode formula,
    finiteIncidenceFormulaDecode_code formula⟩

theorem finiteIncidence_kripke_entails_iff_derives
    (context : List (Formula FiniteIncidence)) (formula : Formula FiniteIncidence) :
    KripkeEntails.{0, 0} context formula ↔ Derives context formula :=
  kripke_entails_iff_derives_of_enumeration finiteIncidenceFormulaEnumeration context formula

/-! A client need not unpack the Boolean coding or the general enumeration:
   every underivable finite-incidence sequent has an explicit canonical
   prime-theory world that forces its assumptions and refutes its conclusion. -/
theorem finiteIncidence_canonical_countermodel_of_not_derives
    {context : List (Formula FiniteIncidence)} {formula : Formula FiniteIncidence}
    (hnot : ¬ Derives context formula) :
    ∃ theory : PrimeTheory FiniteIncidence,
      KripkeContextForces (canonicalKripkeModel FiniteIncidence) theory context ∧
        ¬ KripkeForces (canonicalKripkeModel FiniteIncidence) theory formula :=
  canonical_countermodel_of_not_derives_of_enumeration
    finiteIncidenceFormulaEnumeration hnot

theorem finiteIncidence_not_kripke_entails_of_not_derives
    {context : List (Formula FiniteIncidence)} {formula : Formula FiniteIncidence}
    (hnot : ¬ Derives context formula) :
    ¬ KripkeEntails.{0, 0} context formula :=
  not_kripke_entails_of_not_derives_of_enumeration
    finiteIncidenceFormulaEnumeration hnot

/-! ### A concrete constructive boundary

The preceding completeness result is not merely an abstract transport result:
the incidence atom carried by the nonempty-boundary node `root` has the usual
two-world Kripke counterexample to excluded middle.  Thus the internal logic
of the concrete incidence model remains intuitionistic, while retaining the
double-negated classical principle. -/

def finiteIncidenceRootDelayedKripkeModel : KripkeModel FiniteIncidence :=
  delayedAtomKripkeModel FiniteIncidence .root

theorem finiteIncidence_root_excluded_middle_countermodel :
    ¬ KripkeForces finiteIncidenceRootDelayedKripkeModel false
      (Formula.or (Formula.atom FiniteIncidence.root)
        (Formula.neg (Formula.atom FiniteIncidence.root))) := by
  intro hforces
  rcases hforces with hroot | hnotroot
  · exact Bool.noConfusion hroot.left
  · exact hnotroot true (Or.inl rfl) ⟨rfl, rfl⟩

theorem finiteIncidence_root_excluded_middle_not_derivable :
    ¬ Derives ([] : List (Formula FiniteIncidence))
      (Formula.or (Formula.atom FiniteIncidence.root)
        (Formula.neg (Formula.atom FiniteIncidence.root))) :=
  excluded_middle_not_derivable FiniteIncidence.root

theorem finiteIncidence_root_excluded_middle_not_kripke_entails :
    ¬ KripkeEntails.{0, 0} ([] : List (Formula FiniteIncidence))
      (Formula.or (Formula.atom FiniteIncidence.root)
        (Formula.neg (Formula.atom FiniteIncidence.root))) := by
  intro hentails
  apply finiteIncidence_root_excluded_middle_countermodel
  apply hentails finiteIncidenceRootDelayedKripkeModel false
  intro formula hmem
  exact False.elim (List.not_mem_nil hmem)

theorem finiteIncidence_root_double_neg_excluded_middle_derivable :
    Derives ([] : List (Formula FiniteIncidence))
      (Formula.neg (Formula.neg
        (Formula.or (Formula.atom FiniteIncidence.root)
          (Formula.neg (Formula.atom FiniteIncidence.root))))) :=
  double_neg_excluded_middle_derivable FiniteIncidence.root

theorem finiteIncidence_root_constructive_boundary :
    (¬ Derives ([] : List (Formula FiniteIncidence))
      (Formula.or (Formula.atom FiniteIncidence.root)
        (Formula.neg (Formula.atom FiniteIncidence.root)))) ∧
    Derives ([] : List (Formula FiniteIncidence))
      (Formula.neg (Formula.neg
        (Formula.or (Formula.atom FiniteIncidence.root)
          (Formula.neg (Formula.atom FiniteIncidence.root))))) :=
  ⟨finiteIncidence_root_excluded_middle_not_derivable,
    finiteIncidence_root_double_neg_excluded_middle_derivable⟩

/- A finite extensional-set fragment: subsets of the two atoms `a` and `b`.
   A set incidence has exactly its members as boundary endpoints. -/
structure TwoSet where
  hasA : Bool
  hasB : Bool
deriving DecidableEq, Repr

def twoSetEmpty : TwoSet := { hasA := false, hasB := false }

def twoSetUnion (s t : TwoSet) : TwoSet :=
  { hasA := s.hasA || t.hasA, hasB := s.hasB || t.hasB }

def twoSetFull : TwoSet := { hasA := true, hasB := true }

def twoSetIntersection (s t : TwoSet) : TwoSet :=
  { hasA := s.hasA && t.hasA, hasB := s.hasB && t.hasB }

def twoSetComplement (s : TwoSet) : TwoSet :=
  { hasA := !s.hasA, hasB := !s.hasB }

def twoSetDifference (s t : TwoSet) : TwoSet :=
  twoSetIntersection s (twoSetComplement t)

inductive TwoAtom where | a | b
deriving DecidableEq, Repr

def twoSetContains (s : TwoSet) : TwoAtom → Bool
  | .a => s.hasA
  | .b => s.hasB

theorem twoSetUnion_contains (s t : TwoSet) (atom : TwoAtom) :
    twoSetContains (twoSetUnion s t) atom =
      (twoSetContains s atom || twoSetContains t atom) := by
  cases atom <;> rfl

theorem twoSetIntersection_contains (s t : TwoSet) (atom : TwoAtom) :
    twoSetContains (twoSetIntersection s t) atom =
      (twoSetContains s atom && twoSetContains t atom) := by
  cases atom <;> rfl

theorem twoSetComplement_contains (s : TwoSet) (atom : TwoAtom) :
    twoSetContains (twoSetComplement s) atom = !twoSetContains s atom := by
  cases atom <;> rfl

theorem twoSetDifference_contains (s t : TwoSet) (atom : TwoAtom) :
    twoSetContains (twoSetDifference s t) atom =
      (twoSetContains s atom && !twoSetContains t atom) := by
  cases atom <;> rfl

theorem twoSetUnion_empty_left (s : TwoSet) : twoSetUnion twoSetEmpty s = s := by
  cases s with
  | mk hasA hasB => cases hasA <;> cases hasB <;> rfl

theorem twoSetUnion_empty_right (s : TwoSet) : twoSetUnion s twoSetEmpty = s := by
  cases s with
  | mk hasA hasB => cases hasA <;> cases hasB <;> rfl

theorem twoSetUnion_commutative (s t : TwoSet) : twoSetUnion s t = twoSetUnion t s := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;> rfl

theorem twoSetUnion_associative (s t u : TwoSet) :
    twoSetUnion (twoSetUnion s t) u = twoSetUnion s (twoSetUnion t u) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases u with
      | mk ua ub =>
        cases sa <;> cases sb <;> cases ta <;> cases tb <;>
          cases ua <;> cases ub <;> rfl

theorem twoSetUnion_idempotent (s : TwoSet) : twoSetUnion s s = s := by
  cases s with
  | mk hasA hasB => cases hasA <;> cases hasB <;> rfl

theorem twoSetIntersection_commutative (s t : TwoSet) :
    twoSetIntersection s t = twoSetIntersection t s := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;> rfl

theorem twoSetIntersection_associative (s t u : TwoSet) :
    twoSetIntersection (twoSetIntersection s t) u =
      twoSetIntersection s (twoSetIntersection t u) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases u with
      | mk ua ub =>
        cases sa <;> cases sb <;> cases ta <;> cases tb <;>
          cases ua <;> cases ub <;> rfl

theorem twoSetIntersection_idempotent (s : TwoSet) : twoSetIntersection s s = s := by
  cases s with
  | mk sa sb => cases sa <;> cases sb <;> rfl

theorem twoSetComplement_involutive (s : TwoSet) :
    twoSetComplement (twoSetComplement s) = s := by
  cases s with
  | mk sa sb => cases sa <;> cases sb <;> rfl

theorem twoSet_deMorgan_union (s t : TwoSet) :
    twoSetComplement (twoSetUnion s t) =
      twoSetIntersection (twoSetComplement s) (twoSetComplement t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;> rfl

theorem twoSet_difference_union_intersection (s t : TwoSet) :
    twoSetUnion (twoSetDifference s t) (twoSetIntersection s t) = s := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;> rfl

theorem twoSet_difference_disjoint (s t : TwoSet) :
    twoSetIntersection (twoSetDifference s t) t = twoSetEmpty := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;> rfl

theorem twoSet_union_complement_full (s : TwoSet) :
    twoSetUnion s (twoSetComplement s) = twoSetFull := by
  cases s with
  | mk sa sb => cases sa <;> cases sb <;> rfl

theorem twoSet_intersection_complement_empty (s : TwoSet) :
    twoSetIntersection s (twoSetComplement s) = twoSetEmpty := by
  cases s with
  | mk sa sb => cases sa <;> cases sb <;> rfl

theorem twoSet_extensional (s t : TwoSet)
    (h : ∀ atom, twoSetContains s atom = twoSetContains t atom) : s = t := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      have ha := h TwoAtom.a
      have hb := h TwoAtom.b
      simp [twoSetContains] at ha hb
      cases ha
      cases hb
      rfl

inductive SetIncidence where
  | atomA
  | atomB
  | set (members : TwoSet)
deriving DecidableEq, Repr

def setBoundary : SetIncidence → Boundary SetIncidence GraphRole
  | .atomA | .atomB => []
  | .set members =>
      (if members.hasA then
        [{ i := .atomA, role := .src, sign := .pos, mult := 1, mult_pos := by omega }]
       else []) ++
      (if members.hasB then
        [{ i := .atomB, role := .src, sign := .pos, mult := 1, mult_pos := by omega }]
       else [])

def atomAEndpoint : Endpoint SetIncidence GraphRole :=
  { i := .atomA, role := .src, sign := .pos, mult := 1, mult_pos := by omega }

def atomBEndpoint : Endpoint SetIncidence GraphRole :=
  { i := .atomB, role := .src, sign := .pos, mult := 1, mult_pos := by omega }

theorem setBoundary_membership_atomA (s : TwoSet) :
    atomAEndpoint ∈ setBoundary (.set s) ↔ s.hasA = true := by
  cases s with
  | mk hasA hasB =>
    cases hasA <;> cases hasB <;> simp [setBoundary, atomAEndpoint]

theorem setBoundary_membership_atomB (s : TwoSet) :
    atomBEndpoint ∈ setBoundary (.set s) ↔ s.hasB = true := by
  cases s with
  | mk hasA hasB =>
    cases hasA <;> cases hasB <;> simp [setBoundary, atomBEndpoint]

/- Boundary membership is faithful for every Boolean operation in the
   two-atom fragment, not only for union. -/
theorem setBoundary_intersection_membership_atomA (s t : TwoSet) :
    atomAEndpoint ∈ setBoundary (.set (twoSetIntersection s t)) ↔
      atomAEndpoint ∈ setBoundary (.set s) ∧ atomAEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;>
      simp [setBoundary, atomAEndpoint, twoSetIntersection]

theorem setBoundary_intersection_membership_atomB (s t : TwoSet) :
    atomBEndpoint ∈ setBoundary (.set (twoSetIntersection s t)) ↔
      atomBEndpoint ∈ setBoundary (.set s) ∧ atomBEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;>
      simp [setBoundary, atomBEndpoint, twoSetIntersection]

theorem setBoundary_complement_membership_atomA (s : TwoSet) :
    atomAEndpoint ∈ setBoundary (.set (twoSetComplement s)) ↔
      ¬ atomAEndpoint ∈ setBoundary (.set s) := by
  cases s with
  | mk sa sb => cases sa <;> cases sb <;>
    simp [setBoundary, atomAEndpoint, twoSetComplement]

theorem setBoundary_complement_membership_atomB (s : TwoSet) :
    atomBEndpoint ∈ setBoundary (.set (twoSetComplement s)) ↔
      ¬ atomBEndpoint ∈ setBoundary (.set s) := by
  cases s with
  | mk sa sb => cases sa <;> cases sb <;>
    simp [setBoundary, atomBEndpoint, twoSetComplement]

theorem setBoundary_difference_membership_atomA (s t : TwoSet) :
    atomAEndpoint ∈ setBoundary (.set (twoSetDifference s t)) ↔
      atomAEndpoint ∈ setBoundary (.set s) ∧ ¬ atomAEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;>
      simp [setBoundary, atomAEndpoint, twoSetDifference, twoSetIntersection, twoSetComplement]

theorem setBoundary_difference_membership_atomB (s t : TwoSet) :
    atomBEndpoint ∈ setBoundary (.set (twoSetDifference s t)) ↔
      atomBEndpoint ∈ setBoundary (.set s) ∧ ¬ atomBEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb => cases sa <;> cases sb <;> cases ta <;> cases tb <;>
      simp [setBoundary, atomBEndpoint, twoSetDifference, twoSetIntersection, twoSetComplement]

theorem setBoundary_union_membership_atomA (s t : TwoSet) :
    atomAEndpoint ∈ setBoundary (.set (twoSetUnion s t)) ↔
      atomAEndpoint ∈ setBoundary (.set s) ∨ atomAEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;>
        simp [setBoundary, atomAEndpoint, twoSetUnion]

theorem setBoundary_union_membership_atomB (s t : TwoSet) :
    atomBEndpoint ∈ setBoundary (.set (twoSetUnion s t)) ↔
      atomBEndpoint ∈ setBoundary (.set s) ∨ atomBEndpoint ∈ setBoundary (.set t) := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;>
        simp [setBoundary, atomBEndpoint, twoSetUnion]

def setRank : SetIncidence → Nat
  | .atomA | .atomB => 0
  | .set _ => 1

theorem setBoundary_decreases :
    ∀ i e, e ∈ setBoundary i → setRank e.i < setRank i := by
  intro i e he
  cases i with
  | atomA => simp [setBoundary] at he
  | atomB => simp [setBoundary] at he
  | set members =>
    cases members with
    | mk hasA hasB =>
      cases hasA <;> cases hasB <;> simp [setBoundary] at he
      all_goals rcases he with rfl | rfl <;> simp [setRank]

theorem set_boundary_extensional (s t : TwoSet) :
    setBoundary (.set s) = setBoundary (.set t) ↔ s = t := by
  cases s with
  | mk sa sb =>
    cases t with
    | mk ta tb =>
      cases sa <;> cases sb <;> cases ta <;> cases tb <;>
        simp [setBoundary]

theorem twoSetUnion_hasA (s t : TwoSet) :
    (twoSetUnion s t).hasA = (s.hasA || t.hasA) := rfl

theorem twoSetUnion_hasB (s t : TwoSet) :
    (twoSetUnion s t).hasB = (s.hasB || t.hasB) := rfl

def setGlue (i j : SetIncidence) : Option SetIncidence :=
  if i = .set twoSetEmpty then some j
  else if j = .set twoSetEmpty then some i
  else some i

def setIncidenceModel : Incidence SetIncidence GraphRole GraphType where
  boundary := setBoundary
  typeFunc := fun _ => GraphType.unit
  glue := setGlue
  unit := .set twoSetEmpty
  guards := Guards.permissive SetIncidence
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro i e he; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := well_founded_theorem setBoundary setRank setBoundary_decreases
  unit_left := by intro i; simp [setGlue]
  unit_right := by
    intro i
    by_cases h : i = SetIncidence.set twoSetEmpty <;> simp [setGlue, h]
  type_preserve := by intro i j k hallow hglue; rfl

theorem setGlue_associative (i j k : SetIncidence) :
    Option.bind (setGlue i j) (fun ij => setGlue ij k) =
      Option.bind (setGlue j k) (fun jk => setGlue i jk) := by
  by_cases hi : i = SetIncidence.set twoSetEmpty <;>
    by_cases hj : j = SetIncidence.set twoSetEmpty <;>
    by_cases hk : k = SetIncidence.set twoSetEmpty <;>
    simp [setGlue, hi, hj, hk]

/- A usable finite Boolean-set model certificate.  It packages both the
   algebra on extensional two-atom sets and the fact that the incidence
   boundary displays that algebra faithfully at each atom endpoint. -/
structure SetIncidenceBooleanFragmentCertificate where
  model : Incidence SetIncidence GraphRole GraphType
  model_eq : model = setIncidenceModel
  union_empty_left : ∀ s, twoSetUnion twoSetEmpty s = s
  union_empty_right : ∀ s, twoSetUnion s twoSetEmpty = s
  union_commutative : ∀ s t, twoSetUnion s t = twoSetUnion t s
  union_associative : ∀ s t u,
    twoSetUnion (twoSetUnion s t) u = twoSetUnion s (twoSetUnion t u)
  intersection_commutative : ∀ s t,
    twoSetIntersection s t = twoSetIntersection t s
  intersection_associative : ∀ s t u,
    twoSetIntersection (twoSetIntersection s t) u =
      twoSetIntersection s (twoSetIntersection t u)
  complement_involutive : ∀ s, twoSetComplement (twoSetComplement s) = s
  deMorgan_union : ∀ s t,
    twoSetComplement (twoSetUnion s t) =
      twoSetIntersection (twoSetComplement s) (twoSetComplement t)
  complement_full : ∀ s, twoSetUnion s (twoSetComplement s) = twoSetFull
  complement_empty : ∀ s, twoSetIntersection s (twoSetComplement s) = twoSetEmpty
  difference_reconstruction : ∀ s t,
    twoSetUnion (twoSetDifference s t) (twoSetIntersection s t) = s
  difference_disjoint : ∀ s t,
    twoSetIntersection (twoSetDifference s t) t = twoSetEmpty
  boundary_extensional : ∀ s t, setBoundary (.set s) = setBoundary (.set t) ↔ s = t
  boundary_union_atomA : ∀ s t,
    atomAEndpoint ∈ setBoundary (.set (twoSetUnion s t)) ↔
      atomAEndpoint ∈ setBoundary (.set s) ∨ atomAEndpoint ∈ setBoundary (.set t)
  boundary_union_atomB : ∀ s t,
    atomBEndpoint ∈ setBoundary (.set (twoSetUnion s t)) ↔
      atomBEndpoint ∈ setBoundary (.set s) ∨ atomBEndpoint ∈ setBoundary (.set t)
  boundary_intersection_atomA : ∀ s t,
    atomAEndpoint ∈ setBoundary (.set (twoSetIntersection s t)) ↔
      atomAEndpoint ∈ setBoundary (.set s) ∧ atomAEndpoint ∈ setBoundary (.set t)
  boundary_intersection_atomB : ∀ s t,
    atomBEndpoint ∈ setBoundary (.set (twoSetIntersection s t)) ↔
      atomBEndpoint ∈ setBoundary (.set s) ∧ atomBEndpoint ∈ setBoundary (.set t)
  boundary_complement_atomA : ∀ s,
    atomAEndpoint ∈ setBoundary (.set (twoSetComplement s)) ↔
      ¬ atomAEndpoint ∈ setBoundary (.set s)
  boundary_complement_atomB : ∀ s,
    atomBEndpoint ∈ setBoundary (.set (twoSetComplement s)) ↔
      ¬ atomBEndpoint ∈ setBoundary (.set s)
  boundary_difference_atomA : ∀ s t,
    atomAEndpoint ∈ setBoundary (.set (twoSetDifference s t)) ↔
      atomAEndpoint ∈ setBoundary (.set s) ∧ ¬ atomAEndpoint ∈ setBoundary (.set t)
  boundary_difference_atomB : ∀ s t,
    atomBEndpoint ∈ setBoundary (.set (twoSetDifference s t)) ↔
      atomBEndpoint ∈ setBoundary (.set s) ∧ ¬ atomBEndpoint ∈ setBoundary (.set t)

def setIncidenceBooleanFragmentCertificate : SetIncidenceBooleanFragmentCertificate where
  model := setIncidenceModel
  model_eq := rfl
  union_empty_left := twoSetUnion_empty_left
  union_empty_right := twoSetUnion_empty_right
  union_commutative := twoSetUnion_commutative
  union_associative := twoSetUnion_associative
  intersection_commutative := twoSetIntersection_commutative
  intersection_associative := twoSetIntersection_associative
  complement_involutive := twoSetComplement_involutive
  deMorgan_union := twoSet_deMorgan_union
  complement_full := twoSet_union_complement_full
  complement_empty := twoSet_intersection_complement_empty
  difference_reconstruction := twoSet_difference_union_intersection
  difference_disjoint := twoSet_difference_disjoint
  boundary_extensional := set_boundary_extensional
  boundary_union_atomA := setBoundary_union_membership_atomA
  boundary_union_atomB := setBoundary_union_membership_atomB
  boundary_intersection_atomA := setBoundary_intersection_membership_atomA
  boundary_intersection_atomB := setBoundary_intersection_membership_atomB
  boundary_complement_atomA := setBoundary_complement_membership_atomA
  boundary_complement_atomB := setBoundary_complement_membership_atomB
  boundary_difference_atomA := setBoundary_difference_membership_atomA
  boundary_difference_atomB := setBoundary_difference_membership_atomB

theorem setIncidence_has_boolean_fragment_model :
    Nonempty SetIncidenceBooleanFragmentCertificate :=
  ⟨setIncidenceBooleanFragmentCertificate⟩

/- Hereditarily finite set syntax as a genuinely recursive incidence model.
   Its structural boundary is distinct from extensional set membership. -/
def hfBoundary : HFSet → Boundary HFSet GraphRole
  | .empty => []
  | .insert head tail =>
      [ { i := head, role := .src, sign := .pos, mult := 1, mult_pos := by omega }
      , { i := tail, role := .dst, sign := .pos, mult := 1, mult_pos := by omega } ]

theorem hfBoundary_decreases :
    ∀ i e, e ∈ hfBoundary i → e.i.rank < i.rank := by
  intro i e he
  cases i with
  | empty => simp [hfBoundary] at he
  | insert head tail =>
    simp [hfBoundary] at he
    rcases he with rfl | rfl
    · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

def hfGlue (i j : HFSet) : Option HFSet :=
  if i = .empty then some j else if j = .empty then some i else some i

def hfIncidence : Incidence HFSet GraphRole GraphType where
  boundary := hfBoundary
  typeFunc := fun _ => GraphType.unit
  glue := hfGlue
  unit := .empty
  guards := Guards.permissive HFSet
  type_consistent := fun _ _ _ => rfl
  sign_rules := by intro i e he; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := well_founded_theorem hfBoundary HFSet.rank hfBoundary_decreases
  unit_left := by intro i; simp [hfGlue]
  unit_right := by
    intro i
    by_cases h : i = HFSet.empty <;> simp [hfGlue, h]
  type_preserve := by intro i j k hallow hglue; rfl

theorem hfGlue_associative (i j k : HFSet) :
    Option.bind (hfGlue i j) (fun ij => hfGlue ij k) =
      Option.bind (hfGlue j k) (fun jk => hfGlue i jk) := by
  by_cases hi : i = HFSet.empty <;> by_cases hj : j = HFSet.empty <;>
    by_cases hk : k = HFSet.empty <;> simp [hfGlue, hi, hj, hk]

def hfNatPredecessorBoundary (n : Nat) : Boundary HFSet GraphRole :=
  [ { i := HFSet.vonNeumann n, role := .src, sign := .pos,
      mult := 1, mult_pos := by omega }
  , { i := HFSet.vonNeumann n, role := .dst, sign := .pos,
      mult := 1, mult_pos := by omega } ]

theorem hfIncidence_vonNeumann_zero_boundary :
    hfIncidence.boundary (HFSet.vonNeumann 0) = [] := rfl

theorem hfIncidence_vonNeumann_succ_boundary (n : Nat) :
    hfIncidence.boundary (HFSet.vonNeumann (n + 1)) =
      hfNatPredecessorBoundary n := by
  rfl

theorem hfIncidence_vonNeumann_succ_boundary_nonempty (n : Nat) :
    hfIncidence.boundary (HFSet.vonNeumann (n + 1)) ≠ [] := by
  rw [hfIncidence_vonNeumann_succ_boundary]
  simp [hfNatPredecessorBoundary]

structure HFNatIncidenceEmbedding where
  encode : Nat → HFSet
  injective : ∀ {m n}, encode m = encode n → m = n
  zero_is_unit : encode 0 = hfIncidence.unit
  zero_boundary : hfIncidence.boundary (encode 0) = []
  successor_boundary : ∀ n,
    hfIncidence.boundary (encode (n + 1)) = hfNatPredecessorBoundary n
  successor_nonempty : ∀ n, hfIncidence.boundary (encode (n + 1)) ≠ []

def hfNatIncidenceEmbedding : HFNatIncidenceEmbedding where
  encode := HFSet.vonNeumann
  injective := hf_vonNeumann_injective
  zero_is_unit := rfl
  zero_boundary := hfIncidence_vonNeumann_zero_boundary
  successor_boundary := hfIncidence_vonNeumann_succ_boundary
  successor_nonempty := hfIncidence_vonNeumann_succ_boundary_nonempty

theorem hf_vonNeumann_approxBisim_iff_eq (m n : Nat) :
    approxBisim hfIncidence (HFSet.vonNeumann m) (HFSet.vonNeumann n) ↔ m = n := by
  constructor
  · intro bisim
    induction m generalizing n with
    | zero =>
        cases n with
        | zero => rfl
        | succ n =>
            rcases bisim with ⟨rel, hrel, hzeroSucc⟩
            rcases hrel _ _ hzeroSucc with ⟨_, matched⟩
            let endpoint : Endpoint HFSet GraphRole :=
              { i := HFSet.vonNeumann n, role := .src, sign := .pos,
                mult := 1, mult_pos := by omega }
            have hendpoint : endpoint ∈
                hfIncidence.boundary (HFSet.vonNeumann (n + 1)) := by
              rw [hfIncidence_vonNeumann_succ_boundary]
              simp [hfNatPredecessorBoundary, endpoint]
            rcases matched.right endpoint hendpoint with ⟨endpoint', hempty, _⟩
            have impossible : False := by
              rw [hfIncidence_vonNeumann_zero_boundary] at hempty
              simp at hempty
            exact False.elim impossible
    | succ m ih =>
        cases n with
        | zero =>
            rcases bisim with ⟨rel, hrel, hsuccZero⟩
            rcases hrel _ _ hsuccZero with ⟨_, matched⟩
            let endpoint : Endpoint HFSet GraphRole :=
              { i := HFSet.vonNeumann m, role := .src, sign := .pos,
                mult := 1, mult_pos := by omega }
            have hendpoint : endpoint ∈
                hfIncidence.boundary (HFSet.vonNeumann (m + 1)) := by
              rw [hfIncidence_vonNeumann_succ_boundary]
              simp [hfNatPredecessorBoundary, endpoint]
            rcases matched.left endpoint hendpoint with ⟨endpoint', hempty, _⟩
            have impossible : False := by
              rw [hfIncidence_vonNeumann_zero_boundary] at hempty
              simp at hempty
            exact False.elim impossible
        | succ n =>
            rcases bisim with ⟨rel, hrel, hsucc⟩
            rcases hrel _ _ hsucc with ⟨_, matched⟩
            let endpoint : Endpoint HFSet GraphRole :=
              { i := HFSet.vonNeumann m, role := .src, sign := .pos,
                mult := 1, mult_pos := by omega }
            have hendpoint : endpoint ∈
                hfIncidence.boundary (HFSet.vonNeumann (m + 1)) := by
              rw [hfIncidence_vonNeumann_succ_boundary]
              simp [hfNatPredecessorBoundary, endpoint]
            rcases matched.left endpoint hendpoint with
              ⟨endpoint', htarget, _, hpredecessor⟩
            have targetEq : endpoint'.i = HFSet.vonNeumann n := by
              rw [hfIncidence_vonNeumann_succ_boundary] at htarget
              rcases List.mem_cons.mp htarget with hsrc | htail
              · rw [hsrc]
              · have hdst := List.mem_singleton.mp htail
                rw [hdst]
            have predecessorBisim : approxBisim hfIncidence
                (HFSet.vonNeumann m) (HFSet.vonNeumann n) := by
              exact ⟨rel, hrel, targetEq ▸ hpredecessor⟩
            have indexEq : m = n := ih n predecessorBisim
            exact congrArg Nat.succ indexEq
  · intro equal
    subst n
    exact approxBisim_refl hfIncidence _

structure HFNatIncidenceFaithfulEmbedding where
  embedding : HFNatIncidenceEmbedding
  bisim_iff_eq : ∀ m n,
    approxBisim hfIncidence (embedding.encode m) (embedding.encode n) ↔ m = n

def hfNatIncidenceFaithfulEmbedding : HFNatIncidenceFaithfulEmbedding where
  embedding := hfNatIncidenceEmbedding
  bisim_iff_eq := hf_vonNeumann_approxBisim_iff_eq

def hfNatIncidenceQuotientEncode (n : Nat) : IncidenceQuotient hfIncidence :=
  Quotient.mk (approxBisimSetoid hfIncidence) (HFSet.vonNeumann n)

theorem hfNatIncidenceQuotientEncode_injective {m n : Nat} :
    hfNatIncidenceQuotientEncode m = hfNatIncidenceQuotientEncode n → m = n := by
  intro equal
  have bisim : approxBisim hfIncidence
      (HFSet.vonNeumann m) (HFSet.vonNeumann n) := Quotient.exact equal
  exact (hf_vonNeumann_approxBisim_iff_eq m n).mp bisim

theorem hfNatIncidenceQuotientEncode_eq_iff (m n : Nat) :
    hfNatIncidenceQuotientEncode m = hfNatIncidenceQuotientEncode n ↔ m = n := by
  constructor
  · exact hfNatIncidenceQuotientEncode_injective
  · intro equal
    rw [equal]

theorem hfNatIncidenceQuotient_zero_ne_succ (n : Nat) :
    hfNatIncidenceQuotientEncode 0 ≠ hfNatIncidenceQuotientEncode (n + 1) := by
  intro equal
  have indexEqual : 0 = n + 1 := hfNatIncidenceQuotientEncode_injective equal
  cases indexEqual

theorem hfNatIncidenceQuotient_succ_injective {m n : Nat} :
    hfNatIncidenceQuotientEncode (m + 1) =
      hfNatIncidenceQuotientEncode (n + 1) → m = n := by
  intro equal
  have indexEqual : m + 1 = n + 1 :=
    hfNatIncidenceQuotientEncode_injective equal
  exact Nat.add_right_cancel indexEqual

theorem hfNatIncidenceQuotient_induction
    (predicate : IncidenceQuotient hfIncidence → Prop)
    (zero : predicate (hfNatIncidenceQuotientEncode 0))
    (successor : ∀ n, predicate (hfNatIncidenceQuotientEncode n) →
      predicate (hfNatIncidenceQuotientEncode (n + 1))) :
    ∀ n, predicate (hfNatIncidenceQuotientEncode n) := by
  intro n
  induction n with
  | zero => exact zero
  | succ n ih => exact successor n ih

theorem hfNatIncidenceQuotient_recursion_unique {A : Type}
    (f g : IncidenceQuotient hfIncidence → A) (step : A → A)
    (zero : f (hfNatIncidenceQuotientEncode 0) =
      g (hfNatIncidenceQuotientEncode 0))
    (fSucc : ∀ n, f (hfNatIncidenceQuotientEncode (n + 1)) =
      step (f (hfNatIncidenceQuotientEncode n)))
    (gSucc : ∀ n, g (hfNatIncidenceQuotientEncode (n + 1)) =
      step (g (hfNatIncidenceQuotientEncode n))) :
    ∀ n, f (hfNatIncidenceQuotientEncode n) =
      g (hfNatIncidenceQuotientEncode n) := by
  intro n
  induction n with
  | zero => exact zero
  | succ n ih =>
      calc
        f (hfNatIncidenceQuotientEncode (n + 1)) =
            step (f (hfNatIncidenceQuotientEncode n)) := fSucc n
        _ = step (g (hfNatIncidenceQuotientEncode n)) := congrArg step ih
        _ = g (hfNatIncidenceQuotientEncode (n + 1)) := (gSucc n).symm

structure HFNatIncidenceQuotientEmbedding where
  encode : Nat → IncidenceQuotient hfIncidence
  eq_iff : ∀ m n, encode m = encode n ↔ m = n
  zero_ne_succ : ∀ n, encode 0 ≠ encode (n + 1)
  succ_injective : ∀ {m n}, encode (m + 1) = encode (n + 1) → m = n
  induction : ∀ predicate : IncidenceQuotient hfIncidence → Prop,
    predicate (encode 0) →
    (∀ n, predicate (encode n) → predicate (encode (n + 1))) →
    ∀ n, predicate (encode n)
  recursion_unique : ∀ (A : Type)
    (f g : IncidenceQuotient hfIncidence → A) (step : A → A),
    f (encode 0) = g (encode 0) →
    (∀ n, f (encode (n + 1)) = step (f (encode n))) →
    (∀ n, g (encode (n + 1)) = step (g (encode n))) →
    ∀ n, f (encode n) = g (encode n)

def hfNatIncidenceQuotientEmbedding : HFNatIncidenceQuotientEmbedding where
  encode := hfNatIncidenceQuotientEncode
  eq_iff := hfNatIncidenceQuotientEncode_eq_iff
  zero_ne_succ := hfNatIncidenceQuotient_zero_ne_succ
  succ_injective := hfNatIncidenceQuotient_succ_injective
  induction := hfNatIncidenceQuotient_induction
  recursion_unique := by
    intro A f g step zero fSucc gSucc
    exact hfNatIncidenceQuotient_recursion_unique f g step zero fSucc gSucc

abbrev HFNatIncidenceImage :=
  { value : IncidenceQuotient hfIncidence //
    ∃ n, value = hfNatIncidenceQuotientEncode n }

def hfNatIncidenceImageEncode (n : Nat) : HFNatIncidenceImage :=
  ⟨hfNatIncidenceQuotientEncode n, ⟨n, rfl⟩⟩

noncomputable def HFNatIncidenceImage.index (value : HFNatIncidenceImage) : Nat :=
  Classical.choose value.property

theorem HFNatIncidenceImage.value_eq_encode (value : HFNatIncidenceImage) :
    value.1 = hfNatIncidenceQuotientEncode value.index :=
  Classical.choose_spec value.property

theorem HFNatIncidenceImage.index_encode (n : Nat) :
    (hfNatIncidenceImageEncode n).index = n := by
  apply hfNatIncidenceQuotientEncode_injective
  rw [← HFNatIncidenceImage.value_eq_encode (hfNatIncidenceImageEncode n)]
  rfl

theorem HFNatIncidenceImage.encode_index (value : HFNatIncidenceImage) :
    hfNatIncidenceImageEncode value.index = value := by
  apply Subtype.eq
  exact (HFNatIncidenceImage.value_eq_encode value).symm

structure HFNatIncidenceImageEquivalence where
  forward : Nat → HFNatIncidenceImage
  inverse : HFNatIncidenceImage → Nat
  left_inverse : ∀ n, inverse (forward n) = n
  right_inverse : ∀ value, forward (inverse value) = value

noncomputable def hfNatIncidenceImageEquivalence :
    HFNatIncidenceImageEquivalence where
  forward := hfNatIncidenceImageEncode
  inverse := HFNatIncidenceImage.index
  left_inverse := HFNatIncidenceImage.index_encode
  right_inverse := HFNatIncidenceImage.encode_index

def hfNatIncidenceImageZero : HFNatIncidenceImage :=
  hfNatIncidenceImageEncode 0

noncomputable def HFNatIncidenceImage.succ
    (value : HFNatIncidenceImage) : HFNatIncidenceImage :=
  hfNatIncidenceImageEncode (value.index + 1)

theorem HFNatIncidenceImage.index_succ (value : HFNatIncidenceImage) :
    value.succ.index = value.index + 1 :=
  HFNatIncidenceImage.index_encode (value.index + 1)

theorem hfNatIncidenceImageZero_ne_succ (value : HFNatIncidenceImage) :
    hfNatIncidenceImageZero ≠ value.succ := by
  intro equal
  have indexEqual := congrArg HFNatIncidenceImage.index equal
  unfold hfNatIncidenceImageZero at indexEqual
  rw [HFNatIncidenceImage.index_encode, HFNatIncidenceImage.index_succ] at indexEqual
  cases indexEqual

theorem HFNatIncidenceImage.succ_injective
    {left right : HFNatIncidenceImage} : left.succ = right.succ → left = right := by
  intro equal
  have indexEqual := congrArg HFNatIncidenceImage.index equal
  rw [HFNatIncidenceImage.index_succ, HFNatIncidenceImage.index_succ] at indexEqual
  have predecessorEqual : left.index = right.index := Nat.add_right_cancel indexEqual
  rw [← HFNatIncidenceImage.encode_index left,
    ← HFNatIncidenceImage.encode_index right, predecessorEqual]

theorem hfNatIncidenceImage_induction (predicate : HFNatIncidenceImage → Prop)
    (zero : predicate hfNatIncidenceImageZero)
    (successor : ∀ value, predicate value → predicate value.succ) :
    ∀ value, predicate value := by
  intro value
  have encoded : ∀ n, predicate (hfNatIncidenceImageEncode n) := by
    intro n
    induction n with
    | zero => exact zero
    | succ n ih =>
        have step := successor (hfNatIncidenceImageEncode n) ih
        change predicate (hfNatIncidenceImageEncode
          ((hfNatIncidenceImageEncode n).index + 1)) at step
        rw [HFNatIncidenceImage.index_encode] at step
        exact step
  rw [← HFNatIncidenceImage.encode_index value]
  exact encoded value.index

def hfNatIncidenceImageOne : HFNatIncidenceImage :=
  hfNatIncidenceImageEncode 1

noncomputable def HFNatIncidenceImage.add
    (left right : HFNatIncidenceImage) : HFNatIncidenceImage :=
  hfNatIncidenceImageEncode (left.index + right.index)

noncomputable def HFNatIncidenceImage.mul
    (left right : HFNatIncidenceImage) : HFNatIncidenceImage :=
  hfNatIncidenceImageEncode (left.index * right.index)

theorem HFNatIncidenceImage.index_add (left right : HFNatIncidenceImage) :
    (left.add right).index = left.index + right.index :=
  HFNatIncidenceImage.index_encode _

theorem HFNatIncidenceImage.index_mul (left right : HFNatIncidenceImage) :
    (left.mul right).index = left.index * right.index :=
  HFNatIncidenceImage.index_encode _

theorem HFNatIncidenceImage.eq_of_index_eq {left right : HFNatIncidenceImage}
    (equal : left.index = right.index) : left = right := by
  rw [← HFNatIncidenceImage.encode_index left,
    ← HFNatIncidenceImage.encode_index right, equal]

theorem HFNatIncidenceImage.add_zero (value : HFNatIncidenceImage) :
    value.add hfNatIncidenceImageZero = value := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_add]
  unfold hfNatIncidenceImageZero
  rw [HFNatIncidenceImage.index_encode, Nat.add_zero]

theorem HFNatIncidenceImage.zero_add (value : HFNatIncidenceImage) :
    HFNatIncidenceImage.add hfNatIncidenceImageZero value = value := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_add]
  unfold hfNatIncidenceImageZero
  rw [HFNatIncidenceImage.index_encode, Nat.zero_add]

theorem HFNatIncidenceImage.add_comm (left right : HFNatIncidenceImage) :
    left.add right = right.add left := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_add, HFNatIncidenceImage.index_add, Nat.add_comm]

theorem HFNatIncidenceImage.add_assoc
    (first second third : HFNatIncidenceImage) :
    (first.add second).add third = first.add (second.add third) := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_add, HFNatIncidenceImage.index_add,
    HFNatIncidenceImage.index_add, HFNatIncidenceImage.index_add, Nat.add_assoc]

theorem HFNatIncidenceImage.mul_one (value : HFNatIncidenceImage) :
    value.mul hfNatIncidenceImageOne = value := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_mul]
  unfold hfNatIncidenceImageOne
  rw [HFNatIncidenceImage.index_encode, Nat.mul_one]

theorem HFNatIncidenceImage.one_mul (value : HFNatIncidenceImage) :
    HFNatIncidenceImage.mul hfNatIncidenceImageOne value = value := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_mul]
  unfold hfNatIncidenceImageOne
  rw [HFNatIncidenceImage.index_encode, Nat.one_mul]

theorem HFNatIncidenceImage.mul_zero (value : HFNatIncidenceImage) :
    value.mul hfNatIncidenceImageZero = hfNatIncidenceImageZero := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_mul]
  unfold hfNatIncidenceImageZero
  rw [HFNatIncidenceImage.index_encode, Nat.mul_zero]

theorem HFNatIncidenceImage.zero_mul (value : HFNatIncidenceImage) :
    HFNatIncidenceImage.mul hfNatIncidenceImageZero value = hfNatIncidenceImageZero := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_mul]
  unfold hfNatIncidenceImageZero
  rw [HFNatIncidenceImage.index_encode, Nat.zero_mul]

theorem HFNatIncidenceImage.mul_comm (left right : HFNatIncidenceImage) :
    left.mul right = right.mul left := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_mul, HFNatIncidenceImage.index_mul, Nat.mul_comm]

theorem HFNatIncidenceImage.mul_assoc
    (first second third : HFNatIncidenceImage) :
    (first.mul second).mul third = first.mul (second.mul third) := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_mul, HFNatIncidenceImage.index_mul,
    HFNatIncidenceImage.index_mul, HFNatIncidenceImage.index_mul, Nat.mul_assoc]

theorem HFNatIncidenceImage.mul_add
    (left right third : HFNatIncidenceImage) :
    left.mul (right.add third) = (left.mul right).add (left.mul third) := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_mul, HFNatIncidenceImage.index_add,
    HFNatIncidenceImage.index_add, HFNatIncidenceImage.index_mul,
    HFNatIncidenceImage.index_mul, Nat.mul_add]

theorem HFNatIncidenceImage.add_mul
    (left right third : HFNatIncidenceImage) :
    (left.add right).mul third = (left.mul third).add (right.mul third) := by
  rw [HFNatIncidenceImage.mul_comm (left.add right) third,
    HFNatIncidenceImage.mul_add, HFNatIncidenceImage.mul_comm third left,
    HFNatIncidenceImage.mul_comm third right]

theorem HFNatIncidenceImage.succ_eq_add_one (value : HFNatIncidenceImage) :
    value.succ = value.add hfNatIncidenceImageOne := by
  apply HFNatIncidenceImage.eq_of_index_eq
  rw [HFNatIncidenceImage.index_succ, HFNatIncidenceImage.index_add]
  unfold hfNatIncidenceImageOne
  rw [HFNatIncidenceImage.index_encode]

structure HFNatIncidenceImageSemiringLaws where
  zero : HFNatIncidenceImage
  one : HFNatIncidenceImage
  add : HFNatIncidenceImage → HFNatIncidenceImage → HFNatIncidenceImage
  mul : HFNatIncidenceImage → HFNatIncidenceImage → HFNatIncidenceImage
  add_zero : ∀ value, add value zero = value
  zero_add : ∀ value, add zero value = value
  add_comm : ∀ left right, add left right = add right left
  add_assoc : ∀ first second third,
    add (add first second) third = add first (add second third)
  mul_zero : ∀ value, mul value zero = zero
  zero_mul : ∀ value, mul zero value = zero
  mul_one : ∀ value, mul value one = value
  one_mul : ∀ value, mul one value = value
  mul_comm : ∀ left right, mul left right = mul right left
  mul_assoc : ∀ first second third,
    mul (mul first second) third = mul first (mul second third)
  mul_add : ∀ left right third,
    mul left (add right third) = add (mul left right) (mul left third)
  add_mul : ∀ left right third,
    mul (add left right) third = add (mul left third) (mul right third)

noncomputable def hfNatIncidenceImageSemiringLaws :
    HFNatIncidenceImageSemiringLaws where
  zero := hfNatIncidenceImageZero
  one := hfNatIncidenceImageOne
  add := HFNatIncidenceImage.add
  mul := HFNatIncidenceImage.mul
  add_zero := HFNatIncidenceImage.add_zero
  zero_add := HFNatIncidenceImage.zero_add
  add_comm := HFNatIncidenceImage.add_comm
  add_assoc := HFNatIncidenceImage.add_assoc
  mul_zero := HFNatIncidenceImage.mul_zero
  zero_mul := HFNatIncidenceImage.zero_mul
  mul_one := HFNatIncidenceImage.mul_one
  one_mul := HFNatIncidenceImage.one_mul
  mul_comm := HFNatIncidenceImage.mul_comm
  mul_assoc := HFNatIncidenceImage.mul_assoc
  mul_add := HFNatIncidenceImage.mul_add
  add_mul := HFNatIncidenceImage.add_mul

/- Graph with nodes and edges as incidences. We take I as a sum of Node | Edge. -/
inductive GId where | node (n : Nat) | edge (e : Nat)
deriving DecidableEq, Repr

/- Merkle-ID: implementation.graph_model.simple.boundary
   Boundary encodes endpoints for edges; nodes have empty boundary. -/
def graphBoundary : GId → Boundary GId GraphRole
  | GId.node _ => []
  | GId.edge 0  => []
  | GId.edge (Nat.succ _) => []

/- Merkle-ID: implementation.graph_model.simple.incidence
   Minimal graph incidence with empty boundaries. -/
def graphIncidence : Incidence GId GraphRole GraphType where
  boundary := graphBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if i = (GId.node 0) then some j else some i
  unit     := GId.node 0
  guards   := { allow := fun _ _ => true }
  type_consistent := fun i e h => rfl
  sign_rules := fun i e h => by cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    intro i ⟨e, he, _⟩
    cases i with
    | node n => simp [graphBoundary] at he
    | edge n => cases n <;> simp [graphBoundary] at he
  unit_left := by intro i; simp
  unit_right := by intro i; by_cases h : i = GId.node 0 <;> simp [h]
  type_preserve := by intro i j k _ _; rfl

/- Triangle example identifiers. -/
def A   : GId := GId.node 1
def B   : GId := GId.node 2
def C   : GId := GId.node 3
def AB  : GId := GId.edge 1
def BC  : GId := GId.edge 2
def CA  : GId := GId.edge 3

/- Merkle-ID: implementation.graph_model.triangle.boundary
   For the triangle, override boundary function locally. -/
def triBoundary (i : GId) : Boundary GId GraphRole :=
  match i with
  | GId.node _ => []
  | GId.edge 1 =>  -- AB: A → B
      [ { i := A, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega }
      , { i := B, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ]
  | GId.edge 2 =>  -- BC: B → C
      [ { i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega }
      , { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ]
  | GId.edge 3 =>  -- CA: C → A
      [ { i := C, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega }
      , { i := A, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ]
  | _ => []

def triIncidence : Incidence GId GraphRole GraphType where
  boundary := triBoundary
  typeFunc := fun _ => GraphType.unit
  glue     := fun i j => if h : i = A then some j else some i
  unit     := A
  guards   := { allow := fun _ _ => true }
  type_consistent := by intro i e h; rfl
  sign_rules := by intro i e h; cases e.sign <;> simp
  multiplicities := fun _ e _ => e.mult_pos
  well_founded := by
    intro i ⟨e, he, hei⟩
    cases i with
    | node n => simp [triBoundary] at he
    | edge n =>
      simp only [triBoundary] at he
      split at he <;> simp_all [A, B, C]
      all_goals
        rcases he with rfl | rfl <;> simp at hei
  unit_left := by
    intro i
    change (if A = A then some i else some A) = some i
    simp
  unit_right := by
    intro i
    change (if i = A then some A else some i) = some i
    by_cases h : i = A <;> simp [h]
  type_preserve := by intro i j k _ _; rfl

/- The triangle has a genuinely nontrivial observational quotient.  Its
   directed edges have the same boundary *shape*, even though their endpoint
   identifiers differ.  Conversely an object with a boundary cannot be
   bisimilar to one with no boundary.  We state these facts without claiming
   that the infinite carrier `GId` itself has only finitely many classes. -/
theorem tri_nonempty_not_approxBisim_empty {i j : GId}
    (hi : triIncidence.boundary i ≠ []) (hj : triIncidence.boundary j = []) :
    ¬ approxBisim triIncidence i j := by
  rintro ⟨rel, hrel, hij⟩
  rcases hrel i j hij with ⟨_, hmatched⟩
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hi
  rcases hmatched.left e he with ⟨e', he', _, _⟩
  simp [hj] at he'

def triABBCRel (i j : GId) : Prop :=
  (i = AB ∧ j = BC) ∨ (i = A ∧ j = B) ∨ (i = B ∧ j = C)

theorem triABBC_isBisimulation : IsBisimulation triIncidence triABBCRel := by
  intro i j hij
  rcases hij with h | h | h
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    constructor
    · intro e he
      change e ∈ [{ i := A, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega },
        { i := B, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega }] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (rfl | rfl)
      · refine ⟨{ i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary BC
          simp [triIncidence, triBoundary, BC, B]
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · refine ⟨{ i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary BC
          simp [triIncidence, triBoundary, BC, C]
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · intro e he
      change e ∈ [{ i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega },
        { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega }] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (rfl | rfl)
      · refine ⟨{ i := A, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := A, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary AB
          simp [triIncidence, triBoundary, AB, A]
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · refine ⟨{ i := B, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := B, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary AB
          simp [triIncidence, triBoundary, AB, B]
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    change boundaryMatched triIncidence triABBCRel (GId.node 1) (GId.node 2)
    simp [boundaryMatched, triIncidence, triBoundary]
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    change boundaryMatched triIncidence triABBCRel (GId.node 2) (GId.node 3)
    simp [boundaryMatched, triIncidence, triBoundary]

theorem triangle_AB_approxBisim_BC : approxBisim triIncidence AB BC :=
  ⟨triABBCRel, triABBC_isBisimulation, Or.inl ⟨rfl, rfl⟩⟩

theorem triangle_BC_approxBisim_AB : approxBisim triIncidence BC AB :=
  approxBisim_symm triangle_AB_approxBisim_BC

/- The same local shape matching rotates the remaining edge of the triangle.
   Keeping this relation explicit makes the quotient calculation independent of
   any accidental claim about the vertices themselves. -/
def triBCCARel (i j : GId) : Prop :=
  (i = BC ∧ j = CA) ∨ (i = B ∧ j = C) ∨ (i = C ∧ j = A)

theorem triBCCA_isBisimulation : IsBisimulation triIncidence triBCCARel := by
  intro i j hij
  rcases hij with h | h | h
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    constructor
    · intro e he
      change e ∈ [{ i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega },
        { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega }] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (rfl | rfl)
      · refine ⟨{ i := C, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := C, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary CA
          simp [triIncidence, triBoundary, CA, C]
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · refine ⟨{ i := A, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := A, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary CA
          simp [triIncidence, triBoundary, CA, A]
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · intro e he
      change e ∈ [{ i := C, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega },
        { i := A, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega }] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with (rfl | rfl)
      · refine ⟨{ i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := B, role := GraphRole.src, sign := Sign.neg, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary BC
          simp [triIncidence, triBoundary, BC, B]
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · refine ⟨{ i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := (by omega) }, ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
        · change { i := C, role := GraphRole.dst, sign := Sign.pos, mult := 1, mult_pos := by omega } ∈ triIncidence.boundary BC
          simp [triIncidence, triBoundary, BC, C]
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    change boundaryMatched triIncidence triBCCARel (GId.node 2) (GId.node 3)
    simp [boundaryMatched, triIncidence, triBoundary]
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    change boundaryMatched triIncidence triBCCARel (GId.node 3) (GId.node 1)
    simp [boundaryMatched, triIncidence, triBoundary]

theorem triangle_BC_approxBisim_CA : approxBisim triIncidence BC CA :=
  ⟨triBCCARel, triBCCA_isBisimulation, Or.inl ⟨rfl, rfl⟩⟩

theorem triangle_CA_approxBisim_BC : approxBisim triIncidence CA BC :=
  approxBisim_symm triangle_BC_approxBisim_CA

theorem triangle_AB_approxBisim_CA : approxBisim triIncidence AB CA :=
  approxBisim_trans triangle_AB_approxBisim_BC triangle_BC_approxBisim_CA

theorem triangle_CA_approxBisim_AB : approxBisim triIncidence CA AB :=
  approxBisim_symm triangle_AB_approxBisim_CA

theorem triangle_AB_quotient_eq_BC :
    (Quotient.mk (approxBisimSetoid triIncidence) AB : IncidenceQuotient triIncidence) =
      Quotient.mk (approxBisimSetoid triIncidence) BC :=
  incidence_quotient_sound triangle_AB_approxBisim_BC

theorem triangle_BC_quotient_eq_CA :
    (Quotient.mk (approxBisimSetoid triIncidence) BC : IncidenceQuotient triIncidence) =
      Quotient.mk (approxBisimSetoid triIncidence) CA :=
  incidence_quotient_sound triangle_BC_approxBisim_CA

theorem triangle_AB_quotient_eq_CA :
    (Quotient.mk (approxBisimSetoid triIncidence) AB : IncidenceQuotient triIncidence) =
      Quotient.mk (approxBisimSetoid triIncidence) CA :=
  incidence_quotient_sound triangle_AB_approxBisim_CA

theorem triangle_AB_not_approxBisim_A : ¬ approxBisim triIncidence AB A := by
  apply tri_nonempty_not_approxBisim_empty
  · simp [triIncidence, triBoundary, AB]
  · simp [triIncidence, triBoundary, A]

theorem triangle_AB_quotient_ne_A :
    (Quotient.mk (approxBisimSetoid triIncidence) AB : IncidenceQuotient triIncidence) ≠
      Quotient.mk (approxBisimSetoid triIncidence) A := by
  intro h
  exact triangle_AB_not_approxBisim_A (Quotient.exact h)

theorem tri_glue_associative (i j k : GId) :
    Option.bind (triIncidence.glue i j) (fun ij => triIncidence.glue ij k) =
      Option.bind (triIncidence.glue j k) (fun jk => triIncidence.glue i jk) := by
  by_cases hi : i = A <;> by_cases hj : j = A <;> simp [triIncidence, hi, hj]

def triGluingSpec : GluingSpec triIncidence where
  unit_ok := fun i => ⟨triIncidence.unit_right i, triIncidence.unit_left i⟩
  type_preserve := fun _ _ => rfl
  assoc_when_ok := by
    intro i j k ij ijk jk _ hij _ hijk _ hjk _
    have hleft :
        Option.bind (triIncidence.glue i j) (fun x => triIncidence.glue x k) = some ijk := by
      simp [hij, hijk]
    have hright :
        Option.bind (triIncidence.glue j k) (fun x => triIncidence.glue i x) = some ijk := by
      rw [← tri_glue_associative i j k]
      exact hleft
    simpa [hjk] using hright

/- Merkle-ID: implementation.linear_algebra
   Index set for matrix computations. -/
def triIdx : List GId := [A, B, C, AB, BC, CA]

/- The six displayed identifiers split into the three boundary-free vertices
   and the three directed edges.  This is deliberately a statement about the
   finite calculation index, rather than the infinite ambient `GId`. -/
def triVertex (i : GId) : Prop := i = A ∨ i = B ∨ i = C

def triEdge (i : GId) : Prop := i = AB ∨ i = BC ∨ i = CA

theorem triangle_A_approxBisim_B : approxBisim triIncidence A B :=
  ⟨triABBCRel, triABBC_isBisimulation, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem triangle_B_approxBisim_C : approxBisim triIncidence B C :=
  ⟨triABBCRel, triABBC_isBisimulation, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

theorem triangle_A_approxBisim_C : approxBisim triIncidence A C :=
  approxBisim_trans triangle_A_approxBisim_B triangle_B_approxBisim_C

theorem triangle_vertices_approxBisim {i j : GId}
    (hi : triVertex i) (hj : triVertex j) : approxBisim triIncidence i j := by
  rcases hi with rfl | rfl | rfl
  · rcases hj with rfl | rfl | rfl
    · exact approxBisim_refl triIncidence A
    · exact triangle_A_approxBisim_B
    · exact triangle_A_approxBisim_C
  · rcases hj with rfl | rfl | rfl
    · exact approxBisim_symm triangle_A_approxBisim_B
    · exact approxBisim_refl triIncidence B
    · exact triangle_B_approxBisim_C
  · rcases hj with rfl | rfl | rfl
    · exact approxBisim_symm triangle_A_approxBisim_C
    · exact approxBisim_symm triangle_B_approxBisim_C
    · exact approxBisim_refl triIncidence C

theorem triangle_edges_approxBisim {i j : GId}
    (hi : triEdge i) (hj : triEdge j) : approxBisim triIncidence i j := by
  rcases hi with rfl | rfl | rfl
  · rcases hj with rfl | rfl | rfl
    · exact approxBisim_refl triIncidence AB
    · exact triangle_AB_approxBisim_BC
    · exact triangle_AB_approxBisim_CA
  · rcases hj with rfl | rfl | rfl
    · exact triangle_BC_approxBisim_AB
    · exact approxBisim_refl triIncidence BC
    · exact triangle_BC_approxBisim_CA
  · rcases hj with rfl | rfl | rfl
    · exact triangle_CA_approxBisim_AB
    · exact triangle_CA_approxBisim_BC
    · exact approxBisim_refl triIncidence CA

theorem tri_mem_kind {i : GId} (hi : i ∈ triIdx) : triVertex i ∨ triEdge i := by
  simp only [triIdx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [triVertex, triEdge]

theorem triangle_vertex_boundary_empty {i : GId}
    (hi : triVertex i) : triIncidence.boundary i = [] := by
  rcases hi with rfl | rfl | rfl <;> simp [triIncidence, triBoundary, A, B, C]

theorem triangle_edge_boundary_nonempty {i : GId}
    (hi : triEdge i) : triIncidence.boundary i ≠ [] := by
  rcases hi with rfl | rfl | rfl <;> simp [triIncidence, triBoundary, AB, BC, CA]

theorem triangle_vertex_not_approxBisim_edge {i j : GId}
    (hi : triVertex i) (hj : triEdge j) : ¬ approxBisim triIncidence i j := by
  intro h
  exact tri_nonempty_not_approxBisim_empty (triangle_edge_boundary_nonempty hj)
    (triangle_vertex_boundary_empty hi) (approxBisim_symm h)

theorem triangle_approxBisim_iff_same_kind {i j : GId}
    (hi : i ∈ triIdx) (hj : j ∈ triIdx) :
    approxBisim triIncidence i j ↔
      (triVertex i ∧ triVertex j) ∨ (triEdge i ∧ triEdge j) := by
  constructor
  · intro h
    rcases tri_mem_kind hi with hiv | hie
    · rcases tri_mem_kind hj with hjv | hje
      · exact Or.inl ⟨hiv, hjv⟩
      · exact False.elim (triangle_vertex_not_approxBisim_edge hiv hje h)
    · rcases tri_mem_kind hj with hjv | hje
      · exact False.elim (triangle_vertex_not_approxBisim_edge hjv hie (approxBisim_symm h))
      · exact Or.inr ⟨hie, hje⟩
  · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
    · exact triangle_vertices_approxBisim hi hj
    · exact triangle_edges_approxBisim hi hj

/- Merkle-ID: implementation.linear_algebra
   Boundary matrix and Laplacian for the triangle. -/
def triB : Matrix GId GId Int := boundaryMatrix triIncidence triIdx
def triL : Matrix GId GId Int := laplacian triIncidence triIdx

/- Every oriented triangle edge has one `-1` and one `+1` coefficient in the
   displayed vertex index, while vertex rows are empty.  Thus the explicit
   row-balance hypothesis of the general linear theorem is met. -/
theorem triangle_boundary_rows_balanced : BoundaryRowBalanced triIncidence triIdx := by
  intro row hrow
  simp [triIdx] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem triangle_laplacian_full_row_sum_zero (i : GId) :
    laplacianRowSum triIncidence triIdx i = 0 :=
  laplacian_rowSum_zero_of_boundaryRowBalanced triIncidence triIdx
    triangle_boundary_rows_balanced i

theorem triangle_laplacian_full_column_sum_zero (i : GId) :
    laplacianColumnSum triIncidence triIdx i = 0 :=
  laplacian_columnSum_zero_of_boundaryRowBalanced triIncidence triIdx
    triangle_boundary_rows_balanced i

/- The full constant potential is killed for the structural reason supplied
   by `BoundaryRowBalanced`: applying `L` to `1` is precisely its row sum.
   Unlike the vertex-only potential below, this statement ranges over every
   coordinate in the finite observation index, including the three edges. -/
def triangleFullConstantPotential (_ : GId) : Int := 1

theorem triangleFullConstantPotential_in_kernel (i : GId) :
    triIdx.foldl (fun total j =>
      total + triL i j * triangleFullConstantPotential j) 0 = 0 := by
  simpa [triangleFullConstantPotential, triL, laplacianRowSum, intListSum] using
    triangle_laplacian_full_row_sum_zero i

/- Checked entries of the triangle's incidence matrix and Laplacian. -/
theorem triB_AB_A : triB AB A = -1 := by native_decide
theorem triB_AB_B : triB AB B = 1 := by native_decide
theorem triB_BC_B : triB BC B = -1 := by native_decide
theorem triB_BC_C : triB BC C = 1 := by native_decide
theorem triB_CA_C : triB CA C = -1 := by native_decide
theorem triB_CA_A : triB CA A = 1 := by native_decide

theorem triL_AA : triL A A = 2 := by native_decide
theorem triL_BB : triL B B = 2 := by native_decide
theorem triL_CC : triL C C = 2 := by native_decide

/- The constant potential lies in the kernel of the vertex part of the
   triangle Laplacian: every vertex row has total sum zero. -/
theorem triL_A_vertex_row_sum : triL A A + triL A B + triL A C = 0 := by
  native_decide

theorem triL_B_vertex_row_sum : triL B A + triL B B + triL B C = 0 := by
  native_decide

theorem triL_C_vertex_row_sum : triL C A + triL C B + triL C C = 0 := by
  native_decide

theorem triL_vertex_trace : triL A A + triL B B + triL C C = 6 := by
  native_decide

/- Concrete spectral calculations use the same six-element finite index as
   the triangle Gram matrix.  Edge coordinates are set to zero, so these are
   the familiar vertex potentials embedded in the full incidence carrier. -/
def triLApply (x : GId → Int) (i : GId) : Int :=
  triIdx.foldl (fun total j => total + triL i j * x j) 0

def trianglePotentialAB : GId → Int
  | .node 1 => 1
  | .node 2 => -1
  | _ => 0

def trianglePotentialAC : GId → Int
  | .node 1 => 1
  | .node 3 => -1
  | _ => 0

def triangleConstantPotential : GId → Int
  | .node 1 | .node 2 | .node 3 => 1
  | _ => 0

theorem trianglePotentialAB_eigenvalue_three {i : GId} (hi : i ∈ triIdx) :
    triLApply trianglePotentialAB i = 3 * trianglePotentialAB i := by
  simp [triIdx] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem trianglePotentialAC_eigenvalue_three {i : GId} (hi : i ∈ triIdx) :
    triLApply trianglePotentialAC i = 3 * trianglePotentialAC i := by
  simp [triIdx] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem triangleConstantPotential_in_kernel {i : GId} (hi : i ∈ triIdx) :
    triLApply triangleConstantPotential i = 0 := by
  simp [triIdx] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem triangle_eigenvectors_independent :
    trianglePotentialAB A * trianglePotentialAC B -
      trianglePotentialAB B * trianglePotentialAC A = 1 := by
  native_decide

/- Integer-valued vertex potentials generated by the constant mode and the
   two displayed eigenmodes.  This intentionally describes this explicit
   three-parameter spectral family only; it makes no claim about arbitrary
   functions on the infinite ambient `GId`. -/
def triangleSpectralPotential (constant coeffAB coeffAC : Int) (i : GId) : Int :=
  constant * triangleConstantPotential i +
    coeffAB * trianglePotentialAB i + coeffAC * trianglePotentialAC i

theorem triangleSpectralPotential_A (constant coeffAB coeffAC : Int) :
    triangleSpectralPotential constant coeffAB coeffAC A =
      constant + coeffAB + coeffAC := by
  simp [triangleSpectralPotential, triangleConstantPotential,
    trianglePotentialAB, trianglePotentialAC, A]

theorem triangleSpectralPotential_B (constant coeffAB coeffAC : Int) :
    triangleSpectralPotential constant coeffAB coeffAC B = constant - coeffAB := by
  simp [triangleSpectralPotential, triangleConstantPotential,
    trianglePotentialAB, trianglePotentialAC, B, Int.sub_eq_add_neg]

theorem triangleSpectralPotential_C (constant coeffAB coeffAC : Int) :
    triangleSpectralPotential constant coeffAB coeffAC C = constant - coeffAC := by
  simp [triangleSpectralPotential, triangleConstantPotential,
    trianglePotentialAB, trianglePotentialAC, C, Int.sub_eq_add_neg]

theorem triangleSpectralPotential_edges_zero (constant coeffAB coeffAC : Int) :
    triangleSpectralPotential constant coeffAB coeffAC AB = 0 ∧
      triangleSpectralPotential constant coeffAB coeffAC BC = 0 ∧
      triangleSpectralPotential constant coeffAB coeffAC CA = 0 := by
  simp [triangleSpectralPotential, triangleConstantPotential,
    trianglePotentialAB, trianglePotentialAC, AB, BC, CA]

theorem triangleSpectralPotential_action {i : GId} (constant coeffAB coeffAC : Int)
    (hi : i ∈ triIdx) :
    triLApply (triangleSpectralPotential constant coeffAB coeffAC) i =
      3 * (triangleSpectralPotential constant coeffAB coeffAC i -
        constant * triangleConstantPotential i) := by
  simp [triIdx] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [triLApply, triIdx, triL, laplacian, boundaryMatrix, triIncidence,
      triBoundary, triangleSpectralPotential, triangleConstantPotential,
      trianglePotentialAB, trianglePotentialAC, A, B, C, AB, BC, CA] <;> omega

/- The finite triangle calculation used by the executable. -/
def triangle_boundary_composition (i k : GId) : Int :=
  triIdx.foldl (fun acc j => acc + triB i j * triB j k) 0

def triangle_square_zero_check : Bool :=
  triIdx.all (fun i => triIdx.all (fun k => triangle_boundary_composition i k = 0))

/- This is a concrete theorem, not an assumption about arbitrary incidences. -/
theorem triangle_boundary_square_zero : triangle_square_zero_check = true := by
  native_decide

theorem triangle_satisfies_boundarySquareZero : boundarySquareZero triIncidence triIdx := by
  intro i k hi hk
  simp [triIdx] at hi hk
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

/- A fully concrete T5 witness: the terminal category and its identity
   translation preserve its unique pushout. -/
def terminalCategory : IncCategory Unit where
  Hom := fun _ _ => Unit
  id := fun _ => ()
  comp := fun _ _ => ()
  id_comp := by intro a b f; rfl
  comp_id := by intro a b f; rfl
  assoc := by intro a b c d f g h; rfl

def terminalFunctor : IncFunctor terminalCategory terminalCategory where
  obj := id
  map := fun _ => ()
  map_id := by intro a; rfl
  map_comp := by intro a b c g f; rfl

/- The terminal identity translation has uniform, rather than merely
   one-cospan, pushout preservation.  This is a concrete instance of the
   optional A14--A15 family API. -/
def terminalIdentityPushoutPreservingFamily :
    PushoutPreservingFamily (IncFunctor.identity terminalCategory) :=
  PushoutPreservingFamily.identity terminalCategory

def terminalDoubleIdentityPushoutPreservingFamily :
    PushoutPreservingFamily
      ((IncFunctor.identity terminalCategory).comp (IncFunctor.identity terminalCategory)) :=
  terminalIdentityPushoutPreservingFamily.comp terminalIdentityPushoutPreservingFamily

def terminalCospan : MorphismCospan terminalCategory where
  a := ()
  b := ()
  c := ()
  left := ()
  right := ()

def terminalPushout : MorphismPushout terminalCospan where
  apex := ()
  inl := ()
  inr := ()
  commutes := rfl
  lift := fun _ _ _ _ => ()
  lift_inl := by intro q leftLeg rightLeg h; cases leftLeg; rfl
  lift_inr := by intro q leftLeg rightLeg h; cases rightLeg; rfl
  lift_unique := by intro q leftLeg rightLeg h mediator hl hr; cases mediator; rfl

def terminalIdentityFamilyPreservesPushout :
    PushoutPreserving (IncFunctor.identity terminalCategory) terminalPushout :=
  terminalIdentityPushoutPreservingFamily.at terminalPushout

def terminalFunctorPreservesPushout :
    PushoutPreserving terminalFunctor terminalPushout where
  mapped_pushout := terminalPushout
  apex_is_image := rfl

def terminal_translation_preserves_pushout :
    MorphismPushout (terminalFunctor.mapCospan terminalCospan) :=
  translation_preserves_pushout terminalPushout terminalFunctorPreservesPushout

/- A non-singleton object model using the triangle's incidence identifiers. -/
def triangleCategory : IncCategory GId where
  Hom := fun _ _ => Unit
  id := fun _ => ()
  comp := fun _ _ => ()
  id_comp := by intro a b f; rfl
  comp_id := by intro a b f; rfl
  assoc := by intro a b c d f g h; rfl

def triangleCospan : MorphismCospan triangleCategory where
  a := A
  b := A
  c := B
  left := ()
  right := ()

def trianglePushout : MorphismPushout triangleCospan where
  apex := B
  inl := ()
  inr := ()
  commutes := rfl
  lift := fun _ _ _ _ => ()
  lift_inl := by intro q leftLeg rightLeg h; cases leftLeg; rfl
  lift_inr := by intro q leftLeg rightLeg h; cases rightLeg; rfl
  lift_unique := by intro q leftLeg rightLeg h mediator hl hr; cases mediator; rfl

def triangleIdentityPreservesPushout :
    PushoutPreserving (IncFunctor.identity triangleCategory) trianglePushout where
  mapped_pushout := trianglePushout
  apex_is_image := rfl

def triangle_translation_preserves_pushout :
    MorphismPushout ((IncFunctor.identity triangleCategory).mapCospan triangleCospan) :=
  translation_preserves_pushout trianglePushout triangleIdentityPreservesPushout

/- The concrete triangle model also exercises two-stage translation.  This is
   stronger than merely reusing the identity witness: it invokes the general
   composition theorem and hence verifies that the selected pushout survives
   the intermediate presentation. -/
def triangleDoubleIdentityPreservesPushout :
    PushoutPreserving
      ((IncFunctor.identity triangleCategory).comp (IncFunctor.identity triangleCategory))
      trianglePushout :=
  PushoutPreserving.comp trianglePushout triangleIdentityPreservesPushout
    triangleIdentityPreservesPushout

def triangle_double_translation_preserves_pushout :
    MorphismPushout
      (((IncFunctor.identity triangleCategory).comp
        (IncFunctor.identity triangleCategory)).mapCospan triangleCospan) :=
  translation_preserves_pushout trianglePushout triangleDoubleIdentityPreservesPushout

def terminalSetCospan : Cospan Unit where
  a := ()
  b := ()
  c := ()
  left := id
  right := id

def terminalSetPushout : PushoutWitness terminalSetCospan where
  apex := ()
  inl := id
  inr := id
  commutes := by intro x; rfl
  lift := fun _ _ _ => id
  lift_inl := by
    intro leftLeg rightLeg h x
    cases x
    cases leftLeg ()
    rfl
  lift_inr := by
    intro leftLeg rightLeg h x
    cases x
    cases rightLeg ()
    rfl
  lift_unique := by
    intro leftLeg rightLeg h mediator hl hr
    funext x
    cases x
    cases mediator ()
    rfl

def terminalIncidencePushoutSpec :
    GluePushoutSpec (trivialIncidence : Incidence Unit GraphRole GraphType) where
  diagram := fun _ _ => terminalSetCospan
  witness := by
    intro i j k hglue
    cases i
    cases j
    cases k
    exact ⟨terminalSetPushout, rfl⟩

def terminal_glue_creates_pushout :
    { pushout : PushoutWitness (terminalIncidencePushoutSpec.diagram () ()) //
      pushout.apex = () } :=
  glue_creates_pushout terminalIncidencePushoutSpec rfl

/- The strengthened layer is inhabited: its trivial boundary has `∂² = 0`
   over every finite observation, and its gluing has a genuine terminal
   pushout witness. -/
def terminalChainComplexPushoutIncidence :
    ChainComplexPushoutIncidence Unit GraphRole GraphType where
  inc := trivialIncidence
  boundary_square_zero := by
    intro idx
    exact empty_boundaries_square_zero trivialIncidence idx (by intro i; rfl)
  glue_pushout := terminalIncidencePushoutSpec

noncomputable def terminalCompleteLogic : CompletePropositionalInternalLogic Unit :=
  completeLogicOfAtomCoding (fun _ => ()) (fun _ => 0) (fun _ => rfl)

noncomputable def terminalCoherentIncidence :
    CoherentIncidence Unit GraphRole GraphType where
  chainPushout := terminalChainComplexPushoutIncidence
  completeLogic := terminalCompleteLogic

theorem coherentIncidence_has_model :
    Nonempty (CoherentIncidence Unit GraphRole GraphType) :=
  ⟨terminalCoherentIncidence⟩

theorem terminalCoherentIncidence_empty_logic_consistent :
    DerivationallyConsistent ([] : List (Formula Unit)) :=
  terminalCoherentIncidence.empty_logic_consistent

def terminalQuotientClassification :
    BisimulationQuotientClassification (Q := Unit)
      terminalCoherentIncidence.chainPushout.inc where
  classify := id
  respects := by intro x y _; cases x; cases y; rfl
  reflects := by
    intro x y _
    cases x
    cases y
    exact approxBisim_refl _ _
  surjective := fun target => ⟨target, rfl⟩

noncomputable def terminalCoherentQuotient :
    CoherentQuotient (Q := Unit) terminalCoherentIncidence where
  target := terminalCoherentIncidence
  classification := terminalQuotientClassification
  boundary_preserves := by
    intro i
    cases i
    rfl
  type_preserves := by
    intro i
    cases i
    rfl
  glue_preserves := by
    intro i j k hglue
    cases i
    cases j
    cases k
    rfl

def terminalCoherentQuotientLogicalRetract :
    CoherentQuotientLogicalRetract terminalCoherentQuotient where
  retraction := id
  left_inverse := by
    intro incidence
    cases incidence
    rfl

example (idx : List Unit) (i k : Unit) (hi : i ∈ idx) (hk : k ∈ idx) :
    boundary_composition terminalChainComplexPushoutIncidence.inc idx i k = 0 :=
  terminalChainComplexPushoutIncidence.boundary_composition_zero idx i k hi hk

end IncidenceCore
