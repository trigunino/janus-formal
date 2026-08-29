import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D

/-!
# Local positive scalar root on the canonical C² core

The scalar C² Leibniz algebra has an exact unit and commutative product.
Squaring has derivative `2 id` at the unit, hence the Banach inverse-function
theorem supplies the unique local root branch centered at the positive unit.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Topology
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

def smoothScalarOne : SmoothQuotientField period hPeriod Real :=
  constantSmoothField period hPeriod Real 1

def c2ScalarOne : C2Scalar period hPeriod :=
  smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (smoothScalarOne period hPeriod)

theorem smoothScalarOne_mul
    (field : SmoothQuotientField period hPeriod Real) :
    smoothScalarFieldMul period hPeriod
        (smoothScalarOne period hPeriod) field = field := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp [smoothScalarFieldMul_apply, smoothScalarOne,
    constantSmoothField]

theorem smoothScalar_mul_one
    (field : SmoothQuotientField period hPeriod Real) :
    smoothScalarFieldMul period hPeriod field
        (smoothScalarOne period hPeriod) = field := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact mul_one _

theorem c2ScalarOne_mul (field : C2Scalar period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (c2ScalarOne period hPeriod) field = field := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  let lift := smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
  let one := smoothScalarOne period hPeriod
  refine DenseRange.induction_on
    (smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod)
    field (isClosed_eq (product (lift one)).continuous continuous_id) ?_
  intro smooth
  change product (lift one) (lift smooth) = lift smooth
  rw [canonicalPhysicalScalarC2JetCoreProduct_smooth,
    smoothScalarOne_mul]

theorem c2Scalar_mul_one (field : C2Scalar period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod field
        (c2ScalarOne period hPeriod) = field := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  let lift := smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
  let one := smoothScalarOne period hPeriod
  refine DenseRange.induction_on
    (smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod)
    field (isClosed_eq (product.flip (lift one)).continuous continuous_id) ?_
  intro smooth
  change product (lift smooth) (lift one) = lift smooth
  rw [canonicalPhysicalScalarC2JetCoreProduct_smooth,
    smoothScalar_mul_one]

theorem c2ScalarProduct_comm
    (first second : C2Scalar period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second =
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod second first := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  let lift := smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
  have hDense :=
    smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod
  refine DenseRange.induction_on hDense first
    (isClosed_eq (product.flip second).continuous (product second).continuous) ?_
  intro smoothFirst
  refine DenseRange.induction_on hDense second
    (isClosed_eq (product (lift smoothFirst)).continuous
      (product.flip (lift smoothFirst)).continuous) ?_
  intro smoothSecond
  rw [canonicalPhysicalScalarC2JetCoreProduct_smooth,
    canonicalPhysicalScalarC2JetCoreProduct_smooth]
  apply congrArg lift
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact mul_comm _ _

def c2ScalarSquare (field : C2Scalar period hPeriod) :
    C2Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreProduct period hPeriod field field

def c2ScalarSylvester (root : C2Scalar period hPeriod) :
    C2Scalar period hPeriod →L[Real] C2Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreProduct period hPeriod root +
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip root

theorem c2ScalarSquare_hasFDerivAt
    (root : C2Scalar period hPeriod) :
    HasFDerivAt (c2ScalarSquare period hPeriod)
      (c2ScalarSylvester period hPeriod root) root := by
  change HasFDerivAt
    (fun field : C2Scalar period hPeriod =>
      canonicalPhysicalScalarC2JetCoreProduct
        period hPeriod field field)
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod root +
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip root)
    root
  exact (canonicalPhysicalScalarC2JetCoreProduct
    period hPeriod).hasFDerivAt (x := root) |>.clm_apply
      (hasFDerivAt_id root)

theorem c2ScalarSquare_contDiff :
    ContDiff Real ∞ (c2ScalarSquare period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreProduct
    period hPeriod).contDiff.clm_apply contDiff_id

def c2ScalarDoubleEquiv :
    C2Scalar period hPeriod ≃L[Real] C2Scalar period hPeriod where
  toFun field := (2 : Real) • field
  invFun field := (1 / 2 : Real) • field
  left_inv field := by
    change (1 / 2 : Real) • ((2 : Real) • field) = field
    rw [smul_smul]
    norm_num
  right_inv field := by
    change (2 : Real) • ((1 / 2 : Real) • field) = field
    rw [smul_smul]
    norm_num
  map_add' first second := by simp [smul_add]
  map_smul' scalar field := by simp [smul_smul, mul_comm]
  continuous_toFun :=
    ((2 : Real) • ContinuousLinearMap.id Real
      (C2Scalar period hPeriod)).continuous
  continuous_invFun :=
    ((1 / 2 : Real) • ContinuousLinearMap.id Real
      (C2Scalar period hPeriod)).continuous

theorem c2ScalarDoubleEquiv_forward_eq :
    (c2ScalarDoubleEquiv period hPeriod :
      C2Scalar period hPeriod →L[Real] C2Scalar period hPeriod) =
      c2ScalarSylvester period hPeriod
        (c2ScalarOne period hPeriod) := by
  apply ContinuousLinearMap.ext
  intro field
  change (2 : Real) • field =
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (c2ScalarOne period hPeriod) field +
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod field
        (c2ScalarOne period hPeriod)
  rw [c2ScalarOne_mul, c2Scalar_mul_one]
  exact two_smul Real field

def c2ScalarSylvesterFamily :
    C2Scalar period hPeriod →L[Real]
      C2Scalar period hPeriod →L[Real] C2Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreProduct period hPeriod +
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip

@[simp]
theorem c2ScalarSylvesterFamily_apply (root : C2Scalar period hPeriod) :
    c2ScalarSylvesterFamily period hPeriod root =
      c2ScalarSylvester period hPeriod root :=
  rfl

def c2ScalarSylvesterRegularSet : Set (C2Scalar period hPeriod) :=
  c2ScalarSylvesterFamily period hPeriod ⁻¹'
    Set.range ((↑) :
      (C2Scalar period hPeriod ≃L[Real] C2Scalar period hPeriod) →
        C2Scalar period hPeriod →L[Real] C2Scalar period hPeriod)

theorem c2ScalarSylvesterRegularSet_isOpen :
    IsOpen (c2ScalarSylvesterRegularSet period hPeriod) := by
  apply ContinuousLinearEquiv.isOpen.preimage
  exact (c2ScalarSylvesterFamily period hPeriod).continuous

theorem c2ScalarOne_mem_sylvesterRegularSet :
    c2ScalarOne period hPeriod ∈
      c2ScalarSylvesterRegularSet period hPeriod := by
  exact ⟨c2ScalarDoubleEquiv period hPeriod,
    c2ScalarDoubleEquiv_forward_eq period hPeriod⟩

theorem c2ScalarSquare_contDiff_two :
    ContDiff Real 2 (c2ScalarSquare period hPeriod) :=
  (c2ScalarSquare_contDiff period hPeriod).of_le
    (show (2 : ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)

def c2ScalarBaseSquareChart :
    OpenPartialHomeomorph (C2Scalar period hPeriod)
      (C2Scalar period hPeriod) :=
  (c2ScalarSquare_contDiff_two period hPeriod).contDiffAt
    |>.toOpenPartialHomeomorph
      (c2ScalarSquare period hPeriod)
      ((c2ScalarSquare_hasFDerivAt period hPeriod
        (c2ScalarOne period hPeriod)).congr_fderiv
          (c2ScalarDoubleEquiv_forward_eq period hPeriod).symm)
      (by norm_num)

def c2ScalarLocalSquareChart :
    OpenPartialHomeomorph (C2Scalar period hPeriod)
      (C2Scalar period hPeriod) :=
  (c2ScalarBaseSquareChart period hPeriod).restrOpen
    (c2ScalarSylvesterRegularSet period hPeriod)
    (c2ScalarSylvesterRegularSet_isOpen period hPeriod)

def c2ScalarLocalRootTarget : Set (C2Scalar period hPeriod) :=
  (c2ScalarLocalSquareChart period hPeriod).target

theorem c2ScalarLocalRootTarget_isOpen :
    IsOpen (c2ScalarLocalRootTarget period hPeriod) :=
  (c2ScalarLocalSquareChart period hPeriod).open_target

theorem c2ScalarOne_mem_localSquareChart_source :
    c2ScalarOne period hPeriod ∈
      (c2ScalarLocalSquareChart period hPeriod).source := by
  rw [c2ScalarLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨(c2ScalarSquare_contDiff_two period hPeriod).contDiffAt
      |>.mem_toOpenPartialHomeomorph_source
        ((c2ScalarSquare_hasFDerivAt period hPeriod
          (c2ScalarOne period hPeriod)).congr_fderiv
            (c2ScalarDoubleEquiv_forward_eq period hPeriod).symm)
        (by norm_num),
    c2ScalarOne_mem_sylvesterRegularSet period hPeriod⟩

theorem c2ScalarSquare_one :
    c2ScalarSquare period hPeriod (c2ScalarOne period hPeriod) =
      c2ScalarOne period hPeriod :=
  c2ScalarOne_mul period hPeriod (c2ScalarOne period hPeriod)

theorem c2ScalarOne_mem_localRootTarget :
    c2ScalarOne period hPeriod ∈
      c2ScalarLocalRootTarget period hPeriod := by
  rw [← c2ScalarSquare_one period hPeriod]
  exact (c2ScalarLocalSquareChart period hPeriod).map_source
    (c2ScalarOne_mem_localSquareChart_source period hPeriod)

/-- Local scalar root branch selected by the positive center `1`. -/
def c2ScalarLocalRootBranch :
    C2Scalar period hPeriod → C2Scalar period hPeriod :=
  (c2ScalarLocalSquareChart period hPeriod).symm

theorem c2ScalarLocalRootBranch_square
    {nearby : C2Scalar period hPeriod}
    (hNearby : nearby ∈ c2ScalarLocalRootTarget period hPeriod) :
    c2ScalarSquare period hPeriod
        (c2ScalarLocalRootBranch period hPeriod nearby) = nearby :=
  (c2ScalarLocalSquareChart period hPeriod).right_inv hNearby

theorem c2ScalarLocalRootBranch_at_one :
    c2ScalarLocalRootBranch period hPeriod
        (c2ScalarOne period hPeriod) =
      c2ScalarOne period hPeriod := by
  calc
    c2ScalarLocalRootBranch period hPeriod
        (c2ScalarOne period hPeriod) =
      c2ScalarLocalRootBranch period hPeriod
        (c2ScalarSquare period hPeriod
          (c2ScalarOne period hPeriod)) :=
      congrArg (c2ScalarLocalRootBranch period hPeriod)
        (c2ScalarSquare_one period hPeriod).symm
    _ = c2ScalarOne period hPeriod :=
      (c2ScalarLocalSquareChart period hPeriod).left_inv
        (c2ScalarOne_mem_localSquareChart_source period hPeriod)

theorem c2ScalarLocalRootBranch_contDiffAt
    (nearby : C2Scalar period hPeriod)
    (hNearby : nearby ∈ c2ScalarLocalRootTarget period hPeriod) :
    ContDiffAt Real 2
      (c2ScalarLocalRootBranch period hPeriod) nearby := by
  have hSource :=
    (c2ScalarLocalSquareChart period hPeriod).map_target hNearby
  rw [c2ScalarLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  rcases hSource.2 with ⟨equiv, hEquiv⟩
  apply (c2ScalarLocalSquareChart period hPeriod)
    |>.contDiffAt_symm hNearby (f₀' := equiv)
  · exact (c2ScalarSquare_hasFDerivAt period hPeriod
      ((c2ScalarLocalSquareChart period hPeriod).symm nearby)).congr_fderiv
        hEquiv.symm
  · exact (c2ScalarSquare_contDiff_two period hPeriod).contDiffAt

theorem c2ScalarLocalRootBranch_contDiffOn :
    ContDiffOn Real 2 (c2ScalarLocalRootBranch period hPeriod)
      (c2ScalarLocalRootTarget period hPeriod) := by
  intro nearby hNearby
  exact (c2ScalarLocalRootBranch_contDiffAt
    period hPeriod nearby hNearby).contDiffWithinAt

/-- Summary gate for the local positive scalar C² root. -/
theorem canonical_physical_scalar_c2_local_root_gate :
    IsOpen (c2ScalarLocalRootTarget period hPeriod) ∧
      c2ScalarOne period hPeriod ∈
        c2ScalarLocalRootTarget period hPeriod ∧
      ContDiffOn Real 2 (c2ScalarLocalRootBranch period hPeriod)
        (c2ScalarLocalRootTarget period hPeriod) ∧
      (∀ nearby,
        nearby ∈ c2ScalarLocalRootTarget period hPeriod →
          c2ScalarSquare period hPeriod
              (c2ScalarLocalRootBranch period hPeriod nearby) = nearby) := by
  exact ⟨c2ScalarLocalRootTarget_isOpen period hPeriod,
    c2ScalarOne_mem_localRootTarget period hPeriod,
    c2ScalarLocalRootBranch_contDiffOn period hPeriod,
    fun nearby hNearby =>
      c2ScalarLocalRootBranch_square
        (period := period) (hPeriod := hPeriod)
        (nearby := nearby) hNearby⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
end JanusFormal
