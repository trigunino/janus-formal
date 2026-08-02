import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D

/-!
# Arbitrary finite matrix product on the canonical strong core

The established scalar `C⁰ ∩ H¹` product is assembled for every finite
matrix size.  The product agrees with pointwise multiplication on continuous
representatives, has a dense smooth matrix core, is associative, and makes
squaring smooth with the expected Sylvester derivative.  This extends the
existing `4 × 4` gate without changing it and is needed for redundant finite
tangent generators, whose cardinality need not be four.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev ContinuousScalar :=
  C(EffectiveQuotient period hPeriod, Real)

abbrev StrongFiniteMatrix (dimension : Nat) :=
  Fin dimension → Fin dimension → StrongScalar period hPeriod

abbrev SmoothFiniteMatrix (dimension : Nat) :=
  Fin dimension → Fin dimension → SmoothQuotientField period hPeriod Real

abbrev ContinuousFiniteMatrix (dimension : Nat) :=
  Fin dimension → Fin dimension → ContinuousScalar period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup (StrongScalar period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real (StrongScalar period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace (StrongScalar period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

private def finiteMatrixProductBilinear
    (dimension : Nat)
    {Scalar : Type*} [AddCommMonoid Scalar] [Module Real Scalar]
    (product : Scalar →ₗ[Real] Scalar →ₗ[Real] Scalar) :
    (Fin dimension → Fin dimension → Scalar) →ₗ[Real]
      (Fin dimension → Fin dimension → Scalar) →ₗ[Real]
        (Fin dimension → Fin dimension → Scalar) :=
  LinearMap.mk₂ Real
    (fun first second row column => ∑ middle : Fin dimension,
      product (first row middle) (second middle column))
    (by
      intro first second third
      funext row column
      simp only [Pi.add_apply, map_add, LinearMap.add_apply,
        Finset.sum_add_distrib])
    (by
      intro scalar first second
      funext row column
      simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply,
        Finset.smul_sum])
    (by
      intro first second third
      funext row column
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib])
    (by
      intro scalar first second
      funext row column
      simp only [Pi.smul_apply, map_smul, Finset.smul_sum])

def strongFiniteMatrixProductBilinear (dimension : Nat) :
    StrongFiniteMatrix period hPeriod dimension →ₗ[Real]
      StrongFiniteMatrix period hPeriod dimension →ₗ[Real]
        StrongFiniteMatrix period hPeriod dimension :=
  finiteMatrixProductBilinear dimension
    (scalarStrongProductBilinear period hPeriod)

def strongFiniteMatrixProduct (dimension : Nat) :
    StrongFiniteMatrix period hPeriod dimension →L[Real]
      StrongFiniteMatrix period hPeriod dimension →L[Real]
        StrongFiniteMatrix period hPeriod dimension :=
  LinearMap.mkContinuous₂
    (E := StrongFiniteMatrix period hPeriod dimension)
    (F := StrongFiniteMatrix period hPeriod dimension)
    (G := StrongFiniteMatrix period hPeriod dimension)
    (strongFiniteMatrixProductBilinear
      (period := period) (hPeriod := hPeriod) dimension)
    ((dimension : Real) * smoothStrongH1C0ProductBoundConstant period hPeriod)
    (by
      intro first second
      let C := smoothStrongH1C0ProductBoundConstant period hPeriod
      have hC : 0 ≤ C :=
        smoothStrongH1C0ProductBoundConstant_nonnegative period hPeriod
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro row
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro column
      calc
        ‖∑ middle : Fin dimension,
            scalarStrongProduct period hPeriod
              (first row middle) (second middle column)‖ ≤
            ∑ middle : Fin dimension,
              ‖scalarStrongProduct period hPeriod
                (first row middle) (second middle column)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _middle : Fin dimension, C * ‖first‖ * ‖second‖ := by
          apply Finset.sum_le_sum
          intro middle _
          calc
            ‖scalarStrongProduct period hPeriod
                (first row middle) (second middle column)‖ ≤
                C * ‖first row middle‖ * ‖second middle column‖ :=
              canonicalPhysicalScalarStrongH1C0CoreProduct_norm_le
                period hPeriod (first row middle) (second middle column)
            _ ≤ C * ‖first‖ * ‖second‖ := by
              gcongr
              · exact (norm_le_pi_norm (first row) middle).trans
                  (norm_le_pi_norm first row)
              · exact (norm_le_pi_norm (second middle) column).trans
                  (norm_le_pi_norm second middle)
        _ = ((dimension : Real) * C) * ‖first‖ * ‖second‖ := by
          simp
          ring)

@[simp]
theorem strongFiniteMatrixProduct_apply
    (dimension : Nat)
    (first second : StrongFiniteMatrix period hPeriod dimension)
    (row column : Fin dimension) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension first second row column =
      ∑ middle : Fin dimension,
        scalarStrongProduct period hPeriod
          (first row middle) (second middle column) := by
  simp [strongFiniteMatrixProduct, strongFiniteMatrixProductBilinear,
    finiteMatrixProductBilinear, scalarStrongProductBilinear]

def smoothFiniteMatrixToStrong (dimension : Nat) :
    SmoothFiniteMatrix period hPeriod dimension →ₗ[Real]
      StrongFiniteMatrix period hPeriod dimension where
  toFun matrix row column :=
    smoothToCanonicalPhysicalScalarStrongH1C0Core
      period hPeriod (matrix row column)
  map_add' first second := by
    funext row column
    exact (smoothToCanonicalPhysicalScalarStrongH1C0Core
      period hPeriod).map_add (first row column) (second row column)
  map_smul' scalar matrix := by
    funext row column
    exact (smoothToCanonicalPhysicalScalarStrongH1C0Core
      period hPeriod).map_smul scalar (matrix row column)

def smoothFiniteMatrixProduct (dimension : Nat)
    (first second : SmoothFiniteMatrix period hPeriod dimension) :
    SmoothFiniteMatrix period hPeriod dimension :=
  fun row column => ∑ middle : Fin dimension,
    smoothScalarFieldMul period hPeriod
      (first row middle) (second middle column)

theorem strongFiniteMatrixProduct_smooth
    (dimension : Nat)
    (first second : SmoothFiniteMatrix period hPeriod dimension) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        (smoothFiniteMatrixToStrong period hPeriod dimension first)
        (smoothFiniteMatrixToStrong period hPeriod dimension second) =
      smoothFiniteMatrixToStrong period hPeriod dimension
        (smoothFiniteMatrixProduct period hPeriod dimension first second) := by
  funext row column
  rw [strongFiniteMatrixProduct_apply]
  change (∑ middle : Fin dimension,
      canonicalPhysicalScalarStrongH1C0CoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (first row middle))
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (second middle column))) =
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
      (∑ middle : Fin dimension, smoothScalarFieldMul period hPeriod
        (first row middle) (second middle column))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro middle _
  exact canonicalPhysicalScalarStrongH1C0CoreProduct_smooth
    period hPeriod (first row middle) (second middle column)

def strongFiniteMatrixToContinuous (dimension : Nat) :
    StrongFiniteMatrix period hPeriod dimension →L[Real]
      ContinuousFiniteMatrix period hPeriod dimension :=
  ContinuousLinearMap.piMap fun _ : Fin dimension =>
    ContinuousLinearMap.piMap fun _ : Fin dimension =>
      canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod

def continuousFiniteMatrixProduct (dimension : Nat)
    (first second : ContinuousFiniteMatrix period hPeriod dimension) :
    ContinuousFiniteMatrix period hPeriod dimension :=
  fun row column => ∑ middle : Fin dimension,
    first row middle * second middle column

theorem strongFiniteMatrixProduct_toContinuous
    (dimension : Nat)
    (first second : StrongFiniteMatrix period hPeriod dimension) :
    strongFiniteMatrixToContinuous period hPeriod dimension
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension first second) =
      continuousFiniteMatrixProduct period hPeriod dimension
        (strongFiniteMatrixToContinuous period hPeriod dimension first)
        (strongFiniteMatrixToContinuous period hPeriod dimension second) := by
  funext row column
  change canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
      (strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension first second row column) =
    ∑ middle : Fin dimension,
      canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
          (first row middle) *
        canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
          (second middle column)
  rw [strongFiniteMatrixProduct_apply, map_sum]
  apply Finset.sum_congr rfl
  intro middle _
  exact scalarStrongProduct_toContinuous period hPeriod
    (first row middle) (second middle column)

theorem smoothFiniteMatrixToStrong_denseRange (dimension : Nat) :
    DenseRange (smoothFiniteMatrixToStrong period hPeriod dimension) := by
  exact DenseRange.piMap fun _ : Fin dimension =>
    DenseRange.piMap fun _ : Fin dimension =>
      smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
        period hPeriod

@[simp]
theorem smoothScalarFieldFinsetSum_apply
    {Index : Type*} (indices : Finset Index)
    (fields : Index → SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    (Finset.sum indices fields) point =
      Finset.sum indices (fun index => fields index point) := by
  let evaluation : SmoothQuotientField period hPeriod Real →+ Real :=
    { toFun := fun field => field point
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum evaluation fields indices

theorem smoothFiniteMatrixProduct_assoc
    (dimension : Nat)
    (first second third : SmoothFiniteMatrix period hPeriod dimension) :
    smoothFiniteMatrixProduct period hPeriod dimension
        (smoothFiniteMatrixProduct period hPeriod dimension first second) third =
      smoothFiniteMatrixProduct period hPeriod dimension first
        (smoothFiniteMatrixProduct period hPeriod dimension second third) := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothFiniteMatrixProduct, smoothScalarFieldMul_apply,
    smoothScalarFieldFinsetSum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem smoothScalarFieldMul_assoc
    (first second third : SmoothQuotientField period hPeriod Real) :
    smoothScalarFieldMul period hPeriod
        (smoothScalarFieldMul period hPeriod first second) third =
      smoothScalarFieldMul period hPeriod first
        (smoothScalarFieldMul period hPeriod second third) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothScalarFieldMul_apply, mul_assoc]

theorem scalarStrongProduct_assoc
    (first second third : StrongScalar period hPeriod) :
    scalarStrongProduct period hPeriod
        (scalarStrongProduct period hPeriod first second) third =
      scalarStrongProduct period hPeriod first
        (scalarStrongProduct period hPeriod second third) := by
  let product := scalarStrongProduct period hPeriod
  let lift := smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
  have hDense : DenseRange lift :=
    smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange period hPeriod
  refine DenseRange.induction_on hDense first
    (isClosed_eq
      ((product.flip third).comp (product.flip second)).continuous
      (product.flip (product second third)).continuous) ?_
  intro smoothFirst
  refine DenseRange.induction_on hDense second
    (isClosed_eq
      ((product.flip third).comp (product (lift smoothFirst))).continuous
      ((product (lift smoothFirst)).comp (product.flip third)).continuous) ?_
  intro smoothSecond
  refine DenseRange.induction_on hDense third
    (isClosed_eq
      (product (product (lift smoothFirst) (lift smoothSecond))).continuous
      ((product (lift smoothFirst)).comp
        (product (lift smoothSecond))).continuous) ?_
  intro smoothThird
  change product (product (lift smoothFirst) (lift smoothSecond))
      (lift smoothThird) =
    product (lift smoothFirst)
      (product (lift smoothSecond) (lift smoothThird))
  simp only [product, lift, scalarStrongProduct_apply,
    canonicalPhysicalScalarStrongH1C0CoreProduct_smooth,
    smoothStrongH1C0CoreProduct]
  exact congrArg
    (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)
    (smoothScalarFieldMul_assoc period hPeriod
      smoothFirst smoothSecond smoothThird)

theorem scalarStrongProduct_sum_left
    {Index : Type*} (indices : Finset Index)
    (fields : Index → StrongScalar period hPeriod)
    (second : StrongScalar period hPeriod) :
    scalarStrongProduct period hPeriod (∑ index ∈ indices, fields index) second =
      ∑ index ∈ indices,
        scalarStrongProduct period hPeriod (fields index) second := by
  change (scalarStrongProduct period hPeriod).flip second
      (∑ index ∈ indices, fields index) = _
  exact map_sum ((scalarStrongProduct period hPeriod).flip second) fields indices

theorem scalarStrongProduct_sum_right
    {Index : Type*} (indices : Finset Index)
    (first : StrongScalar period hPeriod)
    (fields : Index → StrongScalar period hPeriod) :
    scalarStrongProduct period hPeriod first (∑ index ∈ indices, fields index) =
      ∑ index ∈ indices,
        scalarStrongProduct period hPeriod first (fields index) := by
  exact map_sum (scalarStrongProduct period hPeriod first) fields indices

theorem strongFiniteMatrixProduct_assoc
    (dimension : Nat)
    (first second third : StrongFiniteMatrix period hPeriod dimension) :
    strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension first second) third =
      strongFiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) dimension first
        (strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) dimension second third) := by
  funext row column
  simp only [strongFiniteMatrixProduct_apply]
  simp_rw [scalarStrongProduct_sum_left, scalarStrongProduct_sum_right]
  conv_lhs => rw [Finset.sum_comm]
  simp only [scalarStrongProduct_assoc]

def strongFiniteMatrixSquare (dimension : Nat)
    (matrix : StrongFiniteMatrix period hPeriod dimension) :
    StrongFiniteMatrix period hPeriod dimension :=
  strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension matrix matrix

def strongFiniteMatrixSylvester (dimension : Nat)
    (root : StrongFiniteMatrix period hPeriod dimension) :
    StrongFiniteMatrix period hPeriod dimension →L[Real]
      StrongFiniteMatrix period hPeriod dimension :=
  strongFiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension root +
    ((strongFiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension).flip root :
      StrongFiniteMatrix period hPeriod dimension →L[Real]
        StrongFiniteMatrix period hPeriod dimension)

theorem strongFiniteMatrixSquare_hasFDerivAt
    (dimension : Nat)
    (root : StrongFiniteMatrix period hPeriod dimension) :
    HasFDerivAt (strongFiniteMatrixSquare period hPeriod dimension)
      (strongFiniteMatrixSylvester period hPeriod dimension root) root := by
  have hDerivative :=
    ((strongFiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) dimension).hasFDerivAt
        (x := root)).clm_apply
      (hasFDerivAt_id root)
  exact hDerivative.congr_fderiv rfl

theorem strongFiniteMatrixSquare_contDiff (dimension : Nat) :
    ContDiff Real ⊤ (strongFiniteMatrixSquare period hPeriod dimension) :=
  (strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) dimension).contDiff.clm_apply contDiff_id

/-- Summary gate for arbitrary finite strong coefficient matrices. -/
theorem canonical_physical_strong_h1_c0_finite_matrix_product_gate
    (dimension : Nat) :
    DenseRange (smoothFiniteMatrixToStrong period hPeriod dimension) ∧
      ContDiff Real ⊤
        (strongFiniteMatrixSquare period hPeriod dimension) := by
  exact ⟨smoothFiniteMatrixToStrong_denseRange period hPeriod dimension,
    strongFiniteMatrixSquare_contDiff period hPeriod dimension⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
end JanusFormal
