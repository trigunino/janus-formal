import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D

/-!
# Matrix product on the canonical strong `C⁰ ∩ H¹` core

The existing scalar product is rebundled in the standard subtype topology and
assembled into the ordinary finite `4 × 4` matrix product. The resulting map
is continuous bilinear, agrees with smooth multiplication, and its continuous
representative is the pointwise matrix product. Matrix squaring is therefore
`C∞` and has the expected Sylvester derivative.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
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

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev ContinuousScalar :=
  C(EffectiveQuotient period hPeriod, Real)

/-- `4 × 4` matrices whose entries lie in the canonical strong core. -/
abbrev StrongMatrix := Fin 4 → Fin 4 → StrongScalar period hPeriod

/-- Smooth coefficient matrices before passage to the strong closure. -/
abbrev SmoothMatrix :=
  Fin 4 → Fin 4 → SmoothQuotientField period hPeriod Real

/-- Matrices of continuous scalar representatives. -/
abbrev ContinuousCoefficientMatrix :=
  Fin 4 → Fin 4 → ContinuousScalar period hPeriod

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

/-- Algebraic form of the scalar extension in the standard subtype topology. -/
def scalarStrongProductBilinear :
    StrongScalar period hPeriod →ₗ[Real]
      StrongScalar period hPeriod →ₗ[Real] StrongScalar period hPeriod :=
  LinearMap.mk₂ Real
    (fun first second =>
      canonicalPhysicalScalarStrongH1C0CoreProduct
        period hPeriod first second)
    (by
      intro first second third
      exact congrArg (fun operator => operator third)
        ((canonicalPhysicalScalarStrongH1C0CoreProduct
          period hPeriod).map_add first second))
    (by
      intro scalar first second
      exact congrArg (fun operator => operator second)
        ((canonicalPhysicalScalarStrongH1C0CoreProduct
          period hPeriod).map_smul scalar first))
    (by
      intro first second third
      exact (canonicalPhysicalScalarStrongH1C0CoreProduct
        period hPeriod first).map_add second third)
    (by
      intro scalar first second
      exact (canonicalPhysicalScalarStrongH1C0CoreProduct
        period hPeriod first).map_smul scalar second)

/-- Scalar multiplication rebundled with the canonical public subtype
topology. Its values are definitionally the previously constructed extension. -/
def scalarStrongProduct :
    StrongScalar period hPeriod →L[Real]
      StrongScalar period hPeriod →L[Real] StrongScalar period hPeriod :=
  LinearMap.mkContinuous₂
    (scalarStrongProductBilinear period hPeriod)
    (smoothStrongH1C0ProductBoundConstant period hPeriod)
    (canonicalPhysicalScalarStrongH1C0CoreProduct_norm_le period hPeriod)

@[simp]
theorem scalarStrongProduct_apply
    (first second : StrongScalar period hPeriod) :
    scalarStrongProduct period hPeriod first second =
      canonicalPhysicalScalarStrongH1C0CoreProduct
        period hPeriod first second :=
  rfl

/-- The scalar extension has the expected pointwise continuous representative
on arbitrary elements of the strong closure. -/
theorem scalarStrongProduct_toContinuous
    (first second : StrongScalar period hPeriod) :
    canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
        (scalarStrongProduct period hPeriod first second) =
      canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod first *
        canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod second := by
  let product := scalarStrongProduct period hPeriod
  let projection :=
    canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
  have hSmoothLeft
      (smooth : SmoothQuotientField period hPeriod Real)
      (field : StrongScalar period hPeriod) :
      projection (product
          (smoothToCanonicalPhysicalScalarStrongH1C0Core
            period hPeriod smooth) field) =
        projection
            (smoothToCanonicalPhysicalScalarStrongH1C0Core
              period hPeriod smooth) * projection field := by
    refine DenseRange.induction_on
      (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
        period hPeriod) field
      (isClosed_eq
        (projection.comp
          (product
            (smoothToCanonicalPhysicalScalarStrongH1C0Core
              period hPeriod smooth))).continuous
        (((ContinuousLinearMap.mul Real (ContinuousScalar period hPeriod))
          (projection
            (smoothToCanonicalPhysicalScalarStrongH1C0Core
              period hPeriod smooth))).comp projection).continuous) ?_
    intro other
    dsimp only [projection, product]
    simp only [scalarStrongProduct_apply,
      canonicalPhysicalScalarStrongH1C0CoreProduct_smooth,
      smoothStrongH1C0CoreProduct,
      strongH1C0CoreToContinuous_smooth]
    apply ContinuousMap.ext
    intro point
    rfl
  refine DenseRange.induction_on
    (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
      period hPeriod) first
    (isClosed_eq
      (projection.comp (product.flip second)).continuous
      (((ContinuousLinearMap.mul Real
          (ContinuousScalar period hPeriod)).flip
        (projection second)).comp projection).continuous) ?_
  intro smooth
  exact hSmoothLeft smooth second

/-- Generic algebraic `4 × 4` multiplication induced by a bilinear scalar
product. Keeping this helper generic avoids unfolding the analytic core in the
finite linearity proof. -/
private def finFourMatrixProductBilinear
    {Scalar : Type*} [AddCommMonoid Scalar] [Module Real Scalar]
    (product : Scalar →ₗ[Real] Scalar →ₗ[Real] Scalar) :
    (Fin 4 → Fin 4 → Scalar) →ₗ[Real]
      (Fin 4 → Fin 4 → Scalar) →ₗ[Real]
        (Fin 4 → Fin 4 → Scalar) :=
  LinearMap.mk₂ Real
    (fun first second row column => ∑ middle : Fin 4,
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

/-- Algebraic finite matrix product on the strong scalar core. -/
def strongMatrixProductBilinear :
    StrongMatrix period hPeriod →ₗ[Real]
      StrongMatrix period hPeriod →ₗ[Real] StrongMatrix period hPeriod :=
  finFourMatrixProductBilinear
    (scalarStrongProductBilinear period hPeriod)

/-- Ordinary finite matrix multiplication on strong coefficient matrices. -/
def strongMatrixProduct :
    StrongMatrix period hPeriod →L[Real]
      StrongMatrix period hPeriod →L[Real] StrongMatrix period hPeriod :=
  LinearMap.mkContinuous₂
    (𝕜 := Real)
    (E := StrongMatrix period hPeriod)
    (F := StrongMatrix period hPeriod)
    (G := StrongMatrix period hPeriod)
    (strongMatrixProductBilinear period hPeriod)
    (4 * smoothStrongH1C0ProductBoundConstant period hPeriod)
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
        ‖∑ middle : Fin 4,
            scalarStrongProduct period hPeriod
              (first row middle) (second middle column)‖ ≤
            ∑ middle : Fin 4,
              ‖scalarStrongProduct period hPeriod
                (first row middle) (second middle column)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _middle : Fin 4, C * ‖first‖ * ‖second‖ := by
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
        _ = (4 * C) * ‖first‖ * ‖second‖ := by
          simp [C]
          ring)

@[simp]
theorem strongMatrixProduct_apply
    (first second : StrongMatrix period hPeriod)
    (row column : Fin 4) :
    strongMatrixProduct period hPeriod first second row column =
      ∑ middle : Fin 4,
        scalarStrongProduct period hPeriod
          (first row middle) (second middle column) :=
  by
    simp [strongMatrixProduct, strongMatrixProductBilinear,
      finFourMatrixProductBilinear, scalarStrongProductBilinear]

/-- Coordinatewise smooth lift into the strong matrix core. -/
def smoothMatrixToStrong :
    SmoothMatrix period hPeriod →ₗ[Real] StrongMatrix period hPeriod where
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

/-- Explicit smooth matrix product using the pre-existing scalar product. -/
def smoothMatrixProduct
    (first second : SmoothMatrix period hPeriod) :
    SmoothMatrix period hPeriod :=
  fun row column => ∑ middle : Fin 4,
    smoothScalarFieldMul period hPeriod
      (first row middle) (second middle column)

theorem strongMatrixProduct_smooth
    (first second : SmoothMatrix period hPeriod) :
    strongMatrixProduct period hPeriod
        (smoothMatrixToStrong period hPeriod first)
        (smoothMatrixToStrong period hPeriod second) =
      smoothMatrixToStrong period hPeriod
        (smoothMatrixProduct period hPeriod first second) := by
  funext row column
  rw [strongMatrixProduct_apply]
  change (∑ middle : Fin 4,
      canonicalPhysicalScalarStrongH1C0CoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (first row middle))
        (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
          (second middle column))) =
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
      (∑ middle : Fin 4, smoothScalarFieldMul period hPeriod
        (first row middle) (second middle column))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro middle _
  exact canonicalPhysicalScalarStrongH1C0CoreProduct_smooth
    period hPeriod (first row middle) (second middle column)

/-- Coordinatewise continuous representative of a strong matrix. -/
def strongMatrixToContinuous :
    StrongMatrix period hPeriod →L[Real]
      ContinuousCoefficientMatrix period hPeriod :=
  ContinuousLinearMap.piMap fun _ : Fin 4 =>
    ContinuousLinearMap.piMap fun _ : Fin 4 =>
      canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod

/-- Ordinary pointwise matrix product on continuous coefficient matrices. -/
def continuousCoefficientMatrixProduct
    (first second : ContinuousCoefficientMatrix period hPeriod) :
    ContinuousCoefficientMatrix period hPeriod :=
  fun row column => ∑ middle : Fin 4,
    first row middle * second middle column

theorem strongMatrixProduct_toContinuous
    (first second : StrongMatrix period hPeriod) :
    strongMatrixToContinuous period hPeriod
        (strongMatrixProduct period hPeriod first second) =
      continuousCoefficientMatrixProduct period hPeriod
        (strongMatrixToContinuous period hPeriod first)
        (strongMatrixToContinuous period hPeriod second) := by
  funext row column
  change canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
      (strongMatrixProduct period hPeriod first second row column) =
    ∑ middle : Fin 4,
      canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
          (first row middle) *
        canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
          (second middle column)
  rw [strongMatrixProduct_apply, map_sum]
  apply Finset.sum_congr rfl
  intro middle _
  exact scalarStrongProduct_toContinuous period hPeriod
    (first row middle) (second middle column)

/-- Squaring on the complete strong matrix core. -/
def strongMatrixSquare (matrix : StrongMatrix period hPeriod) :
    StrongMatrix period hPeriod :=
  strongMatrixProduct period hPeriod matrix matrix

/-- Sylvester linearization `variation ↦ root·variation + variation·root`. -/
def strongMatrixSylvester (root : StrongMatrix period hPeriod) :
    StrongMatrix period hPeriod →L[Real] StrongMatrix period hPeriod :=
  strongMatrixProduct period hPeriod root +
    ((strongMatrixProduct period hPeriod).flip root :
      StrongMatrix period hPeriod →L[Real] StrongMatrix period hPeriod)

theorem strongMatrixSquare_hasFDerivAt
    (root : StrongMatrix period hPeriod) :
    HasFDerivAt (strongMatrixSquare period hPeriod)
      (strongMatrixSylvester period hPeriod root) root := by
  have hDerivative :=
    ((strongMatrixProduct period hPeriod).hasFDerivAt
      (x := root)).clm_apply
        (hasFDerivAt_id (𝕜 := Real) root)
  exact hDerivative.congr_fderiv rfl

theorem strongMatrixSquare_contDiff :
    ContDiff Real ⊤ (strongMatrixSquare period hPeriod) :=
  (strongMatrixProduct period hPeriod).contDiff.clm_apply contDiff_id

theorem strongMatrixProduct_norm_le
    (first second : StrongMatrix period hPeriod) :
    ‖strongMatrixProduct period hPeriod first second‖ ≤
      ‖strongMatrixProduct period hPeriod‖ * ‖first‖ * ‖second‖ := by
  calc
    _ ≤ ‖strongMatrixProduct period hPeriod first‖ * ‖second‖ :=
      (strongMatrixProduct period hPeriod first).le_opNorm second
    _ ≤ (‖strongMatrixProduct period hPeriod‖ * ‖first‖) * ‖second‖ := by
      gcongr
      exact (strongMatrixProduct period hPeriod).le_opNorm first
    _ = _ := by ring

/-- Summary gate for strong matrix multiplication and squaring. -/
theorem canonical_physical_strong_h1_c0_matrix_product_gate :
    (∀ first second : StrongMatrix period hPeriod,
      strongMatrixToContinuous period hPeriod
          (strongMatrixProduct period hPeriod first second) =
        continuousCoefficientMatrixProduct period hPeriod
          (strongMatrixToContinuous period hPeriod first)
          (strongMatrixToContinuous period hPeriod second)) ∧
      ContDiff Real ⊤ (strongMatrixSquare period hPeriod) ∧
      (∀ root : StrongMatrix period hPeriod,
        HasFDerivAt (strongMatrixSquare period hPeriod)
          (strongMatrixSylvester period hPeriod root) root) := by
  exact ⟨strongMatrixProduct_toContinuous period hPeriod,
    strongMatrixSquare_contDiff period hPeriod,
    strongMatrixSquare_hasFDerivAt period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
end JanusFormal
