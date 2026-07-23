import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D

/-!
# Canonical product realization of the Cauchy-jet Euler residual

The product residual is not an additional analytic datum.  It is the global
physical Euler residual of the explicit extension, pulled back by the
measure-preserving product coarea map.  The squared physical bulk `L²` norm of
the Euler image is therefore exactly the product integral of this pullback.

Only a quantitative estimate of this explicit scalar function remains.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Global Euler residual pulled back to product coarea coordinates. -/
def _root_.JanusFormal.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D.CanonicalPhysicalScalarCauchyJetGeometricData.canonicalEulerProductResidual
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  canonicalPhysicalScalarEulerGlobalResidual
    period hPeriod massSquared (geometric.extension period hPeriod data)
      (canonicalLatitudeCauchyJetProductPhysicalMap
        period hPeriod parameter)

/-- Squared Euler norm as a bulk integral. -/
theorem _root_.JanusFormal.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D.CanonicalPhysicalScalarCauchyJetGeometricData.operator_norm_sq_eq_bulk_residual_integral
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    ‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ ^ 2 =
      ∫ point,
        canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared
            (geometric.extension period hPeriod data) point ^ 2
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change ‖(geometric.operatorData period hPeriod).toBulkL2LinearMap
      (geometric.extension period hPeriod data)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [(geometric.operatorData period hPeriod).toBulkL2LinearMap_ae
      (geometric.extension period hPeriod data)] with point hPoint
  rw [hPoint]
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The bulk residual integral is exactly its product-coordinate pullback. -/
theorem _root_.JanusFormal.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D.CanonicalPhysicalScalarCauchyJetGeometricData.bulk_residual_integral_eq_product
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    (∫ point,
      canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared
          (geometric.extension period hPeriod data) point ^ 2
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ parameter,
        geometric.canonicalEulerProductResidual period hPeriod data parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period := by
  let map := canonicalLatitudeCauchyJetProductPhysicalMap period hPeriod
  let sourceMeasure := canonicalLatitudeCauchyJetProductMeasure period
  let targetMeasure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let residual := canonicalPhysicalScalarEulerGlobalResidual
    period hPeriod massSquared (geometric.extension period hPeriod data)
  have hMeasure := canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving
    period hPeriod
  have hIntegrable : Integrable (fun point => residual point ^ 2)
      targetMeasure :=
    ((geometric.operatorData period hPeriod).residual_memLp
      (geometric.extension period hPeriod data)).integrable_sq
  have hStronglyMeasurable : AEStronglyMeasurable
      (fun point => residual point ^ 2) (Measure.map map sourceMeasure) := by
    rw [hMeasure.map_eq]
    exact hIntegrable.aestronglyMeasurable
  have hMapIntegral := MeasureTheory.integral_map
    hMeasure.measurable.aemeasurable hStronglyMeasurable
  rw [hMeasure.map_eq] at hMapIntegral
  simpa [P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D.CanonicalPhysicalScalarCauchyJetGeometricData.canonicalEulerProductResidual,
    residual, map, sourceMeasure,
    targetMeasure] using hMapIntegral

/-- Exact product-coordinate identity for the squared Euler norm. -/
theorem _root_.JanusFormal.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D.CanonicalPhysicalScalarCauchyJetGeometricData.operator_norm_sq_eq_product_residual_integral
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    ‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ ^ 2 =
      ∫ parameter,
        geometric.canonicalEulerProductResidual period hPeriod data parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period := by
  rw [geometric.operator_norm_sq_eq_bulk_residual_integral period hPeriod,
    geometric.bulk_residual_integral_eq_product period hPeriod]

/-- Canonical Euler product realization package. -/
def _root_.JanusFormal.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D.CanonicalPhysicalScalarCauchyJetGeometricData.canonicalEulerProductRealization
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
  (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    geometric.CauchyJetEulerProductRealizationData period hPeriod where
  residual := geometric.canonicalEulerProductResidual period hPeriod
  operator_norm_sq_eq :=
    geometric.operator_norm_sq_eq_product_residual_integral period hPeriod

/-- Canonical Euler-product realization certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    ∀ data : ValueCore × NormalCore,
      ‖(geometric.greenCore period hPeriod).core.operator
          (geometric.extension period hPeriod data)‖ ^ 2 =
        ∫ parameter,
          geometric.canonicalEulerProductResidual period hPeriod data parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period :=
  geometric.operator_norm_sq_eq_product_residual_integral period hPeriod

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
end JanusFormal
