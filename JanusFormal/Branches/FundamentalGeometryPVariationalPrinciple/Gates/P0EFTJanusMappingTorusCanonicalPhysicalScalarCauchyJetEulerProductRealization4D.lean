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
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Global Euler residual pulled back to product coarea coordinates. -/
def canonicalEulerProductResidual
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  canonicalPhysicalScalarEulerGlobalResidual
    period hPeriod massSquared (geometric.extension data)
      (canonicalLatitudeCauchyJetProductPhysicalMap
        period hPeriod parameter)

/-- Squared Euler norm as a bulk integral. -/
theorem operator_norm_sq_eq_bulk_residual_integral
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 =
      ∫ point,
        canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared (geometric.extension data) point ^ 2
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change ‖geometric.operatorData.toBulkL2LinearMap
      (geometric.extension data)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [geometric.operatorData.toBulkL2LinearMap_ae
      (geometric.extension data)] with point hPoint
  rw [hPoint]
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The bulk residual integral is exactly its product-coordinate pullback. -/
theorem bulk_residual_integral_eq_product
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    (∫ point,
      canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared (geometric.extension data) point ^ 2
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ parameter,
        geometric.canonicalEulerProductResidual data parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period := by
  let residual := canonicalPhysicalScalarEulerGlobalResidual
    period hPeriod massSquared (geometric.extension data)
  have hIntegrable : Integrable (fun point => residual point ^ 2)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    (geometric.operatorData.residual_memLp
      (geometric.extension data)).integrable_sq
  have hMap :=
    (canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving
      period hPeriod).integral_comp hIntegrable
  simpa [canonicalEulerProductResidual, residual] using hMap.symm

/-- Exact product-coordinate identity for the squared Euler norm. -/
theorem operator_norm_sq_eq_product_residual_integral
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 =
      ∫ parameter,
        geometric.canonicalEulerProductResidual data parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period := by
  rw [geometric.operator_norm_sq_eq_bulk_residual_integral,
    geometric.bulk_residual_integral_eq_product]

/-- Canonical Euler product realization package. -/
def canonicalEulerProductRealization
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    geometric.CauchyJetEulerProductRealizationData period hPeriod where
  residual := geometric.canonicalEulerProductResidual
  operator_norm_sq_eq := geometric.operator_norm_sq_eq_product_residual_integral

/-- Canonical Euler-product realization certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    ∀ data : ValueCore × NormalCore,
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 =
        ∫ parameter,
          geometric.canonicalEulerProductResidual data parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period :=
  geometric.operator_norm_sq_eq_product_residual_integral

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
end JanusFormal
