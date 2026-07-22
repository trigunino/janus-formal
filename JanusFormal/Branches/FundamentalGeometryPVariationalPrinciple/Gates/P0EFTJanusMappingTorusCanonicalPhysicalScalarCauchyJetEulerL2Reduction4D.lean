import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetBulkL2Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D

/-!
# Reduction of the Cauchy-jet Euler estimate to product coordinates

The remaining graph component is the physical bulk `L²` norm of the Euler
residual of the explicit Cauchy extension.  In product coarea coordinates this
residual is a scalar function assembled from:

* the first and second fixed profile derivatives;
* tangential derivatives of the boundary value and normal data;
* the local physical coefficients of the wave operator.

This file separates the two tasks.  A realization datum identifies the squared
operator norm with the product integral of a local residual.  A product estimate
then gives the squared Euler component consumed by the graph-bound closure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetSquaredGraphBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetBulkL2Reduction4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Product-coordinate realization of the Euler residual of the explicit
Cauchy extension. -/
structure CauchyJetEulerProductRealizationData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) where
  residual : ValueCore × NormalCore →
    CanonicalLatitudeCauchyJetProductParameter → Real
  operator_norm_sq_eq : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 =
      ∫ parameter,
        residual data parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period

/-- Squared product estimate for a realized local Euler residual. -/
structure CauchyJetEulerProductEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod) where
  constant : Real
  nonnegative : 0 ≤ constant
  product_bound_sq : ∀ data : ValueCore × NormalCore,
    (∫ parameter,
      realization.residual data parameter ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
        constant ^ 2 * ‖geometric.boundaryCoreEmbedding data‖ ^ 2

namespace CauchyJetEulerProductEstimateData

/-- Physical squared Euler estimate. -/
theorem operator_bound_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (estimate : geometric.CauchyJetEulerProductEstimateData
      period hPeriod realization)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 ≤
      estimate.constant ^ 2 * ‖geometric.boundaryCoreEmbedding data‖ ^ 2 := by
  rw [realization.operator_norm_sq_eq]
  exact estimate.product_bound_sq data

/-- Combine independently proved bulk and Euler product estimates. -/
def combine
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (estimate : geometric.CauchyJetEulerProductEstimateData
      period hPeriod realization)
    (bulk : geometric.CauchyJetProductL2EstimateData period hPeriod) :
    geometric.CauchyJetSquaredComponentGraphEstimateData period hPeriod :=
  bulk.toSquaredComponentGraphEstimateData
    estimate.constant estimate.nonnegative estimate.operator_bound_sq

/-- Euler-product reduction certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (estimate : geometric.CauchyJetEulerProductEstimateData
      period hPeriod realization) :
    (∀ data : ValueCore × NormalCore,
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 =
        ∫ parameter,
          realization.residual data parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period) ∧
      (∀ data : ValueCore × NormalCore,
        ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 ≤
          estimate.constant ^ 2 * ‖geometric.boundaryCoreEmbedding data‖ ^ 2) :=
  ⟨realization.operator_norm_sq_eq,
    estimate.operator_bound_sq⟩

end CauchyJetEulerProductEstimateData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D
end JanusFormal
