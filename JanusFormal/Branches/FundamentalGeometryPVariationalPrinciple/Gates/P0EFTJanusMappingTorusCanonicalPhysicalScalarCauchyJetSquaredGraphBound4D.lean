import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D

/-!
# Squared component estimates for the explicit Cauchy jet

Energy and coarea arguments naturally produce squared inequalities.  This file
allows the explicit Cauchy extension to be controlled by

`||E(g,h)||² ≤ C₀² ||(g,h)||²`

and

`||A E(g,h)||² ≤ C₁² ||(g,h)||²`.

Nonnegativity of the two constants converts these inequalities to the linear
component bounds consumed by the completed Cauchy-extension theorem.  No
separate graph-norm estimate is required.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetSquaredGraphBound4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Squared bulk and Euler-residual estimates for the explicit extension. -/
structure CauchyJetSquaredComponentGraphEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) where
  inclusionConstant : Real
  inclusionConstant_nonnegative : 0 ≤ inclusionConstant
  operatorConstant : Real
  operatorConstant_nonnegative : 0 ≤ operatorConstant
  inclusion_bound_sq : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ^ 2 ≤
      inclusionConstant ^ 2 * ‖geometric.boundaryCoreEmbedding data‖ ^ 2
  operator_bound_sq : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ^ 2 ≤
      operatorConstant ^ 2 * ‖geometric.boundaryCoreEmbedding data‖ ^ 2

namespace CauchyJetSquaredComponentGraphEstimateData

/-- Linear bulk estimate obtained from the squared energy estimate. -/
theorem inclusion_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetSquaredComponentGraphEstimateData
      period hPeriod)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
      estimate.inclusionConstant * ‖geometric.boundaryCoreEmbedding data‖ := by
  have hSquare := estimate.inclusion_bound_sq data
  have hLeft : 0 ≤
      ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ :=
    norm_nonneg _
  have hRight : 0 ≤
      estimate.inclusionConstant * ‖geometric.boundaryCoreEmbedding data‖ :=
    mul_nonneg estimate.inclusionConstant_nonnegative (norm_nonneg _)
  nlinarith [sq_nonneg
    (‖geometric.greenCore.core.inclusion (geometric.extension data)‖ -
      estimate.inclusionConstant * ‖geometric.boundaryCoreEmbedding data‖)]

/-- Linear Euler-residual estimate obtained from the squared estimate. -/
theorem operator_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetSquaredComponentGraphEstimateData
      period hPeriod)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
      estimate.operatorConstant * ‖geometric.boundaryCoreEmbedding data‖ := by
  have hSquare := estimate.operator_bound_sq data
  have hLeft : 0 ≤
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ :=
    norm_nonneg _
  have hRight : 0 ≤
      estimate.operatorConstant * ‖geometric.boundaryCoreEmbedding data‖ :=
    mul_nonneg estimate.operatorConstant_nonnegative (norm_nonneg _)
  nlinarith [sq_nonneg
    (‖geometric.greenCore.core.operator (geometric.extension data)‖ -
      estimate.operatorConstant * ‖geometric.boundaryCoreEmbedding data‖)]

/-- Conversion to the linear component-estimate package. -/
def toComponentGraphEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetSquaredComponentGraphEstimateData
      period hPeriod) :
    geometric.CauchyJetComponentGraphEstimateData period hPeriod where
  inclusionConstant := estimate.inclusionConstant
  inclusionConstant_nonnegative := estimate.inclusionConstant_nonnegative
  operatorConstant := estimate.operatorConstant
  operatorConstant_nonnegative := estimate.operatorConstant_nonnegative
  inclusion_bound := estimate.inclusion_bound
  operator_bound := estimate.operator_bound

/-- Direct graph bound from the two squared estimates. -/
theorem graph_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetSquaredComponentGraphEstimateData
      period hPeriod)
    (data : ValueCore × NormalCore) :
    ‖P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreToGraph
        geometric.greenCore.core (geometric.extension data)‖ ≤
      max estimate.inclusionConstant estimate.operatorConstant *
        ‖geometric.boundaryCoreEmbedding data‖ :=
  estimate.toComponentGraphEstimateData.graph_bound data

/-- Squared-estimate certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetSquaredComponentGraphEstimateData
      period hPeriod) :
    (∀ data : ValueCore × NormalCore,
      ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
        estimate.inclusionConstant * ‖geometric.boundaryCoreEmbedding data‖) ∧
      (∀ data : ValueCore × NormalCore,
        ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
          estimate.operatorConstant * ‖geometric.boundaryCoreEmbedding data‖) ∧
      (∀ data : ValueCore × NormalCore,
        ‖P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreToGraph
            geometric.greenCore.core (geometric.extension data)‖ ≤
          max estimate.inclusionConstant estimate.operatorConstant *
            ‖geometric.boundaryCoreEmbedding data‖) :=
  ⟨estimate.inclusion_bound, estimate.operator_bound,
    estimate.graph_bound⟩

end CauchyJetSquaredComponentGraphEstimateData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetSquaredGraphBound4D
end JanusFormal
