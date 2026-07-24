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
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

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
    ‖(geometric.greenCore period hPeriod).core.inclusion
        (geometric.extension period hPeriod data)‖ ^ 2 ≤
      inclusionConstant ^ 2 *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2
  operator_bound_sq : ∀ data : ValueCore × NormalCore,
    ‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ ^ 2 ≤
      operatorConstant ^ 2 *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2

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
    ‖(geometric.greenCore period hPeriod).core.inclusion
        (geometric.extension period hPeriod data)‖ ≤
      estimate.inclusionConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ := by
  have hSquare := estimate.inclusion_bound_sq data
  have hLeft : 0 ≤
      ‖(geometric.greenCore period hPeriod).core.inclusion
        (geometric.extension period hPeriod data)‖ :=
    norm_nonneg _
  have hRight : 0 ≤
      estimate.inclusionConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ :=
    mul_nonneg estimate.inclusionConstant_nonnegative (norm_nonneg _)
  nlinarith [sq_nonneg
    (‖(geometric.greenCore period hPeriod).core.inclusion
        (geometric.extension period hPeriod data)‖ -
      estimate.inclusionConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖)]

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
    ‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ ≤
      estimate.operatorConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ := by
  have hSquare := estimate.operator_bound_sq data
  have hLeft : 0 ≤
      ‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ :=
    norm_nonneg _
  have hRight : 0 ≤
      estimate.operatorConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ :=
    mul_nonneg estimate.operatorConstant_nonnegative (norm_nonneg _)
  nlinarith [sq_nonneg
    (‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ -
      estimate.operatorConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖)]

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
  inclusion_bound := estimate.inclusion_bound period hPeriod
  operator_bound := estimate.operator_bound period hPeriod

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
        (geometric.greenCore period hPeriod).core
        (geometric.extension period hPeriod data)‖ ≤
      (Real.sqrt 2 * max estimate.inclusionConstant estimate.operatorConstant) *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ := by
  exact estimate.toComponentGraphEstimateData period hPeriod
    |>.graph_bound period hPeriod data

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
      ‖(geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data)‖ ≤
        estimate.inclusionConstant *
          ‖geometric.boundaryCoreEmbedding period hPeriod data‖) ∧
      (∀ data : ValueCore × NormalCore,
        ‖(geometric.greenCore period hPeriod).core.operator
            (geometric.extension period hPeriod data)‖ ≤
          estimate.operatorConstant *
            ‖geometric.boundaryCoreEmbedding period hPeriod data‖) ∧
      (∀ data : ValueCore × NormalCore,
        ‖P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreToGraph
            (geometric.greenCore period hPeriod).core
            (geometric.extension period hPeriod data)‖ ≤
          (Real.sqrt 2 * max estimate.inclusionConstant estimate.operatorConstant) *
            ‖geometric.boundaryCoreEmbedding period hPeriod data‖) :=
  ⟨estimate.inclusion_bound period hPeriod,
    estimate.operator_bound period hPeriod,
    estimate.graph_bound period hPeriod⟩

end CauchyJetSquaredComponentGraphEstimateData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
end JanusFormal
