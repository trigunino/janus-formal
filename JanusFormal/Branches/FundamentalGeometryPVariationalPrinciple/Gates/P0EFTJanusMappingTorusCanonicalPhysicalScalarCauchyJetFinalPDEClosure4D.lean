import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetReducedPDEClosure4D

/-!
# Final reduced PDE closure for the explicit physical Cauchy jet

The profile moments are theorems, and the product-coordinate Euler residual is
canonically the pullback of the global physical residual.  Hence the complete
explicit-Cauchy boundary closure needs only:

* the compatibility/divergence/tubular geometric data;
* the Gårding energy estimate;
* the higher normal regularity estimate;
* one product integral bound for the canonical Euler residual.

All remaining extension norms, completed trace surjectivity and minimal-core
density are derived.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetFinalPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetReducedPDEClosure4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Minimal explicit-Cauchy PDE input. -/
structure CanonicalPhysicalScalarCauchyJetFinalPDEData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
    period hPeriod massSquared ValueCore NormalCore
  gardingEnergy : geometric.greenCore.EnergyGardingData period hPeriod
  normalRegularity : geometric.greenCore.NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  eulerEstimate : (geometric.toCauchyJetGeometricData period hPeriod).CauchyJetEulerProductEstimateData
    period hPeriod
    ((geometric.toCauchyJetGeometricData period hPeriod)
      |>.canonicalEulerProductRealization period hPeriod)

namespace CanonicalPhysicalScalarCauchyJetFinalPDEData

/-- Conversion to the profile- and realization-free reduced package. -/
def toReducedPDEData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (finalData : CanonicalPhysicalScalarCauchyJetFinalPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarCauchyJetReducedPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  geometric := finalData.geometric
  gardingEnergy := finalData.gardingEnergy
  normalRegularity := finalData.normalRegularity
  eulerRealization :=
    (finalData.geometric.toCauchyJetGeometricData period hPeriod)
      |>.canonicalEulerProductRealization period hPeriod
  eulerEstimate := finalData.eulerEstimate

/-- Genuine completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (finalData : CanonicalPhysicalScalarCauchyJetFinalPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (finalData.toReducedPDEData period hPeriod).triple period hPeriod

/-- Complete physical boundary input. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (finalData : CanonicalPhysicalScalarCauchyJetFinalPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (finalData.toReducedPDEData period hPeriod).completedInputs period hPeriod

/-- Bounded completed Cauchy extension. -/
def completedExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (finalData : CanonicalPhysicalScalarCauchyJetFinalPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (finalData.toReducedPDEData period hPeriod).completedExtension period hPeriod

/-- The sole extension-specific inequality in its final explicit form. -/
theorem euler_product_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (finalData : CanonicalPhysicalScalarCauchyJetFinalPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (data : ValueCore × NormalCore) :
    (∫ parameter,
      ((finalData.geometric.toCauchyJetGeometricData period hPeriod)
        |>.canonicalEulerProductResidual period hPeriod data parameter) ^ 2
      ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
        period) ≤
      finalData.eulerEstimate.constant ^ 2 *
        ‖(finalData.geometric.toCauchyJetGeometricData period hPeriod)
          |>.boundaryCoreEmbedding period hPeriod data‖ ^ 2 :=
  finalData.eulerEstimate.product_bound_sq data

/-- Final reduced physical boundary certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (finalData : CanonicalPhysicalScalarCauchyJetFinalPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    (finalData.geometric.greenCore period hPeriod).MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (finalData.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          (finalData.geometric.greenCore period hPeriod).core
          ((finalData.completedInputs period hPeriod).traceBound period hPeriod
            (finalData.geometric.greenCore period hPeriod))) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            (finalData.geometric.greenCore period hPeriod).core
            ((finalData.completedInputs period hPeriod).traceBound period hPeriod
              (finalData.geometric.greenCore period hPeriod))
            (finalData.completedExtension period hPeriod boundary) = boundary) :=
  (finalData.toReducedPDEData period hPeriod).certificate period hPeriod

end CanonicalPhysicalScalarCauchyJetFinalPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetFinalPDEClosure4D
end JanusFormal
