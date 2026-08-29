import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedBoundary4D

/-!
# Explicit-Cauchy physical scalar boundary triple

The smooth Cauchy extension, its boundary-core density and the physical coarea
realization are now fixed.  The remaining extension estimates are stated in the
coordinates in which they are actually proved:

* a product integral estimate for the local Cauchy field;
* a product residual realization for the Euler operator;
* a product integral estimate for that residual.

These estimates combine automatically into the squared graph bound and hence a
surjective completed physical boundary triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyBoundary4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetBulkL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedBoundary4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period
private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Explicit-coordinate physical boundary inputs. -/
structure CanonicalPhysicalScalarExplicitCauchyBoundaryData
    (massSquared : Real) where
  green : CanonicalPhysicalScalarExplicitCauchyGreenCoreData
    period hPeriod massSquared
  garding : green.greenCore.SquaredGardingEstimate period hPeriod
  normalRegularity : green.greenCore.NormalRegularityData
    period hPeriod (Regularity := Regularity)
  bulkEstimate : green.toCauchyJetGeometricData.CauchyJetProductL2EstimateData
    period hPeriod
  eulerRealization :
    green.toCauchyJetGeometricData.CauchyJetEulerProductRealizationData
      period hPeriod
  eulerEstimate :
    green.toCauchyJetGeometricData.CauchyJetEulerProductEstimateData
      period hPeriod eulerRealization

namespace CanonicalPhysicalScalarExplicitCauchyBoundaryData

/-- Combined squared component estimate. -/
def extensionEstimate
    (boundaryData : CanonicalPhysicalScalarExplicitCauchyBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :=
  boundaryData.eulerEstimate.combine boundaryData.bulkEstimate

/-- Conversion to the canonical Cauchy-closed boundary package. -/
def toCanonicalCauchyClosedBoundaryData
    (boundaryData : CanonicalPhysicalScalarExplicitCauchyBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalCauchyClosedBoundaryData
      period hPeriod massSquared (Regularity := Regularity) where
  core := boundaryData.green.toCanonicalCauchyJetGreenCoreData
  garding := boundaryData.garding
  normalRegularity := boundaryData.normalRegularity
  extensionEstimate := boundaryData.extensionEstimate

/-- Correct completed physical boundary triple. -/
def triple
    (boundaryData : CanonicalPhysicalScalarExplicitCauchyBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :=
  boundaryData.toCanonicalCauchyClosedBoundaryData.triple

/-- Completed physical boundary inputs. -/
def completedInputs
    (boundaryData : CanonicalPhysicalScalarExplicitCauchyBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :=
  boundaryData.toCanonicalCauchyClosedBoundaryData.completedInputs

/-- Explicit-Cauchy boundary certificate. -/
theorem certificate
    (boundaryData : CanonicalPhysicalScalarExplicitCauchyBoundaryData
      period hPeriod massSquared (Regularity := Regularity)) :
    (∀ data : ValueCore period × NormalCore period,
      ‖boundaryData.green.greenCore.core.inclusion
          (boundaryData.green.extension data)‖ ^ 2 ≤
        boundaryData.bulkEstimate.constant ^ 2 *
          ‖boundaryData.green.toCauchyJetGeometricData.boundaryCoreEmbedding
            data‖ ^ 2) ∧
      (∀ data : ValueCore period × NormalCore period,
        ‖boundaryData.green.greenCore.core.operator
            (boundaryData.green.extension data)‖ ^ 2 ≤
          boundaryData.eulerEstimate.constant ^ 2 *
            ‖boundaryData.green.toCauchyJetGeometricData.boundaryCoreEmbedding
              data‖ ^ 2) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          boundaryData.green.greenCore.core
          boundaryData.toCanonicalCauchyClosedBoundaryData
            |>.toCauchyClosedBoundaryData.toCutoffClosedBoundaryData
            |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
            |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound) :=
  ⟨boundaryData.bulkEstimate.inclusion_bound_sq,
    boundaryData.eulerEstimate.operator_bound_sq,
    boundaryData.toCanonicalCauchyClosedBoundaryData
      |>.toCauchyClosedBoundaryData.extensionEstimate
      |>.completedBoundaryTrace_surjective
        (boundaryData.toCanonicalCauchyClosedBoundaryData
          |>.toCauchyClosedBoundaryData.toCutoffClosedBoundaryData
          |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
          |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound)⟩

end CanonicalPhysicalScalarExplicitCauchyBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyBoundary4D
end JanusFormal
