import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenBridge4D

/-!
# Physical bulk Green bridge from the reduced Euler globalization data

Linearity of the physical scalar Euler residual is now a theorem.  Therefore the
operator input consists only of overlap compatibility and continuity of the
global residual.  Supplying the remaining bulk divergence pairing constructs
the complete Euler/Green bridge and hence the corrected physical Green core once
a smooth Cauchy extension establishes dense boundary range.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenGlobalization4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Reduced physical bulk Green input. -/
structure CanonicalPhysicalScalarBulkEulerGreenGlobalizationData
    (massSquared : Real) where
  globalization : CanonicalPhysicalScalarEulerGlobalizationData
    period hPeriod massSquared
  pairing_eq_neg_two_divergence :
    ∀ first second : SmoothQuotientField period hPeriod Real,
      inner Real (globalization.toBulkL2LinearMap first)
            (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
          inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
            (globalization.toBulkL2LinearMap second) =
        -2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          first second Set.univ

namespace CanonicalPhysicalScalarBulkEulerGreenGlobalizationData

/-- Conversion to the full Euler/divergence bridge. -/
def toBulkEulerDivergenceBridge
    (bridge : CanonicalPhysicalScalarBulkEulerGreenGlobalizationData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarBulkEulerDivergenceBridge
      period hPeriod massSquared where
  operatorData := bridge.globalization.toOperatorData
  pairing_eq_neg_two_divergence := bridge.pairing_eq_neg_two_divergence

/-- Exact oriented Green current from the reduced physical inputs. -/
theorem pairing_eq_orientedBoundaryCurrent
    (bridge : CanonicalPhysicalScalarBulkEulerGreenGlobalizationData
      period hPeriod massSquared)
    (first second : SmoothQuotientField period hPeriod Real) :
    inner Real (bridge.globalization.toBulkL2LinearMap first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (bridge.globalization.toBulkL2LinearMap second) =
      P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod first second :=
  bridge.toBulkEulerDivergenceBridge.pairing_eq_orientedBoundaryCurrent
    first second

/-- Build the corrected physical Green-core data from the reduced Euler inputs
and dense smooth Cauchy trace. -/
def toGreenCoreData
    (bridge : CanonicalPhysicalScalarBulkEulerGreenGlobalizationData
      period hPeriod massSquared)
    (boundaryDense : DenseRange
      (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
        period hPeriod)) :
    CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared where
  operatorData := bridge.globalization.toOperatorData
  boundary_dense := boundaryDense
  bulk_green_stokes := bridge.pairing_eq_orientedBoundaryCurrent

/-- Reduced bulk-Euler bridge certificate. -/
theorem certificate
    (bridge : CanonicalPhysicalScalarBulkEulerGreenGlobalizationData
      period hPeriod massSquared) :
    (∀ first second : SmoothQuotientField period hPeriod Real,
      inner Real (bridge.globalization.toBulkL2LinearMap first)
            (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
          inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
            (bridge.globalization.toBulkL2LinearMap second) =
        P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod first second) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.CanonicalPhysicalScalarEulerEquation
            period hPeriod massSquared field ↔
          bridge.globalization.toBulkL2LinearMap field = 0) :=
  ⟨bridge.pairing_eq_orientedBoundaryCurrent,
    bridge.globalization.eulerEquation_iff_operator_eq_zero⟩

end CanonicalPhysicalScalarBulkEulerGreenGlobalizationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenGlobalization4D
end JanusFormal
