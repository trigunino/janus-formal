import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

/-!
# Physical Euler L2 pairing and the global Green current

The geometric boundary half of Green's formula is already complete.  The only
remaining bulk comparison is that the antisymmetric L2 pairing of the concrete
Euler operator equals minus twice the canonical divergence measure.

Green--Stokes then turns this local-to-global bulk identity into the exact
oriented boundary current, and the first-sheet Hilbert trace turns that current
into twice the boundary symplectic form.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenBridge4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

/-- Exact remaining bulk integration-by-parts comparison for the concrete
physical Euler operator. -/
structure CanonicalPhysicalScalarBulkEulerDivergenceBridge
    (massSquared : Real) where
  operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
    period hPeriod massSquared
  pairing_eq_neg_two_divergence :
    ∀ first second : SmoothQuotientField period hPeriod Real,
      inner Real (operatorData.toBulkL2LinearMap first)
            (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
          inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
            (operatorData.toBulkL2LinearMap second) =
        -2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          first second Set.univ

namespace CanonicalPhysicalScalarBulkEulerDivergenceBridge

/-- The bulk L2 defect is the exact oriented global boundary current. -/
theorem pairing_eq_orientedBoundaryCurrent
    (bridge : CanonicalPhysicalScalarBulkEulerDivergenceBridge
      period hPeriod massSquared)
    (first second : SmoothQuotientField period hPeriod Real) :
    inner Real (bridge.operatorData.toBulkL2LinearMap first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (bridge.operatorData.toBulkL2LinearMap second) =
      cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod first second := by
  have hStokes := cutBulkGlobalMeasuredGreenStokes
    period hPeriod massSquared first second
  rw [bridge.pairing_eq_neg_two_divergence]
  linarith

/-- The bulk L2 defect is twice the first-sheet Hilbert symplectic pairing. -/
theorem pairing_eq_firstSheetHilbertSymplectic
    (bridge : CanonicalPhysicalScalarBulkEulerDivergenceBridge
      period hPeriod massSquared)
    (first second : SmoothQuotientField period hPeriod Real) :
    inner Real (bridge.operatorData.toBulkL2LinearMap first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (bridge.operatorData.toBulkL2LinearMap second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod first)
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod second) := by
  rw [bridge.pairing_eq_orientedBoundaryCurrent]
  exact (canonicalPhysicalScalarFirstSheetHilbertTrace_certificate
    period hPeriod first second).2

/-- Install the corrected physical Green-core data once density of the smooth
Cauchy trace is available. -/
def toGreenCoreData
    (bridge : CanonicalPhysicalScalarBulkEulerDivergenceBridge
      period hPeriod massSquared)
    (boundaryDense : DenseRange
      (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod)) :
    CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared where
  operatorData := bridge.operatorData
  boundary_dense := boundaryDense
  bulk_green_stokes := bridge.pairing_eq_orientedBoundaryCurrent

/-- Bulk Euler/Green bridge certificate. -/
theorem certificate
    (bridge : CanonicalPhysicalScalarBulkEulerDivergenceBridge
      period hPeriod massSquared) :
    (∀ first second : SmoothQuotientField period hPeriod Real,
      inner Real (bridge.operatorData.toBulkL2LinearMap first)
            (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
          inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
            (bridge.operatorData.toBulkL2LinearMap second) =
        cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod first second) ∧
      (∀ first second : SmoothQuotientField period hPeriod Real,
        inner Real (bridge.operatorData.toBulkL2LinearMap first)
              (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
            inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
              (bridge.operatorData.toBulkL2LinearMap second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
              period hPeriod first)
            (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
              period hPeriod second)) :=
  ⟨bridge.pairing_eq_orientedBoundaryCurrent,
    bridge.pairing_eq_firstSheetHilbertSymplectic⟩

end CanonicalPhysicalScalarBulkEulerDivergenceBridge

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenBridge4D
end JanusFormal
