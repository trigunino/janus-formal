import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D

/-!
# Geometric bridge to the physical scalar Hilbert Green identity

The global cut-bulk work already constructs the exact oriented scalar Green
boundary form.  The physical Hilbert Green system needs the same quantity in two
analytic descriptions:

1. as the antisymmetric defect of the bulk scalar operator pairing;
2. as twice the Hilbert symplectic pairing of value and normal traces.

This file isolates those two comparison theorems.  Once supplied for a concrete
Euler operator and normal trace, the abstract physical Hilbert Green system is
constructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev SmoothDomain := SmoothQuotientField period hPeriod Real
private abbrev BulkL2 := CanonicalPhysicalBulkL2 period hPeriod
private abbrev ThroatL2 := CanonicalPhysicalThroatL2 period hPeriod

/-- Concrete analytic comparison data between the geometric global boundary
current and the physical bulk/trace Hilbert pairings. -/
structure CanonicalPhysicalScalarGreenIdentityBridgeData where
  operator : SmoothDomain period hPeriod →ₗ[Real] BulkL2 period hPeriod
  normalTrace : SmoothDomain period hPeriod →ₗ[Real] ThroatL2 period hPeriod
  pairedTrace_surjective : Function.Surjective
    (fun field : SmoothDomain period hPeriod =>
      (smoothCanonicalPhysicalTraceL2 period hPeriod field,
        normalTrace field))
  bulk_defect_eq_global_boundary : ∀ first second : SmoothDomain period hPeriod,
    inner Real (operator first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (operator second) =
      cutBulkGlobalScalarBoundaryGreenForm period hPeriod first second
  trace_pairing_eq_global_boundary : ∀ first second : SmoothDomain period hPeriod,
    2 * canonicalScalarHilbertBoundarySymplecticForm
        (smoothCanonicalPhysicalTraceL2 period hPeriod first,
          normalTrace first)
        (smoothCanonicalPhysicalTraceL2 period hPeriod second,
          normalTrace second) =
      cutBulkGlobalScalarBoundaryGreenForm period hPeriod first second

/-- The two comparison laws imply the exact Hilbert Green identity. -/
theorem CanonicalPhysicalScalarGreenIdentityBridgeData.green_identity
    (bridge : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod)
    (first second : SmoothDomain period hPeriod) :
    inner Real (bridge.operator first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (bridge.operator second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (smoothCanonicalPhysicalTraceL2 period hPeriod first,
          bridge.normalTrace first)
        (smoothCanonicalPhysicalTraceL2 period hPeriod second,
          bridge.normalTrace second) := by
  rw [bridge.bulk_defect_eq_global_boundary,
    ← bridge.trace_pairing_eq_global_boundary]

/-- Construction of the physical smooth Hilbert Green data from the geometric
bridge. -/
def CanonicalPhysicalScalarGreenIdentityBridgeData.toSmoothGreenData
    (bridge : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod) :
    CanonicalPhysicalSmoothScalarGreenData period hPeriod where
  operator := bridge.operator
  normalTrace := bridge.normalTrace
  boundary_surjective := bridge.pairedTrace_surjective
  green_identity := bridge.green_identity period hPeriod

/-- The paired trace of the resulting smooth Green data is the supplied paired
trace. -/
theorem CanonicalPhysicalScalarGreenIdentityBridgeData.pairedTrace_apply
    (bridge : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod)
    (field : SmoothDomain period hPeriod) :
    canonicalPhysicalSmoothPairedBoundaryTrace period hPeriod
        (bridge.toSmoothGreenData period hPeriod) field =
      (smoothCanonicalPhysicalTraceL2 period hPeriod field,
        bridge.normalTrace field) :=
  rfl

/-- The abstract physical Hilbert Green system generated by the bridge. -/
def CanonicalPhysicalScalarGreenIdentityBridgeData.toHilbertGreenSystem
    (bridge : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod) :=
  canonicalPhysicalScalarHilbertGreenSystem period hPeriod
    (bridge.toSmoothGreenData period hPeriod)

/-- Geometric Green bridge certificate. -/
theorem canonicalPhysicalScalarGreenIdentityBridge_certificate
    (bridge : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod) :
    Function.Surjective
        (canonicalPhysicalSmoothPairedBoundaryTrace period hPeriod
          (bridge.toSmoothGreenData period hPeriod)) ∧
      (∀ first second : SmoothDomain period hPeriod,
        inner Real (bridge.operator first)
              (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
            inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
              (bridge.operator second) =
          cutBulkGlobalScalarBoundaryGreenForm period hPeriod first second) ∧
      (∀ first second : SmoothDomain period hPeriod,
        inner Real (bridge.operator first)
              (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
            inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
              (bridge.operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            (smoothCanonicalPhysicalTraceL2 period hPeriod first,
              bridge.normalTrace first)
            (smoothCanonicalPhysicalTraceL2 period hPeriod second,
              bridge.normalTrace second)) :=
  ⟨bridge.pairedTrace_surjective,
    bridge.bulk_defect_eq_global_boundary,
    bridge.green_identity period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D
end JanusFormal
