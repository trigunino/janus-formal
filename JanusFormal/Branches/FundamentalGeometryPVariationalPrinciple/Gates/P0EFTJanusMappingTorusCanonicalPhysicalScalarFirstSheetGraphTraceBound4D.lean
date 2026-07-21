import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D

/-!
# Physical paired graph-trace estimate from ellipticity and normal control

The first-sheet value trace has the same norm as the canonical physical throat
trace.  Hence the latitude coarea theorem bounds it by the physical graph-H1
norm.  A graph elliptic estimate then promotes this to the Euler graph norm.

The normal component requires its own graph estimate.  Combining the two bounds
with the product sup norm gives the exact paired Cauchy-trace estimate required
by the completed-graph construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGraphTraceBound4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

/-- First-sheet value L2 norm squared is the canonical latitude integral. -/
theorem smoothCanonicalPhysicalScalarFirstSheetValueL2_norm_sq_eq_latitudeIntegral
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field‖ ^ 2 =
      ∫ base : CanonicalLatitudeBase,
        canonicalLatitudeValue period hPeriod field base 0 ^ 2
        ∂canonicalLatitudeBaseMeasure period := by
  rw [← real_inner_self_eq_norm_sq,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [smoothCanonicalPhysicalScalarFirstSheetValueL2_ae
      period hPeriod field]
    with base hValue
  rw [hValue]
  simp [canonicalPhysicalScalarFirstSheetValue]

/-- The first-sheet value trace and the one-sided physical throat trace have the
same norm on smooth fields. -/
theorem smoothCanonicalPhysicalScalarFirstSheetValueL2_norm_eq_throatTrace
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field‖ =
      ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ := by
  have hFirst :=
    smoothCanonicalPhysicalScalarFirstSheetValueL2_norm_sq_eq_latitudeIntegral
      period hPeriod field
  have hThroat := smoothCanonicalPhysicalTrace_norm_sq_eq_latitudeIntegral
    period hPeriod field
  have hSquares :
      ‖smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field‖ ^ 2 =
        ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 := by
    rw [hFirst, hThroat]
  nlinarith [norm_nonneg
      (smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field),
    norm_nonneg (smoothCanonicalPhysicalTraceL2 period hPeriod field)]

/-- Elliptic estimate comparing the physical graph-H1 norm with the Euler graph
norm. -/
structure CanonicalPhysicalScalarGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : SmoothQuotientField period hPeriod Real,
    ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ≤
      constant * ‖canonicalScalarSmoothToOperatorGraphLinearMap
        green.system field‖

/-- Direct graph estimate for the first-sheet normal trace. -/
structure CanonicalPhysicalScalarNormalGraphEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : SmoothQuotientField period hPeriod Real,
    ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2
        period hPeriod field‖ ≤
      constant * ‖canonicalScalarSmoothToOperatorGraphLinearMap
        green.system field‖

/-- Value trace estimate in Euler graph norm. -/
theorem firstSheetValue_norm_le_graph
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : CanonicalPhysicalScalarGraphEllipticEstimate
      period hPeriod green)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field‖ ≤
      (canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
        elliptic.constant) *
      ‖canonicalScalarSmoothToOperatorGraphLinearMap green.system field‖ := by
  have hTrace := canonicalPhysicalScalarH1TraceOfCoarea_norm_le
    period hPeriod coarea
    (smoothToCanonicalPhysicalScalarH1 period hPeriod field)
  rw [canonicalPhysicalScalarH1TraceOfCoarea_agrees_on_smooth]
    at hTrace
  rw [smoothCanonicalPhysicalScalarFirstSheetValueL2_norm_eq_throatTrace]
  calc
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ≤
        canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
          ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ := hTrace
    _ ≤ canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
        (elliptic.constant *
          ‖canonicalScalarSmoothToOperatorGraphLinearMap green.system field‖) :=
      mul_le_mul_of_nonneg_left (elliptic.bound field)
        (by
          unfold canonicalPhysicalScalarH1TraceCoareaConstant
          exact mul_nonneg
            (canonicalNormalFrameReconstructionBound
              period hPeriod).nonnegative
            (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Explicit paired graph-bound constant. -/
def canonicalPhysicalScalarPairedGraphTraceConstant
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : CanonicalPhysicalScalarGraphEllipticEstimate
      period hPeriod green)
    (normal : CanonicalPhysicalScalarNormalGraphEstimate
      period hPeriod green) : Real :=
  max
    (canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
      elliptic.constant)
    normal.constant

/-- The paired graph-bound constant is nonnegative. -/
theorem canonicalPhysicalScalarPairedGraphTraceConstant_nonnegative
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : CanonicalPhysicalScalarGraphEllipticEstimate
      period hPeriod green)
    (normal : CanonicalPhysicalScalarNormalGraphEstimate
      period hPeriod green) :
    0 ≤ canonicalPhysicalScalarPairedGraphTraceConstant
      period hPeriod green coarea elliptic normal := by
  unfold canonicalPhysicalScalarPairedGraphTraceConstant
  exact le_trans normal.nonnegative (le_max_right _ _)

/-- Exact paired Cauchy-trace estimate in Euler graph norm. -/
theorem firstSheetCauchyTrace_norm_le_graph
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : CanonicalPhysicalScalarGraphEllipticEstimate
      period hPeriod green)
    (normal : CanonicalPhysicalScalarNormalGraphEstimate
      period hPeriod green)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖green.system.boundaryTrace field‖ ≤
      canonicalPhysicalScalarPairedGraphTraceConstant
          period hPeriod green coarea elliptic normal *
        ‖canonicalScalarSmoothToOperatorGraphLinearMap green.system field‖ := by
  let graphNorm :=
    ‖canonicalScalarSmoothToOperatorGraphLinearMap green.system field‖
  have hValue := firstSheetValue_norm_le_graph
    period hPeriod green coarea elliptic field
  have hNormal := normal.bound field
  change max
      ‖smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field‖
      ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field‖ ≤ _
  apply max_le
  · exact hValue.trans
      (mul_le_mul_of_nonneg_right
        (le_max_left
          (canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
            elliptic.constant) normal.constant)
        (norm_nonneg _))
  · exact hNormal.trans
      (mul_le_mul_of_nonneg_right
        (le_max_right
          (canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
            elliptic.constant) normal.constant)
        (norm_nonneg _))

/-- Generic graph-bound package required by the completed physical Green system. -/
def canonicalPhysicalScalarFirstSheetBoundaryGraphBound
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : CanonicalPhysicalScalarGraphEllipticEstimate
      period hPeriod green)
    (normal : CanonicalPhysicalScalarNormalGraphEstimate
      period hPeriod green) :
    HasCanonicalScalarHilbertBoundaryGraphBound green.system where
  constant := canonicalPhysicalScalarPairedGraphTraceConstant
    period hPeriod green coarea elliptic normal
  nonnegative := canonicalPhysicalScalarPairedGraphTraceConstant_nonnegative
    period hPeriod green coarea elliptic normal
  bound := firstSheetCauchyTrace_norm_le_graph
    period hPeriod green coarea elliptic normal

/-- Paired graph-trace closure certificate. -/
theorem canonicalPhysicalScalarFirstSheetGraphTraceBound_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : CanonicalPhysicalScalarGraphEllipticEstimate
      period hPeriod green)
    (normal : CanonicalPhysicalScalarNormalGraphEstimate
      period hPeriod green) :
    ∃ bound : HasCanonicalScalarHilbertBoundaryGraphBound green.system,
      ∀ field : SmoothQuotientField period hPeriod Real,
        ‖green.system.boundaryTrace field‖ ≤
          bound.constant *
            ‖canonicalScalarSmoothToOperatorGraphLinearMap green.system field‖ :=
  ⟨canonicalPhysicalScalarFirstSheetBoundaryGraphBound
      period hPeriod green coarea elliptic normal,
    firstSheetCauchyTrace_norm_le_graph
      period hPeriod green coarea elliptic normal⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGraphTraceBound4D
end JanusFormal
