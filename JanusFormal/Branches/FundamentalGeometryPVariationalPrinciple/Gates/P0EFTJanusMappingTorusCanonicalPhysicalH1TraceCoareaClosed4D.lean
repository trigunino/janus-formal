import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D

/-!
# Unconditional physical scalar `H¹` trace

The generic trace construction in
`P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D` was parameterized
by one latitude coarea domination.  The preceding gate proves that domination,
so this file removes the final hypothesis and exports the completed physical
value trace together with its quantitative estimate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical latitude coarea proposition is now unconditional. -/
theorem canonicalPhysicalScalarLatitudeCoareaTheorem :
    CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod :=
  canonicalLatitudeMeasureToSphereCoareaDomination period hPeriod

/-- The explicit constant in the unconditional physical value-trace estimate. -/
def canonicalPhysicalScalarH1TraceConstant : Real :=
  canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

/-- Unconditional smooth physical value-trace bound. -/
def canonicalPhysicalScalarH1TraceBound :
    CanonicalPhysicalH1TraceBound period hPeriod :=
  canonicalPhysicalScalarH1TraceBoundOfCoarea period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

/-- Unconditional completed physical scalar `H¹` trace. -/
def canonicalPhysicalScalarH1Trace :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  canonicalPhysicalScalarH1TraceOfCoarea period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

/-- Agreement of the completed trace with the genuine smooth restriction. -/
theorem canonicalPhysicalScalarH1Trace_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarH1Trace period hPeriod
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field := by
  simpa [canonicalPhysicalScalarH1Trace] using
    canonicalPhysicalScalarH1TraceOfCoarea_agrees_on_smooth
      period hPeriod
      (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) field

/-- Quantitative norm bound for the unconditional completed trace. -/
theorem canonicalPhysicalScalarH1Trace_norm_le
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    ‖canonicalPhysicalScalarH1Trace period hPeriod field‖ ≤
      canonicalPhysicalScalarH1TraceConstant period hPeriod * ‖field‖ := by
  simpa [canonicalPhysicalScalarH1Trace,
    canonicalPhysicalScalarH1TraceConstant] using
    canonicalPhysicalScalarH1TraceOfCoarea_norm_le
      period hPeriod
      (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) field

/-- Unconditional squared trace estimate on the smooth core. -/
theorem smoothCanonicalPhysicalTrace_norm_sq_le
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 ≤
      (canonicalPhysicalScalarH1TraceConstant period hPeriod) ^ 2 *
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
  simpa [canonicalPhysicalScalarH1TraceConstant] using
    smoothCanonicalPhysicalTrace_norm_sq_le_ofCoarea
      period hPeriod
      (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) field

/-- The physical scalar `H¹` trace exists without an external coarea input. -/
theorem canonicalPhysicalH1TraceExists :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  canonicalPhysicalH1TraceExists_ofCoarea period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

/-- Final closure certificate for the physical scalar value trace. -/
theorem certificate :
    Nonempty (CanonicalPhysicalH1TraceBound period hPeriod) ∧
      CanonicalPhysicalH1TraceExists period hPeriod ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 ≤
          (canonicalPhysicalScalarH1TraceConstant period hPeriod) ^ 2 *
            ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2) := by
  simpa [canonicalPhysicalScalarH1TraceConstant,
    canonicalPhysicalScalarH1TraceBound] using
    canonicalPhysicalH1TraceCoareaClosure_certificate
      period hPeriod
      (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)

end
end P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
end JanusFormal
