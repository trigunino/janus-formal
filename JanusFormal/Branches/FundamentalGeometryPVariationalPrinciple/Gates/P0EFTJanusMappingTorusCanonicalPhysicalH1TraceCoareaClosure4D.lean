import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

/-!
# Physical scalar H1 trace reduced to the latitude coarea theorem

The joint smoothness of the canonical latitude collar and of its normal tangent
lift is already proved.  Consequently the finite-frame reconstruction estimate
for the normal derivative is unconditional.

The sole remaining input for the physical value trace is therefore the explicit
latitude disintegration inequality for `Measure.toSphere`.  This file combines
that one measure theorem with the completed normal-frame reconstruction and
constructs the physical H1 trace with an explicit product constant.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The exact remaining measure-theoretic proposition for the physical scalar
value trace. -/
abbrev CanonicalPhysicalScalarLatitudeCoareaTheorem : Prop :=
  CanonicalLatitudeMeasureToSphereCoareaDomination period hPeriod

/-- The unconditional normal reconstruction combined with the latitude coarea
bound. -/
def canonicalPhysicalLatitudeFrameComparisonOfCoarea
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) :
    CanonicalLatitudeFrameEnergyComparison period hPeriod :=
  (canonicalNormalFrameReconstructionBound period hPeriod).combineCoarea
    period hPeriod
    (canonicalLatitudeCoareaBoundOfMeasureToSphereCoarea
      period hPeriod coarea)

/-- Explicit trace constant obtained from the coarea theorem. -/
def canonicalPhysicalScalarH1TraceCoareaConstant
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) : Real :=
  (canonicalNormalFrameReconstructionBound period hPeriod).constant *
    Real.sqrt (3 * (canonicalLatitudeCoareaMeasureConstant : Real))

/-- The comparison constant is exactly the displayed coarea constant. -/
theorem canonicalPhysicalLatitudeFrameComparisonOfCoarea_constant
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) :
    (canonicalPhysicalLatitudeFrameComparisonOfCoarea
      period hPeriod coarea).constant =
      canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea :=
  rfl

/-- Concrete smooth physical value-trace bound from the single coarea theorem. -/
def canonicalPhysicalScalarH1TraceBoundOfCoarea
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) :
    CanonicalPhysicalH1TraceBound period hPeriod :=
  canonicalPhysicalH1TraceBoundOfLatitudeComparison
    period hPeriod
    (canonicalPhysicalLatitudeFrameComparisonOfCoarea
      period hPeriod coarea)

/-- Completed physical value trace from the single coarea theorem. -/
def canonicalPhysicalScalarH1TraceOfCoarea
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  canonicalPhysicalH1Trace period hPeriod
    (canonicalPhysicalScalarH1TraceBoundOfCoarea period hPeriod coarea)

/-- Agreement of the completed trace with smooth restriction. -/
theorem canonicalPhysicalScalarH1TraceOfCoarea_agrees_on_smooth
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarH1TraceOfCoarea period hPeriod coarea
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field :=
  canonicalPhysicalH1Trace_agrees_on_smooth period hPeriod
    (canonicalPhysicalScalarH1TraceBoundOfCoarea period hPeriod coarea) field

/-- Quantitative operator bound for the completed physical trace. -/
theorem canonicalPhysicalScalarH1TraceOfCoarea_norm_le
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    ‖canonicalPhysicalScalarH1TraceOfCoarea period hPeriod coarea field‖ ≤
      canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
        ‖field‖ := by
  simpa [canonicalPhysicalScalarH1TraceOfCoarea,
    canonicalPhysicalScalarH1TraceBoundOfCoarea,
    canonicalPhysicalScalarH1TraceCoareaConstant,
    canonicalPhysicalLatitudeFrameComparisonOfCoarea] using
    canonicalPhysicalH1Trace_norm_le period hPeriod
      (canonicalPhysicalScalarH1TraceBoundOfCoarea period hPeriod coarea) field

/-- Squared smooth trace estimate with the explicit product constant. -/
theorem smoothCanonicalPhysicalTrace_norm_sq_le_ofCoarea
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 ≤
      (canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea) ^ 2 *
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
  simpa [canonicalPhysicalScalarH1TraceCoareaConstant,
    canonicalPhysicalLatitudeFrameComparisonOfCoarea] using
    CanonicalLatitudeFrameEnergyComparison.squaredBound
      period hPeriod
      (canonicalPhysicalLatitudeFrameComparisonOfCoarea
        period hPeriod coarea) field

/-- The coarea theorem discharges the exact physical H1-trace frontier. -/
theorem canonicalPhysicalH1TraceExists_ofCoarea
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  (canonicalPhysicalH1TraceExists_iff period hPeriod).2
    ⟨canonicalPhysicalScalarH1TraceBoundOfCoarea period hPeriod coarea⟩

/-- Closure certificate identifying the unique remaining analytic input. -/
theorem canonicalPhysicalH1TraceCoareaClosure_certificate
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod) :
    Nonempty (CanonicalPhysicalH1TraceBound period hPeriod) ∧
      CanonicalPhysicalH1TraceExists period hPeriod ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 ≤
          (canonicalPhysicalScalarH1TraceCoareaConstant
            period hPeriod coarea) ^ 2 *
          ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2) :=
  ⟨⟨canonicalPhysicalScalarH1TraceBoundOfCoarea period hPeriod coarea⟩,
    canonicalPhysicalH1TraceExists_ofCoarea period hPeriod coarea,
    smoothCanonicalPhysicalTrace_norm_sq_le_ofCoarea
      period hPeriod coarea⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D
end JanusFormal
