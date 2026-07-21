import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkSmoothScalarGradient4D

/-!
# Smooth covariant scalar Green current on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
open P0EFTJanusMappingTorusCutBulkSmoothInverseMusical4D
open P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D
open P0EFTJanusMappingTorusCutBulkSmoothScalarGradient4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

local instance cutBulkIsManifold :
    IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobal_isManifold period hPeriod

/-- Smooth Green current `φ grad ψ - ψ grad φ` for a cut-bulk metric. -/
def cutBulkSmoothScalarGreenCurrent
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (field test : CutBulkSmoothScalarField period hPeriod) :
    CutBulkSmoothVectorField period hPeriod where
  toFun := fun point =>
    field point • cutBulkSmoothScalarGradient period hPeriod metric test point -
      test point • cutBulkSmoothScalarGradient period hPeriod metric field point
  contMDiff_toFun :=
    (field.contMDiff_toFun.smul_section
      (cutBulkSmoothScalarGradient period hPeriod metric test).contMDiff).sub_section
    (test.contMDiff_toFun.smul_section
      (cutBulkSmoothScalarGradient period hPeriod metric field).contMDiff)

@[simp]
theorem cutBulkSmoothScalarGreenCurrent_apply
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (field test : CutBulkSmoothScalarField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    cutBulkSmoothScalarGreenCurrent period hPeriod metric field test point =
      field point • cutBulkSmoothScalarGradient period hPeriod metric test point -
        test point • cutBulkSmoothScalarGradient period hPeriod metric field point :=
  rfl

/-- Lowering the Green current recovers the expected differential formula. -/
theorem cutBulkSmoothScalarGreenCurrent_flat
    (metric : CutBulkSmoothGeneralLorentzMetric period hPeriod)
    (field test : CutBulkSmoothScalarField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod) :
    metric.musical point
        (cutBulkSmoothScalarGreenCurrent period hPeriod metric field test point) =
      field point • cutBulkSmoothScalarDifferential period hPeriod test point -
        test point • cutBulkSmoothScalarDifferential period hPeriod field point := by
  rw [cutBulkSmoothScalarGreenCurrent_apply, map_sub, map_smul, map_smul,
    cutBulkSmoothScalarGradient_flat, cutBulkSmoothScalarGradient_flat]

/-- Canonical intrinsic Green current of two ambient quotient scalars on the
cut bulk. -/
def intrinsicCutBulkSmoothScalarGreenCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    CutBulkSmoothVectorField period hPeriod :=
  cutBulkSmoothScalarGreenCurrent period hPeriod
    (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod)
    (cutBulkSmoothScalarPullback period hPeriod field)
    (cutBulkSmoothScalarPullback period hPeriod test)

end
end P0EFTJanusMappingTorusCutBulkSmoothScalarGreenCurrent4D
end JanusFormal
