import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkMetricVolumeDensityNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-!
# Canonical intrinsic Lorentz metric and density on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
open P0EFTJanusMappingTorusCutBulkAmbientSmoothGeneralLorentzMetric4D
open P0EFTJanusMappingTorusCutBulkMetricVolumeDensityNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

/-- Canonical intrinsic Lorentz metric pulled back to the cut bulk. -/
def intrinsicCutBulkSmoothGeneralLorentzMetric :
    CutBulkSmoothGeneralLorentzMetric period hPeriod :=
  cutBulkAmbientSmoothGeneralLorentzMetricPullback period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)

/-- Canonical pointwise Lorentz frame pulled back to the cut bulk. -/
def intrinsicCutBulkPointwiseFrame
    (point : PositiveHemisphereCutBulk period hPeriod) :
    Fin 4 → CutBulkTangentFiber period hPeriod point :=
  cutBulkAmbientFramePullback period hPeriod point
    (intrinsicPointwiseFrame period hPeriod
      (cutBulkToAmbient period hPeriod point))

/-- The canonical cut-bulk density is exactly the ambient intrinsic density
at the natural image point. -/
theorem intrinsicCutBulkMetricVolumeDensity_eq_ambient
    (point : PositiveHemisphereCutBulk period hPeriod) :
    cutBulkMetricVolumeDensity period hPeriod
        (intrinsicCutBulkSmoothGeneralLorentzMetric period hPeriod) point
        (intrinsicCutBulkPointwiseFrame period hPeriod point) =
      metricVolumeDensity period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (cutBulkToAmbient period hPeriod point)
        (intrinsicPointwiseFrame period hPeriod
          (cutBulkToAmbient period hPeriod point)) :=
  cutBulkMetricVolumeDensity_ambientPullback period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
    (intrinsicPointwiseFrame period hPeriod
      (cutBulkToAmbient period hPeriod point))

end
end P0EFTJanusMappingTorusCutBulkIntrinsicMetricVolumeDensity4D
end JanusFormal
