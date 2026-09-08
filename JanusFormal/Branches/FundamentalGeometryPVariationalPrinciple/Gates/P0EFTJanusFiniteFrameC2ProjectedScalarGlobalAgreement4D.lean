import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2MobileInteractionResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D

/-! # Global agreement of the finite-frame projected scalar curvature -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ProjectedScalarGlobalAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The redundant finite-frame contraction reconstructs the globally glued
intrinsic scalar curvature at every quotient point. -/
theorem finiteFrameSmoothProjectedScalarCurvature_eq_global
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric metric : SmoothGeneralLorentzMetric period hPeriod) :
    finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric =
      globalSmoothScalarCurvature period hPeriod metric := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate,
    finiteFrameSmoothProjectedScalarCurvature_eq_intrinsic period hPeriod frame baseMetric
      metric patch coordinate,
    globalSmoothScalarCurvature_apply_local period hPeriod metric patch coordinate]

/-- Consequently, the completed C² scalar-curvature readout on every smooth
admissible input is the canonical global intrinsic scalar-curvature field. -/
theorem finiteFrameProjectedScalarCurvatureC0_smooth_eq_global
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) :
    finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothScalarCurvature period hPeriod metric) := by
  rw [finiteFrameProjectedScalarCurvatureC0_smooth period hPeriod frame baseMetric variation
    metric hMetric hVariation,
    finiteFrameSmoothProjectedScalarCurvature_eq_global period hPeriod frame baseMetric metric]

end
end P0EFTJanusFiniteFrameC2ProjectedScalarGlobalAgreement4D
end JanusFormal
