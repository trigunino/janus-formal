import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalShapeTrace4D

/-!
# Canonical induced-metric cancellation for H10

The canonical target shape is `h⁻¹ K`, built from the already installed
coordinate inverse of the induced metric and the already installed smooth
local-section second fundamental form.  This gate proves that pairing it with
the same holonomic induced metric recovers `K` exactly at the physical graph
anchor.  No new inverse, metric, normal, chart, or boundary datum is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000
noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance (priority := 30000)
    canonicalMetricCancellationOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalMetricCancellationOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    canonicalMetricCancellationEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalMetricCancellationEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- At the physical graph anchor, the holonomic induced metric cancels the
canonical target-side inverse metric in `h⁻¹ K`. -/
theorem
    normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt_metric_cancel
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphHolonomicInducedMetricCoordinates period hPeriod variedMetric
        displacement base patch coordinate base
        (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period
          hPeriod variedMetric displacement parameter boundary patch coordinate
          first)
        second =
      normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
        period hPeriod variedMetric displacement boundary parameter patch
          coordinate base first second := by
  dsimp only
  let base :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hRightInverse :=
    (normalGraphHolonomicInducedMetricInverseCoordinates_eventually_rightInverse
      period hPeriod variedMetric displacement base hNonNull patch coordinate
        hGraph).self_of_nhds
  unfold normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt
  dsimp only
  exact hRightInverse
    (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
      period hPeriod variedMetric displacement boundary parameter patch
        coordinate base first)
    second

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
