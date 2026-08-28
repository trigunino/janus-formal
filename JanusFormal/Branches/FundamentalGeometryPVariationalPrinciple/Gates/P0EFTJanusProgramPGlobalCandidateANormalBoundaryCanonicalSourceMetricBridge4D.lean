import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalMetricCancellation4D

/-!
# Source/target induced-metric bridge for the H10 canonical shape

The canonical shape operator is constructed on the effective throat and then
pulled back through the already proved orientation-double tangent equivalence.
This gate proves that pairing the pulled-back shape with the pulled-back
induced metric is exactly the same scalar as pairing the target shape with the
holonomic induced metric.  The preceding metric-cancellation theorem then
recovers the existing local-section second fundamental form.

No new frame, metric, inverse, normal, chart, or boundary datum is introduced.
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
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance (priority := 30000)
    canonicalSourceMetricOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalSourceMetricOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    canonicalSourceMetricEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalSourceMetricEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance (priority := 30000)
    canonicalSourceMetricFixedThroatChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance (priority := 30000)
    canonicalSourceMetricFixedThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  fixedThroatQuotient_isManifold period hPeriod

private def canonicalSourceMetricOrientationCoordinateEquiv
    (boundary : CutThroatBoundary period hPeriod) :
    ThroatCoverCoordinates ≃L[Real] ThroatCoverCoordinates :=
  normalBoundaryOrientationTangentEquiv period hPeriod boundary

private theorem canonicalSourceMetricInducedMetricMusical_apply
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (boundary : CutThroatBoundary period hPeriod)
    (first second : ThroatCoverCoordinates) :
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric
        displacement parameter boundary first second =
      normalGraphInducedMetricValue period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary)
        (canonicalSourceMetricOrientationCoordinateEquiv period hPeriod
          boundary first)
        (canonicalSourceMetricOrientationCoordinateEquiv period hPeriod
          boundary second) := by
  exact normalBoundarySmoothGraphInducedMetricMusical_apply period hPeriod
    variedMetric displacement parameter boundary first second

private theorem canonicalSourceMetricInducedMetricValue_eq_holonomic
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod) × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (first second : ThroatCoverCoordinates) :
    normalGraphInducedMetricValue period hPeriod variedMetric displacement
        base.2 base.1 first second =
      normalGraphHolonomicInducedMetricCoordinates period hPeriod variedMetric
        displacement base patch coordinate base first second := by
  have hChart : base.1 ∈ (chartAt ThroatCoverModel base.1).source :=
    mem_chart_source ThroatCoverModel base.1
  have hTrivialized (vector : ThroatCoverCoordinates) :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector =
        vector := by
    change
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).symmL Real base.1 vector =
        vector
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  have hIntrinsic :=
    (normalGraphHolonomicInducedMetricCoordinates_eq_intrinsic period hPeriod
      variedMetric displacement base patch coordinate hGraph first second).symm
  rw [hTrivialized, hTrivialized] at hIntrinsic
  exact hIntrinsic

set_option backward.isDefEq.respectTransparency false in
/-- Pairing the source-side canonical shape with the source-side induced
metric recovers the already installed target local-section second form. -/
theorem
    normalBoundarySmoothGraphInducedMetricMusical_canonicalShape_eq_localSection
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
    (first second : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric
        displacement parameter boundary
        (normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
          variedMetric displacement parameter hNonNull boundary patch coordinate
            hAt first)
        second =
      normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
        period hPeriod variedMetric displacement boundary parameter patch
          coordinate
          (orientationDoubleToThroat period hPeriod boundary, parameter)
          (canonicalSourceMetricOrientationCoordinateEquiv period hPeriod
            boundary first)
          (canonicalSourceMetricOrientationCoordinateEquiv period hPeriod
            boundary second) := by
  let base :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let tangentEquiv :
      ThroatCoverCoordinates ≃L[Real] ThroatCoverCoordinates :=
    canonicalSourceMetricOrientationCoordinateEquiv period hPeriod boundary
  let firstCoordinate : ThroatCoverCoordinates := first
  let secondCoordinate : ThroatCoverCoordinates := second
  let targetShape :=
    normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period hPeriod
      variedMetric displacement parameter boundary patch coordinate
  let sourceShape :=
    normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
      variedMetric displacement parameter hNonNull boundary patch coordinate hAt
  let transportedFirst : ThroatCoverCoordinates :=
    tangentEquiv firstCoordinate
  let transportedSecond : ThroatCoverCoordinates :=
    tangentEquiv secondCoordinate
  let targetFirst : ThroatCoverCoordinates :=
    targetShape transportedFirst
  change normalBoundarySmoothGraphInducedMetricMusical period hPeriod
      variedMetric displacement parameter boundary
        (sourceShape firstCoordinate) secondCoordinate =
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap period
      hPeriod variedMetric displacement boundary parameter patch coordinate base
        transportedFirst transportedSecond
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hShape :
      tangentEquiv (sourceShape firstCoordinate) =
        targetFirst := by
    change tangentEquiv
        (tangentEquiv.symm targetFirst) = targetFirst
    exact tangentEquiv.apply_symm_apply _
  rw [canonicalSourceMetricInducedMetricMusical_apply]
  rw [hShape]
  calc
    normalGraphInducedMetricValue period hPeriod variedMetric displacement
        parameter base.1 targetFirst transportedSecond =
      normalGraphHolonomicInducedMetricCoordinates period hPeriod variedMetric
        displacement base patch coordinate base targetFirst transportedSecond := by
      exact canonicalSourceMetricInducedMetricValue_eq_holonomic period hPeriod
        variedMetric displacement base patch coordinate hGraph targetFirst
          transportedSecond
    _ = normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
        period hPeriod variedMetric displacement boundary parameter patch
          coordinate base transportedFirst transportedSecond := by
      exact
        normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt_metric_cancel
          period hPeriod variedMetric displacement parameter hNonNull boundary
            patch coordinate hAt transportedFirst transportedSecond

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
