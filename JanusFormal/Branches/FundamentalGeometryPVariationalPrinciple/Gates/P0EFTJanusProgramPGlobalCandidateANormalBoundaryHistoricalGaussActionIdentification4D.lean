import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedHistoricalGHYBridge4D

/-!
# Historical Gauss action identification for the completed Candidate-A boundary

The completed H10 functional has already been identified with the historical
regular-frame GHY action.  This gate isolates the sole remaining geometric
identification: the faithful redundant-frame trace must agree with the fixed
holonomic representative of the chart-free Gauss mean curvature.

Once that scalar trace agreement is supplied, the already proved density
identity propagates it pointwise, through the first-sheet integral, through
the two-sheet multiplicity, and back to the completed `C²` Candidate-A action.
No second boundary action, metric, normal, chart, or physical hypothesis is
introduced here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000
noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle MeasureTheory

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance historicalGaussActionCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance historicalGaussActionCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalGaussActionOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussActionOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalGaussActionEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussActionEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Exact residual trace statement in the fixed holonomic representative.
This is a proof interface, not an additional datum of the action. -/
def CandidateANormalBoundaryHistoricalLocalTraceAgreement
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) : Prop :=
  ∀ (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)),
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt
    candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull boundary =
      normalGraphCanonicalHolonomicLocalMeanCurvatureFamily period hPeriod
        variedMetric displacement base patch coordinate ambient base

/-- Chart-free form of the same residual trace statement. -/
def CandidateANormalBoundaryHistoricalGaussTraceAgreement
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) : Prop :=
  ∀ boundary : CutThroatBoundary period hPeriod,
    candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull boundary =
      normalGraphCanonicalGaussMeanCurvature period hPeriod variedMetric
        displacement parameter hNonNull boundary

/-- The already proved fixed-chart/global comparison promotes the local trace
statement to the chart-free one.  Thus the remaining finite-frame work is
precisely the first predicate above. -/
theorem candidateANormalBoundaryHistoricalGaussTraceAgreement_of_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hLocal : CandidateANormalBoundaryHistoricalLocalTraceAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalGaussTraceAgreement period hPeriod metric
      tensor variedMetric displacement parameter hNonNull := by
  intro boundary
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let patch :=
    normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point
  let coordinate :=
    normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point
  have hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) := by
    simpa [point, patch, coordinate] using
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point)
  let base :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      variedMetric displacement parameter hNonNull boundary patch coordinate hAt
  calc
    candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull boundary =
      normalGraphCanonicalHolonomicLocalMeanCurvatureFamily period hPeriod
        variedMetric displacement base patch coordinate ambient base := by
          simpa [base, ambient] using
            hLocal boundary patch coordinate hAt
    _ = normalGraphCanonicalGaussMeanCurvature period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
          simpa [base, ambient] using
            (normalGraphCanonicalHolonomicLocalMeanCurvatureFamily_base_eq_gauss
              period hPeriod variedMetric displacement parameter hNonNull
                boundary patch coordinate hAt)

set_option backward.isDefEq.respectTransparency false in
/-- Once the scalar trace is identified, the historical regular-frame density
is exactly the chart-free mobile Gauss density without its orientation sign. -/
theorem candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt_eq_gauss
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hVolumeRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hTrace : CandidateANormalBoundaryHistoricalGaussTraceAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt period hPeriod
        einsteinScale metric tensor variedMetric displacement parameter hNonNull
          boundary =
      einsteinScale *
        normalGraphRelativeVolumeDensity period hPeriod variedMetric displacement
          parameter (orientationDoubleToThroat period hPeriod boundary) *
        normalGraphCanonicalGaussMeanCurvature period hPeriod variedMetric
          displacement parameter hNonNull boundary := by
  unfold candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt
  dsimp only
  rw [candidateANormalBoundaryInducedVolumeDensity_smooth_eq_historical
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter boundary hCurrent (hVolumeRootNonneg boundary),
    hTrace boundary]

set_option backward.isDefEq.respectTransparency false in
/-- First-sheet pullback of the historical density is the installed mobile
Gauss integrand. -/
theorem candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt_firstSheet_eq
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hVolumeRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hTrace : CandidateANormalBoundaryHistoricalGaussTraceAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull)
    (base : CanonicalLatitudeBase) :
    candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt period hPeriod
        einsteinScale metric tensor variedMetric displacement parameter hNonNull
          (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) =
      normalGraphCanonicalFirstSheetGaussGHYIntegrand period hPeriod
        einsteinScale variedMetric displacement parameter hNonNull base := by
  rw [candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt_eq_gauss
    period hPeriod einsteinScale metric hTransverse tensor variedMetric hVaried
      displacement parameter hNonNull hCurrent hVolumeRootNonneg hTrace]
  unfold normalGraphCanonicalFirstSheetGaussGHYIntegrand
    normalGraphCanonicalInducedGaussGHYIntegrand
  simp [P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation.sign]

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the historical regular-frame first-sheet action with the
pre-existing chart-free mobile first-sheet action. -/
theorem candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction_eq_gauss
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hVolumeRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hTrace : CandidateANormalBoundaryHistoricalGaussTraceAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction period
        hPeriod einsteinScale metric tensor variedMetric displacement parameter
          hNonNull =
      normalGraphCanonicalFirstSheetGaussGHYAction period hPeriod einsteinScale
        variedMetric displacement parameter hNonNull := by
  unfold candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction
    normalGraphCanonicalFirstSheetGaussGHYAction
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt_firstSheet_eq
      period hPeriod einsteinScale metric hTransverse tensor variedMetric hVaried
        displacement parameter hNonNull hCurrent hVolumeRootNonneg hTrace base

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the historical and chart-free mobile two-sheet actions. -/
theorem candidateANormalBoundaryHistoricalWeingartenTwoSheetGHYAction_eq_gauss
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hVolumeRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hTrace : CandidateANormalBoundaryHistoricalGaussTraceAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    candidateANormalBoundaryHistoricalWeingartenTwoSheetGHYAction period hPeriod
        einsteinScale metric tensor variedMetric displacement parameter hNonNull =
      normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale
        variedMetric displacement parameter hNonNull := by
  unfold candidateANormalBoundaryHistoricalWeingartenTwoSheetGHYAction
  rw [candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction_eq_gauss
    period hPeriod einsteinScale metric hTransverse tensor variedMetric hVaried
      displacement parameter hNonNull hCurrent hVolumeRootNonneg hTrace]
  rw [normalGraphCanonicalTwoSheetGaussGHYAction_eq_two_mul_first]

set_option backward.isDefEq.respectTransparency false in
/-- Terminal smooth-core same-action theorem before promotion into the unique
central Candidate-A action datum. -/
theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_gauss
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hNormalRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hVolumeRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hTrace : CandidateANormalBoundaryHistoricalGaussTraceAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale
        variedMetric displacement parameter hNonNull := by
  rw [candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_historicalWeingarten
    period hPeriod einsteinScale metric hTransverse tensor variedMetric hVaried
      displacement parameter hNonNull hCurrent.1 hNormalRootNonneg]
  exact
    candidateANormalBoundaryHistoricalWeingartenTwoSheetGHYAction_eq_gauss
      period hPeriod einsteinScale metric hTransverse tensor variedMetric hVaried
        displacement parameter hNonNull hCurrent hVolumeRootNonneg hTrace

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
