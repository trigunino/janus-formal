import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussWeingartenClosure4D

/-!
# Historical Weingarten bridge for the completed Candidate-A GHY action

The completed raw Gauss scalar is already identified with the derivative of
the historical physical unit normal.  This file propagates that pointwise
identity through symmetrization, index raising, mean-curvature contraction,
the GHY density and the one- and two-sheet integrals.

The resulting historical action still uses the completed induced inverse and
volume density.  Thus this gate deliberately isolates the final geometric
step: identifying that regular-frame expression with the pre-existing
chart-free normal-graph GHY action.
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

local instance completedHistoricalGHYCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance completedHistoricalGHYCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    completedHistoricalGHYOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedHistoricalGHYOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    completedHistoricalGHYEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedHistoricalGHYEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Symmetric historical second fundamental form in the installed redundant
boundary frame. -/
def candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) : Real :=
  (1 / 2 : Real) *
    (candidateANormalBoundaryHistoricalWeingartenRegularPairingAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull outer inner
          boundary +
      candidateANormalBoundaryHistoricalWeingartenRegularPairingAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull inner outer
          boundary)

/-- The same historical form with one index raised by the fixed reference
metric, encoded in the redundant finite frame. -/
def candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod) :
    Matrix (NormalBoundaryTangentIndex period hPeriod)
      (NormalBoundaryTangentIndex period hPeriod) Real :=
  fun row column =>
    ∑ middle : NormalBoundaryTangentIndex period hPeriod,
      normalBoundaryReferenceDualCoefficientMatrix
          period hPeriod row middle boundary *
        candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt
          period hPeriod metric tensor variedMetric displacement parameter
            hNonNull middle column boundary

/-- Historical regular-frame mean curvature, contracted with the same
completed inverse induced metric as the Candidate-A functional. -/
def candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod) : Real :=
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  Matrix.trace
    (normalBoundaryRealMatrixMul period hPeriod
      (fun row column =>
        candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
          period hPeriod metric current row column boundary)
      (candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull boundary))

/-- Pointwise historical regular-frame GHY integrand relative to the installed
canonical latitude reference measure. -/
def candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod) : Real :=
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  einsteinScale *
    candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric current boundary *
      candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull boundary

/-- First-sheet integral of the historical regular-frame GHY integrand. -/
def candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) : Real :=
  ∫ base,
    candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt period hPeriod
      einsteinScale metric tensor variedMetric displacement parameter hNonNull
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
      ∂canonicalLatitudeBaseMeasure period

/-- Two-sheet historical regular-frame GHY action, with the already proved
sheet multiplicity. -/
def candidateANormalBoundaryHistoricalWeingartenTwoSheetGHYAction
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) : Real :=
  2 * candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction
    period hPeriod einsteinScale metric tensor variedMetric displacement
      parameter hNonNull

set_option backward.isDefEq.respectTransparency false in
/-- The completed symmetric second fundamental form is the symmetrized
historical Weingarten pairing on the smooth admissible core. -/
theorem candidateANormalBoundaryMetricUnitGaussExtrinsicCurvature_eq_historicalWeingarten
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
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull outer inner boundary := by
  unfold candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
    candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt
  simp only [BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.add_apply, smul_eq_mul]
  rw [candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalWeingarten
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent hRootNonneg outer inner boundary patch
          coordinate hAt,
    candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalWeingarten
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent hRootNonneg inner outer boundary patch
          coordinate hAt]

set_option backward.isDefEq.respectTransparency false in
/-- Raising one index commutes with the smooth historical identification. -/
theorem candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrix_eq_historicalWeingarten
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
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) row column boundary =
      candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull boundary row column := by
  classical
  unfold
    candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
    candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro middle _
  rw [candidateANormalBoundaryMetricUnitGaussExtrinsicCurvature_eq_historicalWeingarten
    period hPeriod metric hTransverse tensor variedMetric hVaried displacement
      parameter hNonNull hCurrent hRootNonneg middle column boundary patch
        coordinate hAt]

set_option backward.isDefEq.respectTransparency false in
/-- The completed mean-curvature contraction is the historical regular-frame
mean curvature pointwise on the smooth admissible core. -/
theorem candidateANormalBoundaryMetricUnitGaussMeanCurvature_eq_historicalWeingarten
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
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull boundary := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  rw [candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply_mul]
  unfold candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt
  dsimp only
  apply congrArg Matrix.trace
  ext row column
  unfold normalBoundaryRealMatrixMul
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro middle _
  rw [candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrix_eq_historicalWeingarten
    period hPeriod metric hTransverse tensor variedMetric hVaried displacement
      parameter hNonNull hCurrent hRootNonneg boundary patch coordinate hAt
        middle column]

set_option backward.isDefEq.respectTransparency false in
/-- The completed pointwise GHY density is the historical regular-frame GHY
density on the smooth admissible core. -/
theorem candidateANormalBoundaryGHYIntegrandFiberEvaluation_eq_historicalWeingarten
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
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    candidateANormalBoundaryGHYIntegrandFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt period hPeriod
        einsteinScale metric tensor variedMetric displacement parameter hNonNull
          boundary := by
  unfold candidateANormalBoundaryGHYIntegrandFiberEvaluation
    candidateANormalBoundaryHistoricalWeingartenGHYIntegrandAt
  dsimp only
  simp only [BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.mul_apply, smul_eq_mul]
  rw [candidateANormalBoundaryMetricUnitGaussMeanCurvature_eq_historicalWeingarten
    period hPeriod metric hTransverse tensor variedMetric hVaried displacement
      parameter hNonNull hCurrent hRootNonneg boundary patch coordinate hAt]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the completed first-sheet action with the historical
regular-frame action.  Canonical selected holonomic charts discharge the
pointwise chart witness under the integral. -/
theorem candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation_eq_historicalWeingarten
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
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point) :
    candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction
        period hPeriod einsteinScale metric tensor variedMetric displacement
          parameter hNonNull := by
  rw [candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation_eq_integral]
  unfold candidateANormalBoundaryHistoricalWeingartenFirstSheetGHYAction
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base => by
    let boundary :=
      canonicalLatitudeCutBoundaryFirstLift period hPeriod base
    let point :=
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)
    let patch :=
      normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point
    let coordinate :=
      normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point
    have hAt : patch.coordinateMap coordinate =
        normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter) := by
      simpa [patch, coordinate, point] using
        (normalGraphCanonicalSelectedHolonomicPatchAt_map
          period hPeriod point)
    exact
      candidateANormalBoundaryGHYIntegrandFiberEvaluation_eq_historicalWeingarten
        period hPeriod einsteinScale metric hTransverse tensor variedMetric
          hVaried displacement parameter hNonNull hCurrent hRootNonneg boundary
            patch coordinate hAt

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the completed two-sheet action with the historical
regular-frame two-sheet action. -/
theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_historicalWeingarten
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
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point) :
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      candidateANormalBoundaryHistoricalWeingartenTwoSheetGHYAction
        period hPeriod einsteinScale metric tensor variedMetric displacement
          parameter hNonNull := by
  unfold candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
    candidateANormalBoundaryHistoricalWeingartenTwoSheetGHYAction
  rw [candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation_eq_historicalWeingarten
    period hPeriod einsteinScale metric hTransverse tensor variedMetric hVaried
      displacement parameter hNonNull hCurrent hRootNonneg]

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
