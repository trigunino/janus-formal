import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalCovariantNormalClosure4D

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
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance historicalRawClosureCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance historicalRawClosureCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalRawClosureOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalRawClosureOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalRawClosureEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalRawClosureEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalRawClosureEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalRawClosureEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryHistoricalWeingartenRegularPairingAt_eq_localSectionRaw
    (metric : RegularGeneralLorentzMetric period hPeriod)
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
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let outerTarget := normalBoundaryOrientationTangentEquiv period hPeriod
      boundary (frame.vectorAt boundary outer)
    let innerTarget := normalBoundaryOrientationTangentEquiv period hPeriod
      boundary (frame.vectorAt boundary inner)
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    candidateANormalBoundaryHistoricalWeingartenRegularPairingAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull outer inner
          boundary =
      normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod variedMetric displacement boundary parameter patch
          coordinate outerTarget innerTarget base := by
  dsimp only
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let outerSource := frame.vectorAt boundary outer
  let innerSource := frame.vectorAt boundary inner
  let outerTarget := normalBoundaryOrientationTangentEquiv period hPeriod
    boundary outerSource
  let innerTarget := normalBoundaryOrientationTangentEquiv period hPeriod
    boundary innerSource
  let base :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let outerCoordinate :=
    candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
      metric outer current boundary patch coordinate
  let innerCoordinate :=
    candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
      metric inner current boundary patch coordinate
  let normalCoordinate :=
    candidateANormalBoundaryMetricUnitNormalCoordinates_historical period
      hPeriod metric variedMetric displacement parameter hNonNull boundary patch
        coordinate
  have hPairing :=
    candidateANormalBoundaryHistoricalWeingartenRegularPairingAt_eq_coordinatePairing
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        hNonNull outer inner boundary patch coordinate hAt
  have hCovariant :=
    candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt_eq_localSection
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        hNonNull outer boundary patch coordinate hAt hCurrent
  have hOuter : outerCoordinate =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate outerTarget := by
    simpa only [current, frame, outerSource, outerTarget, base,
      outerCoordinate] using
      (candidateANormalBoundaryGraphTangentCoordinates_historical_eq_source
        period hPeriod metric tensor displacement parameter boundary outer patch
          coordinate hAt)
  have hInner : innerCoordinate =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate innerTarget := by
    simpa only [current, frame, innerSource, innerTarget, base,
      innerCoordinate] using
      (candidateANormalBoundaryGraphTangentCoordinates_historical_eq_source
        period hPeriod metric tensor displacement parameter boundary inner patch
          coordinate hAt)
  have hNormal : normalCoordinate =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt := by
    simpa only [normalCoordinate] using
      (candidateANormalBoundaryMetricUnitNormalCoordinates_historical_eq_holonomic
        period hPeriod metric variedMetric displacement parameter hNonNull
          boundary patch coordinate hAt)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  calc
    candidateANormalBoundaryHistoricalWeingartenRegularPairingAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull outer inner
          boundary =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
          period hPeriod metric tensor variedMetric displacement parameter
            hNonNull outer boundary patch coordinate)
        innerCoordinate := by
          simpa only [current, innerCoordinate] using hPairing
    _ = localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
            period hPeriod variedMetric displacement boundary parameter patch
              coordinate base outerTarget +
          localLeviCivitaChristoffelApply period hPeriod variedMetric patch
            coordinate outerCoordinate normalCoordinate)
        innerCoordinate := by
          simpa only [current, frame, outerSource, outerTarget, base,
            outerCoordinate, normalCoordinate] using
            congrArg
              (fun vector => localMetricCoordinateForm period hPeriod
                variedMetric patch coordinate vector innerCoordinate)
              hCovariant
    _ = localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
            period hPeriod variedMetric displacement boundary parameter patch
              coordinate base outerTarget +
          localLeviCivitaChristoffelApply period hPeriod variedMetric patch
            coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate outerTarget)
            (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
              hPeriod variedMetric displacement parameter hNonNull boundary patch
                coordinate hAt))
        (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate innerTarget) := by
            rw [hOuter, hInner, hNormal]
    _ = normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod variedMetric displacement boundary parameter patch
          coordinate outerTarget innerTarget base := by
      unfold
        normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
        base patch coordinate hGraph]
      rw [normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_base_eq
        period hPeriod variedMetric displacement parameter hNonNull boundary
          patch coordinate hAt]
      rw [← normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family
        period hPeriod displacement base patch coordinate hGraph]

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryMetricUnitGaussRaw_eq_localSectionRaw
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
    (coordinate : CoordinateVector)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let outerTarget := normalBoundaryOrientationTangentEquiv period hPeriod
      boundary (frame.vectorAt boundary outer)
    let innerTarget := normalBoundaryOrientationTangentEquiv period hPeriod
      boundary (frame.vectorAt boundary inner)
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod variedMetric displacement boundary parameter patch
          coordinate outerTarget innerTarget base := by
  dsimp only
  exact
    (candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalWeingarten
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent hRootNonneg outer inner boundary patch
          coordinate hAt).trans
      (candidateANormalBoundaryHistoricalWeingartenRegularPairingAt_eq_localSectionRaw
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          hNonNull hCurrent.1.1 outer inner boundary patch coordinate hAt)

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryCompletedGaussLocalSectionAgreement_smooth
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
    CandidateANormalBoundaryCompletedGaussLocalSectionAgreement period hPeriod
      metric tensor variedMetric displacement parameter := by
  refine { pointwise := ?_ }
  intro boundary patch coordinate hAt row column
  dsimp only
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hRowColumn :=
    candidateANormalBoundaryMetricUnitGaussRaw_eq_localSectionRaw period hPeriod
      metric hTransverse tensor variedMetric hVaried displacement parameter
        hNonNull hCurrent hRootNonneg row column boundary patch coordinate hAt
  have hColumnRow :=
    candidateANormalBoundaryMetricUnitGaussRaw_eq_localSectionRaw period hPeriod
      metric hTransverse tensor variedMetric hVaried displacement parameter
        hNonNull hCurrent hRootNonneg column row boundary patch coordinate hAt
  dsimp only at hRowColumn hColumnRow
  unfold candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul,
    BoundedContinuousFunction.add_apply]
  rw [hRowColumn, hColumnRow]
  rw [normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply]
  ring

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
