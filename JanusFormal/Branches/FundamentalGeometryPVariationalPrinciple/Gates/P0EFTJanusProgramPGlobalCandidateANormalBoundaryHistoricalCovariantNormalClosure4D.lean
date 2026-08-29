import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalNormalLeibniz4D

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

local instance historicalCovariantClosureCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance historicalCovariantClosureCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalCovariantClosureOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalCovariantClosureOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalCovariantClosureEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalCovariantClosureEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalCovariantClosureEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalCovariantClosureEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem finiteFrameCovariantExpansion
    (tangent normal : Fin 4 → Real)
    (frame : Fin 4 → CoordinateVector)
    (frameDerivative : Fin 4 → CoordinateVector →L[Real] CoordinateVector)
    (christoffel : CoordinateVector →ₗ[Real]
      CoordinateVector →ₗ[Real] CoordinateVector) :
    (∑ regular : Fin 4, ∑ upper : Fin 4,
      (tangent regular * normal upper) •
        (frameDerivative upper (frame regular) +
          christoffel (frame regular) (frame upper))) =
      (∑ upper : Fin 4,
        normal upper •
          frameDerivative upper
            (∑ regular : Fin 4, tangent regular • frame regular)) +
        christoffel
          (∑ regular : Fin 4, tangent regular • frame regular)
          (∑ upper : Fin 4, normal upper • frame upper) := by
  classical
  have hDerivative :
      (∑ regular : Fin 4, ∑ upper : Fin 4,
        (tangent regular * normal upper) •
          frameDerivative upper (frame regular)) =
        ∑ upper : Fin 4, normal upper •
          frameDerivative upper
            (∑ regular : Fin 4, tangent regular • frame regular) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro upper _
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro regular _
    rw [mul_comm]
  have hConnection :
      (∑ regular : Fin 4, ∑ upper : Fin 4,
        (tangent regular * normal upper) •
          christoffel (frame regular) (frame upper)) =
        christoffel
          (∑ regular : Fin 4, tangent regular • frame regular)
          (∑ upper : Fin 4, normal upper • frame upper) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro upper _
    apply Finset.sum_congr rfl
    intro regular _
    rw [mul_comm]
  calc
    _ = (∑ regular : Fin 4, ∑ upper : Fin 4,
          (tangent regular * normal upper) •
            frameDerivative upper (frame regular)) +
        (∑ regular : Fin 4, ∑ upper : Fin 4,
          (tangent regular * normal upper) •
            christoffel (frame regular) (frame upper)) := by
        simp only [smul_add, Finset.sum_add_distrib]
    _ = _ := by rw [hDerivative, hConnection]

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt_eq_localSection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let sourceVector := frame.vectorAt boundary outer
    let targetVector :=
      normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let tangentCoordinate :=
      candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
        metric outer current boundary patch coordinate
    let normalCoordinate :=
      candidateANormalBoundaryMetricUnitNormalCoordinates_historical period
        hPeriod metric variedMetric displacement parameter hNonNull boundary
          patch coordinate
    candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
        period hPeriod metric tensor variedMetric displacement parameter hNonNull
          outer boundary patch coordinate =
      normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
          hPeriod variedMetric displacement boundary parameter patch coordinate
            base targetVector +
        localLeviCivitaChristoffelApply period hPeriod variedMetric patch
          coordinate tangentCoordinate normalCoordinate := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let sourceVector := frame.vectorAt boundary outer
  let targetVector :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
  let base :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let tangent := fun regular : Fin 4 =>
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
      period hPeriod metric outer regular current boundary
  let normal := fun upper : Fin 4 =>
    candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
      period hPeriod metric variedMetric displacement parameter hNonNull upper
        boundary
  let frameCoordinate := fun row : Fin 4 =>
    pulledRegularFrameVector period hPeriod metric patch row coordinate
  let frameDerivative := fun upper : Fin 4 =>
    fderiv Real (pulledRegularFrameVector period hPeriod metric patch upper)
      coordinate
  let tangentCoordinate :=
    candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
      metric outer current boundary patch coordinate
  let normalCoordinate :=
    candidateANormalBoundaryMetricUnitNormalCoordinates_historical period
      hPeriod metric variedMetric displacement parameter hNonNull boundary patch
        coordinate
  let localNormalDerivative :=
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
      hPeriod variedMetric displacement boundary parameter patch coordinate base
        targetVector
  let derivativeCoefficientSum :=
    ∑ row : Fin 4,
      candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
            period hPeriod metric variedMetric displacement parameter hNonNull
              outer row boundary • frameCoordinate row
  let connectionCoefficientSum :=
    ∑ row : Fin 4,
      (∑ regular : Fin 4, ∑ upper : Fin 4,
        tangent regular *
          candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod
            metric row regular upper current boundary * normal upper) •
        frameCoordinate row
  let frameDerivativeSum :=
    ∑ upper : Fin 4,
      normal upper • frameDerivative upper tangentCoordinate
  let connection :=
    localLeviCivitaChristoffelBilinearMap period hPeriod variedMetric patch
      coordinate
  have hHistoricalSplit :
      candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
          period hPeriod metric tensor variedMetric displacement parameter
            hNonNull outer boundary patch coordinate =
        derivativeCoefficientSum + connectionCoefficientSum := by
    unfold candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
    dsimp only [current, derivativeCoefficientSum, connectionCoefficientSum,
      tangent, normal, frameCoordinate]
    simp only [add_smul, Finset.sum_add_distrib]
  have hConnection :=
    candidateANormalBoundaryHistoricalRegularConnectionNormalCoordinatesAt_eq_covariantFrameSum
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        hNonNull outer boundary patch coordinate hAt hCurrent
  dsimp only at hConnection
  have hFrameAlgebra := finiteFrameCovariantExpansion
    (tangent := tangent) (normal := normal) (frame := frameCoordinate)
    (frameDerivative := frameDerivative) (christoffel := connection)
  have hFrameExpansion :
      (∑ regular : Fin 4, ∑ upper : Fin 4,
        (tangent regular * normal upper) •
          candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch regular upper coordinate) =
        frameDerivativeSum +
          localLeviCivitaChristoffelApply period hPeriod variedMetric patch
            coordinate tangentCoordinate normalCoordinate := by
    unfold candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
    simpa only [tangent, normal, frameCoordinate, frameDerivative,
      tangentCoordinate, normalCoordinate,
      candidateANormalBoundaryGraphTangentCoordinates_historical,
      candidateANormalBoundaryMetricUnitNormalCoordinates_historical,
      connection, frameDerivativeSum,
      localLeviCivitaChristoffelBilinearMap_apply] using hFrameAlgebra
  have hLeibniz :=
    candidateANormalBoundaryMetricUnitNormalField_historical_mvfderiv_expand
      period hPeriod metric tensor variedMetric displacement parameter hNonNull
        outer boundary patch coordinate hAt
  dsimp only at hLeibniz
  have hNormalDerivative :=
    candidateANormalBoundaryMetricUnitNormalField_historical_mfderiv period
      hPeriod metric variedMetric displacement parameter hNonNull boundary patch
        coordinate hAt targetVector
  dsimp only at hNormalDerivative
  have hDerivativeExpansion :
      localNormalDerivative =
        ∑ row : Fin 4,
          (normal row • frameDerivative row tangentCoordinate +
            candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
                  period hPeriod metric variedMetric displacement parameter
                    hNonNull outer row boundary • frameCoordinate row) := by
    unfold localNormalDerivative
    rw [hNormalDerivative]
    change mvfderiv throatCoverModelWithCorners
        (candidateANormalBoundaryMetricUnitNormalField_historical period hPeriod
          metric variedMetric displacement parameter hNonNull boundary patch
            coordinate) base.1 targetVector = _
    simpa only [current, frame, sourceVector, targetVector, base, tangentCoordinate,
      normal, frameDerivative, frameCoordinate] using hLeibniz
  have hConnectionExpansion :
      connectionCoefficientSum =
        ∑ regular : Fin 4, ∑ upper : Fin 4,
          (tangent regular * normal upper) •
            candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
              period hPeriod metric variedMetric patch regular upper coordinate := by
    unfold connectionCoefficientSum
    simpa only [current, tangent, normal, frameCoordinate] using hConnection
  have hDerivativeSplit :
      localNormalDerivative =
        frameDerivativeSum + derivativeCoefficientSum := by
    rw [hDerivativeExpansion]
    unfold frameDerivativeSum derivativeCoefficientSum
    rw [Finset.sum_add_distrib]
  calc
    candidateANormalBoundaryHistoricalCovariantNormalDerivativeCoordinatesAt
          period hPeriod metric tensor variedMetric displacement parameter
            hNonNull outer boundary patch coordinate =
      derivativeCoefficientSum + connectionCoefficientSum := hHistoricalSplit
    _ = derivativeCoefficientSum +
        (∑ regular : Fin 4, ∑ upper : Fin 4,
          (tangent regular * normal upper) •
            candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
              period hPeriod metric variedMetric patch regular upper coordinate) := by
          rw [hConnectionExpansion]
    _ = derivativeCoefficientSum +
        (frameDerivativeSum +
          localLeviCivitaChristoffelApply period hPeriod variedMetric patch
            coordinate tangentCoordinate normalCoordinate) := by
          rw [hFrameExpansion]
    _ = localNormalDerivative +
        localLeviCivitaChristoffelApply period hPeriod variedMetric patch
          coordinate tangentCoordinate normalCoordinate := by
          rw [hDerivativeSplit]
          module

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
