import ScratchHessianNext
import CheckSum

namespace JanusFormal

set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance gaussCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance gaussCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) gaussOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) gaussOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) gaussEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) gaussEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- The completed raw Gauss scalar uses the coefficients of the historical
physical unit normal in the same installed regular frame. -/
theorem gauss_candidateANormalBoundaryMetricUnitGaussRaw_eq_regularPairing
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
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary)
    :
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      -(∑ row : Fin 4, ∑ column : Fin 4,
        test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
              period hPeriod metric variedMetric displacement parameter
                hNonNull row boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              row column boundary *
          candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer inner column
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary) := by
  classical
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let normal := ∑ row : Fin 4,
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            row boundary •
      metric.frame row point
  have hNormal : normal =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
    simpa [normal, point] using
      test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient_reconstructs
        period hPeriod metric variedMetric displacement parameter hNonNull
          boundary
  have hExpansion :
      variedMetric.tensor.tensor
          (normalGraphOrientationDouble period hPeriod displacement
            (boundary, parameter)) normal
          (test_candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
            period hPeriod metric tensor displacement parameter outer inner
              boundary) =
        ∑ row : Fin 4, ∑ column : Fin 4,
          test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
                period hPeriod metric variedMetric displacement parameter
                  hNonNull row boundary *
            candidateANormalBoundaryActualMetricMatrixFiberEvaluation
                period hPeriod metric
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter)
                row column boundary *
            candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
                period hPeriod metric outer inner column
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter) boundary := by
    unfold normal test_candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
      point
    rw [variedMetric.tensor.symmetric point]
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro row _
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro column _
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary]
    rw [variedMetric.tensor.symmetric]
    ring
  rw [test_candidateANormalBoundaryMetricUnitGaussRaw_smooth_eq_vector
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      outer inner boundary]
  rw [test_candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_historical
    period hPeriod metric hTransverse tensor variedMetric hVaried displacement
      parameter boundary hCurrent hNonNull hRootNonneg]
  rw [← hNormal]
  exact congrArg Neg.neg hExpansion

set_option backward.isDefEq.respectTransparency false in
/-- The candidate Gauss scalar is the regular-frame Weingarten pairing
obtained by differentiating the already proved physical orthogonality. -/
theorem gauss_candidateANormalBoundaryMetricUnitGaussRaw_eq_regularWeingarten
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
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary outer
    let normal := fun row : Fin 4 =>
      test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
        period hPeriod metric variedMetric displacement parameter hNonNull row
    let actual := fun row column : Fin 4 =>
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
        period hPeriod metric current row column boundary
    let outerTangent := fun regular : Fin 4 =>
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric outer regular current boundary
    let innerTangent := fun column : Fin 4 =>
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric inner column current boundary
    let christoffel := fun upper first second : Fin 4 =>
      candidateANormalBoundaryChristoffelFiberEvaluation
        period hPeriod metric upper first second current boundary
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner current boundary =
      (∑ row : Fin 4, ∑ column : Fin 4,
        mvfderiv throatCoverModelWithCorners (normal row) boundary vector *
          actual row column * innerTangent column) +
      ∑ row : Fin 4, ∑ column : Fin 4,
        (∑ regular : Fin 4, ∑ upper : Fin 4,
          outerTangent regular * christoffel row regular upper *
            normal upper boundary) * actual row column * innerTangent column := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  let normal := fun row : Fin 4 =>
    test_normalGraphCanonicalMetricUnitNormalRegularFrameCoefficient
      period hPeriod metric variedMetric displacement parameter hNonNull row
  let normalDerivative := fun row : Fin 4 =>
    mvfderiv throatCoverModelWithCorners (normal row) boundary vector
  let actual := fun row column : Fin 4 =>
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation
      period hPeriod metric current row column boundary
  let outerTangent := fun regular : Fin 4 =>
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
      period hPeriod metric outer regular current boundary
  let innerTangent := fun column : Fin 4 =>
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
      period hPeriod metric inner column current boundary
  let spatialDerivative := fun column : Fin 4 =>
    candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
      period hPeriod metric outer inner column current boundary
  let christoffel := fun upper first second : Fin 4 =>
    candidateANormalBoundaryChristoffelFiberEvaluation
      period hPeriod metric upper first second current boundary
  have hMetricSymmetric (row column : Fin 4) :
      actual row column = actual column row := by
    unfold actual current
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary]
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary]
    exact variedMetric.tensor.symmetric _ _ _
  have hDerivative :=
    next_candidateANormalBoundaryMetricUnitNormalGraphTangent_derivative_zero
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent hRootNonneg boundary outer inner
  have hCompatibility (regular row column : Fin 4) :=
    next_candidateANormalBoundaryActualMetricFirstDerivative_metricCompatible
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary patch coordinate hAt hCurrent.1.1 regular row column
  simp_rw [hCompatibility] at hDerivative
  have hZero :
      (∑ row : Fin 4, ∑ column : Fin 4,
        (normalDerivative row * actual row column * innerTangent column +
          normal row boundary *
            (∑ regular : Fin 4, outerTangent regular *
              ((∑ upper : Fin 4,
                  christoffel upper regular row * actual upper column) +
                ∑ upper : Fin 4,
                  christoffel upper regular column * actual upper row)) *
              innerTangent column +
          normal row boundary * actual row column *
            spatialDerivative column)) = 0 := by
    simpa only [current, vector, normal, normalDerivative, actual,
      outerTangent, innerTangent, spatialDerivative, christoffel] using
        hDerivative
  have hAlgebra := scratch_gauss_weingarten_fin4_algebra
    (fun row => normal row boundary) normalDerivative actual outerTangent
      innerTangent spatialDerivative christoffel hMetricSymmetric hZero
  rw [gauss_candidateANormalBoundaryMetricUnitGaussRaw_eq_regularPairing
    period hPeriod metric hTransverse tensor variedMetric hVaried displacement
      parameter hNonNull hCurrent outer inner boundary (hRootNonneg boundary)]
  simpa only [current, vector, normal, normalDerivative, actual,
    outerTangent, innerTangent, spatialDerivative, christoffel,
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply, ContinuousMap.add_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply] using hAlgebra

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end
end JanusFormal
