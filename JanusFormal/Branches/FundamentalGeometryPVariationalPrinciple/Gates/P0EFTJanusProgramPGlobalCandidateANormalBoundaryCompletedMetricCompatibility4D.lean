import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothKoszulChristoffel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryNamespaceFacade4D

/-!
# Completed regular-frame metric compatibility for Candidate A

This file rewrites the local Levi-Civita compatibility theorem entirely in
terms of the completed boundary metric, Christoffel, and first-derivative
fiber evaluations used by H10.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
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

variable (period : Real) (hPeriod : period ≠ 0)

local instance completedCompatibilityCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance completedCompatibilityCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) completedCompatibilityOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) completedCompatibilityOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) completedCompatibilityEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) completedCompatibilityEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A completed Christoffel coefficient contracted with the completed metric
is exactly the varied-metric pairing of the local covariant derivative. -/
theorem candidateANormalBoundaryChristoffel_metricPairing_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (first second lower : Fin 4) :
    (∑ upper : Fin 4,
      candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
            upper first second
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) boundary *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter)
            upper lower boundary) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
          period hPeriod metric variedMetric patch first second coordinate)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let connection :=
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod metric variedMetric patch first second coordinate
  have hChristoffel (upper : Fin 4) :
      candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
          upper first second current boundary = basis.repr connection upper := by
    exact candidateANormalBoundaryChristoffel_smooth_apply period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary patch
        coordinate hAt hCurrent upper first second
  have hMetric (upper : Fin 4) :
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric current upper lower boundary =
        candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor upper lower
            (patch.coordinateMap coordinate) := by
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary upper lower]
    rw [candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried]
    rw [hAt]
  symm
  calc
    localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        connection
        (pulledRegularFrameVector period hPeriod metric patch lower coordinate) =
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
        (∑ upper : Fin 4, basis.repr connection upper • basis upper)
        (pulledRegularFrameVector period hPeriod metric patch lower
          coordinate) := by rw [basis.sum_repr]
    _ = ∑ upper : Fin 4,
        basis.repr connection upper *
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor upper lower
              (patch.coordinateMap coordinate) := by
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro upper _
      rw [map_smul]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [show basis upper = pulledRegularFrameVector period hPeriod metric
          patch upper coordinate by
        exact pulledRegularFrameBasis_apply period hPeriod metric patch
          coordinate upper]
      rw [candidateANormalBoundaryLocalMetricCoordinateForm_pulledRegularFrameVector
        period hPeriod metric tensor variedMetric hVaried]
    _ = ∑ upper : Fin 4,
        candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
              upper first second current boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric current upper lower boundary := by
      apply Finset.sum_congr rfl
      intro upper _
      rw [hChristoffel, hMetric]

/-- Metric compatibility entirely in the completed regular frame, specialized
to the same smooth moving graph. -/
theorem candidateANormalBoundaryActualMetricFirstDerivative_metricCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (derivative row column : Fin 4) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative row column
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)) =
      (∑ upper : Fin 4,
        candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
              upper derivative row
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              upper column boundary) +
      ∑ upper : Fin 4,
        candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
              upper derivative column
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              upper row boundary := by
  have hCompatibility :=
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivative_metricCompatible
      period hPeriod metric tensor variedMetric hVaried patch coordinate
        derivative row column
  have hFirst :=
    candidateANormalBoundaryChristoffel_metricPairing_smooth period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary patch
        coordinate hAt hCurrent derivative row column
  have hSecond :=
    candidateANormalBoundaryChristoffel_metricPairing_smooth period hPeriod
      metric tensor variedMetric hVaried displacement parameter boundary patch
        coordinate hAt hCurrent derivative column row
  have hSymmetry :
      localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch row coordinate)
          (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch derivative column
              coordinate) =
        localMetricCoordinateForm period hPeriod variedMetric patch coordinate
          (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
            period hPeriod metric variedMetric patch derivative column
              coordinate)
          (pulledRegularFrameVector period hPeriod metric patch row
            coordinate) := by
    rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
    exact variedMetric.tensor.symmetric _ _ _
  rw [candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth]
  rw [← hAt]
  rw [hCompatibility, hSymmetry, ← hFirst, ← hSecond]

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
