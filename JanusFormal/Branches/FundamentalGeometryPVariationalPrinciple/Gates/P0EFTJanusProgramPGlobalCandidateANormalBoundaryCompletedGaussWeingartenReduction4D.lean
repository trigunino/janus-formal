import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedMetricCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalGaussPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussWeingartenFiniteAlgebra4D

/-!
# Completed Gauss--Weingarten reduction for Candidate A

This file installs the H10 reduction from the completed raw Gauss scalar to
the corresponding historical Weingarten pairing.  The derivative of the
physical unit normal is not supplied as a new datum: it is the manifold
derivative of the already reconstructed regular-frame coefficient.

The sole remaining hypothesis is the differentiated scalar orthogonality
identity before metric compatibility is substituted.  The completed
metric-compatibility theorem rewrites that hypothesis into the finite
Gauss--Weingarten algebra, while the historical Gauss-pairing theorem
identifies its left-hand side with the completed raw unit-normal Gauss scalar.
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
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance completedGaussWeingartenCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance completedGaussWeingartenCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    completedGaussWeingartenOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussWeingartenOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    completedGaussWeingartenEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussWeingartenEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Directional derivative of one coefficient of the already reconstructed
historical physical unit normal in the installed regular frame. -/
def
    candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (boundary : CutThroatBoundary period hPeriod) : Real :=
  mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
    (candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
      period hPeriod metric variedMetric displacement parameter hNonNull row)
    boundary
    ((finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer)

/-- The exact scalar identity obtained by differentiating the historical
unit-normal orthogonality along one completed graph tangent, before replacing
the metric derivative by the completed Christoffel coefficients. -/
def candidateANormalBoundaryHistoricalDifferentiatedOrthogonalityAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) : Prop :=
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  (∑ row : Fin 4, ∑ column : Fin 4,
    (candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            outer row boundary *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column boundary *
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner column current boundary +
      candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
            period hPeriod metric variedMetric displacement parameter hNonNull
              row boundary *
        (∑ regular : Fin 4,
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric outer regular current boundary *
            regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame
                  period hPeriod metric)
                metric.metric tensor)
              regular row column
              (normalGraphOrientationDouble period hPeriod displacement
                (boundary, parameter))) *
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner column current boundary +
      candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
            period hPeriod metric variedMetric displacement parameter hNonNull
              row boundary *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column boundary *
        candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
          period hPeriod metric outer inner column current boundary)) = 0

/-- The completed regular-frame Weingarten pairing of the historical physical
unit normal with one inner graph tangent. -/
def candidateANormalBoundaryHistoricalWeingartenRegularPairingAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) : Real :=
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  (∑ row : Fin 4, ∑ column : Fin 4,
    candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            outer row boundary *
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
        period hPeriod metric current row column boundary *
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric inner column current boundary) +
    ∑ row : Fin 4, ∑ column : Fin 4,
      (∑ regular : Fin 4, ∑ upper : Fin 4,
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer regular current boundary *
          candidateANormalBoundaryChristoffelFiberEvaluation
            period hPeriod metric row regular upper current boundary *
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
            period hPeriod metric variedMetric displacement parameter hNonNull
              upper boundary) *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column boundary *
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner column current boundary

set_option backward.isDefEq.respectTransparency false in
/-- H10 reduction theorem.  Once the differentiated orthogonality identity is
available for the historical normal coefficient germ, the completed raw Gauss
scalar is exactly the completed regular-frame Weingarten pairing. -/
theorem
    candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalWeingarten_of_differentiatedOrthogonality
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
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary)
    (hDifferentiatedOrthogonality :
      candidateANormalBoundaryHistoricalDifferentiatedOrthogonalityAt
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull outer inner boundary) :
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      candidateANormalBoundaryHistoricalWeingartenRegularPairingAt period hPeriod
        metric tensor variedMetric displacement parameter hNonNull outer inner
          boundary := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  have hMetricSymmetric :
      ∀ row column : Fin 4,
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric current row column boundary =
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric current column row boundary := by
    intro row column
    rw [
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary row column,
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary column row]
    exact variedMetric.tensor.symmetric _ _ _
  have hZero :
      (∑ row : Fin 4, ∑ column : Fin 4,
        (candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
              period hPeriod metric variedMetric displacement parameter hNonNull
                outer row boundary *
            candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric current row column boundary *
            candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric inner column current boundary +
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
                period hPeriod metric variedMetric displacement parameter hNonNull
                  row boundary *
            (∑ regular : Fin 4,
              candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                    period hPeriod metric outer regular current boundary *
                ((∑ upper : Fin 4,
                    candidateANormalBoundaryChristoffelFiberEvaluation
                          period hPeriod metric upper regular row current
                            boundary *
                      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
                        period hPeriod metric current upper column boundary) +
                  ∑ upper : Fin 4,
                    candidateANormalBoundaryChristoffelFiberEvaluation
                          period hPeriod metric upper regular column current
                            boundary *
                      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
                        period hPeriod metric current upper row boundary)) *
            candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric inner column current boundary +
          candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
                period hPeriod metric variedMetric displacement parameter hNonNull
                  row boundary *
            candidateANormalBoundaryActualMetricMatrixFiberEvaluation
              period hPeriod metric current row column boundary *
            candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
              period hPeriod metric outer inner column current boundary)) = 0 := by
    unfold candidateANormalBoundaryHistoricalDifferentiatedOrthogonalityAt
      at hDifferentiatedOrthogonality
    dsimp only at hDifferentiatedOrthogonality
    simp_rw [
      candidateANormalBoundaryActualMetricFirstDerivative_metricCompatible
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary patch coordinate hAt hCurrent.1.1]
        at hDifferentiatedOrthogonality
    simpa [current] using hDifferentiatedOrthogonality
  have hAlgebra :=
    candidateANormalBoundaryGaussWeingartenFin4Algebra
      (normal := fun row =>
        candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull row
            boundary)
      (normalDerivative := fun row =>
        candidateANormalBoundaryHistoricalUnitNormalRegularFrameSpatialDerivativeCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            outer row boundary)
      (metric := fun row column =>
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column boundary)
      (outerTangent := fun regular =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric outer regular current boundary)
      (innerTangent := fun column =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner column current boundary)
      (spatialDerivative := fun column =>
        candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
          period hPeriod metric outer inner column current boundary)
      (christoffel := fun upper first second =>
        candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
          upper first second current boundary)
      hMetricSymmetric hZero
  rw [
    candidateANormalBoundaryMetricUnitGaussRaw_eq_historicalRegularPairing
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent outer inner boundary hRootNonneg]
  unfold candidateANormalBoundaryHistoricalWeingartenRegularPairingAt
  dsimp only
  unfold
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
  simp only [BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  exact hAlgebra

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
