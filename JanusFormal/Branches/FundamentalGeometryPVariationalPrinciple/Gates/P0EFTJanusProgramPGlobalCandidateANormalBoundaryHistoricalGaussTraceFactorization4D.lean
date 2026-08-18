import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalGaussActionIdentification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatFiniteFrameInverseTraceAlgebra4D

/-!
# Intrinsic factorization of the H10 historical trace

This gate removes the coefficient-space inverse from the final H10 trace
problem.  The residual geometric witness is the intrinsic factorization

`g₀⁻¹ K = (g₀⁻¹ h) ∘ (h⁻¹ K)`.

Once the historical matrix is the redundant encoding of the left-hand side
and the intrinsic trace of `h⁻¹ K` is the already constructed holonomic local
mean curvature, the faithful inverse lift cancels algebraically.  The result
is the local and hence chart-free trace agreement consumed by the action
identification gate.
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
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance historicalGaussTraceCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance historicalGaussTraceCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalGaussTraceOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussTraceOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalGaussTraceEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussTraceEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Intrinsic operator witness for the final historical trace.  The target
operator is the actual shape operator `h⁻¹K`; its composition with the
relative induced metric is the reference-raised form encoded by the
historical redundant matrix. -/
def CandidateANormalBoundaryHistoricalIntrinsicTraceFactorization
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
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
      variedMetric displacement parameter boundary
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt
    ∃ shape : TangentSpace throatCoverModelWithCorners boundary →ₗ[Real]
        TangentSpace throatCoverModelWithCorners boundary,
      candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
          period hPeriod metric tensor variedMetric displacement parameter
            hNonNull boundary =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary (relative.toLinearMap.comp shape) ∧
      LinearMap.trace Real
          (TangentSpace throatCoverModelWithCorners boundary) shape =
        normalGraphCanonicalHolonomicLocalMeanCurvatureFamily period hPeriod
          variedMetric displacement base patch coordinate ambient base

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic factorization discharges all redundant-frame inverse algebra
and produces the exact fixed-chart trace agreement. -/
theorem candidateANormalBoundaryHistoricalLocalTraceAgreement_of_intrinsicFactorization
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
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hFactorization :
      CandidateANormalBoundaryHistoricalIntrinsicTraceFactorization period
        hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalLocalTraceAgreement period hPeriod metric
      tensor variedMetric displacement parameter hNonNull := by
  intro boundary patch coordinate hAt
  unfold CandidateANormalBoundaryHistoricalIntrinsicTraceFactorization at hFactorization
  have hFactorizationAt := hFactorization boundary patch coordinate hAt
  dsimp only at hFactorizationAt
  rcases hFactorizationAt with ⟨shape, hHistorical, hShapeTrace⟩
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
    variedMetric displacement parameter boundary
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let inverseMatrix : Matrix (NormalBoundaryTangentIndex period hPeriod)
      (NormalBoundaryTangentIndex period hPeriod) Real :=
    fun row column =>
      candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
        period hPeriod metric current row column boundary
  have hLift :
      (fun row column =>
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation period hPeriod
          metric current row column boundary) =
        intrinsicThroatFiniteFrameLiftAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary relative.toLinearMap := by
    ext row column
    simpa [current, frame, relative] using
      (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_smooth_apply
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary row column)
  have hInverseField :=
    candidateANormalBoundaryInducedRelativeLift_inverse_mul period hPeriod
      metric current hCurrent
  have hInverseAtCandidate :
      normalBoundaryRealMatrixMul period hPeriod inverseMatrix
          (fun row column =>
            candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
              period hPeriod metric current row column boundary) = 1 := by
    ext row column
    have hEntry := congrArg
      (fun field : BoundedContinuousFunction
          (CutThroatBoundary period hPeriod) Real => field boundary)
      (congrFun (congrFun hInverseField row) column)
    by_cases hRowColumn : row = column <;>
      simpa [inverseMatrix, normalBoundaryRealMatrixMul, Matrix.mul_apply,
        Matrix.one_apply, hRowColumn] using hEntry
  have hInverseAt :
      normalBoundaryRealMatrixMul period hPeriod inverseMatrix
          (intrinsicThroatFiniteFrameLiftAt
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            frame boundary relative.toLinearMap) = 1 := by
    simpa [hLift] using hInverseAtCandidate
  letI : FiniteDimensional Real
      (TangentSpace throatCoverModelWithCorners boundary) := by
    change FiniteDimensional Real ThroatCoverCoordinates
    infer_instance
  have hCancel :=
    redundantFiniteFrame_leftInverse_trace_encoding_of_factorization
      (analysis := intrinsicThroatFiniteFrameAnalysisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        frame boundary)
      (synthesis := intrinsicThroatFiniteFrameSynthesisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        frame boundary)
      (hReconstruct := intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        frame boundary)
      (first := relative.toLinearMap)
      (source := relative.toLinearMap.comp shape)
      (target := shape)
      (inverseMatrix := inverseMatrix)
      hInverseAt rfl
  unfold candidateANormalBoundaryHistoricalWeingartenMeanCurvatureAt
  dsimp only
  unfold normalBoundaryRealMatrixMul
  change Matrix.trace
      (inverseMatrix *
        candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
          period hPeriod metric tensor variedMetric displacement parameter
            hNonNull boundary) = _
  rw [hHistorical]
  exact hCancel.trans hShapeTrace

/-- Chart-free consequence of the intrinsic shape-operator factorization. -/
theorem candidateANormalBoundaryHistoricalGaussTraceAgreement_of_intrinsicFactorization
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
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hFactorization :
      CandidateANormalBoundaryHistoricalIntrinsicTraceFactorization period
        hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalGaussTraceAgreement period hPeriod metric
      tensor variedMetric displacement parameter hNonNull :=
  candidateANormalBoundaryHistoricalGaussTraceAgreement_of_local period hPeriod
    metric tensor variedMetric displacement parameter hNonNull
      (candidateANormalBoundaryHistoricalLocalTraceAgreement_of_intrinsicFactorization
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          hNonNull hCurrent hFactorization)

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
