import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothOrthogonality4D

/-!
# Differentiated graph-normal orthogonality for Candidate A

This file differentiates the already proved pointwise regular-frame
orthogonality on the smooth admissible core.  Every derivative is rewritten
in terms of the completed metric and graph jets, except for the derivative of
the historical physical normal, which is the intended H10 Gauss datum.
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

local instance differentiatedOrthogonalityCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance differentiatedOrthogonalityCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) differentiatedOrthogonalityOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) differentiatedOrthogonalityOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

private theorem candidateANormalBoundary_mvfderiv_finset_sum_apply
    {index : Type*} [DecidableEq index]
    (indices : Finset index)
    (functions : index → CutThroatBoundary period hPeriod → Real)
    (hFunctions : ∀ current, ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (functions current))
    (point : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    mvfderiv throatCoverModelWithCorners
        (fun current => ∑ currentIndex ∈ indices,
          functions currentIndex current) point vector =
      ∑ currentIndex ∈ indices,
        mvfderiv throatCoverModelWithCorners
          (functions currentIndex) point vector := by
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [mvfderiv_const]
      rfl
  | @insert currentIndex indices hNotMem inductionHypothesis =>
      have hCurrent : MDifferentiableAt throatCoverModelWithCorners
          (modelWithCornersSelf Real Real) (functions currentIndex) point :=
        (hFunctions currentIndex).mdifferentiableAt (by simp)
      have hSum : MDifferentiableAt throatCoverModelWithCorners
          (modelWithCornersSelf Real Real)
          (fun current => ∑ index ∈ indices, functions index current) point := by
        exact (ContMDiff.sum fun index _ => hFunctions index)
          |>.mdifferentiableAt (by simp)
      have hAdd := congrArg (fun derivative => derivative vector)
        (mvfderiv_add hCurrent hSum)
      simp only [Finset.sum_insert hNotMem]
      rw [show mvfderiv throatCoverModelWithCorners
            (fun current => functions currentIndex current +
              ∑ index ∈ indices, functions index current) point vector =
          mvfderiv throatCoverModelWithCorners
              (functions currentIndex) point vector +
            mvfderiv throatCoverModelWithCorners
              (fun current => ∑ index ∈ indices, functions index current)
                point vector by
          change mvfderiv throatCoverModelWithCorners
              (functions currentIndex +
                fun current => ∑ index ∈ indices, functions index current)
                point vector = _
          simpa only [add_apply] using hAdd]
      rw [inductionHypothesis]

set_option backward.isDefEq.respectTransparency false in
/-- Differentiated regular-frame orthogonality on the smooth admissible core.
The remaining normal derivative is exactly the historical physical-normal
coefficient derivative. -/
theorem candidateANormalBoundaryMetricUnitNormalGraphTangent_derivative_zero
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
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary outer
    let normal := fun row : Fin 4 =>
      candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
        period hPeriod metric variedMetric displacement parameter hNonNull row
    let actual := fun row column : Fin 4 => fun point =>
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
        period hPeriod metric current row column point
    let tangent := fun column : Fin 4 => fun point =>
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric inner column current point
    (∑ row : Fin 4, ∑ column : Fin 4,
      (mvfderiv throatCoverModelWithCorners (normal row) boundary vector *
          actual row column boundary * tangent column boundary +
        normal row boundary *
          (∑ regular : Fin 4,
            candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                  period hPeriod metric outer regular current boundary *
              regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
                (smoothToGeneralMetricRelativeC2Core period hPeriod
                  (regularGeneralLorentzMetricSmoothD8Frame period hPeriod
                    metric) metric.metric tensor)
                regular row column
                (normalGraphOrientationDouble period hPeriod displacement
                  (boundary, parameter))) *
            tangent column boundary +
        normal row boundary * actual row column boundary *
          candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
            period hPeriod metric outer inner column current boundary)) = 0 := by
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
    candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
      period hPeriod metric variedMetric displacement parameter hNonNull row
  let actual := fun row column : Fin 4 => fun point =>
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation
      period hPeriod metric current row column point
  let tangent := fun column : Fin 4 => fun point =>
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
      period hPeriod metric inner column current point
  let summand := fun row column : Fin 4 => fun point =>
    normal row point * actual row column point * tangent column point
  have hNormal (row : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (normal row) :=
    candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient_contMDiff
      period hPeriod metric variedMetric displacement parameter hNonNull row
  have hActual (row column : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (actual row column) := by
    simpa [actual, current] using
      (candidateANormalBoundaryActualMetricMatrix_smooth period hPeriod
        metric tensor displacement parameter row column)
  have hTangent (column : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (tangent column) := by
    simpa [tangent, current] using
      (candidateANormalBoundaryGraphTangentRegularFrameCoefficient_smooth
        period hPeriod metric tensor displacement parameter inner column)
  have hSummand (row column : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (summand row column) :=
    ((hNormal row).mul (hActual row column)).mul (hTangent column)
  have hOrthogonal :
      (fun point : CutThroatBoundary period hPeriod =>
        ∑ row : Fin 4, ∑ column : Fin 4, summand row column point) =
        fun _ => 0 := by
    funext point
    unfold summand normal actual tangent current
    exact
      candidateANormalBoundaryMetricUnitNormalGraphTangent_orthogonal_smooth
        period hPeriod metric hTransverse tensor variedMetric hVaried displacement
          parameter hNonNull hCurrent point inner (hRootNonneg point)
  have hSummandDerivative (row column : Fin 4) :
      mvfderiv throatCoverModelWithCorners (summand row column) boundary vector =
        mvfderiv throatCoverModelWithCorners (normal row) boundary vector *
              actual row column boundary * tangent column boundary +
          normal row boundary *
              mvfderiv throatCoverModelWithCorners (actual row column) boundary
                vector * tangent column boundary +
          normal row boundary * actual row column boundary *
              mvfderiv throatCoverModelWithCorners (tangent column) boundary
                vector := by
    have hFirst := congrArg (fun derivative => derivative vector)
      (mvfderiv_mul
        ((hNormal row).mdifferentiableAt (by simp))
        ((hActual row column).mdifferentiableAt (by simp)))
    have hSecond := congrArg (fun derivative => derivative vector)
      (mvfderiv_mul
        (((hNormal row).mul (hActual row column)).mdifferentiableAt (by simp))
        ((hTangent column).mdifferentiableAt (by simp)))
    change mvfderiv throatCoverModelWithCorners
        (normal row * actual row column) boundary vector = _ at hFirst
    change mvfderiv throatCoverModelWithCorners (summand row column)
        boundary vector = _ at hSecond
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
      at hFirst hSecond
    rw [hFirst] at hSecond
    rw [hSecond]
    ring
  have hInnerDerivative (row : Fin 4) :
      mvfderiv throatCoverModelWithCorners
          (fun point => ∑ column : Fin 4, summand row column point)
          boundary vector =
        ∑ column : Fin 4,
          mvfderiv throatCoverModelWithCorners (summand row column)
            boundary vector :=
    candidateANormalBoundary_mvfderiv_finset_sum_apply period hPeriod
      Finset.univ (summand row) (hSummand row) boundary vector
  have hOuterSmooth (row : Fin 4) : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point => ∑ column : Fin 4, summand row column point) :=
    ContMDiff.sum fun column _ => hSummand row column
  have hOuterDerivative :
      mvfderiv throatCoverModelWithCorners
          (fun point => ∑ row : Fin 4, ∑ column : Fin 4,
            summand row column point) boundary vector =
        ∑ row : Fin 4,
          mvfderiv throatCoverModelWithCorners
            (fun point => ∑ column : Fin 4, summand row column point)
              boundary vector :=
    candidateANormalBoundary_mvfderiv_finset_sum_apply period hPeriod
      Finset.univ _ hOuterSmooth boundary vector
  have hDerivativeZero := congrArg
    (fun function => mvfderiv throatCoverModelWithCorners function boundary
      vector) hOrthogonal
  have hZero : mvfderiv throatCoverModelWithCorners
      (fun _ : CutThroatBoundary period hPeriod => (0 : Real)) boundary vector =
      0 := by
    rw [mvfderiv_const]
    rfl
  rw [hOuterDerivative] at hDerivativeZero
  simp_rw [hInnerDerivative] at hDerivativeZero
  rw [hZero] at hDerivativeZero
  simp_rw [hSummandDerivative] at hDerivativeZero
  have hActualDerivative (row column : Fin 4) :
      mvfderiv throatCoverModelWithCorners (actual row column) boundary vector =
        ∑ regular : Fin 4,
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric outer regular current boundary *
            regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              regular row column
              (normalGraphOrientationDouble period hPeriod displacement
                (boundary, parameter)) := by
    unfold actual vector current
    exact candidateANormalBoundaryActualMetricMatrix_mvfderiv_smooth period
      hPeriod metric tensor displacement parameter boundary outer row column
  have hTangentDerivative (column : Fin 4) :
      mvfderiv throatCoverModelWithCorners (tangent column) boundary vector =
        candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
          period hPeriod metric outer inner column current boundary := by
    unfold tangent vector current
    exact
      candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivative_smooth
        period hPeriod metric tensor displacement parameter boundary outer inner
          column |>.symm
  simp_rw [hActualDerivative, hTangentDerivative] at hDerivativeZero
  unfold vector normal actual tangent at hDerivativeZero
  simp only [current] at hDerivativeZero
  convert hDerivativeZero using 1 <;> ring

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
