import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothActualMetric4D

/-!
# Smooth directional derivative of the Candidate-A actual metric

The completed boundary matrix derivative is identified with the directional
derivative of the already installed smooth varied-metric matrix along a graph
tangent.  No connection or metric is introduced here.
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

local instance smoothActualMetricDerivativeCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance smoothActualMetricDerivativeCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) smoothActualMetricDerivativeOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) smoothActualMetricDerivativeOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) smoothActualMetricDerivativeEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) smoothActualMetricDerivativeEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- For real-valued functions, the specialized `mvfderiv` notation is the
same manifold derivative used by the generic API. -/
theorem candidateANormalBoundary_mvfderiv_real_eq_mfderiv
    (field : CutThroatBoundary period hPeriod → Real)
    (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mvfderiv throatCoverModelWithCorners field boundary vector =
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        field boundary vector := by
  rfl

/-- The first derivative stored in the regular C² metric core is the frame
derivative of the promoted smooth actual-metric matrix. -/
theorem candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative row column point =
      frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor row column) point derivative := by
  unfold regularGeneralMetricC0MetricFirstDerivative
  rw [candidateANormalBoundaryRegularGeneralMetricC2MetricMatrix_smooth]
  exact regularFrameC2FirstDerivative_smooth period hPeriod metric derivative
    (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
      period hPeriod metric tensor row column) point

set_option backward.isDefEq.respectTransparency false in
/-- Directional derivative of a completed actual-metric coefficient along a
completed graph generator. -/
theorem candidateANormalBoundaryActualMetricMatrix_mvfderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer : NormalBoundaryTangentIndex period hPeriod)
    (row column : Fin 4) :
    mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) row column point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) =
      ∑ regular : Fin 4,
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer regular
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter) boundary *
          regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            regular row column
            (normalGraphOrientationDouble period hPeriod displacement
              (boundary, parameter)) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let graph : CutThroatBoundary period hPeriod →
      MappingTorus (reflectedSphereData period hPeriod) := fun point =>
    normalGraphOrientationDouble period hPeriod displacement (point, parameter)
  let field := candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
    period hPeriod metric tensor row column
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  have hFunction :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column point) = field ∘ graph := by
    funext point
    unfold field graph current
    rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_existing]
    change regularGeneralMetricC0MetricCoefficient period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        row column
        (normalBoundaryC2Graph period hPeriod
          (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod
            displacement) parameter point) = _
    rw [normalBoundaryC2Graph_smooth]
    exact
      candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
        period hPeriod metric tensor row column _
  have hGraphSmooth : ContMDiff throatCoverModelWithCorners
      coverModelWithCorners ∞ graph := by
    exact (normalGraphOrientationDouble_contMDiff period hPeriod displacement).comp
      (contMDiff_id.prodMk contMDiff_const)
  have hComp := mfderiv_comp_apply boundary
    (field.contMDiff_toFun.mdifferentiableAt (by simp))
    (hGraphSmooth.mdifferentiableAt (by simp)) vector
  have hTangent := candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary outer
  change mvfderiv throatCoverModelWithCorners
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column point) boundary vector = _
  rw [hFunction, candidateANormalBoundary_mvfderiv_real_eq_mfderiv, hComp]
  change mfderiv coverModelWithCorners (modelWithCornersSelf Real Real)
      field.toFun (graph boundary)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary
          vector) = _
  change (∑ regular : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric outer regular current boundary •
        metric.frame regular (graph boundary)) =
    mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary
      vector at hTangent
  rw [← hTangent, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro regular _
  change _ * mvfderiv coverModelWithCorners field.toFun (graph boundary)
      ((regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric).vectorAt
        (graph boundary) regular) = _
  rw [← frameDerivative_eq_mfderiv]
  unfold field graph current
  rw [candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth]

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
