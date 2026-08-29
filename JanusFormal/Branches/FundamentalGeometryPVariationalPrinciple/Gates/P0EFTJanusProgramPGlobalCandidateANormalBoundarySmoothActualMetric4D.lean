import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothGraphTangent4D

/-!
# Smooth actual-metric coefficient bridge for Candidate A

This file promotes the smooth finite-matrix representative of the varied
regular metric and proves smoothness of every completed actual-metric
coefficient along the mobile boundary graph.  It adds no metric choice: the
matrix is the existing regular-frame metric multiplied by the existing
relative endomorphism.
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

local instance smoothActualMetricCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance smoothActualMetricCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) smoothActualMetricOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) smoothActualMetricOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) smoothActualMetricEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) smoothActualMetricEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Existing smooth relative endomorphism, viewed as a finite smooth matrix in
the regular frame. -/
def candidateANormalBoundarySmoothRegularGeneralMetricRelativeMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothFiniteMatrix period hPeriod 4 := by
  simpa using
    (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor)

/-- Smooth regular-frame matrix of the varied metric. -/
def candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :=
  smoothFiniteMatrixProduct period hPeriod 4
    (regularFrameMetricMatrix period hPeriod metric)
    (smoothFiniteMatrixIdentity period hPeriod 4 +
      candidateANormalBoundarySmoothRegularGeneralMetricRelativeMatrix
        period hPeriod metric tensor)

/-- The installed C² actual-metric matrix is the C² image of the smooth
regular-frame matrix above. -/
theorem candidateANormalBoundaryRegularGeneralMetricC2MetricMatrix_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2MetricMatrix period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor) := by
  unfold regularGeneralMetricC2MetricMatrix
    generalMetricRelativeC2ExtendedMatrix
    regularFrameMetricC2Matrix
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
    smoothToGeneralMetricRelativeC2Core
    smoothGeneralMetricRelativeEndomorphismToC2
  change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      (smoothFiniteMatrixToC2 period hPeriod 4
        (regularFrameMetricMatrix period hPeriod metric))
      (c2FiniteMatrixIdentity period hPeriod 4 +
        smoothFiniteMatrixToC2 period hPeriod 4
          (candidateANormalBoundarySmoothRegularGeneralMetricRelativeMatrix
            period hPeriod metric tensor)) = _
  rw [show c2FiniteMatrixIdentity period hPeriod 4 +
        smoothFiniteMatrixToC2 period hPeriod 4
          (candidateANormalBoundarySmoothRegularGeneralMetricRelativeMatrix
            period hPeriod metric tensor) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothFiniteMatrixIdentity period hPeriod 4 +
          candidateANormalBoundarySmoothRegularGeneralMetricRelativeMatrix
            period hPeriod metric tensor) by
      rw [map_add]
      rfl]
  exact c2FiniteMatrixProduct_smooth period hPeriod 4 _ _

/-- Pointwise coefficient form of the smooth C²-matrix identity. -/
theorem candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    regularGeneralMetricC0MetricCoefficient period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        row column point =
      candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor row column point := by
  unfold regularGeneralMetricC0MetricCoefficient
  rw [candidateANormalBoundaryRegularGeneralMetricC2MetricMatrix_smooth]
  rfl

/-- Global fidelity of the smooth relative-metric chart: the installed
coefficient is exactly the background metric plus the smooth symmetric
variation in the regular frame. -/
theorem candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    regularGeneralMetricC0MetricCoefficient period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        row column point =
      metric.metric.tensor.tensor point (metric.frame row point)
          (metric.frame column point) +
        tensor.tensor point (metric.frame row point)
          (metric.frame column point) := by
  classical
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  let raised := inverseMetricSharp period hPeriod metric.metric point
    (tensor.tensor point (metric.frame column point))
  have hCoefficient (middle : Fin 4) :
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
          metric.metric tensor middle column point =
        generalMetricFiniteFrameCoefficientAt period hPeriod frame
          metric.metric point middle raised := by
    rfl
  have hReconstruct := generalMetricFiniteFrameCoefficientAt_reconstructs
    period hPeriod frame metric.metric point raised
  have hRaised : raised = ∑ middle : Fin 4,
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
          metric.metric tensor middle column point •
        metric.frame middle point := by
    calc
      raised = ∑ middle : Fin 4,
          generalMetricFiniteFrameCoefficientAt period hPeriod frame
              metric.metric point middle raised • metric.frame middle point :=
        hReconstruct
      _ = _ := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [hCoefficient]
  have hPair :
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
            metric.metric tensor middle column point =
        metric.metric.tensor.tensor point (metric.frame row point) raised := by
    calc
      _ = ∑ middle : Fin 4,
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
              metric.metric tensor middle column point *
            regularFrameMetricMatrix period hPeriod metric row middle point := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [mul_comm]
      _ = metric.metric.tensor.tensor point (metric.frame row point)
          (∑ middle : Fin 4,
            smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
                metric.metric tensor middle column point •
              metric.frame middle point) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul, regularFrameMetricMatrix_apply]
      _ = _ := congrArg
        (fun vector => metric.metric.tensor.tensor point
          (metric.frame row point) vector) hRaised.symm
  have hFlat := congrArg
    (fun covector => covector (metric.frame row point))
    (metric_flat_inverseMetricSharp period hPeriod metric.metric point
      (tensor.tensor point (metric.frame column point)))
  have hPairRaised :
      metric.metric.tensor.tensor point (metric.frame row point) raised =
        tensor.tensor point (metric.frame row point)
          (metric.frame column point) := by
    calc
      metric.metric.tensor.tensor point (metric.frame row point) raised =
          metric.metric.tensor.tensor point raised (metric.frame row point) :=
        metric.metric.tensor.symmetric _ _ _
      _ = tensor.tensor point (metric.frame column point)
          (metric.frame row point) := by
        rw [← metric.metric.musical_eq_tensor point]
        exact hFlat
      _ = _ := tensor.symmetric _ _ _
  have hBase :
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          (1 : Matrix (Fin 4) (Fin 4) Real) middle column =
        regularFrameMetricMatrix period hPeriod metric row column point := by
    let base : Matrix (Fin 4) (Fin 4) Real := fun first second =>
      regularFrameMetricMatrix period hPeriod metric first second point
    exact congrFun (congrFun (Matrix.mul_one base) row) column
  rw [regularGeneralMetricC0MetricCoefficient_apply_expansion]
  change (∑ middle : Fin 4,
      regularFrameMetricMatrix period hPeriod metric row middle point *
        ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame
            metric.metric tensor middle column point)) = _
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hBase, hPair, hPairRaised,
    regularFrameMetricMatrix_apply]

/-- Evaluation of the smooth actual-metric matrix against the genuine varied
metric represented by the same tensor. -/
theorem candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (row column : Fin 4)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor row column point =
      variedMetric.tensor.tensor point (metric.frame row point)
        (metric.frame column point) := by
  rw [← candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
    period hPeriod metric tensor row column point]
  rw [candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth
    period hPeriod metric tensor row column point]
  change _ = variedMetric.tensor.tensor point (metric.frame row point)
    (metric.frame column point)
  rw [hVaried]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Smooth-core boundary regularity of each completed actual-metric
coefficient. -/
theorem candidateANormalBoundaryActualMetricMatrix_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (row column : Fin 4) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) row column point) := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let graph : CutThroatBoundary period hPeriod →
      MappingTorus (reflectedSphereData period hPeriod) := fun point =>
    normalGraphOrientationDouble period hPeriod displacement (point, parameter)
  let field := candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
    period hPeriod metric tensor row column
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
  rw [hFunction]
  exact field.contMDiff_toFun.comp
    ((normalGraphOrientationDouble_contMDiff period hPeriod displacement).comp
      (contMDiff_id.prodMk contMDiff_const))

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
