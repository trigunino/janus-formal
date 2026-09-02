import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D

/-!
# Exact bulk/GHY Hessian split

The genuine second Frechet derivative of the combined action is decomposed
into the Einstein--Maxwell pullback Hessian and the completed GHY Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYHessianSplit4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartActions4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance regularGeneralMetricC2CoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (RegularGeneralMetricC2Core period hPeriod metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric).normedAddCommGroup

local instance regularGeneralMetricC2CoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (RegularGeneralMetricC2Core period hPeriod metric) :=
  Submodule.normedSpace
    (generalMetricRelativeC2CoreSubmodule period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric)

local instance regularMetricBoundaryC3CoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  regularGeneralMetricBoundaryC3CoreNormedAddCommGroup
    period hPeriod metric

local instance regularMetricBoundaryC3CoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  regularGeneralMetricBoundaryC3CoreNormedSpace period hPeriod metric

local instance candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance candidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod metric

/-- Einstein--Maxwell bulk action pulled back to the boundary-enhanced current
through its canonical metric `C²` projection. -/
def candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) : Real :=
  regularGeneralMetricC2LorentzEinsteinMaxwellAction period hPeriod metric
    measure couplings first second
      (candidateANormalBoundaryMetricC2Projection period hPeriod metric current)

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
        period hPeriod metric measure couplings first second)
      (candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric) :=
  (regularGeneralMetricC2LorentzEinsteinMaxwellAction_contDiffOn_two
    period hPeriod metric measure couplings first second).comp
      (candidateANormalBoundaryMetricC2Projection
        period hPeriod metric).contDiff.contDiffOn
      (fun _current hCurrent =>
        candidateANormalBoundaryMetricC2Projection_mem_lorentzChart
          period hPeriod metric hCurrent)

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction_contDiffAt_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffAt Real 2
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
        period hPeriod metric measure couplings first second) 0 :=
  (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction_contDiffOn_two
      period hPeriod metric measure couplings first second).contDiffAt
    ((candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
      period hPeriod metric).mem_nhds
        (zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric hTransverse))

def candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real
      →L[Real]
      (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real
        →L[Real] Real) :=
  fderiv Real
    (fderiv Real
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
        period hPeriod metric measure couplings first second)) 0

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (firstDirection secondDirection : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
          period hPeriod metric measure couplings first second
          firstDirection secondDirection =
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
          period hPeriod metric measure couplings first second
          secondDirection firstDirection := by
  have hSmooth : minSmoothness Real 2 ≤ (2 : ℕ∞ω) := by
    simp [minSmoothness_of_isRCLikeNormedField]
  exact
    (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction_contDiffAt_two
      period hPeriod metric measure couplings first second hTransverse).isSymmSndFDerivAt
        hSmooth firstDirection secondDirection

/-- Exact additivity of the genuine combined Hessian. -/
theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian_eq_bulk_add_boundary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
        period hPeriod metric measure couplings first second einsteinScale =
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
          period hPeriod metric measure couplings first second +
        candidateANormalBoundaryTwoSheetGHYActionHessian
          period hPeriod einsteinScale metric := by
  let bulk :=
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
      period hPeriod metric measure couplings first second
  let boundary :=
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
      period hPeriod einsteinScale metric
  have hBulk : ContDiffAt Real 2 bulk 0 :=
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction_contDiffAt_two
      period hPeriod metric measure couplings first second hTransverse
  have hBoundary : ContDiffAt Real 2 boundary 0 :=
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffAt_two
      period hPeriod einsteinScale metric hTransverse
  have hGradient :
      fderiv Real (fun current => bulk current + boundary current) =ᶠ[𝓝 0]
        fun current => fderiv Real bulk current + fderiv Real boundary current := by
    filter_upwards [hBulk.eventually (by norm_num),
      hBoundary.eventually (by norm_num)] with current hBulkAt hBoundaryAt
    exact fderiv_add
      (hBulkAt.differentiableAt (by norm_num))
      (hBoundaryAt.differentiableAt (by norm_num))
  have hBulkGradient : DifferentiableAt Real (fderiv Real bulk) 0 :=
    (hBulk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hBoundaryGradient : DifferentiableAt Real (fderiv Real boundary) 0 :=
    (hBoundary.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  change fderiv Real
      (fderiv Real (fun current => bulk current + boundary current)) 0 =
    fderiv Real (fderiv Real bulk) 0 +
      fderiv Real (fderiv Real boundary) 0
  rw [hGradient.fderiv_eq]
  exact fderiv_add hBulkGradient hBoundaryGradient

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian_apply_eq_bulk_add_boundary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (firstDirection secondDirection : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
          period hPeriod metric measure couplings first second einsteinScale
          firstDirection secondDirection =
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
            period hPeriod metric measure couplings first second
            firstDirection secondDirection +
        candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
          einsteinScale metric firstDirection secondDirection := by
  have hSplit := congrArg
    (fun hessian => hessian firstDirection secondDirection)
    (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian_eq_bulk_add_boundary
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse)
  simpa using hSplit

/-- Gate marker for the exact bulk/boundary Hessian decomposition. -/
theorem global_candidateA_normal_boundary_c2_lorentz_positive_einstein_maxwell_ghy_hessian_split_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
        period hPeriod metric measure couplings first second einsteinScale =
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
          period hPeriod metric measure couplings first second +
        candidateANormalBoundaryTwoSheetGHYActionHessian
          period hPeriod einsteinScale metric :=
  candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian_eq_bulk_add_boundary
    period hPeriod metric measure couplings first second einsteinScale
      hTransverse

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYHessianSplit4D
end JanusFormal
