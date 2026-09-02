import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYHessianSplit4D

/-!
# Exact bulk/GHY Euler split

The genuine first Frechet derivative of the combined action is decomposed on
the whole positive Candidate-A domain.  Its derivative at the physical origin
recovers the exact Hessian split.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYEulerSplit4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory Set
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
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYHessianSplit4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev Current
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real

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

/-- Genuine Euler covector of the combined bulk--boundary action. -/
def candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (current : Current period hPeriod metric) :
    Current period hPeriod metric →L[Real] Real :=
  fderiv Real
    (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction period
      hPeriod metric measure couplings first second einsteinScale) current

/-- Genuine Euler covector of the pulled-back Einstein--Maxwell term. -/
def candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackEulerCovector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (current : Current period hPeriod metric) :
    Current period hPeriod metric →L[Real] Real :=
  fderiv Real
    (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
      period hPeriod metric measure couplings first second) current

/-- Genuine Euler covector of the completed mobile GHY term. -/
def candidateANormalBoundaryTwoSheetGHYActionEulerCovector
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Current period hPeriod metric) :
    Current period hPeriod metric →L[Real] Real :=
  fderiv Real
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale metric) current

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_contDiffAt_one
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    {current : Current period hPeriod metric}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric) :
    ContDiffAt Real 1
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
        period hPeriod metric measure couplings first second einsteinScale)
      current :=
  ((candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_contDiffOn_two
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse).contDiffAt
    ((candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
      period hPeriod metric).mem_nhds hCurrent)).fderiv_right
        (m := 1) (by norm_num)

/-- Exact Euler decomposition at every point of the positive domain. -/
theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_eq_bulk_add_boundary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    {current : Current period hPeriod metric}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric) :
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
          period hPeriod metric measure couplings first second einsteinScale
          current =
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackEulerCovector
            period hPeriod metric measure couplings first second current +
        candidateANormalBoundaryTwoSheetGHYActionEulerCovector period hPeriod
          einsteinScale metric current := by
  have hBulkAt : ContDiffAt Real 2
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
        period hPeriod metric measure couplings first second) current :=
    (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction_contDiffOn_two
      period hPeriod metric measure couplings first second).contDiffAt
        ((candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
          period hPeriod metric).mem_nhds hCurrent)
  have hBoundaryAt : ContDiffAt Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric) current :=
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale metric hTransverse).contDiffAt
        ((candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
          (candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy
            period hPeriod metric hCurrent))
  change fderiv Real
      (fun state =>
        candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
              period hPeriod metric measure couplings first second state +
          candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period
            hPeriod einsteinScale metric state) current =
    fderiv Real
        (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackAction
          period hPeriod metric measure couplings first second) current +
      fderiv Real
        (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale metric) current
  exact fderiv_add
    (hBulkAt.differentiableAt (by norm_num))
    (hBoundaryAt.differentiableAt (by norm_num))

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_fderiv_zero_eq_hessian
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real) :
    fderiv Real
        (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
          period hPeriod metric measure couplings first second einsteinScale) 0 =
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
        period hPeriod metric measure couplings first second einsteinScale :=
  rfl

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_fderiv_zero_eq_bulk_add_boundary
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    fderiv Real
        (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
          period hPeriod metric measure couplings first second einsteinScale) 0 =
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
          period hPeriod metric measure couplings first second +
        candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
          einsteinScale metric := by
  rw [candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_fderiv_zero_eq_hessian]
  exact
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian_eq_bulk_add_boundary
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse

/-- Gate marker: the exact Euler split on the positive domain and its exact
bulk/GHY linearization at the physical origin. -/
theorem global_candidateA_normal_boundary_c2_lorentz_positive_einstein_maxwell_ghy_euler_split_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (∀ {current : Current period hPeriod metric},
      current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric →
        candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
              period hPeriod metric measure couplings first second einsteinScale
              current =
          candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackEulerCovector
                period hPeriod metric measure couplings first second current +
            candidateANormalBoundaryTwoSheetGHYActionEulerCovector period hPeriod
              einsteinScale metric current) ∧
      ContDiffAt Real 1
        (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
          period hPeriod metric measure couplings first second einsteinScale) 0 ∧
      fderiv Real
          (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector
            period hPeriod metric measure couplings first second einsteinScale) 0 =
        candidateANormalBoundaryLorentzPositiveEinsteinMaxwellBulkPullbackHessian
            period hPeriod metric measure couplings first second +
          candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
            einsteinScale metric := by
  refine ⟨?_, ?_, ?_⟩
  · intro current hCurrent
    exact
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_eq_bulk_add_boundary
        period hPeriod metric measure couplings first second einsteinScale
          hTransverse hCurrent
  · exact
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_contDiffAt_one
        period hPeriod metric measure couplings first second einsteinScale
          hTransverse
          (zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain
            period hPeriod metric hTransverse)
  · exact
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionEulerCovector_fderiv_zero_eq_bulk_add_boundary
        period hPeriod metric measure couplings first second einsteinScale
          hTransverse

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYEulerSplit4D
end JanusFormal
