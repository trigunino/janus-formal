import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartActions4D

/-!
# Einstein--Maxwell plus mobile GHY on one Candidate-A chart

The boundary-enhanced metric coordinate is projected to the Lorentz `C²`
bulk chart.  The bulk Einstein--Maxwell action and the completed two-sheet GHY
action therefore live on the same positive Candidate-A neighborhood.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartActions4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D

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

/-- The metric coordinate of the completed normal-boundary current, projected
to the existing relative `C²` bulk chart. -/
def candidateANormalBoundaryMetricC2Projection
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real
      →L[Real] RegularGeneralMetricC2Core period hPeriod metric :=
  (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric).comp
    ((ContinuousLinearMap.fst Real
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric)
      (NormalBoundaryC2JetCore period hPeriod)).comp
      (ContinuousLinearMap.fst Real
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real))

@[simp]
theorem candidateANormalBoundaryMetricC2Projection_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    candidateANormalBoundaryMetricC2Projection period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      regularGeneralMetricSmoothC2Variation period hPeriod metric tensor :=
  rfl

theorem candidateANormalBoundaryMetricC2Projection_mem_lorentzChart
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric) :
    candidateANormalBoundaryMetricC2Projection period hPeriod metric current ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric :=
  candidateANormalBoundaryLorentzGHYDomain_metric_mem period hPeriod metric
    (candidateANormalBoundaryLorentzPositiveGHYDomain_mem_lorentzGHY
      period hPeriod metric hCurrent)

/-- Bulk Einstein--Maxwell plus the completed mobile two-sheet GHY action,
all evaluated from the same Candidate-A metric-normal current. -/
def candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) : Real :=
  regularGeneralMetricC2LorentzEinsteinMaxwellAction period hPeriod metric
      measure couplings first second
        (candidateANormalBoundaryMetricC2Projection period hPeriod metric current) +
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale metric current

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction
        period hPeriod metric measure couplings first second einsteinScale)
      (candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric) := by
  have hBulk : ContDiffOn Real 2
      (fun current =>
        regularGeneralMetricC2LorentzEinsteinMaxwellAction period hPeriod metric
          measure couplings first second
            (candidateANormalBoundaryMetricC2Projection
              period hPeriod metric current))
      (candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric) :=
    (regularGeneralMetricC2LorentzEinsteinMaxwellAction_contDiffOn_two
      period hPeriod metric measure couplings first second).comp
        (candidateANormalBoundaryMetricC2Projection
          period hPeriod metric).contDiff.contDiffOn
        (fun current hCurrent =>
          candidateANormalBoundaryMetricC2Projection_mem_lorentzChart
            period hPeriod metric hCurrent)
  have hBoundary : ContDiffOn Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric)
      (candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric) :=
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale metric hTransverse).mono (by
        intro current hCurrent
        exact candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy
          period hPeriod metric hCurrent)
  exact hBulk.add hBoundary

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real) :
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction period
        hPeriod metric measure couplings first second einsteinScale 0 =
      (intrinsicEinsteinHilbertAction period hPeriod couplings
          (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
            period hPeriod metric)
          measure +
        ∫ point, metric.volume point *
          globalMaxwellPairing period hPeriod metric.metric first second point
          ∂measure) +
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale metric 0 := by
  rw [candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction,
    map_zero,
    regularGeneralMetricC2LorentzEinsteinMaxwellAction_zero]

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_smooth_eq_bulk_add_globalCandidateA
    {configuration : GlobalFieldConfiguration period hPeriod}
    {actionCouplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration
      actionCouplings NonNullFace NullFace)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction period
        hPeriod metric measure couplings first second einsteinScale
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      regularGeneralMetricC2LorentzEinsteinMaxwellAction period hPeriod metric
          measure couplings first second
            (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) +
        globalCandidateAGHYAction period hPeriod
          (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod
            data einsteinScale metric tensor displacement parameter hCurrent) := by
  rw [candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction,
    candidateANormalBoundaryMetricC2Projection_smooth,
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_lorentzPositiveGHY
      period hPeriod data einsteinScale metric hTransverse tensor displacement
        parameter hCurrent]

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_contDiffAt_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffAt Real 2
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction period
        hPeriod metric measure couplings first second einsteinScale) 0 :=
  (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_contDiffOn_two
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse).contDiffAt
    ((candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
      period hPeriod metric).mem_nhds
        (zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric hTransverse))

/-- Genuine second Frechet derivative of the combined bulk--boundary action. -/
def candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real) :
    Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real
      →L[Real]
      (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real
        →L[Real] Real) :=
  fderiv Real
    (fderiv Real
      (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction period
        hPeriod metric measure couplings first second einsteinScale)) 0

theorem candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian_symmetric
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
      candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
          period hPeriod metric measure couplings first second einsteinScale
          secondDirection firstDirection := by
  have hSmooth : minSmoothness Real 2 ≤ (2 : ℕ∞ω) := by
    simp [minSmoothness_of_isRCLikeNormedField]
  exact
    (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_contDiffAt_two
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse).isSymmSndFDerivAt hSmooth firstDirection secondDirection

/-- Genuine Hessian certificate for the combined bulk--boundary action. -/
theorem global_candidateA_normal_boundary_c2_lorentz_positive_einstein_maxwell_ghy_hessian_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffAt Real 2
        (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction period
          hPeriod metric measure couplings first second einsteinScale) 0 ∧
      ∀ firstDirection secondDirection,
        candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
              period hPeriod metric measure couplings first second einsteinScale
              firstDirection secondDirection =
          candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian
              period hPeriod metric measure couplings first second einsteinScale
              secondDirection firstDirection :=
  ⟨candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_contDiffAt_two
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse,
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYActionHessian_symmetric
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse⟩

/-- Gate marker: bulk Einstein--Maxwell and the canonical mobile GHY source
now share one explicit positive Lorentz Candidate-A chart. -/
theorem global_candidateA_normal_boundary_c2_lorentz_positive_einstein_maxwell_ghy_action_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsOpen (candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric) ∧
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
          candidateANormalBoundaryLorentzPositiveGHYDomain
            period hPeriod metric ∧
      ContDiffOn Real 2
        (candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction
          period hPeriod metric measure couplings first second einsteinScale)
        (candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :=
  ⟨candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
      period hPeriod metric,
    zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric hTransverse,
    candidateANormalBoundaryLorentzPositiveEinsteinMaxwellGHYAction_contDiffOn_two
      period hPeriod metric measure couplings first second einsteinScale
        hTransverse⟩

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D
end JanusFormal
