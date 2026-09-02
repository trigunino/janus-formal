import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D

/-!
# Positive Lorentz/GHY Candidate-A domain

The joint Lorentz/GHY neighborhood is restricted to unit balls around both
selected scalar roots.  This makes their pointwise positivity intrinsic to
the domain instead of an additional downstream hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D

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

/-- Explicit open subdomain on which both selected GHY roots stay within one
unit of the positive base root. -/
def candidateANormalBoundaryLorentzPositiveGHYDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :=
  (candidateANormalBoundaryLorentzGHYDomain period hPeriod metric ∩
    candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric ⁻¹'
      Metric.ball
        (1 : CandidateANormalBoundaryScalarField period hPeriod) 1) ∩
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric ⁻¹'
      Metric.ball
        (1 : CandidateANormalBoundaryScalarField period hPeriod) 1

theorem candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric) := by
  have hNormalContinuous : ContinuousOn
      (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryLorentzGHYDomain
        period hPeriod metric) :=
    (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_contDiffOn_two
      period hPeriod metric).continuousOn.mono (by
        intro current hCurrent
        exact hCurrent.1.1)
  have hNormalOpen : IsOpen
      (candidateANormalBoundaryLorentzGHYDomain period hPeriod metric ∩
        candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
            period hPeriod metric ⁻¹'
          Metric.ball
            (1 : CandidateANormalBoundaryScalarField period hPeriod) 1) :=
    hNormalContinuous.isOpen_inter_preimage
      (candidateANormalBoundaryLorentzGHYDomain_isOpen
        period hPeriod metric) Metric.isOpen_ball
  have hVolumeContinuous : ContinuousOn
      (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryLorentzGHYDomain period hPeriod metric ∩
        candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
            period hPeriod metric ⁻¹'
          Metric.ball
            (1 : CandidateANormalBoundaryScalarField period hPeriod) 1) :=
    (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_contDiffOn_two
      period hPeriod metric).continuousOn.mono (by
        intro current hCurrent
        exact hCurrent.1.1)
  exact hVolumeContinuous.isOpen_inter_preimage hNormalOpen Metric.isOpen_ball

theorem zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric := by
  constructor
  · constructor
    · exact zero_mem_candidateANormalBoundaryLorentzGHYDomain
        period hPeriod metric hTransverse
    · change candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
          period hPeriod metric 0 ∈ Metric.ball 1 1
      rw [candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_zero
        period hPeriod metric hTransverse]
      exact Metric.mem_ball_self one_pos
  · change candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric 0 ∈ Metric.ball 1 1
    rw [candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_zero
      period hPeriod metric hTransverse]
    exact Metric.mem_ball_self one_pos

theorem candidateANormalBoundaryLorentzPositiveGHYDomain_mem_lorentzGHY
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric) :
    current ∈ candidateANormalBoundaryLorentzGHYDomain
      period hPeriod metric :=
  hCurrent.1.1

theorem candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric) :
    current ∈ candidateANormalBoundaryGHYDomain period hPeriod metric :=
  candidateANormalBoundaryLorentzGHYDomain_mem_ghy period hPeriod metric
    (candidateANormalBoundaryLorentzPositiveGHYDomain_mem_lorentzGHY
      period hPeriod metric hCurrent)

theorem candidateANormalBoundaryLorentzPositiveGHYDomain_mem_metricNormalRoot
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric) :
    current ∈ candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric :=
  (candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy
    period hPeriod metric hCurrent).1

private theorem scalarField_pos_of_mem_ball_one
    (field : CandidateANormalBoundaryScalarField period hPeriod)
    (hField : field ∈ Metric.ball
      (1 : CandidateANormalBoundaryScalarField period hPeriod) 1)
    (boundary : OrientationBoundary period hPeriod) :
    0 < field boundary := by
  have hNear : dist field 1 < 1 := hField
  rw [dist_eq_norm] at hNear
  have hEvaluation := (field - 1).norm_coe_le_norm boundary
  change |field boundary - 1| ≤ ‖field - 1‖ at hEvaluation
  have hPointwise : |field boundary - 1| < 1 :=
    lt_of_le_of_lt hEvaluation hNear
  linarith [abs_lt.mp hPointwise |>.1]

theorem candidateANormalBoundaryLorentzPositiveGHYDomain_normalRoot_pos
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) :
    0 < candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
      period hPeriod metric current boundary :=
  scalarField_pos_of_mem_ball_one period hPeriod _ hCurrent.1.2 boundary

theorem candidateANormalBoundaryLorentzPositiveGHYDomain_volumeRoot_pos
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) :
    0 < candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
      period hPeriod metric current boundary :=
  scalarField_pos_of_mem_ball_one period hPeriod _ hCurrent.2 boundary

/-- Canonical Lorentz metric inherited from the joint positive domain. -/
def candidateANormalBoundaryLorentzPositiveGHYMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    SmoothGeneralLorentzMetric period hPeriod :=
  candidateANormalBoundaryLorentzGHYMetric period hPeriod metric tensor
    displacement parameter
      (candidateANormalBoundaryLorentzPositiveGHYDomain_mem_lorentzGHY
        period hPeriod metric hCurrent)

@[simp]
theorem candidateANormalBoundaryLorentzPositiveGHYMetric_tensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod metric
      tensor displacement parameter hCurrent).tensor =
        metric.metric.tensor + tensor :=
  candidateANormalBoundaryLorentzGHYMetric_tensor period hPeriod metric tensor
    displacement parameter _

theorem candidateANormalBoundaryLorentzPositiveGHYMetric_normalGraphNonNull
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    NormalGraphNonNullAt period hPeriod
      (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod metric
        tensor displacement parameter hCurrent)
      displacement parameter :=
  candidateANormalBoundaryLorentzGHYMetric_normalGraphNonNull period hPeriod
    metric tensor displacement parameter _

/-- Gate marker: the common open zero-neighborhood supplies the Lorentz metric,
non-null graph and pointwise-positive selected normal and volume roots. -/
theorem global_candidateA_normal_boundary_c2_lorentz_positive_ghy_domain_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsOpen (candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric) ∧
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
          candidateANormalBoundaryLorentzPositiveGHYDomain
            period hPeriod metric ∧
      ∀ (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
        (displacement : SmoothNormalDisplacement period hPeriod)
        (parameter : Real)
        (hCurrent :
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) ∈
            candidateANormalBoundaryLorentzPositiveGHYDomain
              period hPeriod metric),
        (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod metric
            tensor displacement parameter hCurrent).tensor =
              metric.metric.tensor + tensor ∧
          NormalGraphNonNullAt period hPeriod
            (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod
              metric tensor displacement parameter hCurrent)
            displacement parameter ∧
          (∀ boundary : OrientationBoundary period hPeriod,
            0 < candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
              period hPeriod metric
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter) boundary) ∧
          (∀ boundary : OrientationBoundary period hPeriod,
            0 < candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
              period hPeriod metric
                (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                  metric (tensor, displacement), parameter) boundary) := by
  refine ⟨candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
      period hPeriod metric,
    zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric hTransverse, ?_⟩
  intro tensor displacement parameter hCurrent
  exact ⟨candidateANormalBoundaryLorentzPositiveGHYMetric_tensor period
      hPeriod metric tensor displacement parameter hCurrent,
    candidateANormalBoundaryLorentzPositiveGHYMetric_normalGraphNonNull period
      hPeriod metric tensor displacement parameter hCurrent,
    fun boundary =>
      candidateANormalBoundaryLorentzPositiveGHYDomain_normalRoot_pos period
        hPeriod metric hCurrent boundary,
    fun boundary =>
      candidateANormalBoundaryLorentzPositiveGHYDomain_volumeRoot_pos period
        hPeriod metric hCurrent boundary⟩

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
end JanusFormal
