import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzChartMetricBridge4D

/-!
# Unified Candidate-A Lorentz/GHY domain

The mobile-boundary GHY domain is intersected with the pullback of the
Lorentz metric chart.  On its genuine smooth core, both the varied Lorentz
metric and non-nullity of the moving graph are then canonical.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D

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

/-- One open domain carrying both the mobile GHY conditions and the ambient
Lorentz-signature certificate. -/
def candidateANormalBoundaryLorentzGHYDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :=
  candidateANormalBoundaryGHYDomain period hPeriod metric ∩
    (fun current => regularGeneralMetricBoundaryC3CoreToC2 period hPeriod
      metric current.1.1) ⁻¹'
        regularGeneralMetricC2LorentzChartDomain period hPeriod metric

theorem candidateANormalBoundaryLorentzGHYDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (candidateANormalBoundaryLorentzGHYDomain
      period hPeriod metric) := by
  have hMetric : Continuous (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      current.1.1) :=
    continuous_fst.comp continuous_fst
  exact (candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).inter
    ((regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric).preimage
      ((regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric).continuous.comp
        hMetric))

theorem zero_mem_candidateANormalBoundaryLorentzGHYDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryLorentzGHYDomain
        period hPeriod metric := by
  constructor
  · exact zero_mem_candidateANormalBoundaryGHYDomain
      period hPeriod metric hTransverse
  · change regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
        (0 : RegularGeneralMetricBoundaryC3Core period hPeriod metric) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric
    rw [map_zero]
    exact zero_mem_regularGeneralMetricC2LorentzChartDomain
      period hPeriod metric

theorem candidateANormalBoundaryLorentzGHYDomain_mem_ghy
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzGHYDomain
      period hPeriod metric) :
    current ∈ candidateANormalBoundaryGHYDomain period hPeriod metric :=
  hCurrent.1

theorem candidateANormalBoundaryLorentzGHYDomain_metric_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryLorentzGHYDomain
      period hPeriod metric) :
    regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric current.1.1 ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric :=
  hCurrent.2

theorem candidateANormalBoundaryLorentzGHYDomain_smoothMetric_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzGHYDomain period hPeriod metric) :
    regularGeneralMetricSmoothC2Variation period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric := by
  have hMetric := candidateANormalBoundaryLorentzGHYDomain_metric_mem
    period hPeriod metric hCurrent
  change regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
      (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric tensor) ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod metric at hMetric
  rw [regularGeneralMetricBoundaryC3CoreToC2_smooth] at hMetric
  exact hMetric

/-- Canonical varied metric selected by the joint Lorentz/GHY domain. -/
def candidateANormalBoundaryLorentzGHYMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzGHYDomain period hPeriod metric) :
    SmoothGeneralLorentzMetric period hPeriod :=
  regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
    (candidateANormalBoundaryLorentzGHYDomain_smoothMetric_mem period hPeriod
      metric tensor displacement parameter hCurrent)

@[simp]
theorem candidateANormalBoundaryLorentzGHYMetric_tensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzGHYDomain period hPeriod metric) :
    (candidateANormalBoundaryLorentzGHYMetric period hPeriod metric tensor
      displacement parameter hCurrent).tensor =
        metric.metric.tensor + tensor :=
  regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric tensor _

theorem candidateANormalBoundaryLorentzGHYMetric_normalGraphNonNull
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzGHYDomain period hPeriod metric) :
    NormalGraphNonNullAt period hPeriod
      (candidateANormalBoundaryLorentzGHYMetric period hPeriod metric tensor
        displacement parameter hCurrent)
      displacement parameter := by
  exact normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod metric tensor
    (candidateANormalBoundaryLorentzGHYMetric period hPeriod metric tensor
      displacement parameter hCurrent)
    (candidateANormalBoundaryLorentzGHYMetric_tensor period hPeriod metric
      tensor displacement parameter hCurrent)
    displacement parameter hCurrent.1

/-- Gate marker: one open zero-neighbourhood now constructs both the ambient
Lorentz metric and the non-null mobile graph on every genuine smooth point. -/
theorem global_candidateA_normal_boundary_c2_lorentz_ghy_domain_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsOpen (candidateANormalBoundaryLorentzGHYDomain period hPeriod metric) ∧
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
          candidateANormalBoundaryLorentzGHYDomain period hPeriod metric ∧
      ∀ (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
        (displacement : SmoothNormalDisplacement period hPeriod)
        (parameter : Real)
        (hCurrent :
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) ∈
            candidateANormalBoundaryLorentzGHYDomain period hPeriod metric),
        (candidateANormalBoundaryLorentzGHYMetric period hPeriod metric tensor
            displacement parameter hCurrent).tensor =
              metric.metric.tensor + tensor ∧
          NormalGraphNonNullAt period hPeriod
            (candidateANormalBoundaryLorentzGHYMetric period hPeriod metric
              tensor displacement parameter hCurrent)
            displacement parameter := by
  exact ⟨candidateANormalBoundaryLorentzGHYDomain_isOpen
      period hPeriod metric,
    zero_mem_candidateANormalBoundaryLorentzGHYDomain
      period hPeriod metric hTransverse,
    fun tensor displacement parameter hCurrent =>
      ⟨candidateANormalBoundaryLorentzGHYMetric_tensor period hPeriod metric
          tensor displacement parameter hCurrent,
        candidateANormalBoundaryLorentzGHYMetric_normalGraphNonNull
          period hPeriod metric tensor displacement parameter hCurrent⟩⟩

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
end JanusFormal
