import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D

/-!
# Positive Lorentz/GHY action certificate

The explicit positive joint domain, its canonical smooth central-source
identity, and the genuine symmetric second Frechet derivative are packaged in
one auditable certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionCertificate4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

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
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
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

/-- One certificate for the positive Lorentz/GHY action chart and its genuine
smooth central-source interpretation. -/
structure CandidateANormalBoundaryLorentzPositiveGHYActionCertificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod) : Prop where
  domain_isOpen :
    IsOpen (candidateANormalBoundaryLorentzPositiveGHYDomain
      period hPeriod metric)
  zero_mem_domain :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric
  action_contDiffOn_two :
    ContDiffOn Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric)
      (candidateANormalBoundaryLorentzPositiveGHYDomain
        period hPeriod metric)
  smooth_canonical_source :
    ∀ (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
      (displacement : SmoothNormalDisplacement period hPeriod)
      (parameter : Real)
      (hCurrent :
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) ∈
          candidateANormalBoundaryLorentzPositiveGHYDomain
            period hPeriod metric),
      candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) =
        globalCandidateAGHYAction period hPeriod
          (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod
            data einsteinScale metric tensor displacement parameter hCurrent)
  hessian_is_secondFrechet :
    candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
        einsteinScale metric =
      fderiv Real
        (fderiv Real
          (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
            einsteinScale metric)) 0
  hessian_symmetric :
    ∀ first second : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real,
      candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
            einsteinScale metric first second =
        candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
            einsteinScale metric second first

theorem candidateANormalBoundaryLorentzPositiveGHYActionCertificate_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    CandidateANormalBoundaryLorentzPositiveGHYActionCertificate period hPeriod
      data einsteinScale metric := by
  refine
    { domain_isOpen :=
        candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen
          period hPeriod metric
      zero_mem_domain :=
        zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric hTransverse
      action_contDiffOn_two :=
        (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
          period hPeriod einsteinScale metric hTransverse).mono (by
            intro current hCurrent
            exact candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy
              period hPeriod metric hCurrent)
      smooth_canonical_source := ?_
      hessian_is_secondFrechet := rfl
      hessian_symmetric := ?_ }
  · intro tensor displacement parameter hCurrent
    exact
      candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_lorentzPositiveGHY
        period hPeriod data einsteinScale metric hTransverse tensor displacement
          parameter hCurrent
  · intro first second
    exact candidateANormalBoundaryTwoSheetGHYActionHessian_symmetric
      period hPeriod einsteinScale metric hTransverse first second

/-- Gate marker for the complete positive Lorentz/GHY local action package. -/
theorem global_candidateA_normal_boundary_c2_lorentz_positive_ghy_action_certificate_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    CandidateANormalBoundaryLorentzPositiveGHYActionCertificate period hPeriod
      data einsteinScale metric :=
  candidateANormalBoundaryLorentzPositiveGHYActionCertificate_smooth
    period hPeriod data einsteinScale metric hTransverse

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionCertificate4D
end JanusFormal
