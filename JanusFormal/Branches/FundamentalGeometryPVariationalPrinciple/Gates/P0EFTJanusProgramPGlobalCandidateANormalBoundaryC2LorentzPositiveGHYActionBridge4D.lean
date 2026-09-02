import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionGermHessian4D

/-!
# Canonical positive Lorentz/GHY action bridge

On the positive joint domain, the terminal smooth GHY equality needs no
external varied metric, non-null graph, root-sign or source witness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Replace the unique central non-null boundary source by the metric and graph
canonically selected on the positive Lorentz/GHY domain. -/
def candidateANormalBoundaryLorentzPositiveGHYActionData
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace :=
  normalGraphCanonicalCandidateAActionData period hPeriod data einsteinScale
    (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod metric
      tensor displacement parameter hCurrent)
    displacement parameter
      (candidateANormalBoundaryLorentzPositiveGHYMetric_normalGraphNonNull
        period hPeriod metric tensor displacement parameter hCurrent)

@[simp]
theorem candidateANormalBoundaryLorentzPositiveGHYActionData_nonNullBoundary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod data
      einsteinScale metric tensor displacement parameter hCurrent).nonNullBoundary =
      normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
        (NonNullFace := NonNullFace) einsteinScale
        (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod metric
          tensor displacement parameter hCurrent)
        displacement parameter
          (candidateANormalBoundaryLorentzPositiveGHYMetric_normalGraphNonNull
            period hPeriod metric tensor displacement parameter hCurrent) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Terminal smooth GHY source equality on the canonical positive Lorentz/GHY
domain, with all former geometric side witnesses discharged internally. -/
theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_lorentzPositiveGHY
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      globalCandidateAGHYAction period hPeriod
        (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod
          data einsteinScale metric tensor displacement parameter hCurrent) := by
  unfold candidateANormalBoundaryLorentzPositiveGHYActionData
  exact
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_smooth
      period hPeriod
      (normalGraphCanonicalCandidateAActionData period hPeriod data
        einsteinScale
        (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod metric
          tensor displacement parameter hCurrent)
        displacement parameter
          (candidateANormalBoundaryLorentzPositiveGHYMetric_normalGraphNonNull
            period hPeriod metric tensor displacement parameter hCurrent))
      einsteinScale metric hTransverse tensor
      (candidateANormalBoundaryLorentzPositiveGHYMetric period hPeriod metric
        tensor displacement parameter hCurrent)
      (candidateANormalBoundaryLorentzPositiveGHYMetric_tensor period hPeriod
        metric tensor displacement parameter hCurrent)
      displacement parameter
      (candidateANormalBoundaryLorentzPositiveGHYMetric_normalGraphNonNull
        period hPeriod metric tensor displacement parameter hCurrent)
      (candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy period hPeriod
        metric hCurrent)
      (fun point =>
        (candidateANormalBoundaryLorentzPositiveGHYDomain_normalRoot_pos
          period hPeriod metric hCurrent point).le)
      (fun point =>
        (candidateANormalBoundaryLorentzPositiveGHYDomain_volumeRoot_pos
          period hPeriod metric hCurrent point).le)
      rfl

/-- Gate marker for the witness-free canonical smooth H10 action bridge. -/
theorem global_candidateA_normal_boundary_c2_lorentz_positive_ghy_action_bridge_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain
          period hPeriod metric) :
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      globalCandidateAGHYAction period hPeriod
        (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod
          data einsteinScale metric tensor displacement parameter hCurrent) :=
  candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_lorentzPositiveGHY
    period hPeriod data einsteinScale metric hTransverse tensor displacement
      parameter hCurrent

end

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
end JanusFormal
