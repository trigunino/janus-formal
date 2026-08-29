import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalTerminalActionClosure4D

/-!
# H10 same-action germ and Hessian certificate

This gate promotes the terminal smooth-core action equality to a genuine
neighborhood statement at the physical origin.  The central Candidate-A data
is not replaced by a second boundary action: an existing global action datum is
updated only in its unique non-null boundary source slot with the canonical
mobile normal-graph datum already constructed in the ledger.

The resulting certificate packages the open admissible domain, `C²`
regularity, equality with the central Candidate-A summand on the smooth germ,
and symmetry of the genuine second Fréchet derivative.  No new metric, normal,
chart, action, geometric datum or axiom is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance sameActionHessianCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance sameActionHessianCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance sameActionHessianCandidateANormalBoundaryFunctionalCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

/-- Replace only the unique non-null boundary source of an existing central
Candidate-A datum by the already constructed canonical mobile normal graph. -/
def normalGraphCanonicalCandidateAActionData
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace :=
  { data with
    nonNullBoundary :=
      normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
        (NonNullFace := NonNullFace) einsteinScale variedMetric displacement
          parameter hNonNull }

@[simp]
theorem normalGraphCanonicalCandidateAActionData_nonNullBoundary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    (normalGraphCanonicalCandidateAActionData period hPeriod data
        einsteinScale variedMetric displacement parameter hNonNull).nonNullBoundary =
      normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
        (NonNullFace := NonNullFace) einsteinScale variedMetric displacement
          parameter hNonNull :=
  rfl

/-- At one completed parameter, the same-action assertion means admissibility
and equality with the central Candidate-A GHY summand for every smooth
presentation of that parameter.  The non-null source is installed by record
update, so the statement contains no supplied scalar boundary action. -/
def CandidateANormalBoundarySameActionAtSmoothCurrent
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    Prop :=
  current ∈ candidateANormalBoundaryGHYDomain period hPeriod metric ∧
    ∀ (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
      (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
      (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
      (displacement : SmoothNormalDisplacement period hPeriod)
      (parameter : Real)
      (hCurrentEq : current =
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter))
      (hCurrent : current ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric),
      let hNonNull :=
        normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod metric tensor
          variedMetric hVaried displacement parameter (hCurrentEq ▸ hCurrent)
      candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale metric current =
        globalCandidateAGHYAction period hPeriod
          (normalGraphCanonicalCandidateAActionData period hPeriod data
            einsteinScale variedMetric displacement parameter hNonNull)

/-- The terminal smooth equality holds on a true neighborhood of zero in the
completed metric-normal parameter space. -/
theorem
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eventually_eq_globalCandidateA_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ∀ᶠ current in 𝓝
        (0 : Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      CandidateANormalBoundarySameActionAtSmoothCurrent period hPeriod data
        einsteinScale metric current := by
  filter_upwards
    [candidateANormalBoundaryMetricNormalRelativeRoot_eventually_pos
      period hPeriod metric hTransverse,
     candidateANormalBoundaryInducedRelativeVolumeRoot_eventually_pos
      period hPeriod metric hTransverse] with current hNormal hVolume
  refine ⟨hNormal.1, ?_⟩
  intro tensor variedMetric hVaried displacement parameter hCurrentEq hCurrent
  subst current
  let hNonNull :=
    normalGraphNonNullAt_of_candidate_GHY_mem period hPeriod metric tensor
      variedMetric hVaried displacement parameter hCurrent
  change candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
    globalCandidateAGHYAction period hPeriod
      (normalGraphCanonicalCandidateAActionData period hPeriod data
        einsteinScale variedMetric displacement parameter hNonNull)
  exact
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_smooth
      period hPeriod
      (normalGraphCanonicalCandidateAActionData period hPeriod data
        einsteinScale variedMetric displacement parameter hNonNull)
      einsteinScale metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent
        (fun point => (hNormal.2 point).le)
        (fun point => (hVolume.2 point).le) rfl

/-- Auditable H10 certificate: the unique completed two-sheet action is `C²`,
agrees on the smooth germ with the central Candidate-A source update, and has
the symmetric second Fréchet derivative already constructed in the analytic
fiber chart. -/
structure CandidateANormalBoundarySameActionHessianCertificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod) : Prop where
  domain_isOpen :
    IsOpen (candidateANormalBoundaryGHYDomain period hPeriod metric)
  zero_mem_domain :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric
  contDiffAt_two :
    ContDiffAt Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric) 0
  sameAction_germ :
    ∀ᶠ current in 𝓝
        (0 : Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      CandidateANormalBoundarySameActionAtSmoothCurrent period hPeriod data
        einsteinScale metric current
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

/-- The existing completed action and terminal smooth-source theorem construct
the full same-action Hessian certificate without any additional assumption. -/
theorem candidateANormalBoundarySameActionHessianCertificate_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    CandidateANormalBoundarySameActionHessianCertificate period hPeriod data
      einsteinScale metric := by
  refine
    { domain_isOpen :=
        candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric
      zero_mem_domain :=
        zero_mem_candidateANormalBoundaryGHYDomain period hPeriod metric
          hTransverse
      contDiffAt_two :=
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffAt_two
          period hPeriod einsteinScale metric hTransverse
      sameAction_germ :=
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eventually_eq_globalCandidateA_smooth
          period hPeriod data einsteinScale metric hTransverse
      hessian_is_secondFrechet := rfl
      hessian_symmetric := ?_ }
  intro first second
  exact candidateANormalBoundaryTwoSheetGHYActionHessian_symmetric period hPeriod
    einsteinScale metric hTransverse first second

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
