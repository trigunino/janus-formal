import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionSmoothFactorization4D

/-!
# Terminal H10 closure certificate

The mobile non-null Candidate-A boundary sector is already represented by one
completed two-sheet GHY action.  The preceding gates prove that this action is
`C²`, that its genuine second Fréchet derivative is symmetric, that every
smooth presentation agrees with the unique central Candidate-A source on a
true germ at the physical origin, and that the smooth source factors through
the completed metric-normal core.

This file packages those results into one auditable H10 certificate.  It adds
no boundary action, no normal, no metric, no chart and no physical premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter
open scoped Topology
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance h10CandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance h10CandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance h10CandidateANormalBoundaryFunctionalCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

/-- Final H10 packet.  `sameActionHessian` is the genuine second-Fréchet
certificate, while `smoothSourceFactorization` records that the unique mobile
Candidate-A source is independent of every smooth presentation of one
completed admissible parameter. -/
structure GlobalCandidateAH10ClosureCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod) : Prop where
  sameActionHessian :
    CandidateANormalBoundarySameActionHessianCertificate period hPeriod data
      einsteinScale metric
  smoothSourceFactorization :
    ∀ᶠ current in 𝓝
        (0 : Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      CandidateANormalBoundarySmoothSourceFactorizationAtCurrent period hPeriod
        data einsteinScale metric current

/-- The already proved smooth-source and completed-Hessian theorems close H10
without an additional hypothesis beyond the physical throat
transversality already required to enter the GHY domain. -/
theorem global_candidateA_h10_closure_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    GlobalCandidateAH10ClosureCertificate4D period hPeriod data einsteinScale
      metric where
  sameActionHessian :=
    candidateANormalBoundarySameActionHessianCertificate_smooth period hPeriod
      data einsteinScale metric hTransverse
  smoothSourceFactorization :=
    candidateANormalBoundarySmoothSourceFactorization_eventually period hPeriod
      data einsteinScale metric hTransverse

/-- Convenient projection of the terminal H10 packet to the exact certificate
consumed by the H14 assembly. -/
theorem GlobalCandidateAH10ClosureCertificate4D.boundaryHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace}
    {einsteinScale : Real}
    {metric : RegularGeneralLorentzMetric period hPeriod}
    (certificate : GlobalCandidateAH10ClosureCertificate4D period hPeriod data
      einsteinScale metric) :
    CandidateANormalBoundarySameActionHessianCertificate period hPeriod data
      einsteinScale metric :=
  certificate.sameActionHessian

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
end JanusFormal
