import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTGram4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-! Signed realization of the actual diagonal diffeomorphism BRST graph.
The two metric sectors retain their original weights and one shared triplet. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12SignedBRSTGram4D

attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace
  globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace
  globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace
  diagonalGraphModule
  diagonalGraphInnerProductSpace
  diagonalGraphCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

def diffeomorphismSignedRiesz
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric :=
  diffeomorphismSignedGram
    (globalDiffeomorphismOffShellDeDonderProjection period hPeriod metric)
    (globalDiffeomorphismOffShellBProjection period hPeriod metric)
    (globalDiffeomorphismOffShellBFlatProjection period hPeriod metric)
    (globalDiffeomorphismOffShellFPProjection period hPeriod metric)
    (globalDiffeomorphismOffShellAntighostProjection period hPeriod metric)

theorem diffeomorphismSignedRiesz_pairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    inner Real (diffeomorphismSignedRiesz period hPeriod metric first) second =
      globalDiffeomorphismOffShellHessian period hPeriod metric first second := by
  rw [diffeomorphismSignedRiesz, diffeomorphismSignedGram_pairing]
  rfl

theorem diffeomorphismSignedRiesz_eq_actual
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    diffeomorphismSignedRiesz period hPeriod metric =
      globalDiffeomorphismOffShellRieszOperator period hPeriod metric := by
  apply ContinuousLinearMap.ext
  intro first
  apply ext_inner_right Real
  intro second
  exact (diffeomorphismSignedRiesz_pairing period hPeriod metric first second).trans
    (globalDiffeomorphismOffShellRieszOperator_pairing
      period hPeriod metric first second).symm

/-- Pull back the signed mono-metric realizations to the same diagonal graph. -/
def diagonalDiffeomorphismSignedRiesz
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric :=
  candidateAPlusEinsteinKineticWeight couplings •
      pullback
        (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection period hPeriod metric)
        (diffeomorphismSignedRiesz period hPeriod (metric .plus)) +
    candidateAMinusEinsteinKineticWeight couplings •
      pullback
        (globalCandidateADiagonalDiffeomorphismOffShellMinusProjection period hPeriod metric)
        (diffeomorphismSignedRiesz period hPeriod (metric .minus))

theorem diagonalDiffeomorphismSignedRiesz_pairing
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) :
    inner Real (diagonalDiffeomorphismSignedRiesz period hPeriod couplings metric first)
      second =
      globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings metric first second := by
  simp only [diagonalDiffeomorphismSignedRiesz, add_apply, smul_apply,
    inner_add_left, real_inner_smul_left, pullback_pairing,
    diffeomorphismSignedRiesz_pairing,
    globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]

theorem diagonalDiffeomorphismSignedRiesz_eq_actual
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    diagonalDiffeomorphismSignedRiesz period hPeriod couplings metric =
      globalCandidateADiagonalDiffeomorphismOffShellRieszOperator
        period hPeriod couplings metric := by
  apply ContinuousLinearMap.ext
  intro first
  apply ext_inner_right Real
  intro second
  exact (diagonalDiffeomorphismSignedRiesz_pairing
    period hPeriod couplings metric first second).trans
    (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing
      period hPeriod couplings metric first second).symm

theorem diagonalDiffeomorphismSignedRiesz_smooth_pairing
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real
      (diagonalDiffeomorphismSignedRiesz period hPeriod couplings metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric first))
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction
        period hPeriod couplings metric first second := by
  rw [diagonalDiffeomorphismSignedRiesz_pairing,
    globalCandidateADiagonalDiffeomorphismOffShellHessian_smooth_eq_BRST]

end
end P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
end JanusFormal
