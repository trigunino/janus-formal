import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeAbelianGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-!
# Strong Riesz residual of the diagonal diffeomorphism BRST graph action
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeDiffeomorphismGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance (priority := 10000) localDiagonalGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
        hPeriod metric) :=
  diagonalGraphNormedSpace period hPeriod metric

local instance (priority := 10000) localDiagonalGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
        hPeriod metric) :=
  diagonalGraphModule period hPeriod metric

local instance (priority := 10001) localDiagonalGraphContinuousAdd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
        hPeriod metric) :=
  diagonalGraphContinuousAdd period hPeriod metric

local instance (priority := 10000) localDiagonalGraphInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
        hPeriod metric) :=
  diagonalGraphInnerProductSpace period hPeriod metric

/-- Strong Hilbert residual of the actual diagonal diffeomorphism graph
action. -/
def globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidual
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric :=
  globalCandidateADiagonalDiffeomorphismOffShellRieszOperator period hPeriod
    couplings metric state

/-- Weak Hilbert pairing of the diagonal diffeomorphism residual. -/
def globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualPairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (residual test :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric) : Real :=
  inner Real residual test

/-- The diagonal diffeomorphism Hessian is represented by its Riesz
residual. -/
theorem globalCandidateADiagonalDiffeomorphismOffShellHessian_eq_rieszResidualPairing
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state test :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric) :
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings metric state test =
      globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualPairing
        period hPeriod metric
          (globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidual
            period hPeriod couplings metric state) test := by
  simpa only [
    globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualPairing,
    globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidual] using
      (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing
        period hPeriod couplings metric state test).symm

/-- Complete graph tests separate the diagonal diffeomorphism residual. -/
theorem globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualPairing_separates
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (residual :
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric) :
    (∀ test,
      globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualPairing
        period hPeriod metric residual test = 0) ↔ residual = 0 := by
  constructor
  · intro hPairing
    exact (@inner_self_eq_zero Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
        hPeriod metric) _ _
      (diagonalGraphInnerProductSpace period hPeriod metric)).mp
        (hPairing residual)
  · intro hResidual test
    rw [hResidual]
    exact inner_zero_left test

/-- Separating residual representation of the diagonal diffeomorphism graph
Euler covector. -/
def globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualRepresentation
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) :
    SeparatingPDEResidualRepresentation
      (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings metric state).toLinearMap where
  Residual := GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
    period hPeriod metric
  zeroResidual := 0
  residual :=
    globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidual period
      hPeriod couplings metric state
  pairing :=
    globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualPairing
      period hPeriod metric
  represents :=
    globalCandidateADiagonalDiffeomorphismOffShellHessian_eq_rieszResidualPairing
      period hPeriod couplings metric state
  separates :=
    globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualPairing_separates
      period hPeriod metric
        (globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidual period
          hPeriod couplings metric state)

/-- The exact Frechet covector of the diagonal diffeomorphism graph action
vanishes precisely when its strong Riesz residual vanishes. -/
theorem globalCandidateADiagonalDiffeomorphismOffShellGraphEulerCovector_eq_zero_iff_rieszResidual
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) :
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings metric state = 0 ↔
      globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidual period
        hPeriod couplings metric state = 0 := by
  let representation :=
    globalCandidateADiagonalDiffeomorphismOffShellGraphRieszResidualRepresentation
      period hPeriod couplings metric state
  constructor
  · intro hEuler
    apply (separatingPDEResidualRepresentation_covector_eq_zero_iff
      representation).mp
    exact congrArg ContinuousLinearMap.toLinearMap hEuler
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro test
    have hCovector :=
      (separatingPDEResidualRepresentation_covector_eq_zero_iff
        representation).mpr hResidual
    exact LinearMap.congr_fun hCovector test

end
end P0EFTJanusProgramPGlobalEulerLagrangeDiffeomorphismGraphRieszResidual4D
end JanusFormal
