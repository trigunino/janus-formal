import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-!
# Strong Riesz residual of the paired Abelian off-shell graph action
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeAbelianGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Strong Hilbert residual of the actual paired Abelian graph action. -/
def globalPairedAbelianOffShellGraphRieszResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  globalPairedAbelianOffShellRieszOperator period hPeriod metric state

/-- Weak pairing of the paired Abelian strong residual. -/
def globalPairedAbelianOffShellGraphRieszResidualPairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (residual test :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) : Real :=
  inner Real residual test

/-- The paired Abelian Hessian is represented by its Riesz residual. -/
theorem globalPairedAbelianOffShellHessian_eq_rieszResidualPairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state test :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellHessian period hPeriod metric state test =
      globalPairedAbelianOffShellGraphRieszResidualPairing period hPeriod
        metric
          (globalPairedAbelianOffShellGraphRieszResidual period hPeriod metric
            state) test := by
  simpa only [globalPairedAbelianOffShellGraphRieszResidualPairing,
    globalPairedAbelianOffShellGraphRieszResidual] using
      (globalPairedAbelianOffShellRieszOperator_pairing period hPeriod metric
        state test).symm

/-- Tests from the complete off-shell graph separate the Abelian residual. -/
theorem globalPairedAbelianOffShellGraphRieszResidualPairing_separates
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (residual :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    (∀ test, globalPairedAbelianOffShellGraphRieszResidualPairing period
      hPeriod metric residual test = 0) ↔ residual = 0 := by
  constructor
  · intro hPairing
    exact inner_self_eq_zero.mp (hPairing residual)
  · intro hResidual test
    rw [hResidual]
    exact inner_zero_left test

/-- Separating residual representation of the paired Abelian graph Euler
covector. -/
def globalPairedAbelianOffShellGraphRieszResidualRepresentation
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    SeparatingPDEResidualRepresentation
      (globalPairedAbelianOffShellHessian period hPeriod metric
        state).toLinearMap where
  Residual := GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric
  zeroResidual := 0
  residual := globalPairedAbelianOffShellGraphRieszResidual period hPeriod
    metric state
  pairing := globalPairedAbelianOffShellGraphRieszResidualPairing period hPeriod
    metric
  represents := globalPairedAbelianOffShellHessian_eq_rieszResidualPairing
    period hPeriod metric state
  separates :=
    globalPairedAbelianOffShellGraphRieszResidualPairing_separates period
      hPeriod metric
        (globalPairedAbelianOffShellGraphRieszResidual period hPeriod metric
          state)

/-- Stationarity of the genuine paired Abelian graph action is exactly its
strong Riesz equation. -/
theorem globalPairedAbelianOffShellGraphAction_fderiv_eq_zero_iff_rieszResidual
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    fderiv Real
        (globalPairedAbelianOffShellGraphAction period hPeriod metric) state =
      0 ↔
    globalPairedAbelianOffShellGraphRieszResidual period hPeriod metric state =
      0 := by
  rw [globalPairedAbelianOffShellGraphAction_fderiv]
  let representation :=
    globalPairedAbelianOffShellGraphRieszResidualRepresentation period hPeriod
      metric state
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
end P0EFTJanusProgramPGlobalEulerLagrangeAbelianGraphRieszResidual4D
end JanusFormal
