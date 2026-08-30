import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeDiffeomorphismGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D

/-!
# Strong residual of the faithful BRST--SpinC--LL same-action sum

This is the aggregate strong graph equation.  It does not include the seven
physical action blocks that remain outside the faithful same-action Riesz sum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeFaithfulSameActionRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Strong residual of the faithful BRST--SpinC--LL graph sum. -/
def globalCandidateAFaithfulSameActionRieszResidual
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
      data analysis :=
  globalCandidateAFaithfulSameActionRieszOperator period hPeriod configuration
    data analysis state

/-- Hilbert pairing of the faithful aggregate residual. -/
def globalCandidateAFaithfulSameActionRieszResidualPairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (residual test : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) : Real :=
  by
    letI : InnerProductSpace Real
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis) :=
      diagonalL2ExtendedBulkInnerProductSpace period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
    exact inner Real residual test

/-- The faithful graph Hessian is represented by the aggregate strong
residual. -/
theorem globalCandidateAFaithfulSameActionHessian_eq_rieszResidualPairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (state test : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    diagonalExtendedBulkL2Hessian period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis state test =
      globalCandidateAFaithfulSameActionRieszResidualPairing period hPeriod
        configuration data analysis
          (globalCandidateAFaithfulSameActionRieszResidual period hPeriod
            configuration data analysis state) test := by
  simpa only [globalCandidateAFaithfulSameActionRieszResidualPairing,
    globalCandidateAFaithfulSameActionRieszResidual] using
      (globalCandidateAFaithfulSameActionRieszOperator_pairing period hPeriod
        configuration data analysis state test).symm

/-- Faithful graph tests separate the aggregate residual. -/
theorem globalCandidateAFaithfulSameActionRieszResidualPairing_separates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (residual : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    (∀ test, globalCandidateAFaithfulSameActionRieszResidualPairing period
      hPeriod configuration data analysis residual test = 0) ↔ residual = 0 := by
  letI : InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    diagonalL2ExtendedBulkInnerProductSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
  constructor
  · intro hPairing
    have hSelf := hPairing residual
    change inner Real residual residual = 0 at hSelf
    exact (@inner_self_eq_zero Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) _ _
      (diagonalL2ExtendedBulkInnerProductSpace period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis)).mp hSelf
  · intro hResidual test
    rw [hResidual]
    change inner Real (0 : GlobalCandidateAFaithfulSameActionHilbert period
      hPeriod configuration data analysis) test = 0
    exact inner_zero_left test

/-- Concrete separating representation of the faithful aggregate graph Euler
covector. -/
def globalCandidateAFaithfulSameActionRieszResidualRepresentation
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    SeparatingPDEResidualRepresentation
      (diagonalExtendedBulkL2Hessian period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis state).toLinearMap where
  Residual := GlobalCandidateAFaithfulSameActionHilbert period hPeriod
    configuration data analysis
  zeroResidual := 0
  residual := globalCandidateAFaithfulSameActionRieszResidual period hPeriod
    configuration data analysis state
  pairing := globalCandidateAFaithfulSameActionRieszResidualPairing period
    hPeriod configuration data analysis
  represents := globalCandidateAFaithfulSameActionHessian_eq_rieszResidualPairing
    period hPeriod configuration data analysis state
  separates :=
    globalCandidateAFaithfulSameActionRieszResidualPairing_separates period
      hPeriod configuration data analysis
        (globalCandidateAFaithfulSameActionRieszResidual period hPeriod
          configuration data analysis state)

/-- The faithful aggregate graph Euler covector vanishes exactly when its
strong Riesz residual vanishes. -/
theorem globalCandidateAFaithfulSameActionEulerCovector_eq_zero_iff_rieszResidual
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    diagonalExtendedBulkL2Hessian period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis state = 0 ↔
      globalCandidateAFaithfulSameActionRieszResidual period hPeriod
        configuration data analysis state = 0 := by
  let representation :=
    globalCandidateAFaithfulSameActionRieszResidualRepresentation period
      hPeriod configuration data analysis state
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
end P0EFTJanusProgramPGlobalEulerLagrangeFaithfulSameActionRieszResidual4D
end JanusFormal
