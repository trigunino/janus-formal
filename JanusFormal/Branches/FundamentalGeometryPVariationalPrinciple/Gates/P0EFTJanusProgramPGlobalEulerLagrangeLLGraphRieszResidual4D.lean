import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

/-!
# Strong Riesz residual of the complete LL graph action

The already constructed complete three-slot LL Riesz operator is the strong
Hilbert residual of its genuine same-action quadratic graph functional.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance fullLLGraphInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalFullLLGraphInnerProductSpace period hPeriod data analysis

/-- Strong residual of the actual complete LL graph action. -/
def globalCandidateAFullLLGraphRieszResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    GlobalFullLLGraphHilbert period hPeriod data analysis :=
  globalCandidateAFullLLGraphRieszOperator period hPeriod data analysis state

/-- Hilbert weak pairing of the complete LL strong residual. -/
def globalCandidateAFullLLGraphRieszResidualPairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (residual test : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    Real :=
  inner Real residual test

/-- The complete graph form is represented by its Riesz residual. -/
theorem globalCandidateAFullLLGraphForm_eq_rieszResidualPairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state test : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    globalCandidateAFullLLGraphForm period hPeriod data analysis state test =
      globalCandidateAFullLLGraphRieszResidualPairing period hPeriod data
        analysis
          (globalCandidateAFullLLGraphRieszResidual period hPeriod data
            analysis state) test := by
  rw [globalCandidateAFullLLGraphForm_apply]
  simpa only [globalCandidateAFullLLGraphRieszResidualPairing,
    globalCandidateAFullLLGraphRieszResidual] using
      (globalCandidateAFullLLGraphRieszOperator_pairing period hPeriod data
        analysis state test).symm

/-- Testing against the complete graph separates its Hilbert residual. -/
theorem globalCandidateAFullLLGraphRieszResidualPairing_separates
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (residual : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    (∀ test, globalCandidateAFullLLGraphRieszResidualPairing period hPeriod
      data analysis residual test = 0) ↔ residual = 0 := by
  letI : InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
    globalFullLLGraphInnerProductSpace period hPeriod data analysis
  constructor
  · intro hPairing
    exact (@inner_self_eq_zero Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) _ _
      (globalFullLLGraphInnerProductSpace period hPeriod data analysis)).mp
        (hPairing residual)
  · intro hResidual test
    rw [hResidual]
    exact inner_zero_left test

/-- Concrete separating residual representation of the complete LL Euler
covector. -/
def globalCandidateAFullLLGraphRieszResidualRepresentation
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAFullLLGraphForm period hPeriod data analysis
        state).toLinearMap where
  Residual := GlobalFullLLGraphHilbert period hPeriod data analysis
  zeroResidual := 0
  residual := globalCandidateAFullLLGraphRieszResidual period hPeriod data
    analysis state
  pairing := globalCandidateAFullLLGraphRieszResidualPairing period hPeriod
    data analysis
  represents := globalCandidateAFullLLGraphForm_eq_rieszResidualPairing period
    hPeriod data analysis state
  separates := globalCandidateAFullLLGraphRieszResidualPairing_separates period
    hPeriod data analysis
      (globalCandidateAFullLLGraphRieszResidual period hPeriod data analysis
        state)

/-- Stationarity of the genuine complete LL graph action is exactly its strong
Riesz equation. -/
theorem globalCandidateAFullLLGraphAction_fderiv_eq_zero_iff_rieszResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalFullLLGraphHilbert period hPeriod data analysis) :
    fderiv Real (globalCandidateAFullLLGraphAction period hPeriod data analysis)
        state = 0 ↔
      globalCandidateAFullLLGraphRieszResidual period hPeriod data analysis
        state = 0 := by
  rw [globalCandidateAFullLLGraphAction_fderiv]
  let representation :=
    globalCandidateAFullLLGraphRieszResidualRepresentation period hPeriod
      data analysis state
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
end P0EFTJanusProgramPGlobalEulerLagrangeLLGraphRieszResidual4D
end JanusFormal
