import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D

/-!
# Self-adjoint common-domain spectral--LL Friedrichs family

Dense formal self-adjointness plus surjectivity gives self-adjointness for a
real `LinearPMap`.  Applied to every nonnegative LL shift, this closes the
self-adjointness of the D11 product family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSelfAdjointFamily4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped LinearPMap
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusImmersionFiberAlgebra

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

/-- A densely defined, formally self-adjoint, surjective real operator is
self-adjoint. -/
theorem linearPMap_isSelfAdjoint_of_dense_of_isFormalAdjoint_of_surjective
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    (operator : E →ₗ.[Real] E)
    (hDense : Dense (operator.domain : Set E))
    (hFormal : operator.IsFormalAdjoint operator)
    (hSurjective : Function.Surjective operator) :
    IsSelfAdjoint operator := by
  have hOperatorLeAdjoint : operator ≤ operator.adjoint :=
    hFormal.le_adjoint hDense
  have hAdjointDomain : operator.adjoint.domain ≤ operator.domain := by
    intro state hState
    let adjointState : operator.adjoint.domain := ⟨state, hState⟩
    obtain ⟨preimage, hPreimage⟩ :=
      hSurjective (operator.adjoint adjointState)
    have hStateEq : (preimage : E) = state := by
      apply ext_inner_left Real
      intro test
      obtain ⟨testPreimage, hTestPreimage⟩ := hSurjective test
      have hAdjoint :=
        LinearPMap.adjoint_isFormalAdjoint hDense
          adjointState testPreimage
      calc
        inner Real test (preimage : E) =
            inner Real (operator testPreimage) (preimage : E) := by
          rw [hTestPreimage]
        _ = inner Real (testPreimage : E) (operator preimage) :=
          hFormal testPreimage preimage
        _ = inner Real (testPreimage : E)
            (operator.adjoint adjointState) := by
          rw [hPreimage]
        _ = inner Real (operator.adjoint adjointState)
            (testPreimage : E) := real_inner_comm _ _
        _ = inner Real (adjointState : E)
            (operator testPreimage) := hAdjoint
        _ = inner Real (operator testPreimage)
            (adjointState : E) := real_inner_comm _ _
        _ = inner Real test state := by
          rw [hTestPreimage]
    exact hStateEq ▸ preimage.2
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt
    (le_antisymm hAdjointDomain hOperatorLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hOperatorLeAdjoint.2 hState.symm).symm

variable (period : Real) (hPeriod : period ≠ 0)

/-- A real scalar shift preserves formal self-adjointness on the Friedrichs
domain. -/
theorem canonicalLLFriedrichsShiftedJacobi_isFormalAdjoint_self
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) :
    (canonicalLLFriedrichsShiftedJacobi
      period hPeriod analysis shift).IsFormalAdjoint
        (canonicalLLFriedrichsShiftedJacobi
          period hPeriod analysis shift) := by
  intro first second
  have hBase := canonicalLLFriedrichsJacobi_isFormalAdjoint_self
    period hPeriod analysis first second
  rw [canonicalLLFriedrichsShiftedJacobi_apply,
    canonicalLLFriedrichsShiftedJacobi_apply,
    inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hBase]

/-- Every nonnegative scalar shift of the canonical LL Friedrichs operator is
self-adjoint. -/
theorem canonicalLLFriedrichsShiftedJacobi_isSelfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    IsSelfAdjoint
      (canonicalLLFriedrichsShiftedJacobi
        period hPeriod analysis shift) := by
  apply linearPMap_isSelfAdjoint_of_dense_of_isFormalAdjoint_of_surjective
  · exact canonicalLLFriedrichsJacobi_domain_dense
      period hPeriod analysis
  · exact canonicalLLFriedrichsShiftedJacobi_isFormalAdjoint_self
      period hPeriod analysis shift
  · exact canonicalLLFriedrichsShiftedJacobi_surjective
      period hPeriod analysis shift hShift

/-- Self-adjointness of the LL fibre at every D11 parameter. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLOperator_selfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsSelfAdjoint
      (programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter) :=
  canonicalLLFriedrichsShiftedJacobi_isSelfAdjoint
    period hPeriod analysis
    (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
    (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter)

local instance programPT12GaugeFixedLLFriedrichsD11LinearPMapStar
    {configuration : GlobalFieldConfiguration period hPeriod}
    (ι : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Star
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis →ₗ.[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis) :=
  LinearPMap.instStar

/-- Every fibre of the common-domain spectral--LL family is self-adjoint. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_selfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsSelfAdjoint
      (programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter) := by
  have hSpectral :=
    programPGlobalGaugeFixedSpectralHessianRealOperator_selfAdjoint
      period hPeriod covector matterMass
  unfold
    programPGlobalGaugeFixedSpectralHessianHilbertRealLinearPMapStar at hSpectral
  exact linearPMapProd_selfAdjoint _ _ hSpectral
    (programPT12GaugeFixedLLFriedrichsD11LLOperator_selfAdjoint
      period hPeriod analysis parameter)

theorem programPT12GaugeFixedLLFriedrichsD11Operator_closed
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).IsClosed :=
  (programPT12GaugeFixedLLFriedrichsD11Operator_selfAdjoint
    period hPeriod covector matterMass analysis parameter).isClosed

/-- Positive self-adjoint-family gate on the already proved common domain. -/
theorem programPT12GaugeFixedLLFriedrichsD11SelfAdjointFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ∀ parameter : Real,
      IsSelfAdjoint
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis parameter) ∧
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).IsClosed :=
  fun parameter =>
    ⟨programPT12GaugeFixedLLFriedrichsD11Operator_selfAdjoint
        period hPeriod covector matterMass analysis parameter,
      programPT12GaugeFixedLLFriedrichsD11Operator_closed
        period hPeriod covector matterMass analysis parameter⟩

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSelfAdjointFamily4D
end JanusFormal
