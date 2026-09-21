import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSelfAdjointFamily4D

/-!
# Self-adjoint physical Friedrichs family

A bounded self-adjoint perturbation of a self-adjoint real `LinearPMap`
preserves self-adjointness and its domain.  This applies to the transported
physical Riesz residual.  Since that residual is independent of the D11
parameter, the common-domain derivative remains the LL variation operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSelfAdjointFamily4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

/-- A bounded self-adjoint perturbation preserves self-adjointness of a real
partially defined operator. -/
theorem linearPMap_vadd_isSelfAdjoint_of_selfAdjoint_boundedPerturbation
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    (operator : E →ₗ.[Real] E)
    (perturbation : E →L[Real] E)
    (hOperator : IsSelfAdjoint operator)
    (hPerturbation : IsSelfAdjoint perturbation) :
    IsSelfAdjoint (perturbation.toLinearMap +ᵥ operator) := by
  have hOperatorFormal : operator.IsFormalAdjoint operator := by
    have hAdjointFormal :=
      LinearPMap.adjoint_isFormalAdjoint hOperator.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hOperator] at hAdjointFormal
  have hSumFormal :
      (perturbation.toLinearMap +ᵥ operator).IsFormalAdjoint
        (perturbation.toLinearMap +ᵥ operator) := by
    intro first second
    change inner Real
        (perturbation first + operator first) (second : E) =
      inner Real (first : E) (perturbation second + operator second)
    rw [inner_add_left, inner_add_right]
    have hPerturbationPairing :
        inner Real (perturbation (first : E)) (second : E) =
          inner Real (first : E) (perturbation (second : E)) := by
      simpa only [ContinuousLinearMap.coe_coe] using
        hPerturbation.isSymmetric (first : E) (second : E)
    exact congrArg₂ (· + ·) hPerturbationPairing
      (hOperatorFormal first second)
  have hSumLeAdjoint :
      perturbation.toLinearMap +ᵥ operator ≤
        (perturbation.toLinearMap +ᵥ operator).adjoint :=
    hSumFormal.le_adjoint hOperator.dense_domain
  have hAdjointDomain :
      (perturbation.toLinearMap +ᵥ operator).adjoint.domain ≤
        (perturbation.toLinearMap +ᵥ operator).domain := by
    intro state hState
    have hSum : Continuous (fun input : operator.domain =>
        inner Real state (perturbation input.1 + operator input)) := by
      have h :=
        ((perturbation.toLinearMap +ᵥ operator).mem_adjoint_domain_iff
          state).mp hState
      change Continuous (fun input : operator.domain =>
        inner Real state (perturbation input.1 + operator input)) at h
      exact h
    have hBounded : Continuous (fun input : operator.domain =>
        inner Real state (perturbation input.1)) := by
      fun_prop
    have hBase : Continuous (fun input : operator.domain =>
        inner Real state (operator input)) := by
      simpa only [Pi.sub_apply, inner_add_right, add_sub_cancel_left] using
        hSum.sub hBounded
    have hStateAdjoint : state ∈ operator.adjoint.domain := by
      rw [operator.mem_adjoint_domain_iff]
      change Continuous (fun input : operator.domain =>
        inner Real state (operator input))
      exact hBase
    rw [LinearPMap.isSelfAdjoint_def.mp hOperator] at hStateAdjoint
    exact hStateAdjoint
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt
    (le_antisymm hAdjointDomain hSumLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hSumLeAdjoint.2 hState.symm).symm

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance programPT12GaugeFixedLLFriedrichsPhysicalLinearPMapStar
    {configuration : GlobalFieldConfiguration period hPeriod}
    (ι : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Star
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis →ₗ.[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis) :=
  LinearPMap.instStar

local instance programPT12GaugeFixedLLFriedrichsPhysicalContinuousLinearMapStar
    {configuration : GlobalFieldConfiguration period hPeriod}
    (ι : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Star
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis →L[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis) :=
  ContinuousLinearMap.instStarId

section Physical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

/-- The transported bounded physical perturbation is symmetric. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_isSymmetric
    {iota : Type*} [DecidableEq iota] :
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod).toLinearMap.IsSymmetric := by
  intro first second
  calc
    inner Real
        (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod first)
        second =
      programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod first second :=
      programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_pairing
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod first second
    _ = programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod second first :=
      programPT12GaugeFixedLLFriedrichsPhysicalResidualForm_symmetric
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod first second
    _ = inner Real
        (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod second)
        first :=
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_pairing
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod second first).symm
    _ = inner Real first
        (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod second) :=
      real_inner_comm _ _

/-- The transported physical perturbation is a bounded self-adjoint
operator. -/
theorem programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_isSelfAdjoint
    {iota : Type*} [DecidableEq iota] :
    IsSelfAdjoint
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod) :=
  (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_isSymmetric
    (configuration := configuration) (data := data) (analysis := analysis)
      (chart := chart) (sameAction := sameAction) (physical := physical)
        (iota := iota) period hPeriod).isSelfAdjoint

/-- Every fibre of the physical common-domain family is self-adjoint. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_selfAdjoint
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real) :
    IsSelfAdjoint
      (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod covector parameter) := by
  rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator]
  exact
    linearPMap_vadd_isSelfAdjoint_of_selfAdjoint_boundedPerturbation
      (programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
        couplings.matterMassSquared analysis parameter)
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod)
      (programPT12GaugeFixedLLFriedrichsD11Operator_selfAdjoint
        period hPeriod covector couplings.matterMassSquared analysis parameter)
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_isSelfAdjoint
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod)

/-- Every fibre of the physical common-domain family is closed. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_closed
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter).IsClosed :=
  (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_selfAdjoint
    (configuration := configuration) (data := data) (analysis := analysis)
      (chart := chart) (sameAction := sameAction) (physical := physical)
        period hPeriod covector parameter).isClosed

/-- The bounded physical residual is parameter-independent, so the derivative
on the common domain is the original LL variation operator. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_apply_hasDerivAt
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real)
    (state : ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
      covector couplings.matterMassSquared analysis) :
    HasDerivAt
      (fun value =>
        programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                period hPeriod covector value state)
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter state.1)
      parameter := by
  have hBase :=
    programPT12GaugeFixedLLFriedrichsD11Operator_apply_hasDerivAt
      period hPeriod couplings.matterMassSquared analysis parameter state
  change HasDerivAt
    (fun value =>
      programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod state.1 +
        programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
          couplings.matterMassSquared analysis value state)
    (programPT12GaugeFixedLLFriedrichsD11VariationOperator
      (iota := iota) period hPeriod analysis parameter state.1)
    parameter
  convert hBase.const_add
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod state.1) using 1

/-- Positive gate for the self-adjoint, closed physical family on the proved
common domain. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalSelfAdjointFamily_gate
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    ∀ parameter : Real,
      (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).domain =
          ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
            covector couplings.matterMassSquared analysis ∧
        IsSelfAdjoint
          (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
            (configuration := configuration) (data := data)
              (analysis := analysis) (chart := chart)
                (sameAction := sameAction) (physical := physical)
                  period hPeriod covector parameter) ∧
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).IsClosed := by
  intro parameter
  exact ⟨
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_domain
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter,
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_selfAdjoint
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter,
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_closed
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter⟩

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D
end JanusFormal
