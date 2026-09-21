import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D

/-!
# A common-domain D11 family for the spectral--LL Friedrichs product

The real parameter `a` shifts only the canonical LL Friedrichs block by
`a ^ 2`.  Thus every fibre has the same dense domain, the fibre at zero is
the existing spectral--LL product, and the LL shifted resolvent is compact
and two-sided.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 120000
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
open P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- A nonnegative D11 parameterization that retains the unshifted fibre at
the origin. -/
def programPT12GaugeFixedLLFriedrichsD11Shift
    (parameter : Real) : Real :=
  parameter ^ 2

theorem programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative
    (parameter : Real) :
    0 ≤ programPT12GaugeFixedLLFriedrichsD11Shift parameter :=
  sq_nonneg parameter

/-- The LL component of the D11 family. -/
abbrev programPT12GaugeFixedLLFriedrichsD11LLOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    CanonicalLLL2 period hPeriod analysis →ₗ.[Real]
      CanonicalLLL2 period hPeriod analysis :=
  canonicalLLFriedrichsShiftedJacobi period hPeriod analysis
    (programPT12GaugeFixedLLFriedrichsD11Shift parameter)

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11LLOperator_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis 0 =
      canonicalLLFriedrichsJacobi period hPeriod analysis := by
  apply LinearPMap.dExt
    (f := programPT12GaugeFixedLLFriedrichsD11LLOperator
      period hPeriod analysis 0)
    (g := canonicalLLFriedrichsJacobi period hPeriod analysis) rfl
  intro shiftedField baseField hField
  have hFields : shiftedField = baseField := Subtype.ext hField
  subst baseField
  simp [canonicalLLFriedrichsShiftedJacobi_apply,
    programPT12GaugeFixedLLFriedrichsD11Shift]

/-- Fixed spectral block times the shifted LL Friedrichs block. -/
abbrev programPT12GaugeFixedLLFriedrichsD11Operator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod ι analysis →ₗ.[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod ι analysis :=
  linearPMapProd
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass)
    (programPT12GaugeFixedLLFriedrichsD11LLOperator
      period hPeriod analysis parameter)

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11Operator_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis 0 =
      programPGlobalGaugeFixedLLFriedrichsHessianOperator
        period hPeriod covector matterMass analysis := by
  change linearPMapProd _
      (programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis 0) =
    linearPMapProd _
      (canonicalLLFriedrichsJacobi period hPeriod analysis)
  rw [programPT12GaugeFixedLLFriedrichsD11LLOperator_zero]

/-- The exact common graph domain of the family. -/
abbrev ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  (programPGlobalGaugeFixedLLFriedrichsHessianOperator
    period hPeriod covector matterMass analysis).domain

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11Operator_domain
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain =
      ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
        period hPeriod covector matterMass analysis :=
  rfl

theorem programPT12GaugeFixedLLFriedrichsD11Operator_domain_dense
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    Dense
      ((programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).domain :
        Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis)) :=
  linearPMapProd_domain_dense _ _
    (programPGlobalGaugeFixedSpectralHessianRealDomain_dense
      period hPeriod covector matterMass)
    (canonicalLLFriedrichsJacobi_domain_dense period hPeriod analysis)

/-- Compact ambient inverse of the shifted LL fibre. -/
def programPT12GaugeFixedLLFriedrichsD11LLResolvent
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    CanonicalLLL2 period hPeriod analysis →L[Real]
      CanonicalLLL2 period hPeriod analysis :=
  canonicalLLFriedrichsShiftedResolvent period hPeriod analysis
    (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
    (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter)

theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_compact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter) :=
  canonicalLLFriedrichsShiftedResolvent_compact period hPeriod analysis
    (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
    (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter)

theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_right_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (source : CanonicalLLL2 period hPeriod analysis) :
    programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter
        (canonicalLLFriedrichsShiftedWeakDomainElement
          period hPeriod analysis
          (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
          (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter)
          source) =
      source :=
  canonicalLLFriedrichsShiftedResolvent_right_inverse
    period hPeriod analysis
    (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
    (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter)
    source

theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_left_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (field : (canonicalLLFriedrichsJacobi
      period hPeriod analysis).domain) :
    programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter field) =
      (field : CanonicalLLL2 period hPeriod analysis) :=
  canonicalLLFriedrichsShiftedResolvent_left_inverse
    period hPeriod analysis
    (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
    (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter)
    field

theorem programPT12GaugeFixedLLFriedrichsD11LLOperator_range_eq_top
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    LinearMap.range
        (programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter).toFun =
      (⊤ : Submodule Real (CanonicalLLL2 period hPeriod analysis)) :=
  LinearMap.range_eq_top.mpr
    (canonicalLLFriedrichsShiftedJacobi_surjective
      period hPeriod analysis
      (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
      (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter))

theorem programPT12GaugeFixedLLFriedrichsD11LLOperator_ker_eq_bot
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter).toFun =
      (⊥ : Submodule Real
        (programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter).domain) :=
  LinearMap.ker_eq_bot.mpr
    (canonicalLLFriedrichsShiftedJacobi_injective
      period hPeriod analysis
      (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
      (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter))

theorem programPT12GaugeFixedLLFriedrichsD11LLOperator_fredholm
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsClosed
        (LinearMap.range
          (programPT12GaugeFixedLLFriedrichsD11LLOperator
            period hPeriod analysis parameter).toFun :
          Set (CanonicalLLL2 period hPeriod analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPT12GaugeFixedLLFriedrichsD11LLOperator
            period hPeriod analysis parameter).toFun) ∧
      FiniteDimensional Real
        ((CanonicalLLL2 period hPeriod analysis) ⧸
          LinearMap.range
            (programPT12GaugeFixedLLFriedrichsD11LLOperator
              period hPeriod analysis parameter).toFun) := by
  rw [programPT12GaugeFixedLLFriedrichsD11LLOperator_range_eq_top,
    programPT12GaugeFixedLLFriedrichsD11LLOperator_ker_eq_bot]
  exact ⟨isClosed_univ, FiniteDimensional.of_rank_eq_zero (by simp),
    FiniteDimensional.of_rank_eq_zero (by simp)⟩

theorem programPT12GaugeFixedLLFriedrichsD11Operator_fredholm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsClosed
        (LinearMap.range
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis parameter).toFun :
          Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod ι analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis parameter).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod ι analysis ⧸
          LinearMap.range
            (programPT12GaugeFixedLLFriedrichsD11Operator
              period hPeriod covector matterMass analysis parameter).toFun) :=
  linearPMapProd_fredholm _ _
    (programPGlobalGaugeFixedSpectralHessianRealOperator_fredholm
      period hPeriod d9Ellipticity matterMass)
    (programPT12GaugeFixedLLFriedrichsD11LLOperator_fredholm
      period hPeriod analysis parameter)

/-- Positive gate: an actual real family on one dense graph domain, with a
compact two-sided LL resolvent at every parameter. -/
structure ProgramPT12GaugeFixedLLFriedrichsD11CommonDomainFamilyCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) : Prop where
  commonDomain : ∀ parameter,
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain =
      ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
        period hPeriod covector matterMass analysis
  domainDense : ∀ parameter,
    Dense
      ((programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).domain :
        Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis))
  llResolventCompact : ∀ parameter,
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter)

theorem programPT12GaugeFixedLLFriedrichsD11CommonDomainFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPT12GaugeFixedLLFriedrichsD11CommonDomainFamilyCertificate4D
      period hPeriod covector matterMass analysis where
  commonDomain :=
    programPT12GaugeFixedLLFriedrichsD11Operator_domain
      period hPeriod covector matterMass analysis
  domainDense :=
    programPT12GaugeFixedLLFriedrichsD11Operator_domain_dense
      period hPeriod covector matterMass analysis
  llResolventCompact :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_compact
      period hPeriod analysis

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
end JanusFormal
