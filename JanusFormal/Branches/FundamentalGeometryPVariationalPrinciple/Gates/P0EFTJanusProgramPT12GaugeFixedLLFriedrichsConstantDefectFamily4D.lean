import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D

/-!
# Constant Fredholm defect of the spectral--LL Friedrichs family

The shifted LL block is bijective at every parameter.  Consequently the
kernel and range of the product family are exactly the zero extension of the
fixed spectral kernel and the product of the fixed spectral range with the
whole LL Hilbert space.  In particular both defects are independent of the
parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsConstantDefectFamily4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped LinearPMap
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- First-coordinate projection from the common product domain to the fixed
spectral domain. -/
def programPT12GaugeFixedLLFriedrichsD11CommonDomainSpectralProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
        period hPeriod covector matterMass analysis →ₗ[Real]
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain where
  toFun state := ⟨(WithLp.ofLp state.1).1, state.2.1⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Ambient LL coordinate of a vector in the common product domain. -/
def programPT12GaugeFixedLLFriedrichsD11CommonDomainLLValue
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
        period hPeriod covector matterMass analysis →ₗ[Real]
      CanonicalLLL2 period hPeriod analysis where
  toFun state := (WithLp.ofLp state.1).2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The fixed spectral kernel, embedded in the common domain with zero LL
coordinate. -/
def programPT12GaugeFixedLLFriedrichsD11SpectralKernelLift
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Submodule Real
      (ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
        period hPeriod covector matterMass analysis) :=
  (LinearMap.ker
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).toFun).comap
    (programPT12GaugeFixedLLFriedrichsD11CommonDomainSpectralProjection
      period hPeriod covector matterMass analysis) ⊓
  LinearMap.ker
    (programPT12GaugeFixedLLFriedrichsD11CommonDomainLLValue
      period hPeriod covector matterMass analysis)

/-- The fixed spectral range times the whole LL Hilbert factor. -/
def programPT12GaugeFixedLLFriedrichsD11SpectralRangeLift
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Submodule Real
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis) :=
  ((LinearMap.range
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).toFun).prod
    (⊤ : Submodule Real (CanonicalLLL2 period hPeriod analysis))).map
      (WithLp.linearEquiv 2 Real
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota ×
          CanonicalLLL2 period hPeriod analysis)).symm.toLinearMap

/-- Every fibre kernel is exactly the fixed spectral kernel with zero LL
coordinate. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq_spectralLift
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).toFun =
      programPT12GaugeFixedLLFriedrichsD11SpectralKernelLift
        period hPeriod covector matterMass analysis := by
  ext state
  let spectralState :=
    programPT12GaugeFixedLLFriedrichsD11CommonDomainSpectralProjection
      period hPeriod covector matterMass analysis state
  let llState :
      (programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter).domain :=
    ⟨(WithLp.ofLp state.1).2, state.2.2⟩
  change
    WithLp.toLp 2
        (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass spectralState,
          programPT12GaugeFixedLLFriedrichsD11LLOperator
            period hPeriod analysis parameter llState) = 0 ↔
      programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
          period hPeriod covector matterMass spectralState = 0 ∧
        (llState : CanonicalLLL2 period hPeriod analysis) = 0
  constructor
  · intro hState
    have hPair := congrArg
      (WithLp.linearEquiv 2 Real
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota ×
          CanonicalLLL2 period hPeriod analysis)) hState
    have hPair' :
        (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass spectralState,
          programPT12GaugeFixedLLFriedrichsD11LLOperator
            period hPeriod analysis parameter llState) = (0, 0) := by
      simpa using hPair
    refine ⟨congrArg Prod.fst hPair', ?_⟩
    have hLLImage :
        programPT12GaugeFixedLLFriedrichsD11LLOperator
            period hPeriod analysis parameter llState = 0 :=
      congrArg Prod.snd hPair'
    have hInjective : Function.Injective
        (programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter).toFun :=
      LinearMap.ker_eq_bot.mp
        (programPT12GaugeFixedLLFriedrichsD11LLOperator_ker_eq_bot
          period hPeriod analysis parameter)
    have hLLState : llState = 0 := by
      apply hInjective
      simpa using hLLImage
    exact congrArg Subtype.val hLLState
  · rintro ⟨hSpectral, hLLValue⟩
    have hLLState : llState = 0 := by
      apply Subtype.ext
      exact hLLValue
    rw [hSpectral, hLLState]
    simp

/-- Every fibre range is the fixed spectral range times the full LL factor. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_range_eq_spectralLift
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    LinearMap.range
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).toFun =
      programPT12GaugeFixedLLFriedrichsD11SpectralRangeLift
        period hPeriod covector matterMass analysis := by
  unfold programPT12GaugeFixedLLFriedrichsD11SpectralRangeLift
  change LinearMap.range
      (linearPMapProd
        (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
          period hPeriod covector matterMass)
        (programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter)).toFun = _
  rw [linearPMapProd_range
      (E := ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
      (F := CanonicalLLL2 period hPeriod analysis),
    programPT12GaugeFixedLLFriedrichsD11LLOperator_range_eq_top]
  rfl

/-- The kernel submodule is independent of the D11 parameter. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis first).toFun =
      LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis second).toFun := by
  rw [programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq_spectralLift,
    programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq_spectralLift]

/-- The range submodule is independent of the D11 parameter. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_range_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    LinearMap.range
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis first).toFun =
      LinearMap.range
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis second).toFun := by
  rw [programPT12GaugeFixedLLFriedrichsD11Operator_range_eq_spectralLift,
    programPT12GaugeFixedLLFriedrichsD11Operator_range_eq_spectralLift]

/-- Kernel dimension is constant along the family. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_kernel_finrank_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    Module.finrank Real
        (LinearMap.ker
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis first).toFun) =
      Module.finrank Real
        (LinearMap.ker
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis second).toFun) := by
  rw [programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq
    period hPeriod covector matterMass analysis first second]
  rfl

/-- Cokernel dimension is constant along the family. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_cokernel_finrank_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    Module.finrank Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis ⧸
          LinearMap.range
            (programPT12GaugeFixedLLFriedrichsD11Operator
              period hPeriod covector matterMass analysis first).toFun) =
      Module.finrank Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis ⧸
          LinearMap.range
            (programPT12GaugeFixedLLFriedrichsD11Operator
              period hPeriod covector matterMass analysis second).toFun) := by
  rw [programPT12GaugeFixedLLFriedrichsD11Operator_range_eq
    period hPeriod covector matterMass analysis first second]

/-- Auditable constant-defect package for the common-domain family. -/
structure ProgramPT12GaugeFixedLLFriedrichsD11ConstantDefectCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) : Prop where
  kernelSpectral : ∀ parameter,
    LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).toFun =
      programPT12GaugeFixedLLFriedrichsD11SpectralKernelLift
        period hPeriod covector matterMass analysis
  rangeSpectral : ∀ parameter,
    LinearMap.range
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).toFun =
      programPT12GaugeFixedLLFriedrichsD11SpectralRangeLift
        period hPeriod covector matterMass analysis
  kernelConstant : ∀ first second,
    LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis first).toFun =
      LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis second).toFun
  rangeConstant : ∀ first second,
    LinearMap.range
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis first).toFun =
      LinearMap.range
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis second).toFun
  fredholm : ∀ parameter,
    IsClosed
        (LinearMap.range
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis parameter).toFun :
          Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis parameter).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis ⧸
          LinearMap.range
            (programPT12GaugeFixedLLFriedrichsD11Operator
              period hPeriod covector matterMass analysis parameter).toFun)

theorem programPT12GaugeFixedLLFriedrichsD11ConstantDefectFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPT12GaugeFixedLLFriedrichsD11ConstantDefectCertificate4D
      period hPeriod d9Ellipticity matterMass analysis where
  kernelSpectral :=
    programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq_spectralLift
      period hPeriod covector matterMass analysis
  rangeSpectral :=
    programPT12GaugeFixedLLFriedrichsD11Operator_range_eq_spectralLift
      period hPeriod covector matterMass analysis
  kernelConstant :=
    programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq
      period hPeriod covector matterMass analysis
  rangeConstant :=
    programPT12GaugeFixedLLFriedrichsD11Operator_range_eq
      period hPeriod covector matterMass analysis
  fredholm :=
    programPT12GaugeFixedLLFriedrichsD11Operator_fredholm
      period hPeriod d9Ellipticity matterMass analysis

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsConstantDefectFamily4D
end JanusFormal
