import Mathlib.Algebra.Module.LinearMap.Index
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsConstantDefectFamily4D

/-!
# Fredholm-index family for the common-domain Friedrichs realization

The exact constancy of the kernel and range gives canonical transports of
both Fredholm defects and makes the algebraic Fredholm index constant.  This
packet applies directly to the common graph domain; it does not replace the
unbounded operators by bounded operators on another Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped LinearPMap
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsConstantDefectFamily4D

/-- A Fredholm family of linear maps on one fixed domain whose two defect
submodules are literally constant. -/
structure CommonDomainFredholmIndexFamilyData
    {Parameter Ambient Codomain : Type*}
    [AddCommGroup Ambient] [Module Real Ambient]
    [AddCommGroup Codomain] [Module Real Codomain] [TopologicalSpace Codomain]
    (operator : Parameter → Ambient →ₗ.[Real] Codomain) where
  domainConstant : ∀ first second,
    (operator first).domain = (operator second).domain
  fredholm : ∀ parameter,
    IsClosed (LinearMap.range (operator parameter).toFun : Set Codomain) ∧
      FiniteDimensional Real (LinearMap.ker (operator parameter).toFun) ∧
      FiniteDimensional Real
        (Codomain ⧸ LinearMap.range (operator parameter).toFun)
  kernelTransport : ∀ first second,
    LinearMap.ker (operator first).toFun ≃ₗ[Real]
      LinearMap.ker (operator second).toFun
  rangeConstant : ∀ first second,
    LinearMap.range (operator first).toFun =
      LinearMap.range (operator second).toFun

namespace CommonDomainFredholmIndexFamilyData

variable {Parameter Ambient Codomain : Type*}
  [AddCommGroup Ambient] [Module Real Ambient]
  [AddCommGroup Codomain] [Module Real Codomain] [TopologicalSpace Codomain]
  {operator : Parameter → Ambient →ₗ.[Real] Codomain}

/-- Algebraic cokernel of one fibre. -/
abbrev cokernel
    (_data : CommonDomainFredholmIndexFamilyData operator)
    (parameter : Parameter) :=
  Codomain ⧸ LinearMap.range (operator parameter).toFun

/-- Identity transport between the quotients by the equal range submodules. -/
def cokernelTransport
    (data : CommonDomainFredholmIndexFamilyData operator)
    (first second : Parameter) :
    data.cokernel first ≃ₗ[Real] data.cokernel second :=
  Submodule.quotEquivOfEq _ _ (data.rangeConstant first second)

/-- Kernel dimension is constant. -/
theorem kernel_finrank_eq
    (data : CommonDomainFredholmIndexFamilyData operator)
    (first second : Parameter) :
    Module.finrank Real (LinearMap.ker (operator first).toFun) =
      Module.finrank Real (LinearMap.ker (operator second).toFun) :=
  (data.kernelTransport first second).finrank_eq

/-- Cokernel dimension is constant. -/
theorem cokernel_finrank_eq
    (data : CommonDomainFredholmIndexFamilyData operator)
    (first second : Parameter) :
    Module.finrank Real (data.cokernel first) =
      Module.finrank Real (data.cokernel second) := by
  exact (data.cokernelTransport first second).finrank_eq

/-- The algebraic Fredholm index is constant along a constant-defect family. -/
theorem index_eq
    (data : CommonDomainFredholmIndexFamilyData operator)
    (first second : Parameter) :
    (operator first).toFun.index = (operator second).toFun.index := by
  rw [LinearMap.index_eq_finrank_sub,
    LinearMap.index_eq_finrank_sub,
    data.kernel_finrank_eq first second,
    data.cokernel_finrank_eq first second]

end CommonDomainFredholmIndexFamilyData

variable (period : Real) (hPeriod : period ≠ 0)

/-- The common-domain spectral--LL Friedrichs family as a genuine abstract
Fredholm-index family. -/
def programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CommonDomainFredholmIndexFamilyData
      (fun parameter : Real ↦
        programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter) where
  domainConstant first second := by
    rw [programPT12GaugeFixedLLFriedrichsD11Operator_domain,
      programPT12GaugeFixedLLFriedrichsD11Operator_domain]
  fredholm :=
    programPT12GaugeFixedLLFriedrichsD11Operator_fredholm
      period hPeriod d9Ellipticity matterMass analysis
  kernelTransport first second :=
    LinearEquiv.ofEq _ _
      (programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq
        period hPeriod covector matterMass analysis first second)
  rangeConstant :=
    programPT12GaugeFixedLLFriedrichsD11Operator_range_eq
      period hPeriod covector matterMass analysis

/-- Canonical kernel transport inside the actual common graph domain. -/
def programPT12GaugeFixedLLFriedrichsD11KernelTransport
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis first).toFun ≃ₗ[Real]
      LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis second).toFun :=
  LinearEquiv.ofEq _ _
    (programPT12GaugeFixedLLFriedrichsD11Operator_kernel_eq
      period hPeriod covector matterMass analysis first second)

/-- Canonical cokernel transport induced by constancy of the actual range. -/
def programPT12GaugeFixedLLFriedrichsD11CokernelTransport
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis ⧸
        LinearMap.range
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis first).toFun) ≃ₗ[Real]
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis ⧸
        LinearMap.range
          (programPT12GaugeFixedLLFriedrichsD11Operator
            period hPeriod covector matterMass analysis second).toFun) :=
  Submodule.quotEquivOfEq _ _
    (programPT12GaugeFixedLLFriedrichsD11Operator_range_eq
      period hPeriod covector matterMass analysis first second)

/-- The Fredholm index of the common-domain family is independent of the D11
parameter. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_index_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    (programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis first).toFun.index =
      (programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis second).toFun.index := by
  rw [LinearMap.index_eq_finrank_sub,
    LinearMap.index_eq_finrank_sub,
    programPT12GaugeFixedLLFriedrichsD11Operator_kernel_finrank_eq
      period hPeriod covector matterMass analysis first second,
    programPT12GaugeFixedLLFriedrichsD11Operator_cokernel_finrank_eq
      period hPeriod covector matterMass analysis first second]

/-- Public constant-index family gate. -/
def programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CommonDomainFredholmIndexFamilyData
      (fun parameter : Real ↦
        programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter) :=
  programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily
    period hPeriod d9Ellipticity matterMass analysis

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D
end JanusFormal
