import Mathlib.LinearAlgebra.ExteriorPower.Basis
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D

/-!
# Algebraic determinant line of the T12 common-domain family

The constant kernel and cokernel transports induce equivalences on their top
exterior powers and hence on `Hom(det coker, det ker)`.  This is only the
algebraic Fredholm determinant line.  No topology, Quillen metric or
Bismut--Freed connection is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D

namespace CommonDomainFredholmIndexFamilyData

variable {Parameter Ambient Codomain : Type*}
  [AddCommGroup Ambient] [Module Real Ambient]
  [AddCommGroup Codomain] [Module Real Codomain] [TopologicalSpace Codomain]
  {operator : Parameter → Ambient →ₗ.[Real] Codomain}

/-- Exterior-power equivalence induced by a linear equivalence. -/
def exteriorPowerEquiv
    {first second : Type*}
    [AddCommGroup first] [Module Real first]
    [AddCommGroup second] [Module Real second]
    (degree : Nat) (equivalence : first ≃ₗ[Real] second) :
    ⋀[Real]^degree first ≃ₗ[Real] ⋀[Real]^degree second :=
  LinearEquiv.ofBijective
    (exteriorPower.map degree equivalence.toLinearMap)
    ⟨exteriorPower.map_injective_field equivalence.injective,
      exteriorPower.map_surjective equivalence.surjective⟩

/-- Fixed kernel determinant degree, anchored at one parameter. -/
abbrev kernelDeterminantDegree
    (_data : CommonDomainFredholmIndexFamilyData operator)
    (base : Parameter) : Nat :=
  Module.finrank Real (LinearMap.ker (operator base).toFun)

/-- Fixed cokernel determinant degree, anchored at one parameter. -/
abbrev cokernelDeterminantDegree
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base : Parameter) : Nat :=
  Module.finrank Real (data.cokernel base)

/-- Top exterior power of one actual kernel. -/
abbrev kernelDeterminant
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :=
  ⋀[Real]^(data.kernelDeterminantDegree base)
    (LinearMap.ker (operator parameter).toFun)

/-- Top exterior power of one actual cokernel. -/
abbrev cokernelDeterminant
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :=
  ⋀[Real]^(data.cokernelDeterminantDegree base) (data.cokernel parameter)

/-- Algebraic Fredholm determinant fibre `Hom(det coker, det ker)`. -/
abbrev determinantLine
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :=
  data.cokernelDeterminant base parameter →ₗ[Real]
    data.kernelDeterminant base parameter

/-- Kernel top-exterior transport induced by the stored kernel transport. -/
def kernelDeterminantTransport
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base first second : Parameter) :
    data.kernelDeterminant base first ≃ₗ[Real]
      data.kernelDeterminant base second :=
  exteriorPowerEquiv (data.kernelDeterminantDegree base)
    (data.kernelTransport first second)

/-- Cokernel top-exterior transport induced by the canonical quotient
transport. -/
def cokernelDeterminantTransport
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base first second : Parameter) :
    data.cokernelDeterminant base first ≃ₗ[Real]
      data.cokernelDeterminant base second :=
  exteriorPowerEquiv (data.cokernelDeterminantDegree base)
    (data.cokernelTransport first second)

/-- Algebraic trivialization of the Fredholm determinant line from the
anchored fibre. -/
def determinantTrivialization
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :
    data.determinantLine base base ≃ₗ[Real]
      data.determinantLine base parameter :=
  (data.cokernelDeterminantTransport base base parameter).arrowCongr
    (data.kernelDeterminantTransport base base parameter)

/-- Coherent transport obtained from the anchored trivialization.  This does
not require extra coherence assumptions on the stored pairwise kernel
transports. -/
def determinantTransport
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base first second : Parameter) :
    data.determinantLine base first ≃ₗ[Real]
      data.determinantLine base second :=
  (data.determinantTrivialization base first).symm.trans
    (data.determinantTrivialization base second)

/-- Every kernel determinant fibre is one-dimensional. -/
theorem kernelDeterminant_finrank_one
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :
    Module.finrank Real (data.kernelDeterminant base parameter) = 1 := by
  letI : FiniteDimensional Real
      (LinearMap.ker (operator parameter).toFun) :=
    (data.fredholm parameter).2.1
  change Module.finrank Real
      (⋀[Real]^(Module.finrank Real
        (LinearMap.ker (operator base).toFun))
        (LinearMap.ker (operator parameter).toFun)) = 1
  rw [exteriorPower.finrank_eq, data.kernel_finrank_eq parameter base,
    Nat.choose_self]

/-- Every cokernel determinant fibre is one-dimensional. -/
theorem cokernelDeterminant_finrank_one
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :
    Module.finrank Real (data.cokernelDeterminant base parameter) = 1 := by
  letI : FiniteDimensional Real (data.cokernel parameter) :=
    (data.fredholm parameter).2.2
  change Module.finrank Real
      (⋀[Real]^(Module.finrank Real (data.cokernel base))
        (data.cokernel parameter)) = 1
  rw [exteriorPower.finrank_eq, data.cokernel_finrank_eq parameter base,
    Nat.choose_self]

/-- Every algebraic Fredholm determinant fibre is a line. -/
theorem determinantLine_finrank_one
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :
    Module.finrank Real (data.determinantLine base parameter) = 1 := by
  letI : FiniteDimensional Real
      (LinearMap.ker (operator parameter).toFun) :=
    (data.fredholm parameter).2.1
  letI : FiniteDimensional Real (data.cokernel parameter) :=
    (data.fredholm parameter).2.2
  change Module.finrank Real
      (data.cokernelDeterminant base parameter →ₗ[Real]
        data.kernelDeterminant base parameter) = 1
  rw [Module.finrank_linearMap,
    data.cokernelDeterminant_finrank_one base parameter,
    data.kernelDeterminant_finrank_one base parameter, Nat.one_mul]

@[simp]
theorem determinantTransport_self
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base parameter : Parameter) :
    data.determinantTransport base parameter parameter =
      LinearEquiv.refl Real _ := by
  apply LinearEquiv.ext
  intro value
  simp [determinantTransport]

/-- Exact composition law for the anchored determinant-line transport. -/
theorem determinantTransport_trans
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base first second third : Parameter) :
    (data.determinantTransport base first second).trans
        (data.determinantTransport base second third) =
      data.determinantTransport base first third := by
  apply LinearEquiv.ext
  intro value
  simp [determinantTransport]

/-- Algebraic determinant-line certificate for a constant-defect family. -/
structure DeterminantLineCertificate
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base : Parameter) : Prop where
  fibreLine : ∀ parameter,
    Module.finrank Real (data.determinantLine base parameter) = 1
  transportBijective : ∀ first second,
    Function.Bijective (data.determinantTransport base first second)
  transportSelf : ∀ parameter,
    data.determinantTransport base parameter parameter =
      LinearEquiv.refl Real _
  transportTrans : ∀ first second third,
    (data.determinantTransport base first second).trans
        (data.determinantTransport base second third) =
      data.determinantTransport base first third

/-- Public algebraic determinant-line checkpoint. -/
def determinantLineCertificate
    (data : CommonDomainFredholmIndexFamilyData operator)
    (base : Parameter) :
    DeterminantLineCertificate data base where
  fibreLine := data.determinantLine_finrank_one base
  transportBijective := fun first second =>
    (data.determinantTransport base first second).bijective
  transportSelf := data.determinantTransport_self base
  transportTrans := data.determinantTransport_trans base

end CommonDomainFredholmIndexFamilyData
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D

namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsDeterminantLineFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The concrete algebraic determinant line of one T12 fibre. -/
abbrev ProgramPT12GaugeFixedLLFriedrichsD11DeterminantLine
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :=
  (programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily
    period hPeriod d9Ellipticity matterMass analysis).determinantLine 0 parameter

/-- Trivialization of the concrete determinant line from the zero fibre. -/
def programPT12GaugeFixedLLFriedrichsD11DeterminantTrivialization
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPT12GaugeFixedLLFriedrichsD11DeterminantLine
        period hPeriod d9Ellipticity matterMass analysis 0 ≃ₗ[Real]
      ProgramPT12GaugeFixedLLFriedrichsD11DeterminantLine
        period hPeriod d9Ellipticity matterMass analysis parameter :=
  (programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily
    period hPeriod d9Ellipticity matterMass analysis).determinantTrivialization
      0 parameter

/-- Coherent transport between two concrete determinant-line fibres. -/
def programPT12GaugeFixedLLFriedrichsD11DeterminantTransport
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    ProgramPT12GaugeFixedLLFriedrichsD11DeterminantLine
        period hPeriod d9Ellipticity matterMass analysis first ≃ₗ[Real]
      ProgramPT12GaugeFixedLLFriedrichsD11DeterminantLine
        period hPeriod d9Ellipticity matterMass analysis second :=
  (programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily
    period hPeriod d9Ellipticity matterMass analysis).determinantTransport
      0 first second

/-- Public T12 algebraic determinant-line gate. -/
def programPT12GaugeFixedLLFriedrichsD11DeterminantLineFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CommonDomainFredholmIndexFamilyData.DeterminantLineCertificate
      (programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily
        period hPeriod d9Ellipticity matterMass analysis) 0 :=
  (programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily
    period hPeriod d9Ellipticity matterMass analysis).determinantLineCertificate 0

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsDeterminantLineFamily4D
end JanusFormal
