import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalProperShiftFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D

/-!
# D10-free gauge--ghost spectral target

This corrects one field-content error in the historical global target: it
combines the existing D9 gauge--ghost multiplier with two signed SpinC matter
sectors while leaving D10 as background spectral data for regulator and
determinant constructions.

This file proves the maximal analytic realization is densely defined,
self-adjoint, closed and Fredholm under the existing finite-characteristic
D9 hypothesis.  It is not yet the complete action Hessian: the installed D9
packet has no distinct antighost/Nakanishi--Lautrup fields, and metric/normal
action blocks and the global chart agreement remain separate gates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- D10-free mode family of the current gauge--ghost spectral target. -/
abbrev ProgramPGlobalGaugeFixedSpectralHessianMode (ι : Type*) :=
  (ι × Fin 8) ⊕
    (Sector × PrimitiveSpinCGeometricSignedMode)

local instance programPGlobalGaugeFixedSpectralHessianModeDecidableEq
    (ι : Type*) [DecidableEq ι] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode ι) :=
  Classical.decEq _

/-- Exact block weight: D9 gauge--ghost and two copies of `2D + m²`. -/
def programPGlobalGaugeFixedSpectralHessianWeight
    {ι : Type*}
    (covector : ι → TangentVector3)
    (matterMass : Real) :
    ProgramPGlobalGaugeFixedSpectralHessianMode ι → Real :=
  complexDiagonalSumWeight
    (d9GaugeGhostUnboundedWeight covector)
    (fun mode : Sector × PrimitiveSpinCGeometricSignedMode =>
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode.2 + matterMass)

@[simp]
theorem programPGlobalGaugeFixedSpectralHessianWeight_d9
    {ι : Type*}
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (mode : ι × Fin 8) :
    programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass (.inl mode) =
      d9GaugeGhostUnboundedWeight covector mode :=
  rfl

@[simp]
theorem programPGlobalGaugeFixedSpectralHessianWeight_matter
    {ι : Type*}
    (covector : ι → TangentVector3)
    (matterMass : Real)
    (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode) :
    programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass (.inr (sector, mode)) =
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + matterMass :=
  rfl

/-- Ellipticity modulo the genuine finite D9 and mass-resonant matter
kernels. -/
def programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real) :
    ComplexDiagonalFiniteZeroGap
      (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
      (programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass) :=
  complexDiagonalFiniteZeroGap_sum
    (d9GaugeGhostUnboundedWeight covector)
    (fun mode : Sector × PrimitiveSpinCGeometricSignedMode =>
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode.2 + matterMass)
    d9Ellipticity.toFiniteZeroGap
    (complexDiagonalFiniteZeroGap_finiteProduct
      PrimitiveSpinCGeometricSignedMode
      (fun mode =>
        primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + matterMass)
      (primitiveSpinCGeometricSignedActionHessianFiniteZeroGap
        period hPeriod matterMass))

/-- Ambient complex Hilbert space of the D10-free spectral target. -/
abbrev ProgramPGlobalGaugeFixedSpectralHessianHilbert (ι : Type*) :=
  ComplexDiagonalHilbert
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)

local instance
    programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
    (ι : Type*) :
    InnerProductSpace Real
      (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι) :=
  InnerProductSpace.complexToReal

local instance
    programPGlobalGaugeFixedSpectralHessianHilbertRealLinearPMapStar
    (ι : Type*) :
    Star (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι →ₗ.[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert ι) :=
  LinearPMap.instStar

/-- Maximal complex realization on the D10-free target mode space. -/
abbrev programPGlobalGaugeFixedSpectralHessianMaximalOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :=
  complexDiagonalOperator
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)

/-- Underlying real maximal realization proposed for variational comparison. -/
abbrev programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :=
  complexDiagonalRealOperator
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)

theorem programPGlobalGaugeFixedSpectralHessianRealDomain_dense
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :
    Dense
      ((programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain :
        Set (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)) :=
  complexDiagonalRealDomain_dense
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)

theorem programPGlobalGaugeFixedSpectralHessianRealOperator_selfAdjoint
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :
    IsSelfAdjoint
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass) :=
  complexDiagonalRealOperator_isSelfAdjoint
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)

theorem programPGlobalGaugeFixedSpectralHessianRealOperator_closed
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (matterMass : Real) :
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass).IsClosed :=
  complexDiagonalRealOperator_isClosed
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)

/-- Real Fredholm theorem for the D10-free spectral block. -/
theorem programPGlobalGaugeFixedSpectralHessianRealOperator_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real) :
    IsClosed
        (LinearMap.range
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).toFun :
          Set (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι ⧸
          LinearMap.range
            (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
              period hPeriod covector matterMass).toFun) :=
  complexDiagonalRealOperator_fredholm_of_finiteZeroGap
    (ProgramPGlobalGaugeFixedSpectralHessianMode ι)
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)
    (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity matterMass)

/-- Consolidated analytic certificate for the corrected spectral target. -/
structure ProgramPGlobalGaugeFixedSpectralHessianFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real) : Prop where
  domainDense :
    Dense
      ((programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain :
        Set (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι))
  selfAdjoint :
    IsSelfAdjoint
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass)
  closed :
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass).IsClosed
  fredholm :
    IsClosed
        (LinearMap.range
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).toFun :
          Set (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
            period hPeriod covector matterMass).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert ι ⧸
          LinearMap.range
            (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
              period hPeriod covector matterMass).toFun)

def programPGlobalGaugeFixedSpectralHessianFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real) :
    ProgramPGlobalGaugeFixedSpectralHessianFredholmCertificate4D
      period hPeriod d9Ellipticity matterMass where
  domainDense :=
    programPGlobalGaugeFixedSpectralHessianRealDomain_dense
      period hPeriod covector matterMass
  selfAdjoint :=
    programPGlobalGaugeFixedSpectralHessianRealOperator_selfAdjoint
      period hPeriod covector matterMass
  closed :=
    programPGlobalGaugeFixedSpectralHessianRealOperator_closed
      period hPeriod covector matterMass
  fredholm :=
    programPGlobalGaugeFixedSpectralHessianRealOperator_fredholm
      period hPeriod d9Ellipticity matterMass

end

end P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
end JanusFormal
