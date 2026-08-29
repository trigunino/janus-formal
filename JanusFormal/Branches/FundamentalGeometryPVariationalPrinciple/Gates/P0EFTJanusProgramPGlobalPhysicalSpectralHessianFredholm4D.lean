import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D

/-!
# Legacy D10-extended first-order spectral target

This replaces the former squared SpinC control block by the signed,
geometrically scaled action Hessian `2D + m²`.  It is
assembled with the D9 gauge--ghost and D10 blocks on one maximal domain.
Finite D9 characteristic modes and possible finite mass resonances are
retained rather than excluded.

The D10 coordinate is not varied by the Candidate-A action.  Consequently
this D10-extended operator is retained for regulator/backward compatibility,
not as the physical action Hessian.  The D10-free target is constructed in
`P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalPhysicalSpectralHessianFredholm4D

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
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Mode family of the first-order physical spectral Hessian. -/
abbrev ProgramPGlobalPhysicalSpectralHessianMode
    (ι : Type*) (data : ProductThroatSpectralData) :=
  (ι × Fin 8) ⊕
    ((Sector × PrimitiveSpinCGeometricSignedMode) ⊕
      ProgramPD10Mode4D data)

local instance programPGlobalPhysicalSpectralHessianModeDecidableEq
    (ι : Type*) [DecidableEq ι] (data : ProductThroatSpectralData) :
    DecidableEq (ProgramPGlobalPhysicalSpectralHessianMode ι data) :=
  Classical.decEq _

/-- Exact block weight: D9, two copies of `2D + massSquared`, and D10. -/
def programPGlobalPhysicalSpectralHessianWeight
    {ι : Type*}
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :
    ProgramPGlobalPhysicalSpectralHessianMode ι data → Real :=
  complexDiagonalSumWeight
    (d9GaugeGhostUnboundedWeight covector)
    (complexDiagonalSumWeight
      (fun mode : Sector × PrimitiveSpinCGeometricSignedMode =>
        primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode.2 + matterMass)
      (fun mode : ProgramPD10Mode4D data =>
        productDiracEigenvalueSquared data mode.separatedMode))

@[simp]
theorem programPGlobalPhysicalSpectralHessianWeight_d9
    {ι : Type*}
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real)
    (mode : ι × Fin 8) :
    programPGlobalPhysicalSpectralHessianWeight
        period hPeriod covector data matterMass (.inl mode) =
      d9GaugeGhostUnboundedWeight covector mode :=
  rfl

@[simp]
theorem programPGlobalPhysicalSpectralHessianWeight_matter
    {ι : Type*}
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real)
    (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode) :
    programPGlobalPhysicalSpectralHessianWeight
        period hPeriod covector data matterMass
        (.inr (.inl (sector, mode))) =
      primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode +
        matterMass :=
  rfl

@[simp]
theorem programPGlobalPhysicalSpectralHessianWeight_d10
    {ι : Type*}
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real)
    (mode : ProgramPD10Mode4D data) :
    programPGlobalPhysicalSpectralHessianWeight
        period hPeriod covector data matterMass
        (.inr (.inr mode)) =
      productDiracEigenvalueSquared data mode.separatedMode :=
  rfl

/-- D10 has a uniform positive gap and therefore no zero modes. -/
def programPD10FiniteZeroGap
    (data : ProductThroatSpectralData) :
    ComplexDiagonalFiniteZeroGap (ProgramPD10Mode4D data)
      (fun mode =>
        productDiracEigenvalueSquared data mode.separatedMode) :=
  complexDiagonalFiniteZeroGap_of_gap
    (ProgramPD10Mode4D data)
    (fun mode =>
      productDiracEigenvalueSquared data mode.separatedMode)
    (programPD10SpectralGap4D data)
    (programPD10SpectralGap4D_pos data)
    (fun mode => by
      rw [abs_of_pos
        ((programPD10SpectralGap4D_pos data).trans_le
          (programPD10SpectralGap4D_le data mode))]
      exact programPD10SpectralGap4D_le data mode)

/-- Ellipticity modulo the genuine finite D9 and mass-resonant matter
kernels. -/
def programPGlobalPhysicalSpectralHessianFiniteZeroGap
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :
    ComplexDiagonalFiniteZeroGap
      (ProgramPGlobalPhysicalSpectralHessianMode ι data)
      (programPGlobalPhysicalSpectralHessianWeight
        period hPeriod covector data matterMass) := by
  exact
    complexDiagonalFiniteZeroGap_sum
      (d9GaugeGhostUnboundedWeight covector)
      (complexDiagonalSumWeight
        (fun mode : Sector × PrimitiveSpinCGeometricSignedMode =>
          primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode.2 + matterMass)
        (fun mode : ProgramPD10Mode4D data =>
          productDiracEigenvalueSquared data mode.separatedMode))
      d9Ellipticity.toFiniteZeroGap
      (complexDiagonalFiniteZeroGap_sum
        (fun mode : Sector × PrimitiveSpinCGeometricSignedMode =>
          primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode.2 + matterMass)
        (fun mode : ProgramPD10Mode4D data =>
          productDiracEigenvalueSquared data mode.separatedMode)
        (complexDiagonalFiniteZeroGap_finiteProduct
          PrimitiveSpinCGeometricSignedMode
          (fun mode =>
            primitiveSpinCGeometricSignedKineticHessianWeight
              period hPeriod mode + matterMass)
          (primitiveSpinCGeometricSignedActionHessianFiniteZeroGap
            period hPeriod matterMass))
        (programPD10FiniteZeroGap data))

/-- Ambient complex Hilbert space of the physical spectral Hessian. -/
abbrev ProgramPGlobalPhysicalSpectralHessianHilbert
    (ι : Type*) (data : ProductThroatSpectralData) :=
  ComplexDiagonalHilbert
    (ProgramPGlobalPhysicalSpectralHessianMode ι data)

local instance
    programPGlobalPhysicalSpectralHessianHilbertRealInnerProductSpace
    (ι : Type*) (data : ProductThroatSpectralData) :
    InnerProductSpace Real
      (ProgramPGlobalPhysicalSpectralHessianHilbert ι data) :=
  InnerProductSpace.complexToReal

local instance
    programPGlobalPhysicalSpectralHessianHilbertRealLinearPMapStar
    (ι : Type*) (data : ProductThroatSpectralData) :
    Star (ProgramPGlobalPhysicalSpectralHessianHilbert ι data →ₗ.[Real]
      ProgramPGlobalPhysicalSpectralHessianHilbert ι data) :=
  LinearPMap.instStar

/-- Genuine maximal first-order complex realization. -/
abbrev programPGlobalPhysicalSpectralHessianMaximalOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :=
  complexDiagonalOperator
    (ProgramPGlobalPhysicalSpectralHessianMode ι data)
    (programPGlobalPhysicalSpectralHessianWeight
      period hPeriod covector data matterMass)

/-- Underlying real maximal realization used by the variational Hessian. -/
abbrev programPGlobalPhysicalSpectralHessianRealMaximalOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :=
  complexDiagonalRealOperator
    (ProgramPGlobalPhysicalSpectralHessianMode ι data)
    (programPGlobalPhysicalSpectralHessianWeight
      period hPeriod covector data matterMass)

theorem programPGlobalPhysicalSpectralHessianRealDomain_dense
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :
    Dense
      ((programPGlobalPhysicalSpectralHessianRealMaximalOperator
        period hPeriod covector data matterMass).domain :
        Set (ProgramPGlobalPhysicalSpectralHessianHilbert ι data)) :=
  complexDiagonalRealDomain_dense
    (ProgramPGlobalPhysicalSpectralHessianMode ι data)
    (programPGlobalPhysicalSpectralHessianWeight
      period hPeriod covector data matterMass)

theorem programPGlobalPhysicalSpectralHessianRealOperator_selfAdjoint
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :
    IsSelfAdjoint
      (programPGlobalPhysicalSpectralHessianRealMaximalOperator
        period hPeriod covector data matterMass) :=
  complexDiagonalRealOperator_isSelfAdjoint
    (ProgramPGlobalPhysicalSpectralHessianMode ι data)
    (programPGlobalPhysicalSpectralHessianWeight
      period hPeriod covector data matterMass)

theorem programPGlobalPhysicalSpectralHessianRealOperator_closed
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :
    (programPGlobalPhysicalSpectralHessianRealMaximalOperator
      period hPeriod covector data matterMass).IsClosed :=
  complexDiagonalRealOperator_isClosed
    (ProgramPGlobalPhysicalSpectralHessianMode ι data)
    (programPGlobalPhysicalSpectralHessianWeight
      period hPeriod covector data matterMass)

/-- Real Fredholm theorem for the corrected first-order global block. -/
theorem programPGlobalPhysicalSpectralHessianRealOperator_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :
    IsClosed
        (LinearMap.range
          (programPGlobalPhysicalSpectralHessianRealMaximalOperator
            period hPeriod covector data matterMass).toFun :
          Set (ProgramPGlobalPhysicalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalPhysicalSpectralHessianRealMaximalOperator
            period hPeriod covector data matterMass).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalPhysicalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalPhysicalSpectralHessianRealMaximalOperator
              period hPeriod covector data matterMass).toFun) :=
  complexDiagonalRealOperator_fredholm_of_finiteZeroGap
    (ProgramPGlobalPhysicalSpectralHessianMode ι data)
    (programPGlobalPhysicalSpectralHessianWeight
      period hPeriod covector data matterMass)
    (programPGlobalPhysicalSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity data matterMass)

/-- Consolidated analytic certificate for the physical first-order block. -/
structure ProgramPGlobalPhysicalSpectralHessianFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData)
    (matterMass : Real) : Prop where
  domainDense :
    Dense
      ((programPGlobalPhysicalSpectralHessianRealMaximalOperator
        period hPeriod covector data matterMass).domain :
        Set (ProgramPGlobalPhysicalSpectralHessianHilbert ι data))
  selfAdjoint :
    IsSelfAdjoint
      (programPGlobalPhysicalSpectralHessianRealMaximalOperator
        period hPeriod covector data matterMass)
  closed :
    (programPGlobalPhysicalSpectralHessianRealMaximalOperator
      period hPeriod covector data matterMass).IsClosed
  fredholm :
    IsClosed
        (LinearMap.range
          (programPGlobalPhysicalSpectralHessianRealMaximalOperator
            period hPeriod covector data matterMass).toFun :
          Set (ProgramPGlobalPhysicalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalPhysicalSpectralHessianRealMaximalOperator
            period hPeriod covector data matterMass).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalPhysicalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalPhysicalSpectralHessianRealMaximalOperator
              period hPeriod covector data matterMass).toFun)

def programPGlobalPhysicalSpectralHessianFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData)
    (matterMass : Real) :
    ProgramPGlobalPhysicalSpectralHessianFredholmCertificate4D
      period hPeriod d9Ellipticity data matterMass where
  domainDense :=
    programPGlobalPhysicalSpectralHessianRealDomain_dense
      period hPeriod covector data matterMass
  selfAdjoint :=
    programPGlobalPhysicalSpectralHessianRealOperator_selfAdjoint
      period hPeriod covector data matterMass
  closed :=
    programPGlobalPhysicalSpectralHessianRealOperator_closed
      period hPeriod covector data matterMass
  fredholm :=
    programPGlobalPhysicalSpectralHessianRealOperator_fredholm
      period hPeriod d9Ellipticity data matterMass

end
end P0EFTJanusProgramPGlobalPhysicalSpectralHessianFredholm4D
end JanusFormal
