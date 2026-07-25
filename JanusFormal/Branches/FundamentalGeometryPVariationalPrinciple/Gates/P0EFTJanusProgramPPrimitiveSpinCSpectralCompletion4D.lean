import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10SmoothCoreHilbertCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatUnboundedDiracFredholm4D

/-!
# Primitive SpinC spectral completion

This gate instantiates the already proved product-throat Hilbert and unbounded
operator theory with the charge-one monopole actually constructed on D9.
It replaces the old neutral canonical example (`q = 0`) by a charge-compatible
domain (`q = 1`), without assuming a geometric Fourier transform.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD10SmoothCoreHilbertCompletion4D
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Charge-one D10 completion matching the primitive D9 SpinC bundle. -/
def canonicalPrimitiveD10SpectralCompletion : D10SpectralCompletion where
  sphereRadius := 1
  sphereRadiusPositive := by norm_num
  monopoleCharge := 1

/-- Canonical common geometric domain with primitive, rather than neutral,
spectral charge. -/
def canonicalPrimitiveProgramPCommonGeometricDomain4D :
    ProgramPCommonGeometricDomain4D period hPeriod :=
  ProgramPCommonGeometricDomain4D.ofOperatorData period hPeriod
    (canonicalPositiveLLH1Data period hPeriod)
    canonicalPrimitiveD10SpectralCompletion

@[simp]
theorem canonicalPrimitiveProgramPCommonGeometricDomain4D_monopoleCharge :
    (canonicalPrimitiveProgramPCommonGeometricDomain4D
      period hPeriod).d10Completion.monopoleCharge = 1 :=
  rfl

@[simp]
theorem canonicalPrimitiveProgramPCommonGeometricDomain4D_sphereRadius :
    (canonicalPrimitiveProgramPCommonGeometricDomain4D
      period hPeriod).d7d10SpectralData.sphereRadius = 1 :=
  rfl

@[simp]
theorem canonicalPrimitiveProgramPCommonGeometricDomain4D_spectralCharge :
    (canonicalPrimitiveProgramPCommonGeometricDomain4D
      period hPeriod).d7d10SpectralData.monopoleCharge = 1 :=
  rfl

/-- Charge-one product spectral datum. -/
abbrev PrimitiveSpinCSpectralData :=
  (canonicalPrimitiveProgramPCommonGeometricDomain4D
    period hPeriod).d7d10SpectralData

/-- The completed spectral `L²` spinor space. -/
abbrev PrimitiveSpinCL2 :=
  ProductThroatHeatHilbert
    (PrimitiveSpinCSpectralData period hPeriod)

/-- The maximal first-order (`H¹` graph) domain. -/
abbrev PrimitiveSpinCH1 (fold : Fold) (twist : CircleTwist) :=
  productThroatDiracDomain
    (PrimitiveSpinCSpectralData period hPeriod) fold twist

/-- The maximal squared (`H²` graph/Fredholm) domain. -/
abbrev PrimitiveSpinCH2 (fold : Fold) (twist : CircleTwist) :=
  productThroatDiracSquaredDomain
    (PrimitiveSpinCSpectralData period hPeriod) fold twist

/-- First-order charge-one maximal Dirac realization. -/
abbrev primitiveSpinCUnboundedDirac
    (fold : Fold) (twist : CircleTwist) :=
  productThroatUnboundedDirac
    (PrimitiveSpinCSpectralData period hPeriod) fold twist

/-- Squared charge-one maximal Dirac realization. -/
abbrev primitiveSpinCUnboundedDiracSquared
    (fold : Fold) (twist : CircleTwist) :=
  productThroatUnboundedDiracSquared
    (PrimitiveSpinCSpectralData period hPeriod) fold twist

/-- The algebraic finite-mode core is dense in the real
multiplicity-aware D10 completion at primitive charge. -/
theorem primitiveSpinCD10FiniteModeCore_dense :
    Dense
      (programPD10FiniteModeCore4D
          (PrimitiveSpinCSpectralData period hPeriod) :
        Set (ProgramPD10ModeHilbert4D
          (PrimitiveSpinCSpectralData period hPeriod))) :=
  programPD10FiniteModeCore4D_dense
    (PrimitiveSpinCSpectralData period hPeriod)

/-- Complete closure/self-adjointness/Fredholm certificate at the same
primitive charge as the constructed D9 SpinC bundle. -/
structure ProgramPPrimitiveSpinCSpectralCompletionCertificate4D where
  spinCBundle :
    ProgramPD9PrimitiveSpinCBundleCertificate4D period hPeriod
  domain : ProgramPCommonGeometricDomain4D period hPeriod
  domainCanonical :
    domain =
      canonicalPrimitiveProgramPCommonGeometricDomain4D period hPeriod
  chargeAgreement :
    spinCBundle.charge = domain.d10Completion.monopoleCharge
  firstOrderDense :
    ∀ fold twist,
      Dense
        ((productThroatDiracDomain domain.d7d10SpectralData fold twist :
          Submodule Complex
            (ProductThroatHeatHilbert domain.d7d10SpectralData)) :
          Set (ProductThroatHeatHilbert domain.d7d10SpectralData))
  firstOrderSelfAdjoint :
    ∀ fold twist,
      IsSelfAdjoint
        (productThroatUnboundedDirac
          domain.d7d10SpectralData fold twist)
  firstOrderFredholm :
    ∀ fold twist,
      IsClosed
          (LinearMap.range
              (productThroatUnboundedDirac
                domain.d7d10SpectralData fold twist).toFun :
            Set (ProductThroatHeatHilbert domain.d7d10SpectralData)) ∧
        FiniteDimensional Complex
          (LinearMap.ker
            (productThroatUnboundedDirac
              domain.d7d10SpectralData fold twist).toFun) ∧
        FiniteDimensional Complex
          (ProductThroatDiracCokernel
            domain.d7d10SpectralData fold twist)
  firstOrderIndexZero :
    ∀ fold twist,
      productThroatUnboundedDiracIndex
        domain.d7d10SpectralData fold twist = 0
  squaredDense :
    ∀ fold twist,
      Dense
        ((productThroatDiracSquaredDomain
            domain.d7d10SpectralData fold twist :
          Submodule Complex
            (ProductThroatHeatHilbert domain.d7d10SpectralData)) :
          Set (ProductThroatHeatHilbert domain.d7d10SpectralData))
  squaredClosed :
    ∀ fold twist,
      (productThroatUnboundedDiracSquared
        domain.d7d10SpectralData fold twist).IsClosed
  squaredSelfAdjoint :
    ∀ fold twist,
      IsSelfAdjoint
        (productThroatUnboundedDiracSquared
          domain.d7d10SpectralData fold twist)
  squareIsIteratedFirstOrder :
    ∀ fold twist,
      (productThroatDiracSquaredDomain
          domain.d7d10SpectralData fold twist :
        Set (ProductThroatHeatHilbert domain.d7d10SpectralData)) =
        productThroatDiracIteratedDomain
          domain.d7d10SpectralData fold twist

def programPPrimitiveSpinCSpectralCompletionCertificate4D :
    ProgramPPrimitiveSpinCSpectralCompletionCertificate4D
      period hPeriod where
  spinCBundle :=
    programPD9PrimitiveSpinCBundleCertificate4D period hPeriod
  domain :=
    canonicalPrimitiveProgramPCommonGeometricDomain4D period hPeriod
  domainCanonical := rfl
  chargeAgreement := rfl
  firstOrderDense :=
    productThroatDiracDomain_dense
      (PrimitiveSpinCSpectralData period hPeriod)
  firstOrderSelfAdjoint :=
    productThroatUnboundedDirac_isSelfAdjoint
      (PrimitiveSpinCSpectralData period hPeriod)
  firstOrderFredholm :=
    productThroatUnboundedDirac_fredholm_criterion
      (PrimitiveSpinCSpectralData period hPeriod)
  firstOrderIndexZero :=
    productThroatUnboundedDiracIndex_zero
      (PrimitiveSpinCSpectralData period hPeriod)
  squaredDense :=
    productThroatDiracSquaredDomain_dense
      (PrimitiveSpinCSpectralData period hPeriod)
  squaredClosed :=
    productThroatUnboundedDiracSquared_isClosed
      (PrimitiveSpinCSpectralData period hPeriod)
  squaredSelfAdjoint :=
    productThroatUnboundedDiracSquared_isSelfAdjoint
      (PrimitiveSpinCSpectralData period hPeriod)
  squareIsIteratedFirstOrder :=
    productThroatDiracSquaredDomain_eq_iteratedDomain
      (PrimitiveSpinCSpectralData period hPeriod)

theorem programPPrimitiveSpinCSpectralCompletionCertificate4D_nonempty :
    Nonempty
      (ProgramPPrimitiveSpinCSpectralCompletionCertificate4D
        period hPeriod) :=
  ⟨programPPrimitiveSpinCSpectralCompletionCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
end JanusFormal
