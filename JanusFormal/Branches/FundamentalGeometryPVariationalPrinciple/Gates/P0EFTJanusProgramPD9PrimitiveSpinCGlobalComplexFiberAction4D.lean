import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexLocalCoordinate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D

/-!
# Intrinsic and transported complex actions on the SpinC fiber

The primitive SpinC bundle already carries multiplication by a complex scalar
through the transported half-spinor representation.  The global smooth
section construction instead uses the intrinsic real formula

`z ψ = re(z) ψ + im(z) J ψ`.

This gate proves that the two definitions agree on every doubled matter
fiber.  It also proves that the scalar representation is faithful on every
nonzero fiber vector and rewrites local coordinates of global complex lines
using the transported complex action directly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexLocalCoordinate4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The transported complex action equals the intrinsic real/imaginary
formula on every doubled matter fiber. -/
theorem d9PrimitiveSpinCComplexAction_eq_re_add_im
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar matter =
      scalar.re • matter +
        scalar.im • d9PrimitiveSpinCImaginaryAction matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_add, map_smul, map_smul]
  unfold d9PrimitiveSpinCImaginaryAction
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction]
  change
    scalar • d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
      (scalar.re : Complex) •
          d9DoubledMatterFiberHalfSpinorLinearEquiv matter +
        (scalar.im : Complex) •
          (Complex.I •
            d9DoubledMatterFiberHalfSpinorLinearEquiv matter)
  have hScalar :
      scalar =
        (scalar.re : Complex) + (scalar.im : Complex) * Complex.I := by
    apply Complex.ext <;> simp
  calc
    scalar • d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
        ((scalar.re : Complex) +
          (scalar.im : Complex) * Complex.I) •
            d9DoubledMatterFiberHalfSpinorLinearEquiv matter := by
      exact congrArg
        (fun current : Complex =>
          current • d9DoubledMatterFiberHalfSpinorLinearEquiv matter)
        hScalar
    _ = _ := by
      rw [add_smul, mul_smul]

/-- Local coordinates of a global intrinsic complex scalar are exactly the
transported complex action on the local fiber coordinate. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (scalar : Complex)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar state) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base state) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_complexScalar
    period hPeriod index base hBase scalar state,
    d9PrimitiveSpinCComplexAction_eq_re_add_im]

/-- Local coordinates of one complex eigenspinor coefficient are transported
complex scalar multiplication of the underlying real eigensection. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_complexLine_eq_action
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)
    (coefficient : Complex) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod .positiveQuarter state coefficient) =
      d9PrimitiveSpinCComplexActionCLM coefficient
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base state) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_complexLine
    period hPeriod index base hBase state coefficient,
    d9PrimitiveSpinCComplexAction_eq_re_add_im]

/-- The transported complex scalar action on a nonzero fiber vector is
faithful in the scalar. -/
theorem d9PrimitiveSpinCComplexAction_scalar_injective
    (matter : D9DoubledMatterFiber) (hMatter : matter ≠ 0) :
    Function.Injective
      (fun scalar : Complex =>
        d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  intro first second hEqual
  have hHalfEqual := congrArg
    d9DoubledMatterFiberHalfSpinorLinearEquiv hEqual
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction] at hHalfEqual
  have hDifference :
      (first - second) •
          d9DoubledMatterFiberHalfSpinorLinearEquiv matter = 0 := by
    rw [sub_smul, hHalfEqual, sub_self]
  have hHalfNonzero :
      d9DoubledMatterFiberHalfSpinorLinearEquiv matter ≠ 0 := by
    intro hZero
    apply hMatter
    apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
    simpa using hZero
  have hScalar : first - second = 0 :=
    (smul_eq_zero.mp hDifference).resolve_right hHalfNonzero
  exact sub_eq_zero.mp hScalar

/-- A complex scalar annihilates a nonzero fiber vector only when the scalar
itself is zero. -/
theorem d9PrimitiveSpinCComplexAction_eq_zero_iff
    (scalar : Complex) (matter : D9DoubledMatterFiber)
    (hMatter : matter ≠ 0) :
    d9PrimitiveSpinCComplexActionCLM scalar matter = 0 ↔ scalar = 0 := by
  have hActionZero :
      d9PrimitiveSpinCComplexActionCLM 0 matter = 0 := by
    rw [d9PrimitiveSpinCComplexAction_eq_re_add_im]
    simp
  constructor
  · intro hZero
    apply d9PrimitiveSpinCComplexAction_scalar_injective matter hMatter
    exact hZero.trans hActionZero.symm
  · intro hScalar
    subst scalar
    exact hActionZero

/-- The transported complex action is additive in its scalar argument. -/
theorem d9PrimitiveSpinCComplexAction_add_scalar
    (first second : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM (first + second) matter =
      d9PrimitiveSpinCComplexActionCLM first matter +
        d9PrimitiveSpinCComplexActionCLM second matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_add,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  exact add_smul first second
    (d9DoubledMatterFiberHalfSpinorLinearEquiv matter)

/-- Consolidated faithful fiber complex-action package. -/
theorem d9PrimitiveSpinCGlobalComplexFiberAction_closed :
    (∀ scalar matter,
      d9PrimitiveSpinCComplexActionCLM scalar matter =
        scalar.re • matter +
          scalar.im • d9PrimitiveSpinCImaginaryAction matter) ∧
      (∀ matter, matter ≠ 0 →
        Function.Injective
          (fun scalar : Complex =>
            d9PrimitiveSpinCComplexActionCLM scalar matter)) ∧
      (∀ scalar matter, matter ≠ 0 →
        (d9PrimitiveSpinCComplexActionCLM scalar matter = 0 ↔
          scalar = 0)) :=
  ⟨d9PrimitiveSpinCComplexAction_eq_re_add_im,
    d9PrimitiveSpinCComplexAction_scalar_injective,
    d9PrimitiveSpinCComplexAction_eq_zero_iff⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
end JanusFormal
