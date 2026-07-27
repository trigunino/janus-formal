import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D

/-!
# Full global complex scalar action on genuine primitive SpinC sections

The preceding gate descends the fiberwise imaginary action to a global
real-linear complex structure `J` on the genuine primitive SpinC smooth
section core.  The full complex scalar action is therefore defined
intrinsically by

`z • ψ = re(z) ψ + im(z) J ψ`.

This definition does not choose a trivialization and does not require a
second local descent construction.  The resulting endomorphisms form a
unital ring representation of `ℂ`; real scalars recover the existing real
module structure, `i` recovers `J`, and the representation commutes with the
actual differential Dirac operator on the positive-quarter geometric core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
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

/-- Intrinsic multiplication by a constant complex scalar on an arbitrary
genuine smooth primitive SpinC section. -/
def d9PrimitiveSpinCComplexScalarSection
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  scalar.re • state +
    scalar.im •
      d9PrimitiveSpinCImaginarySection period hPeriod choice state

@[simp]
theorem d9PrimitiveSpinCComplexScalarSection_apply
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state base =
      scalar.re • (show D9DoubledMatterFiber from state base) +
        scalar.im • d9PrimitiveSpinCImaginaryAction
          (show D9DoubledMatterFiber from state base) := by
  change
    scalar.re • state base +
        scalar.im •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state base = _
  rw [d9PrimitiveSpinCImaginarySection_apply]
  rfl

/-- Section-level real/imaginary formula, exposed for later complex-linear
packet constructions. -/
@[simp]
theorem d9PrimitiveSpinCComplexScalarSection_eq_re_add_im
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state =
      scalar.re • state +
        scalar.im •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state :=
  rfl

/-- The global scalar action is real-linear in the section variable. -/
def d9PrimitiveSpinCComplexScalarSectionLinearMap
    (choice : NormalRootChoice) (scalar : Complex) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod choice where
  toFun :=
    d9PrimitiveSpinCComplexScalarSection
      period hPeriod choice scalar
  map_add' first second := by
    change
      scalar.re • (first + second) +
          scalar.im •
            d9PrimitiveSpinCImaginarySection
              period hPeriod choice (first + second) =
        (scalar.re • first +
            scalar.im •
              d9PrimitiveSpinCImaginarySection
                period hPeriod choice first) +
          (scalar.re • second +
            scalar.im •
              d9PrimitiveSpinCImaginarySection
                period hPeriod choice second)
    rw [show
      d9PrimitiveSpinCImaginarySection
          period hPeriod choice (first + second) =
        d9PrimitiveSpinCImaginarySection period hPeriod choice first +
          d9PrimitiveSpinCImaginarySection period hPeriod choice second by
      exact map_add
        (d9PrimitiveSpinCImaginarySectionLinearMap
          period hPeriod choice) first second]
    module
  map_smul' real state := by
    change
      scalar.re • (real • state) +
          scalar.im •
            d9PrimitiveSpinCImaginarySection
              period hPeriod choice (real • state) =
        real •
          (scalar.re • state +
            scalar.im •
              d9PrimitiveSpinCImaginarySection
                period hPeriod choice state)
    rw [show
      d9PrimitiveSpinCImaginarySection
          period hPeriod choice (real • state) =
        real •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state by
      exact map_smul
        (d9PrimitiveSpinCImaginarySectionLinearMap
          period hPeriod choice) real state]
    module

@[simp]
theorem d9PrimitiveSpinCComplexScalarSectionLinearMap_apply
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSectionLinearMap
        period hPeriod choice scalar state =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state :=
  rfl

/-- Zero complex scalar gives the zero smooth section. -/
@[simp]
theorem d9PrimitiveSpinCComplexScalarSection_zero_scalar
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice 0 state = 0 := by
  simp [d9PrimitiveSpinCComplexScalarSection]

/-- One complex scalar gives the original smooth section. -/
@[simp]
theorem d9PrimitiveSpinCComplexScalarSection_one
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice 1 state = state := by
  simp [d9PrimitiveSpinCComplexScalarSection]

/-- Addition of complex scalars is addition of the corresponding global
endomorphisms. -/
theorem d9PrimitiveSpinCComplexScalarSection_add_scalar
    (choice : NormalRootChoice) (first second : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice (first + second) state =
      d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice first state +
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice second state := by
  simp only [d9PrimitiveSpinCComplexScalarSection,
    Complex.add_re, Complex.add_im, add_smul]
  module

/-- The global complex structure rotates an arbitrary real/imaginary linear
combination according to `J(a ψ + b Jψ) = a Jψ - b ψ`. -/
theorem d9PrimitiveSpinCImaginarySection_re_add_im
    (choice : NormalRootChoice) (real imaginary : Real)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCImaginarySection period hPeriod choice
        (real • state +
          imaginary •
            d9PrimitiveSpinCImaginarySection
              period hPeriod choice state) =
      real •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state -
        imaginary • state := by
  change
    d9PrimitiveSpinCImaginarySectionLinearMap
        period hPeriod choice
        (real • state +
          imaginary •
            d9PrimitiveSpinCImaginarySection
              period hPeriod choice state) = _
  rw [map_add, map_smul, map_smul,
    d9PrimitiveSpinCImaginarySectionLinearMap_apply,
    d9PrimitiveSpinCImaginarySectionLinearMap_apply,
    d9PrimitiveSpinCImaginarySection_sq]
  module

/-- Multiplication of complex scalars is composition of the corresponding
global endomorphisms. -/
theorem d9PrimitiveSpinCComplexScalarSection_mul
    (choice : NormalRootChoice) (first second : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice (first * second) state =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice first
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice second state) := by
  change
    (first * second).re • state +
        (first * second).im •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state =
      first.re •
          (second.re • state +
            second.im •
              d9PrimitiveSpinCImaginarySection
                period hPeriod choice state) +
        first.im •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice
            (second.re • state +
              second.im •
                d9PrimitiveSpinCImaginarySection
                  period hPeriod choice state)
  rw [Complex.mul_re, Complex.mul_im,
    d9PrimitiveSpinCImaginarySection_re_add_im]
  module

/-- The transported complex action restricts to the existing real scalar
action. -/
theorem d9PrimitiveSpinCComplexScalarSection_ofReal
    (choice : NormalRootChoice) (real : Real)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice (real : Complex) state =
      real • state := by
  simp [d9PrimitiveSpinCComplexScalarSection]

/-- The scalar `i` recovers the previously descended global complex
structure. -/
theorem d9PrimitiveSpinCComplexScalarSection_I
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice Complex.I state =
      d9PrimitiveSpinCImaginarySection
        period hPeriod choice state := by
  simp [d9PrimitiveSpinCComplexScalarSection]

/-- The complete complex scalar representation on the real smooth-section
module. -/
def d9PrimitiveSpinCComplexScalarRepresentation
    (choice : NormalRootChoice) :
    Complex →+* Module.End Real
      (D9PrimitiveSpinCSmoothSection period hPeriod choice) where
  toFun scalar :=
    d9PrimitiveSpinCComplexScalarSectionLinearMap
      period hPeriod choice scalar
  map_zero' := by
    apply LinearMap.ext
    intro state
    exact d9PrimitiveSpinCComplexScalarSection_zero_scalar
      period hPeriod choice state
  map_one' := by
    apply LinearMap.ext
    intro state
    exact d9PrimitiveSpinCComplexScalarSection_one
      period hPeriod choice state
  map_add' first second := by
    apply LinearMap.ext
    intro state
    exact d9PrimitiveSpinCComplexScalarSection_add_scalar
      period hPeriod choice first second state
  map_mul' first second := by
    apply LinearMap.ext
    intro state
    exact d9PrimitiveSpinCComplexScalarSection_mul
      period hPeriod choice first second state

@[simp]
theorem d9PrimitiveSpinCComplexScalarRepresentation_apply
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarRepresentation
        period hPeriod choice scalar state =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state :=
  rfl

/-- Generic algebraic closure of the descended complex scalar representation. -/
theorem d9PrimitiveSpinCGlobalComplexScalarRepresentation_closed
    (choice : NormalRootChoice) :
    (∀ scalar state,
      d9PrimitiveSpinCComplexScalarRepresentation
          period hPeriod choice scalar state =
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar state) ∧
      (∀ (real : Real) state,
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod choice (real : Complex) state =
          real • state) ∧
      (∀ state,
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod choice Complex.I state =
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state) :=
  ⟨d9PrimitiveSpinCComplexScalarRepresentation_apply
      period hPeriod choice,
    d9PrimitiveSpinCComplexScalarSection_ofReal
      period hPeriod choice,
    d9PrimitiveSpinCComplexScalarSection_I
      period hPeriod choice⟩

/-- Real-linear packaging of the actual differential geometric Dirac operator
on the positive-quarter core used by the geometric Hopf construction. -/
def d9PrimitiveSpinCGeometricDiracRealLinearMap :
    D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter where
  toFun :=
    d9PrimitiveSpinCGeometricDiracOperator
      period hPeriod .positiveQuarter
  map_add' first second :=
    d9PrimitiveSpinCGeometricDiracOperator_add
      period hPeriod first second
  map_smul' scalar state :=
    d9PrimitiveSpinCGeometricDiracOperator_real_smul
      period hPeriod .positiveQuarter scalar state

@[simp]
theorem d9PrimitiveSpinCGeometricDiracRealLinearMap_apply
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) :
    d9PrimitiveSpinCGeometricDiracRealLinearMap
        period hPeriod state =
      d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state :=
  rfl

/-- Every intrinsic complex scalar endomorphism commutes with the actual
differential geometric Dirac operator on the positive-quarter core. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_complexScalar
    (scalar : Complex)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar state) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state) := by
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (scalar.re • state +
          scalar.im •
            d9PrimitiveSpinCImaginarySection
              period hPeriod .positiveQuarter state) =
      scalar.re •
          d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter state +
        scalar.im •
          d9PrimitiveSpinCImaginarySection
            period hPeriod .positiveQuarter
            (d9PrimitiveSpinCGeometricDiracOperator
              period hPeriod .positiveQuarter state)
  rw [d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    d9PrimitiveSpinCGeometricDiracOperator_imaginary]

/-- Endomorphism-level commutation relation on the geometric
positive-quarter core. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_commutes_complexRepresentation
    (scalar : Complex) :
    (d9PrimitiveSpinCGeometricDiracRealLinearMap
        period hPeriod).comp
        (d9PrimitiveSpinCComplexScalarRepresentation
          period hPeriod .positiveQuarter scalar) =
      (d9PrimitiveSpinCComplexScalarRepresentation
          period hPeriod .positiveQuarter scalar).comp
        (d9PrimitiveSpinCGeometricDiracRealLinearMap
          period hPeriod) := by
  apply LinearMap.ext
  intro state
  exact d9PrimitiveSpinCGeometricDiracOperator_complexScalar
    period hPeriod scalar state

/-- Consolidated global complex-scalar closure on the geometric core. -/
theorem d9PrimitiveSpinCGlobalComplexScalarAction_closed :
    (∀ scalar state,
      d9PrimitiveSpinCComplexScalarRepresentation
          period hPeriod .positiveQuarter scalar state =
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar state) ∧
      (∀ (real : Real) state,
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter (real : Complex) state =
          real • state) ∧
      (∀ state,
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter Complex.I state =
          d9PrimitiveSpinCImaginarySection
            period hPeriod .positiveQuarter state) ∧
      (∀ scalar,
        (d9PrimitiveSpinCGeometricDiracRealLinearMap
            period hPeriod).comp
            (d9PrimitiveSpinCComplexScalarRepresentation
              period hPeriod .positiveQuarter scalar) =
          (d9PrimitiveSpinCComplexScalarRepresentation
              period hPeriod .positiveQuarter scalar).comp
            (d9PrimitiveSpinCGeometricDiracRealLinearMap
              period hPeriod)) :=
  ⟨d9PrimitiveSpinCComplexScalarRepresentation_apply
      period hPeriod .positiveQuarter,
    d9PrimitiveSpinCComplexScalarSection_ofReal
      period hPeriod .positiveQuarter,
    d9PrimitiveSpinCComplexScalarSection_I
      period hPeriod .positiveQuarter,
    d9PrimitiveSpinCGeometricDiracOperator_commutes_complexRepresentation
      period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
end JanusFormal
