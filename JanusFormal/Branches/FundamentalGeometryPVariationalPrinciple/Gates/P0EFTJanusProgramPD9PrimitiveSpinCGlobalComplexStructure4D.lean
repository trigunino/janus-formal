import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D

/-!
# Global complex structure on genuine primitive SpinC sections

The fiberwise action of `i` already commutes with every primitive SpinC
transition and with the local geometric Dirac expression.  This gate descends
that action to the complete genuine smooth-section core, proves the global
identity `J² = -1`, and proves exact commutation with the actual differential
Dirac operator.

Every nonzero real eigensection therefore generates a faithful complex line.
The three positive and three negative first-sphere eigensections acquire their
missing imaginary companions without choosing a global trivialization of the
nontrivial SpinC bundle.  This supplies the two real representatives required
by one abstract complex spectral coordinate.  Joint complex independence of
all three multiplicities is deliberately not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
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

/-- Apply the fiberwise multiplication by `i` to an arbitrary genuine smooth
primitive SpinC section and descend the resulting compatible local family. -/
def d9PrimitiveSpinCImaginarySection
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  (d9PrimitiveSpinCImaginaryLocalGaugeFamily
    period hPeriod choice
    (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state)).toSmoothSection
        period hPeriod choice

@[simp]
theorem d9PrimitiveSpinCImaginarySection_apply
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCImaginarySection
        period hPeriod choice state base =
      d9PrimitiveSpinCImaginaryAction (state base) := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  have hRecover :
      family.toSmoothSection period hPeriod choice = state :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection
      period hPeriod choice state
  have hAt := congrArg
    (fun current : D9PrimitiveSpinCSmoothSection period hPeriod choice =>
      current base) hRecover
  change
    d9PrimitiveSpinCImaginaryAction
        (family.localValue
          ((d9PrimitiveSpinCVectorBundleCore
            period hPeriod choice).indexAt base) base) =
      d9PrimitiveSpinCImaginaryAction (state base)
  congr 1

/-- Real-linear global complex structure on the genuine smooth section core. -/
def d9PrimitiveSpinCImaginarySectionLinearMap
    (choice : NormalRootChoice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod choice where
  toFun := d9PrimitiveSpinCImaginarySection period hPeriod choice
  map_add' first second := by
    apply ContMDiffSection.ext
    intro base
    change
      d9PrimitiveSpinCImaginarySection
          period hPeriod choice (first + second) base =
        d9PrimitiveSpinCImaginarySection period hPeriod choice first base +
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice second base
    rw [d9PrimitiveSpinCImaginarySection_apply
        period hPeriod choice (first + second) base,
      d9PrimitiveSpinCImaginarySection_apply
        period hPeriod choice first base,
      d9PrimitiveSpinCImaginarySection_apply
        period hPeriod choice second base]
    rw [show (first + second) base = first base + second base by rfl]
    exact map_add d9PrimitiveSpinCImaginaryAction _ _
  map_smul' scalar state := by
    apply ContMDiffSection.ext
    intro base
    change
      d9PrimitiveSpinCImaginarySection
          period hPeriod choice (scalar • state) base =
        scalar •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state base
    rw [d9PrimitiveSpinCImaginarySection_apply
        period hPeriod choice (scalar • state) base,
      d9PrimitiveSpinCImaginarySection_apply
        period hPeriod choice state base]
    rw [show (scalar • state) base = scalar • state base by rfl]
    exact map_smul d9PrimitiveSpinCImaginaryAction scalar (state base)

@[simp]
theorem d9PrimitiveSpinCImaginarySectionLinearMap_apply
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCImaginarySectionLinearMap
        period hPeriod choice state =
      d9PrimitiveSpinCImaginarySection period hPeriod choice state :=
  rfl

@[simp]
theorem d9PrimitiveSpinCImaginarySection_zero
    (choice : NormalRootChoice) :
    d9PrimitiveSpinCImaginarySection period hPeriod choice 0 = 0 :=
  map_zero (d9PrimitiveSpinCImaginarySectionLinearMap
    period hPeriod choice)

/-- The descended global complex structure squares to minus the identity. -/
@[simp]
theorem d9PrimitiveSpinCImaginarySection_sq
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCImaginarySection period hPeriod choice
        (d9PrimitiveSpinCImaginarySection
          period hPeriod choice state) =
      -state := by
  apply ContMDiffSection.ext
  intro base
  rw [d9PrimitiveSpinCImaginarySection_apply
    period hPeriod choice
      (d9PrimitiveSpinCImaginarySection period hPeriod choice state) base]
  rw [d9PrimitiveSpinCImaginarySection_apply
    period hPeriod choice state base]
  rw [d9PrimitiveSpinCImaginaryAction_sq]
  rfl

/-- Multiplication by `i` is injective on genuine smooth sections. -/
theorem d9PrimitiveSpinCImaginarySection_injective
    (choice : NormalRootChoice) :
    Function.Injective
      (d9PrimitiveSpinCImaginarySection period hPeriod choice) := by
  intro first second hEqual
  have hApplied := congrArg
    (d9PrimitiveSpinCImaginarySection period hPeriod choice) hEqual
  rw [d9PrimitiveSpinCImaginarySection_sq,
    d9PrimitiveSpinCImaginarySection_sq] at hApplied
  exact neg_injective hApplied

set_option maxHeartbeats 2000000 in
/-- The actual descended differential Dirac operator is complex linear on the
entire genuine smooth primitive SpinC section core. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_imaginary
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod choice
        (d9PrimitiveSpinCImaginarySection
          period hPeriod choice state) =
      d9PrimitiveSpinCImaginarySection
        period hPeriod choice
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod choice state) := by
  apply ContMDiffSection.ext
  intro base
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  let imaginaryFamily :=
    d9PrimitiveSpinCImaginaryLocalGaugeFamily
      period hPeriod choice family
  have hState :
      family.toSmoothSection period hPeriod choice = state :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection
      period hPeriod choice state
  have hImaginary :
      d9PrimitiveSpinCImaginarySection
          period hPeriod choice state =
        imaginaryFamily.toSmoothSection period hPeriod choice := by
    rfl
  let core := d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (core.indexAt base) :=
    core.mem_baseSet_at base
  rw [hImaginary,
    d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection,
    d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCImaginarySection_apply,
    ← hState,
    d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection,
    d9PrimitiveSpinCGeometricDiracSection_apply]
  exact d9PrimitiveSpinCLocalGeometricDirac_imaginary
    period hPeriod choice family (core.indexAt base) base hBase

/-- The real and imaginary representatives generated by one genuine section. -/
def d9PrimitiveSpinCComplexLineLinearMap
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    Complex →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod choice where
  toFun coefficient :=
    coefficient.re • state +
      coefficient.im •
        d9PrimitiveSpinCImaginarySection period hPeriod choice state
  map_add' first second := by
    simp only [Complex.add_re, Complex.add_im]
    module
  map_smul' scalar coefficient := by
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero]
    change
      (scalar * coefficient.re) • state +
          (scalar * coefficient.im) •
            d9PrimitiveSpinCImaginarySection
              period hPeriod choice state =
        scalar •
          (coefficient.re • state +
            coefficient.im •
              d9PrimitiveSpinCImaginarySection
                period hPeriod choice state)
    rw [smul_add, smul_smul, smul_smul]

@[simp]
theorem d9PrimitiveSpinCComplexLineLinearMap_apply
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (coefficient : Complex) :
    d9PrimitiveSpinCComplexLineLinearMap
        period hPeriod choice state coefficient =
      coefficient.re • state +
        coefficient.im •
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state :=
  rfl

/-- A nonzero real section and its imaginary companion form one faithful
complex spectral coordinate. -/
theorem d9PrimitiveSpinCComplexLineLinearMap_injective
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (hState : state ≠ 0) :
    Function.Injective
      (d9PrimitiveSpinCComplexLineLinearMap
        period hPeriod choice state) := by
  intro first second hEqual
  let delta : Complex := first - second
  let imaginaryState :=
    d9PrimitiveSpinCImaginarySection period hPeriod choice state
  have hMapZero :
      d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod choice state delta = 0 := by
    rw [show delta = first - second by rfl, map_sub, hEqual, sub_self]
  have hZero :
      delta.re • state + delta.im • imaginaryState = 0 := by
    simpa [d9PrimitiveSpinCComplexLineLinearMap_apply, imaginaryState]
      using hMapZero
  have hImaginarySq :
      d9PrimitiveSpinCImaginarySection
          period hPeriod choice imaginaryState =
        -state := by
    dsimp [imaginaryState]
    exact d9PrimitiveSpinCImaginarySection_sq
      period hPeriod choice state
  have hApplied := congrArg
    (d9PrimitiveSpinCImaginarySectionLinearMap
      period hPeriod choice) hZero
  have hRotatedRaw :
      delta.re • imaginaryState +
          delta.im •
            d9PrimitiveSpinCImaginarySection
              period hPeriod choice imaginaryState = 0 := by
    simpa only [map_add, map_smul, map_zero,
      d9PrimitiveSpinCImaginarySectionLinearMap_apply] using hApplied
  have hRotated :
      delta.re • imaginaryState - delta.im • state = 0 := by
    rw [hImaginarySq] at hRotatedRaw
    simpa only [smul_neg, sub_eq_add_neg] using hRotatedRaw
  have hNormScaled :
      (delta.re ^ 2 + delta.im ^ 2) • state = 0 := by
    calc
      (delta.re ^ 2 + delta.im ^ 2) • state =
          delta.re •
              (delta.re • state + delta.im • imaginaryState) -
            delta.im •
              (delta.re • imaginaryState - delta.im • state) := by
        module
      _ = 0 := by rw [hZero, hRotated]; simp
  have hNorm : delta.re ^ 2 + delta.im ^ 2 = 0 :=
    (smul_eq_zero.mp hNormScaled).resolve_right hState
  have hReal : delta.re = 0 := by
    nlinarith [sq_nonneg delta.im]
  have hImaginary : delta.im = 0 := by
    nlinarith [sq_nonneg delta.re]
  have hDelta : delta = 0 := by
    apply Complex.ext
    · exact hReal
    · exact hImaginary
  have hDifference : first - second = 0 := by
    simpa [delta] using hDelta
  exact sub_eq_zero.mp hDifference

/-- If a positive-quarter genuine section is a real Dirac eigensection, its
entire faithful complex line has the same eigenvalue.  This is the geometric
root sector used by the primitive Hopf construction; the external normal-root
label remains an independent mode label. -/
theorem d9PrimitiveSpinCComplexLineLinearMap_eigen
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)
    (eigenvalue : Real)
    (hEigen :
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state = eigenvalue • state)
    (coefficient : Complex) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod .positiveQuarter state coefficient) =
      eigenvalue •
        d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod .positiveQuarter state coefficient := by
  have hImaginaryEigen :
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCImaginarySection
            period hPeriod .positiveQuarter state) =
        eigenvalue •
          d9PrimitiveSpinCImaginarySection
            period hPeriod .positiveQuarter state := by
    rw [d9PrimitiveSpinCGeometricDiracOperator_imaginary, hEigen]
    exact map_smul
      (d9PrimitiveSpinCImaginarySectionLinearMap
        period hPeriod .positiveQuarter) eigenvalue state
  rw [d9PrimitiveSpinCComplexLineLinearMap_apply,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    hEigen, hImaginaryEigen]
  module

/-- Missing imaginary companion of one positive first-sphere eigensection. -/
def primitiveSpinCHopfFirstSpherePositiveImaginarySection
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  d9PrimitiveSpinCImaginarySection
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)

/-- Missing imaginary companion of one negative first-sphere eigensection. -/
def primitiveSpinCHopfFirstSphereNegativeImaginarySection
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  d9PrimitiveSpinCImaginarySection
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)

/-- The positive imaginary companion obeys the same first-order eigen-equation. -/
theorem primitiveSpinCHopfFirstSpherePositiveImaginaryGeometricDiracOperator_eigen
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSpherePositiveImaginarySection
          period hPeriod coordinate sector mode) =
      primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
        primitiveSpinCHopfFirstSpherePositiveImaginarySection
          period hPeriod coordinate sector mode := by
  unfold primitiveSpinCHopfFirstSpherePositiveImaginarySection
  rw [d9PrimitiveSpinCGeometricDiracOperator_imaginary,
    primitiveSpinCHopfFirstSpherePositiveGeometricDiracOperator_eigen]
  exact map_smul
    (d9PrimitiveSpinCImaginarySectionLinearMap
      period hPeriod .positiveQuarter)
    (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode)
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)

/-- The negative imaginary companion obeys the same first-order eigen-equation. -/
theorem primitiveSpinCHopfFirstSphereNegativeImaginaryGeometricDiracOperator_eigen
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereNegativeImaginarySection
          period hPeriod coordinate sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        primitiveSpinCHopfFirstSphereNegativeImaginarySection
          period hPeriod coordinate sector mode := by
  unfold primitiveSpinCHopfFirstSphereNegativeImaginarySection
  rw [d9PrimitiveSpinCGeometricDiracOperator_imaginary,
    primitiveSpinCHopfFirstSphereNegativeGeometricDiracOperator_eigen]
  exact map_smul
    (d9PrimitiveSpinCImaginarySectionLinearMap
      period hPeriod .positiveQuarter)
    (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode)
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)

/-- One abstract complex positive first-sphere coordinate realized by the
real eigensection and its global imaginary companion. -/
def primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    Complex →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  d9PrimitiveSpinCComplexLineLinearMap
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)

/-- One abstract complex negative first-sphere coordinate realized by the
real eigensection and its global imaginary companion. -/
def primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    Complex →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  d9PrimitiveSpinCComplexLineLinearMap
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)

/-- Each positive abstract complex coordinate is represented faithfully. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap_injective
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
        period hPeriod coordinate sector mode) :=
  d9PrimitiveSpinCComplexLineLinearMap_injective
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)
    (primitiveSpinCHopfFirstSpherePositiveSection_ne_zero
      period hPeriod coordinate sector mode)

/-- Each negative abstract complex coordinate is represented faithfully. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap_injective
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
        period hPeriod coordinate sector mode) :=
  d9PrimitiveSpinCComplexLineLinearMap_injective
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)
    (primitiveSpinCHopfFirstSphereNegativeSection_ne_zero
      period hPeriod coordinate sector mode)

/-- Every coefficient in one positive complex line is an actual smooth
first-order Dirac eigensection. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap_eigen
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (coefficient : Complex) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
          period hPeriod coordinate sector mode coefficient) =
      primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
        primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
          period hPeriod coordinate sector mode coefficient :=
  d9PrimitiveSpinCComplexLineLinearMap_eigen
    period hPeriod
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)
    (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode)
    (primitiveSpinCHopfFirstSpherePositiveGeometricDiracOperator_eigen
      period hPeriod coordinate sector mode)
    coefficient

/-- Every coefficient in one negative complex line is an actual smooth
first-order Dirac eigensection. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap_eigen
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (coefficient : Complex) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
          period hPeriod coordinate sector mode coefficient) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
          period hPeriod coordinate sector mode coefficient :=
  d9PrimitiveSpinCComplexLineLinearMap_eigen
    period hPeriod
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)
    (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode)
    (primitiveSpinCHopfFirstSphereNegativeGeometricDiracOperator_eigen
      period hPeriod coordinate sector mode)
    coefficient

/-- Consolidated complex-line realization for every constructed first-sphere
coordinate.  This is coordinatewise faithfulness, not yet joint complex
independence of the three multiplicities. -/
theorem primitiveSpinCHopfFirstSphereComplexCoordinateRealization_closed
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
        (primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
          period hPeriod coordinate sector mode) ∧
      Function.Injective
        (primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
          period hPeriod coordinate sector mode) ∧
      (∀ coefficient : Complex,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
              period hPeriod coordinate sector mode coefficient) =
          primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
            primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap
              period hPeriod coordinate sector mode coefficient) ∧
      (∀ coefficient : Complex,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
              period hPeriod coordinate sector mode coefficient) =
          (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
            primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap
              period hPeriod coordinate sector mode coefficient) :=
  ⟨primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap_injective
      period hPeriod coordinate sector mode,
    primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap_injective
      period hPeriod coordinate sector mode,
    primitiveSpinCHopfFirstSpherePositiveComplexCoefficientLinearMap_eigen
      period hPeriod coordinate sector mode,
    primitiveSpinCHopfFirstSphereNegativeComplexCoefficientLinearMap_eigen
      period hPeriod coordinate sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
end JanusFormal
