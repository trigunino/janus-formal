import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D

/-!
# Full global complex scalar action on genuine primitive SpinC sections

The previous gate descended multiplication by `i`.  The local SpinC cocycle
and local geometric Dirac operator are already covariant under multiplication
by every constant complex scalar.  This gate descends that entire action to
the genuine smooth-section core.

The resulting real-linear endomorphisms form a unital ring representation of
`ℂ`; real scalars recover the pre-existing real module structure, `i` recovers
the global complex structure, and every scalar endomorphism commutes with the
actual differential Dirac operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
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

/-- Multiplication by a constant complex scalar on an arbitrary genuine
smooth primitive SpinC section. -/
def d9PrimitiveSpinCComplexScalarSection
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  (d9PrimitiveSpinCComplexLocalGaugeFamily
    period hPeriod choice scalar
    (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state)).toSmoothSection
        period hPeriod choice

@[simp]
theorem d9PrimitiveSpinCComplexScalarSection_apply
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state base =
      d9PrimitiveSpinCComplexActionCLM scalar (state base) := by
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
    d9PrimitiveSpinCComplexActionCLM scalar
        (family.localValue
          ((d9PrimitiveSpinCVectorBundleCore
            period hPeriod choice).indexAt base) base) =
      d9PrimitiveSpinCComplexActionCLM scalar (state base)
  congr 1
  simpa only [SmoothPrimitiveSpinCLocalGaugeFamily.toSmoothSection_apply]
    using hAt

/-- The global scalar action is real-linear in the section variable. -/
def d9PrimitiveSpinCComplexScalarSectionLinearMap
    (choice : NormalRootChoice) (scalar : Complex) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod choice where
  toFun :=
    d9PrimitiveSpinCComplexScalarSection
      period hPeriod choice scalar
  map_add' first second := by
    ext base
    change
      d9PrimitiveSpinCComplexActionCLM scalar
          (first base + second base) =
        d9PrimitiveSpinCComplexActionCLM scalar (first base) +
          d9PrimitiveSpinCComplexActionCLM scalar (second base)
    exact map_add (d9PrimitiveSpinCComplexActionCLM scalar) _ _
  map_smul' real state := by
    ext base
    change
      d9PrimitiveSpinCComplexActionCLM scalar
          (real • state base) =
        real • d9PrimitiveSpinCComplexActionCLM scalar (state base)
    exact map_smul (d9PrimitiveSpinCComplexActionCLM scalar) real (state base)

@[simp]
theorem d9PrimitiveSpinCComplexScalarSectionLinearMap_apply
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSectionLinearMap
        period hPeriod choice scalar state =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar state :=
  rfl

private theorem d9PrimitiveSpinCComplexAction_zero
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM 0 matter = 0 := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  simp

private theorem d9PrimitiveSpinCComplexAction_add
    (first second : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM (first + second) matter =
      d9PrimitiveSpinCComplexActionCLM first matter +
        d9PrimitiveSpinCComplexActionCLM second matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_add,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  simp only [add_smul]

/-- Zero complex scalar gives the zero smooth section. -/
@[simp]
theorem d9PrimitiveSpinCComplexScalarSection_zero_scalar
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice 0 state = 0 := by
  ext base
  exact d9PrimitiveSpinCComplexAction_zero (state base)

/-- One complex scalar gives the original smooth section. -/
@[simp]
theorem d9PrimitiveSpinCComplexScalarSection_one
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice 1 state = state := by
  ext base
  change d9PrimitiveSpinCComplexActionCLM 1 (state base) = state base
  exact d9PrimitiveSpinCComplexAction_one (state base)

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
  ext base
  exact d9PrimitiveSpinCComplexAction_add first second (state base)

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
  ext base
  change
    d9PrimitiveSpinCComplexActionCLM (first * second) (state base) =
      d9PrimitiveSpinCComplexActionCLM first
        (d9PrimitiveSpinCComplexActionCLM second (state base))
  exact d9PrimitiveSpinCComplexAction_mul first second (state base)

/-- The transported complex action restricts to the existing real scalar
action. -/
theorem d9PrimitiveSpinCComplexScalarSection_ofReal
    (choice : NormalRootChoice) (real : Real)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice (real : Complex) state =
      real • state := by
  ext base
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction, map_smul]
  simp only [Complex.real_smul]

/-- The scalar `i` recovers the previously descended global complex
structure. -/
theorem d9PrimitiveSpinCComplexScalarSection_I
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice Complex.I state =
      d9PrimitiveSpinCImaginarySection
        period hPeriod choice state := by
  ext base
  change
    d9PrimitiveSpinCComplexActionCLM Complex.I (state base) =
      d9PrimitiveSpinCImaginaryAction (state base)
  rfl

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

/-- Real-linear packaging of the actual differential geometric Dirac
operator. -/
def d9PrimitiveSpinCGeometricDiracRealLinearMap
    (choice : NormalRootChoice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod choice where
  toFun := d9PrimitiveSpinCGeometricDiracOperator period hPeriod choice
  map_add' first second :=
    d9PrimitiveSpinCGeometricDiracOperator_add
      period hPeriod first second
  map_smul' scalar state :=
    d9PrimitiveSpinCGeometricDiracOperator_real_smul
      period hPeriod choice scalar state

@[simp]
theorem d9PrimitiveSpinCGeometricDiracRealLinearMap_apply
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricDiracRealLinearMap
        period hPeriod choice state =
      d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod choice state :=
  rfl

/-- Every global complex scalar endomorphism commutes with the actual
differential geometric Dirac operator. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_complexScalar
    (choice : NormalRootChoice) (scalar : Complex)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod choice
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar state) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod choice state) := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  let complexFamily :=
    d9PrimitiveSpinCComplexLocalGaugeFamily
      period hPeriod choice scalar family
  rw [show
      d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar state =
        complexFamily.toSmoothSection period hPeriod choice by rfl]
  rw [d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection]
  ext base
  let core := d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (core.indexAt base) :=
    core.mem_baseSet_at base
  rw [d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCComplexScalarSection_apply]
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice complexFamily (core.indexAt base) base =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family (core.indexAt base) base)
  exact d9PrimitiveSpinCLocalGeometricDirac_complexAction
    period hPeriod choice scalar family (core.indexAt base) base hBase

/-- Endomorphism-level commutation relation for the full complex scalar
representation. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_commutes_complexRepresentation
    (choice : NormalRootChoice) (scalar : Complex) :
    (d9PrimitiveSpinCGeometricDiracRealLinearMap
        period hPeriod choice).comp
        (d9PrimitiveSpinCComplexScalarRepresentation
          period hPeriod choice scalar) =
      (d9PrimitiveSpinCComplexScalarRepresentation
          period hPeriod choice scalar).comp
        (d9PrimitiveSpinCGeometricDiracRealLinearMap
          period hPeriod choice) := by
  apply LinearMap.ext
  intro state
  exact d9PrimitiveSpinCGeometricDiracOperator_complexScalar
    period hPeriod choice scalar state

/-- Consolidated global complex-scalar closure. -/
theorem d9PrimitiveSpinCGlobalComplexScalarAction_closed
    (choice : NormalRootChoice) :
    (∀ scalar state,
      d9PrimitiveSpinCComplexScalarRepresentation
          period hPeriod choice scalar state =
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar state) ∧
      (∀ real state,
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod choice (real : Complex) state =
          real • state) ∧
      (∀ state,
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod choice Complex.I state =
          d9PrimitiveSpinCImaginarySection
            period hPeriod choice state) ∧
      (∀ scalar,
        (d9PrimitiveSpinCGeometricDiracRealLinearMap
            period hPeriod choice).comp
            (d9PrimitiveSpinCComplexScalarRepresentation
              period hPeriod choice scalar) =
          (d9PrimitiveSpinCComplexScalarRepresentation
              period hPeriod choice scalar).comp
            (d9PrimitiveSpinCGeometricDiracRealLinearMap
              period hPeriod choice)) :=
  ⟨d9PrimitiveSpinCComplexScalarRepresentation_apply
      period hPeriod choice,
    d9PrimitiveSpinCComplexScalarSection_ofReal
      period hPeriod choice,
    d9PrimitiveSpinCComplexScalarSection_I
      period hPeriod choice,
    d9PrimitiveSpinCGeometricDiracOperator_commutes_complexRepresentation
      period hPeriod choice⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
end JanusFormal
