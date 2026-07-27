import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexClosure4D

/-!
# Finite circle-mode core of the low-energy geometric SpinC block

For one fixed normal-root sector, this gate assembles finitely many circle
labels of the faithful seven-complex-coordinate zero-plus-first-level block.
The actual differential Dirac operator intertwines the finite geometric
synthesis with the modewise explicit coefficient diagonal.

The coefficient diagonal is an automorphism, with inverse assembled
mode-by-mode from the fixed-label inverse.  Injectivity of the simultaneous
geometric synthesis across distinct circle labels is deliberately left to the
next Fourier-separation gate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Finite circle-mode packets of the seven complex low-energy coordinates,
at one fixed normal-root sector. -/
abbrev PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients :=
  Int →₀ PrimitiveSpinCLowEnergyGeometricComplexCoefficients

/-- One circle-mode geometric synthesis block. -/
def primitiveSpinCHopfLowEnergyFiniteModeSynthesisBlock
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
    period hPeriod sector mode

/-- Finite geometric synthesis over all supported circle labels of one root
sector. -/
def primitiveSpinCHopfLowEnergyFiniteModeSynthesis
    (sector : NormalRootChoice) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  Finsupp.lsum Real fun mode =>
    primitiveSpinCHopfLowEnergyFiniteModeSynthesisBlock
      period hPeriod sector mode

@[simp]
theorem primitiveSpinCHopfLowEnergyFiniteModeSynthesis_single
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyFiniteModeSynthesis
        period hPeriod sector (Finsupp.single mode coefficients) =
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
        period hPeriod sector mode coefficients := by
  rw [primitiveSpinCHopfLowEnergyFiniteModeSynthesis,
    Finsupp.lsum_single]
  rfl

/-- One modewise coefficient Dirac block inserted back into finite support. -/
def primitiveSpinCHopfLowEnergyFiniteModeCoefficientBlock
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients :=
  (Finsupp.lsingle mode).comp
    (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
      period sector mode)

/-- Explicit modewise Dirac diagonal on finite low-energy packets. -/
def primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
    (sector : NormalRootChoice) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients :=
  Finsupp.lsum Real fun mode =>
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientBlock
      period sector mode

@[simp]
theorem primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_single
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
        period sector (Finsupp.single mode coefficients) =
      Finsupp.single mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients) := by
  rw [primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator,
    Finsupp.lsum_single]
  rfl

/-- One inverse coefficient block inserted back into finite support. -/
def primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverseBlock
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients :=
  (Finsupp.lsingle mode).comp
    (primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
      period sector mode)

/-- Explicit modewise inverse diagonal on finite low-energy packets. -/
def primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse
    (sector : NormalRootChoice) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients :=
  Finsupp.lsum Real fun mode =>
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverseBlock
      period sector mode

@[simp]
theorem primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse_single
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse
        period sector (Finsupp.single mode coefficients) =
      Finsupp.single mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
          period sector mode coefficients) := by
  rw [primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse,
    Finsupp.lsum_single]
  rfl

include hPeriod

/-- The finite modewise inverse is a left inverse of the finite coefficient
Dirac diagonal. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse_left
    (sector : NormalRootChoice) :
    (primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse
        period sector).comp
      (primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
        period sector) =
      LinearMap.id := by
  apply Finsupp.lhom_ext
  intro mode coefficients
  rw [LinearMap.comp_apply,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_single,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse_single,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_left
      (hPeriod := hPeriod)]
  rfl

/-- The finite modewise inverse is also a right inverse. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse_right
    (sector : NormalRootChoice) :
    (primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
        period sector).comp
      (primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse
        period sector) =
      LinearMap.id := by
  apply Finsupp.lhom_ext
  intro mode coefficients
  rw [LinearMap.comp_apply,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse_single,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_single,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_right
      (hPeriod := hPeriod)]
  rfl

/-- The finite coefficient Dirac diagonal is an exact real-linear
automorphism. -/
def primitiveSpinCHopfLowEnergyFiniteModeCoefficientLinearEquiv
    (sector : NormalRootChoice) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients ≃ₗ[Real]
      PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients where
  toLinearMap :=
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
      period sector
  invFun :=
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse
      period sector
  left_inv coefficients := by
    exact LinearMap.congr_fun
      (primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse_left
        period hPeriod sector) coefficients
  right_inv coefficients := by
    exact LinearMap.congr_fun
      (primitiveSpinCHopfLowEnergyFiniteModeCoefficientInverse_right
        period hPeriod sector) coefficients

/-- The actual differential Dirac operator intertwines finite geometric
synthesis with the finite modewise coefficient diagonal. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeSynthesis_intertwines_dirac
    (sector : NormalRootChoice) :
    (d9PrimitiveSpinCGeometricDiracRealLinearMap
        period hPeriod).comp
      (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
        period hPeriod sector) =
      (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
        period hPeriod sector).comp
        (primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
          period sector) := by
  apply Finsupp.lhom_ext
  intro mode coefficients
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    primitiveSpinCHopfLowEnergyFiniteModeSynthesis_single,
    primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator_single,
    primitiveSpinCHopfLowEnergyFiniteModeSynthesis_single,
    d9PrimitiveSpinCGeometricDiracRealLinearMap_apply]
  exact
    primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_intertwines_dirac
      period hPeriod sector mode coefficients

/-- The geometric range of finite circle-mode packets is invariant under the
actual differential Dirac operator. -/
abbrev PrimitiveSpinCHopfLowEnergyFiniteModeSpan
    (sector : NormalRootChoice) :=
  LinearMap.range
    (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
      period hPeriod sector)

/-- Dirac invariance of the finite circle-mode geometric range. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeSpan_dirac_mem
    (sector : NormalRootChoice)
    (state : PrimitiveSpinCHopfLowEnergyFiniteModeSpan
      period hPeriod sector) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter state.1 ∈
      PrimitiveSpinCHopfLowEnergyFiniteModeSpan
        period hPeriod sector := by
  rcases state.property with ⟨coefficients, hCoefficients⟩
  refine ⟨primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
    period sector coefficients, ?_⟩
  have hIntertwining := LinearMap.congr_fun
    (primitiveSpinCHopfLowEnergyFiniteModeSynthesis_intertwines_dirac
      period hPeriod sector) coefficients
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    d9PrimitiveSpinCGeometricDiracRealLinearMap_apply] at hIntertwining
  rw [← hCoefficients]
  exact hIntertwining.symm

/-- Consolidated finite-circle-mode core.  The remaining theorem is
simultaneous Fourier faithfulness of the geometric synthesis. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeCore_closed
    (sector : NormalRootChoice) :
    Function.Bijective
        (primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
          period sector) ∧
      (d9PrimitiveSpinCGeometricDiracRealLinearMap
          period hPeriod).comp
        (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
          period hPeriod sector) =
        (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
          period hPeriod sector).comp
          (primitiveSpinCHopfLowEnergyFiniteModeCoefficientOperator
            period sector) ∧
      (∀ state : PrimitiveSpinCHopfLowEnergyFiniteModeSpan
          period hPeriod sector,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter state.1 ∈
          PrimitiveSpinCHopfLowEnergyFiniteModeSpan
            period hPeriod sector) :=
  ⟨(primitiveSpinCHopfLowEnergyFiniteModeCoefficientLinearEquiv
      period hPeriod sector).bijective,
    primitiveSpinCHopfLowEnergyFiniteModeSynthesis_intertwines_dirac
      period hPeriod sector,
    primitiveSpinCHopfLowEnergyFiniteModeSpan_dirac_mem
      period hPeriod sector⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D
end JanusFormal
