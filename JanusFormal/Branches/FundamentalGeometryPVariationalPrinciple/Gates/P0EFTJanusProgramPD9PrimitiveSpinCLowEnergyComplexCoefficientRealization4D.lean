import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereSignedComplexMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D

/-!
# Faithful complex coordinates for the geometric low-energy SpinC block

The Hopf zero line has one complex coefficient and the complete signed first
sphere has six complex coefficients.  The two-witness theorem now makes the
first-sphere synthesis faithful, while the squared spectral gap separates it
from the zero line.

This gate packages the resulting seven complex coordinates into one exact
linear equivalence onto the genuine zero-plus-first-level smooth-section
range.  The actual differential Dirac operator is conjugate there to the
explicit block diagonal with eigenvalues `-k`, `+sqrt (k² + 2)` and
`-sqrt (k² + 2)`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereSignedComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- One complex Hopf coefficient and the two three-coordinate complex signed
first-sphere packets. -/
abbrev PrimitiveSpinCLowEnergyGeometricComplexCoefficients :=
  Complex × PrimitiveSpinCFirstSphereSignedComplexCoefficients

/-- A single Hopf coefficient is faithfully represented in its geometric
complex line. -/
theorem primitiveSpinCHopfZeroModeCoefficientLinearMap_injective_at
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod (sector, mode)) := by
  intro first second hEqual
  have hSynthesis :
      primitiveSpinCHopfFiniteZeroModeSynthesis period hPeriod
          (Finsupp.single (sector, mode) first) =
        primitiveSpinCHopfFiniteZeroModeSynthesis period hPeriod
          (Finsupp.single (sector, mode) second) := by
    simpa only [primitiveSpinCHopfFiniteZeroModeSynthesis_single]
      using hEqual
  have hSingle :=
    primitiveSpinCHopfFiniteZeroModeSynthesis_injective
      period hPeriod hSynthesis
  have hAt := congrArg
    (fun coefficients : PrimitiveSpinCGeometricFiniteZeroModeCoefficients =>
      coefficients (sector, mode)) hSingle
  simpa using hAt

/-- Exact complex coordinate on the genuine Hopf zero-mode range. -/
def primitiveSpinCHopfZeroModeComplexCoefficientEquiv
    (sector : NormalRootChoice) (mode : Int) :
    Complex ≃ₗ[Real]
      PrimitiveSpinCHopfZeroModeComplexSpan
        period hPeriod sector mode :=
  LinearEquiv.ofInjective
    (primitiveSpinCHopfZeroModeCoefficientLinearMap
      period hPeriod (sector, mode))
    (primitiveSpinCHopfZeroModeCoefficientLinearMap_injective_at
      period hPeriod sector mode)

@[simp]
theorem primitiveSpinCHopfZeroModeComplexCoefficientEquiv_coe
    (sector : NormalRootChoice) (mode : Int) (coefficient : Complex) :
    ((primitiveSpinCHopfZeroModeComplexCoefficientEquiv
        period hPeriod sector mode coefficient :
      PrimitiveSpinCHopfZeroModeComplexSpan
        period hPeriod sector mode) :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) =
      primitiveSpinCHopfZeroModeCoefficientLinearMap
        period hPeriod (sector, mode) coefficient :=
  rfl

/-- Exact product coordinates on the zero and signed first-sphere geometric
ranges before adding them as ambient smooth sections. -/
def primitiveSpinCHopfLowEnergyComplexCoefficientBlockEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients ≃ₗ[Real]
      PrimitiveSpinCLowEnergyComplexBlocks
        period hPeriod sector mode :=
  (primitiveSpinCHopfZeroModeComplexCoefficientEquiv
      period hPeriod sector mode).prodCongr
    (primitiveSpinCHopfFirstSphereSignedComplexSynthesisEquiv
      period hPeriod sector mode)

/-- Seven faithful complex coordinates on the actual geometric low-energy
smooth-section range. -/
def primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients ≃ₗ[Real]
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode :=
  (primitiveSpinCHopfLowEnergyComplexCoefficientBlockEquiv
      period hPeriod sector mode).trans
    (primitiveSpinCHopfLowEnergyComplexAdditionEquiv
      period hPeriod sector mode)

@[simp]
theorem primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv_coe
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    ((primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
        period hPeriod sector mode coefficients :
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode) :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) =
      primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) coefficients.1 +
        primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode coefficients.2 :=
  rfl

/-- Ambient smooth-section synthesis attached to the exact low-energy complex
coordinate equivalence. -/
def primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  (Submodule.subtype
      (PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode)).comp
    (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
      period hPeriod sector mode).toLinearMap

@[simp]
theorem primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
        period hPeriod sector mode coefficients =
      primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode) coefficients.1 +
        primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode coefficients.2 :=
  rfl

/-- The seven-complex-coordinate ambient synthesis is faithful. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_injective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
      (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
        period hPeriod sector mode) := by
  intro first second hEqual
  have hRange :
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
          period hPeriod sector mode first =
        primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
          period hPeriod sector mode second := by
    apply Subtype.ext
    exact hEqual
  exact
    (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
      period hPeriod sector mode).injective hRange

/-- Explicit Dirac diagonal on the seven complex low-energy coordinates. -/
def primitiveSpinCHopfLowEnergyComplexCoefficientOperator
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients where
  toFun coefficients :=
    ((-normalRootLeviCivitaCorrectedFrequency period sector mode) •
        coefficients.1,
      primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
        period sector mode coefficients.2)
  map_add' first second := by
    apply Prod.ext
    · change
        (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
            (first.1 + second.1) =
          (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
              first.1 +
            (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
              second.1
      rw [smul_add]
    · change
        primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode (first.2 + second.2) =
          primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode first.2 +
            primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode second.2
      exact map_add
        (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode) first.2 second.2
  map_smul' scalar coefficients := by
    apply Prod.ext
    · change
        (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
            (scalar • coefficients.1) =
          scalar •
            ((-normalRootLeviCivitaCorrectedFrequency period sector mode) •
              coefficients.1)
      module
    · change
        primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode (scalar • coefficients.2) =
          scalar •
            primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode coefficients.2
      exact map_smul
        (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode) scalar coefficients.2

@[simp]
theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperator_apply
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator
        period sector mode coefficients =
      ((-normalRootLeviCivitaCorrectedFrequency period sector mode) •
          coefficients.1,
        primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode coefficients.2) :=
  rfl

/-- The genuine differential Dirac operator intertwines the faithful ambient
low-energy complex synthesis with the explicit coefficient diagonal. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_intertwines_dirac
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients) =
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients) := by
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) coefficients.1 +
          primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients.2) =
      primitiveSpinCHopfZeroModeCoefficientLinearMap
          period hPeriod (sector, mode)
          ((-normalRootLeviCivitaCorrectedFrequency
            period sector mode) • coefficients.1) +
        primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode
          (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode coefficients.2)
  rw [d9PrimitiveSpinCGeometricDiracOperator_add,
    primitiveSpinCHopfZeroModeCoefficientGeometricDiracOperator_eigen,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_intertwines_dirac,
    map_smul]

/-- In exact seven-complex-coordinate form, the actual low-energy Dirac
restriction is the explicit coefficient diagonal. -/
@[simp]
theorem primitiveSpinCHopfLowEnergyComplexActualDirac_synthesisEquiv
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
          period hPeriod sector mode coefficients) =
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients) := by
  apply Subtype.ext
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients) =
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients)
  exact
    primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_intertwines_dirac
      period hPeriod sector mode coefficients

/-- Exact conjugacy of the genuine low-energy differential Dirac restriction
with the seven-complex-coordinate diagonal. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDirac_coefficient_conjugate
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode =
      (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
          period hPeriod sector mode).toLinearMap.comp
        ((primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode).comp
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
            period hPeriod sector mode).symm.toLinearMap) := by
  apply LinearMap.ext
  intro state
  rcases (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
    period hPeriod sector mode).surjective state with ⟨coefficients, rfl⟩
  rw [primitiveSpinCHopfLowEnergyComplexActualDirac_synthesisEquiv]
  simp

/-- Consolidated faithful complex low-energy coordinate theorem. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientRealization_closed
    (sector : NormalRootChoice) (mode : Int) :
    Function.Injective
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode) ∧
      (∀ coefficients,
        d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter
            (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
              period hPeriod sector mode coefficients) =
          primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode
            (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
              period sector mode coefficients)) ∧
      primitiveSpinCHopfLowEnergyComplexActualDirac
          period hPeriod sector mode =
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
            period hPeriod sector mode).toLinearMap.comp
          ((primitiveSpinCHopfLowEnergyComplexCoefficientOperator
              period sector mode).comp
            (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
              period hPeriod sector mode).symm.toLinearMap) :=
  ⟨primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_injective
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_intertwines_dirac
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDirac_coefficient_conjugate
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
end JanusFormal
