import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D

/-!
# Complex linearity of the geometric first-sphere packet

The smooth primitive SpinC core is packaged as a real module, while the
preceding gate supplies its intrinsic global `ℂ`-scalar representation.
This gate identifies the previously constructed complex-line coordinates
with that action and proves that the positive, negative and signed
first-sphere packet syntheses respect arbitrary complex scalars.

Consequently the actual geometric packet range is invariant under the global
complex action, and the genuine differential Dirac operator commutes with
that action on the range.  No joint injectivity of the three complex
multiplicities is used or claimed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexLinearity4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The earlier real-linear complex-line coordinate map is definitionally the
intrinsic global complex scalar action on its real generator. -/
theorem d9PrimitiveSpinCComplexLineLinearMap_eq_complexScalarSection
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (coefficient : Complex) :
    d9PrimitiveSpinCComplexLineLinearMap
        period hPeriod choice state coefficient =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice coefficient state :=
  rfl

/-- Multiplication of complex coefficients is composition of the corresponding
geometric scalar actions on one complex eigenspinor line. -/
theorem d9PrimitiveSpinCComplexLineLinearMap_mul
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : Complex) :
    d9PrimitiveSpinCComplexLineLinearMap
        period hPeriod choice state (first * second) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice first
        (d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod choice state second) := by
  rw [d9PrimitiveSpinCComplexLineLinearMap_eq_complexScalarSection,
    d9PrimitiveSpinCComplexLineLinearMap_eq_complexScalarSection,
    d9PrimitiveSpinCComplexScalarSection_mul]

/-- A fixed complex scalar action distributes over every finite sum of genuine
smooth sections. -/
theorem d9PrimitiveSpinCComplexScalarSection_finset_sum
    {ι : Type} [DecidableEq ι]
    (choice : NormalRootChoice) (scalar : Complex)
    (states : ι → D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (indices : Finset ι) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod choice scalar
        (∑ index ∈ indices, states index) =
      ∑ index ∈ indices,
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod choice scalar (states index) := by
  change
    d9PrimitiveSpinCComplexScalarSectionLinearMap
        period hPeriod choice scalar
        (∑ index ∈ indices, states index) =
      ∑ index ∈ indices,
        d9PrimitiveSpinCComplexScalarSectionLinearMap
          period hPeriod choice scalar (states index)
  rw [map_sum]

/-- The positive first-sphere synthesis respects arbitrary complex scalar
multiplication on all three coefficient coordinates simultaneously. -/
theorem primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_complex_smul
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
        period hPeriod sector mode (scalar • coefficients) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode coefficients) := by
  rw [primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply,
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_apply,
    d9PrimitiveSpinCComplexScalarSection_finset_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  change
    d9PrimitiveSpinCComplexLineLinearMap
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode)
        (scalar * coefficients coordinate) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod coordinate sector mode)
          (coefficients coordinate))
  exact d9PrimitiveSpinCComplexLineLinearMap_mul
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSpherePositiveSection
      period hPeriod coordinate sector mode)
    scalar (coefficients coordinate)

/-- The negative first-sphere synthesis respects arbitrary complex scalar
multiplication on all three coefficient coordinates simultaneously. -/
theorem primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_complex_smul
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (coefficients : PrimitiveSpinCFirstSphereComplexCoefficients) :
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
        period hPeriod sector mode (scalar • coefficients) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode coefficients) := by
  rw [primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply,
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_apply,
    d9PrimitiveSpinCComplexScalarSection_finset_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  change
    d9PrimitiveSpinCComplexLineLinearMap
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode)
        (scalar * coefficients coordinate) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (d9PrimitiveSpinCComplexLineLinearMap
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod coordinate sector mode)
          (coefficients coordinate))
  exact d9PrimitiveSpinCComplexLineLinearMap_mul
    period hPeriod .positiveQuarter
    (primitiveSpinCHopfFirstSphereNegativeSection
      period hPeriod coordinate sector mode)
    scalar (coefficients coordinate)

/-- The complete signed first-sphere packet is compatible with the global
complex scalar action. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_complex_smul
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
        period hPeriod sector mode (scalar • coefficients) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode coefficients) := by
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply,
    primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_apply]
  change
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
          period hPeriod sector mode (scalar • coefficients.1) +
        primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
          period hPeriod sector mode (scalar • coefficients.2) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
            period hPeriod sector mode coefficients.1 +
          primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
            period hPeriod sector mode coefficients.2)
  rw [
    primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis_complex_smul,
    primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis_complex_smul]
  exact
    (map_add
      (d9PrimitiveSpinCComplexScalarSectionLinearMap
        period hPeriod .positiveQuarter scalar)
      (primitiveSpinCHopfFirstSpherePositiveComplexPacketSynthesis
        period hPeriod sector mode coefficients.1)
      (primitiveSpinCHopfFirstSphereNegativeComplexPacketSynthesis
        period hPeriod sector mode coefficients.2)).symm

/-- The signed coefficient Dirac diagonal commutes with arbitrary complex
scalar multiplication. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_complex_smul
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients) :
    primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
        period sector mode (scalar • coefficients) =
      scalar •
        primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode coefficients := by
  apply Prod.ext <;> funext coordinate <;> dsimp
  · change
      (primitiveSpinCHopfFirstSphereDiracFrequency
          period sector mode : Complex) *
          (scalar * coefficients.1 coordinate) =
        scalar *
          ((primitiveSpinCHopfFirstSphereDiracFrequency
            period sector mode : Complex) * coefficients.1 coordinate)
    ring
  · change
      ((-primitiveSpinCHopfFirstSphereDiracFrequency
          period sector mode : Real) : Complex) *
          (scalar * coefficients.2 coordinate) =
        scalar *
          (((-primitiveSpinCHopfFirstSphereDiracFrequency
            period sector mode : Real) : Complex) * coefficients.2 coordinate)
    ring

/-- The actual geometric range of the signed first-sphere packet is invariant
under every complex scalar action. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexSpan_complexScalar_mem
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar state.1 ∈
      PrimitiveSpinCHopfFirstSphereSignedComplexSpan
        period hPeriod sector mode := by
  rcases state.property with ⟨coefficients, hCoefficients⟩
  refine ⟨scalar • coefficients, ?_⟩
  rw [primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_complex_smul,
    hCoefficients]

/-- On the actual geometric first-sphere range, the genuine differential
Dirac operator commutes with every complex scalar action. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexSpan_dirac_complexScalar
    (sector : NormalRootChoice) (mode : Int)
    (scalar : Complex)
    (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
      period hPeriod sector mode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar state.1) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state.1) :=
  d9PrimitiveSpinCGeometricDiracOperator_complexScalar
    period hPeriod scalar state.1

/-- Consolidated complex-linearity result for the geometric signed packet. -/
theorem primitiveSpinCHopfFirstSphereSignedComplexLinearity_closed
    (sector : NormalRootChoice) (mode : Int) :
    (∀ (scalar : Complex)
        (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients),
      primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
          period hPeriod sector mode (scalar • coefficients) =
        d9PrimitiveSpinCComplexScalarSection
          period hPeriod .positiveQuarter scalar
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients)) ∧
      (∀ (scalar : Complex)
          (coefficients : PrimitiveSpinCFirstSphereSignedComplexCoefficients),
        primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode (scalar • coefficients) =
          scalar •
            primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode coefficients) ∧
      (∀ (scalar : Complex)
          (state : PrimitiveSpinCHopfFirstSphereSignedComplexSpan
            period hPeriod sector mode),
        d9PrimitiveSpinCComplexScalarSection
            period hPeriod .positiveQuarter scalar state.1 ∈
          PrimitiveSpinCHopfFirstSphereSignedComplexSpan
            period hPeriod sector mode) :=
  ⟨primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis_complex_smul
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_complex_smul
      period sector mode,
    primitiveSpinCHopfFirstSphereSignedComplexSpan_complexScalar_mem
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexLinearity4D
end JanusFormal
