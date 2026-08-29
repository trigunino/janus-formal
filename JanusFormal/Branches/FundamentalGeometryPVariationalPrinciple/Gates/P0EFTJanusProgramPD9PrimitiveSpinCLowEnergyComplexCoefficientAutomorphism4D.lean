import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D

/-!
# Automorphism of the faithful low-energy complex coefficient diagonal

The seven-coordinate low-energy Dirac diagonal has one scalar zero-mode block
and one signed first-sphere block.  The quarter-root frequency is nonzero and
the first-sphere square is the strictly positive scalar `k² + 2`.

This gate constructs the inverse coefficient operator explicitly and packages
the diagonal as a real-linear automorphism.  Through the already established
geometric synthesis equivalence, this is the concrete inverse model for the
actual low-energy differential Dirac restriction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientAutomorphism4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Explicit inverse of the seven-complex-coordinate Dirac diagonal. -/
def primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients →ₗ[Real]
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients where
  toFun coefficients :=
    ((-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
        coefficients.1,
      (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
        primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode coefficients.2)
  map_add' first second := by
    apply Prod.ext
    · change
        (-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
            (first.1 + second.1) =
          (-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
              first.1 +
            (-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
              second.1
      rw [smul_add]
    · change
        (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
            primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode (first.2 + second.2) =
          (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
              primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
                period sector mode first.2 +
            (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
              primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
                period sector mode second.2
      rw [map_add, smul_add]
  map_smul' scalar coefficients := by
    apply Prod.ext
    · change
        (-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
            (scalar • coefficients.1) =
          scalar •
            ((-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
              coefficients.1)
      module
    · change
        (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
            primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode (scalar • coefficients.2) =
          scalar •
            ((normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
              primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
                period sector mode coefficients.2)
      rw [map_smul]
      module

@[simp]
theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_apply
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
        period sector mode coefficients =
      ((-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
          coefficients.1,
        (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
          primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode coefficients.2) :=
  rfl

include hPeriod

/-- The explicit coefficient inverse is a left inverse. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_left
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
        period sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode coefficients) =
      coefficients := by
  have hZero :
      -normalRootLeviCivitaCorrectedFrequency period sector mode ≠ 0 :=
    neg_ne_zero.mpr
      (normalRootLeviCivitaCorrectedFrequency_ne_zero
        period hPeriod sector mode)
  have hFirst :
      normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2 ≠ 0 := by
    positivity
  apply Prod.ext
  · change
      (-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
          ((-normalRootLeviCivitaCorrectedFrequency period sector mode) •
            coefficients.1) = coefficients.1
    exact inv_smul_smul₀ hZero coefficients.1
  · change
      (normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
          primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
            period sector mode
            (primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode coefficients.2) =
        coefficients.2
    rw [primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_sq,
      ← mul_smul]
    simp [hFirst]

/-- The explicit coefficient inverse is also a right inverse. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_right
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator
        period sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
          period sector mode coefficients) =
      coefficients := by
  have hZero :
      -normalRootLeviCivitaCorrectedFrequency period sector mode ≠ 0 :=
    neg_ne_zero.mpr
      (normalRootLeviCivitaCorrectedFrequency_ne_zero
        period hPeriod sector mode)
  have hFirst :
      normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2 ≠ 0 := by
    positivity
  apply Prod.ext
  · change
      (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
          ((-normalRootLeviCivitaCorrectedFrequency period sector mode)⁻¹ •
            coefficients.1) = coefficients.1
    exact smul_inv_smul₀ hZero coefficients.1
  · change
      primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
          period sector mode
          ((normalRootLeviCivitaCorrectedFrequency period sector mode ^ 2 + 2)⁻¹ •
            primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator
              period sector mode coefficients.2) = coefficients.2
    rw [map_smul,
      primitiveSpinCHopfFirstSphereSignedComplexCoefficientOperator_sq,
      ← mul_smul]
    simp [hFirst]

/-- Linear automorphism carried by the explicit low-energy coefficient Dirac
diagonal. -/
def primitiveSpinCHopfLowEnergyComplexCoefficientOperatorLinearEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCLowEnergyGeometricComplexCoefficients ≃ₗ[Real]
      PrimitiveSpinCLowEnergyGeometricComplexCoefficients where
  toLinearMap :=
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator
      period sector mode
  invFun :=
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
      period sector mode
  left_inv :=
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_left
      period hPeriod sector mode
  right_inv :=
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_right
      period hPeriod sector mode

/-- The explicit seven-complex-coordinate Dirac diagonal is bijective. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperator_bijective
    (sector : NormalRootChoice) (mode : Int) :
    Function.Bijective
      (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
        period sector mode) :=
  (primitiveSpinCHopfLowEnergyComplexCoefficientOperatorLinearEquiv
    period hPeriod sector mode).bijective

/-- Its coefficient kernel is exactly zero. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientOperator_ker_eq_bot
    (sector : NormalRootChoice) (mode : Int) :
    LinearMap.ker
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode) = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr
    (primitiveSpinCHopfLowEnergyComplexCoefficientOperator_bijective
      period hPeriod sector mode).1

/-- Consolidated automorphism theorem for the faithful low-energy coefficient
model. -/
theorem primitiveSpinCHopfLowEnergyComplexCoefficientAutomorphism_closed
    (sector : NormalRootChoice) (mode : Int) :
    Function.Bijective
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
          period sector mode) ∧
      LinearMap.ker
          (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode) = ⊥ ∧
      (∀ coefficients,
        primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
            period sector mode
            (primitiveSpinCHopfLowEnergyComplexCoefficientOperator
              period sector mode coefficients) = coefficients) ∧
      (∀ coefficients,
        primitiveSpinCHopfLowEnergyComplexCoefficientOperator
            period sector mode
            (primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
              period sector mode coefficients) = coefficients) :=
  ⟨primitiveSpinCHopfLowEnergyComplexCoefficientOperator_bijective
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperator_ker_eq_bot
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_left
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_right
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientAutomorphism4D
end JanusFormal
