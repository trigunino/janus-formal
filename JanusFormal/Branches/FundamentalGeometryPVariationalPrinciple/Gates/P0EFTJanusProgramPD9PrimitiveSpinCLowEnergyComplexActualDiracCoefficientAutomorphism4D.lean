import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientAutomorphism4D

/-!
# Explicit coefficient inverse for the actual low-energy geometric Dirac

The faithful seven-complex-coordinate synthesis identifies the actual
zero-plus-first-level smooth-section range with the explicit coefficient
space.  Conjugating the coefficient automorphism gives a linear equivalence
whose underlying map is exactly the genuine differential Dirac restriction.
Its inverse is therefore the synthesis of the explicit coefficient inverse.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexActualDiracCoefficientAutomorphism4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientAutomorphism4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Actual geometric low-energy Dirac equivalence obtained by conjugating the
explicit seven-coordinate diagonal. -/
def primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientLinearEquiv
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode ≃ₗ[Real]
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode :=
  ((primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
      period hPeriod sector mode).symm.trans
    (primitiveSpinCHopfLowEnergyComplexCoefficientOperatorLinearEquiv
      period hPeriod sector mode)).trans
    (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
      period hPeriod sector mode)

/-- Its underlying linear map is exactly the actual differential Dirac
restriction already defined geometrically. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDirac_eq_coefficientLinearEquiv
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode =
      (primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientLinearEquiv
        period hPeriod sector mode).toLinearMap := by
  rw [primitiveSpinCHopfLowEnergyComplexActualDirac_coefficient_conjugate]
  rfl

/-- Explicit inverse of the actual geometric low-energy Dirac restriction,
written by synthesis of the coefficient inverse. -/
def primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
    (sector : NormalRootChoice) (mode : Int) :
    PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode →ₗ[Real]
      PrimitiveSpinCHopfLowEnergyComplexSpan
        period hPeriod sector mode :=
  (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
      period hPeriod sector mode).toLinearMap.comp
    ((primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
        period sector mode).comp
      (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
        period hPeriod sector mode).symm.toLinearMap)

/-- Coordinate formula for the explicit actual inverse. -/
@[simp]
theorem primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_synthesisEquiv
    (sector : NormalRootChoice) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
          period hPeriod sector mode coefficients) =
      primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse
          period sector mode coefficients) := by
  simp [primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse]

/-- The explicit geometric inverse is a left inverse of the actual Dirac. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_left
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfLowEnergyComplexSpan
      period hPeriod sector mode) :
    primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexActualDirac
          period hPeriod sector mode state) =
      state := by
  rcases (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
    period hPeriod sector mode).surjective state with ⟨coefficients, rfl⟩
  rw [primitiveSpinCHopfLowEnergyComplexActualDirac_synthesisEquiv,
    primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_synthesisEquiv,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_left
      (hPeriod := hPeriod)]

/-- The explicit geometric inverse is a right inverse of the actual Dirac. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_right
    (sector : NormalRootChoice) (mode : Int)
    (state : PrimitiveSpinCHopfLowEnergyComplexSpan
      period hPeriod sector mode) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode
        (primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
          period hPeriod sector mode state) =
      state := by
  rcases (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesisEquiv
    period hPeriod sector mode).surjective state with ⟨coefficients, rfl⟩
  rw [primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_synthesisEquiv,
    primitiveSpinCHopfLowEnergyComplexActualDirac_synthesisEquiv,
    primitiveSpinCHopfLowEnergyComplexCoefficientOperatorInverse_right
      (hPeriod := hPeriod)]

/-- Consolidated exact inverse theorem for the actual low-energy geometric
Dirac restriction. -/
theorem primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientAutomorphism_closed
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfLowEnergyComplexActualDirac
        period hPeriod sector mode =
      (primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientLinearEquiv
        period hPeriod sector mode).toLinearMap ∧
      (∀ state,
        primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
            period hPeriod sector mode
            (primitiveSpinCHopfLowEnergyComplexActualDirac
              period hPeriod sector mode state) = state) ∧
      (∀ state,
        primitiveSpinCHopfLowEnergyComplexActualDirac
            period hPeriod sector mode
            (primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse
              period hPeriod sector mode state) = state) :=
  ⟨primitiveSpinCHopfLowEnergyComplexActualDirac_eq_coefficientLinearEquiv
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_left
      period hPeriod sector mode,
    primitiveSpinCHopfLowEnergyComplexActualDiracCoefficientInverse_right
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexActualDiracCoefficientAutomorphism4D
end JanusFormal
