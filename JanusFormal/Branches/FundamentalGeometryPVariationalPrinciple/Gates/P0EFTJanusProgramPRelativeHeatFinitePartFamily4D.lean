import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-!
# Differentiable families of finite-part relative determinants

A parameter-uniform short-time subtraction produces a real logarithmic
determinant at every parameter.  Once the derivative of that finite part is
identified, the positive determinant and its squared metric have automatic
variation formulas.

This is the real-magnitude component of the Quillen metric variation.  The
phase and complex connection are treated by the zeta family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatFinitePartFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-- One differentiable real family of finite-part heat renormalizations. -/
structure RelativeHeatFinitePartFamilyData where
  heatTrace : Real → HeatTime → Real
  finitePart : ∀ parameter, RelativeHeatFinitePartData (heatTrace parameter)
  logDerivative : Real → Real
  hasDerivAt_logDeterminant : ∀ parameter,
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant (finitePart current))
      (logDerivative parameter) parameter

/-- Positive determinant magnitude along the family. -/
def relativeHeatFinitePartDeterminantFamily
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) : Real :=
  relativeHeatFinitePartDeterminant (family.finitePart parameter)

/-- Derivative of the positive determinant. -/
def relativeHeatFinitePartDeterminantFamilyDerivative
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) : Real :=
  family.logDerivative parameter *
    relativeHeatFinitePartDeterminantFamily family parameter

/-- Chain rule for the positive determinant family. -/
theorem relativeHeatFinitePartDeterminantFamily_hasDerivAt
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) :
    HasDerivAt (relativeHeatFinitePartDeterminantFamily family)
      (relativeHeatFinitePartDeterminantFamilyDerivative family parameter)
      parameter := by
  change HasDerivAt
    (fun current => Real.exp
      (relativeHeatFinitePartLogDeterminant (family.finitePart current)))
    (relativeHeatFinitePartDeterminantFamilyDerivative family parameter)
    parameter
  refine (family.hasDerivAt_logDeterminant parameter).exp.congr_deriv ?_
  unfold relativeHeatFinitePartDeterminantFamilyDerivative
    relativeHeatFinitePartDeterminantFamily relativeHeatFinitePartDeterminant
  ring

/-- Squared determinant magnitude, the local Hermitian metric coefficient. -/
def relativeHeatFinitePartMetricWeight
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) : Real :=
  (relativeHeatFinitePartDeterminantFamily family parameter) ^ 2

/-- Variation of the metric coefficient. -/
def relativeHeatFinitePartMetricWeightDerivative
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) : Real :=
  2 * family.logDerivative parameter *
    relativeHeatFinitePartMetricWeight family parameter

/-- Differentiation of the squared determinant magnitude. -/
theorem relativeHeatFinitePartMetricWeight_hasDerivAt
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) :
    HasDerivAt (relativeHeatFinitePartMetricWeight family)
      (relativeHeatFinitePartMetricWeightDerivative family parameter)
      parameter := by
  have hDet :=
    relativeHeatFinitePartDeterminantFamily_hasDerivAt family parameter
  change HasDerivAt
    (fun current => relativeHeatFinitePartDeterminantFamily family current ^ 2)
    (relativeHeatFinitePartMetricWeightDerivative family parameter) parameter
  refine (hDet.pow 2).congr_deriv ?_
  unfold relativeHeatFinitePartMetricWeightDerivative
    relativeHeatFinitePartDeterminantFamilyDerivative
    relativeHeatFinitePartMetricWeight
  ring

/-- Every determinant magnitude is positive. -/
theorem relativeHeatFinitePartDeterminantFamily_pos
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) :
    0 < relativeHeatFinitePartDeterminantFamily family parameter :=
  relativeHeatFinitePartDeterminant_pos (family.finitePart parameter)

/-- Every metric weight is strictly positive. -/
theorem relativeHeatFinitePartMetricWeight_pos
    (family : RelativeHeatFinitePartFamilyData)
    (parameter : Real) :
    0 < relativeHeatFinitePartMetricWeight family parameter := by
  exact sq_pos_of_pos
    (relativeHeatFinitePartDeterminantFamily_pos family parameter)

/-- Public finite-part family checkpoint. -/
theorem relative_heat_finite_part_family_gate
    (family : RelativeHeatFinitePartFamilyData) :
    (∀ parameter,
      HasDerivAt (relativeHeatFinitePartDeterminantFamily family)
        (relativeHeatFinitePartDeterminantFamilyDerivative family parameter)
        parameter) ∧
      (∀ parameter,
        HasDerivAt (relativeHeatFinitePartMetricWeight family)
          (relativeHeatFinitePartMetricWeightDerivative family parameter)
          parameter) ∧
      (∀ parameter,
        0 < relativeHeatFinitePartMetricWeight family parameter) :=
  ⟨relativeHeatFinitePartDeterminantFamily_hasDerivAt family,
    relativeHeatFinitePartMetricWeight_hasDerivAt family,
    relativeHeatFinitePartMetricWeight_pos family⟩

end
end P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
end JanusFormal
