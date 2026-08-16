import Mathlib.LinearAlgebra.TensorProduct.Tower
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmNamedCoordinate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorCollapseFormula4D

/-!
# Canonical complex coordinate of the full Fredholm--zeta determinant fibre

The named real Fredholm coordinate extends along `Real -> Complex`.  Composing
that scalar extension with the canonical reduced-factor collapse gives an
honest complex-linear coordinate

`FullDet(H_a) ≃ₗ[Complex] Complex`.

In this coordinate the full tensor section constructed from a reduced scalar
`z` has coordinate exactly `z`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFullComplexCoordinate4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmNamedCoordinate4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
open P0EFTJanusProgramPFullTensorCollapseFormula4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Complex scalar coordinate of the complexified finite Fredholm line. -/
def complexifiedDeterminantCoordinateEquiv
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.complexifiedDeterminantLine parameter ≃ₗ[Complex] Complex :=
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl Complex Complex)
      (data.determinantFrameCoordinateEquiv parameter)).trans
    (TensorProduct.AlgebraTensorModule.rid Real Complex Complex)

/-- The complexified named Fredholm frame is the unit vector. -/
@[simp]
theorem complexifiedDeterminantCoordinateEquiv_frame
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.complexifiedDeterminantCoordinateEquiv parameter
        (data.complexifiedDeterminantFrame parameter) = 1 := by
  simp [complexifiedDeterminantCoordinateEquiv,
    complexifiedDeterminantFrame,
    data.determinantFrameCoordinateEquiv_frame]

/-- Complexified Fredholm sections have their defining scalar as coordinate. -/
@[simp]
theorem complexifiedDeterminantCoordinateEquiv_section
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (coordinate : Complex) :
    data.complexifiedDeterminantCoordinateEquiv parameter
        (data.complexifiedDeterminantSection parameter coordinate) = coordinate := by
  simp [complexifiedDeterminantSection,
    data.complexifiedDeterminantCoordinateEquiv_frame]

/-- Canonical complex coordinate of the genuine full determinant fibre. -/
def fullTensorDeterminantCoordinateEquiv
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.fullTensorDeterminantLine parameter ≃ₗ[Complex] Complex :=
  (data.fullTensorDeterminantCollapse parameter).trans
    (data.complexifiedDeterminantCoordinateEquiv parameter)

/-- The full tensor section has exactly its reduced scalar as canonical complex
coordinate. -/
@[simp]
theorem fullTensorDeterminantCoordinateEquiv_section
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (coordinate : Complex) :
    data.fullTensorDeterminantCoordinateEquiv parameter
        (data.fullTensorDeterminantSection parameter coordinate) = coordinate := by
  rw [fullTensorDeterminantCoordinateEquiv]
  rw [fullTensorCollapse_formula]
  exact data.complexifiedDeterminantCoordinateEquiv_section parameter coordinate

/-- The inverse full coordinate is precisely the canonical full tensor section. -/
@[simp]
theorem fullTensorDeterminantCoordinateEquiv_symm_apply
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (coordinate : Complex) :
    (data.fullTensorDeterminantCoordinateEquiv parameter).symm coordinate =
      data.fullTensorDeterminantSection parameter coordinate := by
  apply (data.fullTensorDeterminantCoordinateEquiv parameter).injective
  simp

/-- Public full complex-coordinate checkpoint. -/
theorem self_adjoint_fredholm_full_complex_coordinate_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter coordinate,
      data.fullTensorDeterminantCoordinateEquiv parameter
          (data.fullTensorDeterminantSection parameter coordinate) = coordinate) ∧
    (∀ parameter coordinate,
      (data.fullTensorDeterminantCoordinateEquiv parameter).symm coordinate =
        data.fullTensorDeterminantSection parameter coordinate) :=
  ⟨data.fullTensorDeterminantCoordinateEquiv_section,
    data.fullTensorDeterminantCoordinateEquiv_symm_apply⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmFullComplexCoordinate4D
end JanusFormal
