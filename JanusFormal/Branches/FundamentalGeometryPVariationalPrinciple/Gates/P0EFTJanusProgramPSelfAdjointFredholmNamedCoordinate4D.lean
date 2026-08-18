import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D

/-!
# Canonical scalar coordinate of the named Fredholm line

Every actual self-adjoint Fredholm determinant fibre is one-dimensional over
`Real`, and the physical kernel basis fixes a canonical nonzero Fredholm frame.
Therefore that frame determines an honest linear coordinate

`Det_Fred(H_a) ≃ₗ[Real] Real`.

This turns the earlier "frame" into a genuine trivialization coordinate rather
than merely a distinguished nonzero vector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmNamedCoordinate4D
end P0EFTJanusProgramPSelfAdjointFredholmNamedCoordinate4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- The canonical singleton basis of the actual real Fredholm line. -/
def determinantFrameBasis
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    Module.Basis Unit Real (data.determinantLine parameter) := by
  letI : FiniteDimensional Real (operator parameter).ker :=
    (data.gap parameter).kernel_finite
  letI : FiniteDimensional Real (data.cokernel parameter) :=
    FiniteDimensional.of_injective
      (data.cokernelKernelEquiv parameter).toLinearMap
      (data.cokernelKernelEquiv parameter).injective
  exact FiniteDimensional.basisSingleton Unit
    (data.determinantLine_finrank_one parameter)
    (data.determinantFrame parameter)
    (data.determinantFrame_ne_zero parameter)

/-- Coordinate equivalence in which the named Fredholm frame has coordinate
`1`. -/
def determinantFrameCoordinateEquiv
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.determinantLine parameter ≃ₗ[Real] Real :=
  (data.determinantFrameBasis parameter).repr.trans
    (Finsupp.uniqueLinearEquiv Real Real Unit.unit)

/-- The canonical Fredholm frame is the unit vector of its named coordinate. -/
@[simp]
theorem determinantFrameCoordinateEquiv_frame
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.determinantFrameCoordinateEquiv parameter
        (data.determinantFrame parameter) = 1 := by
  change (Finsupp.uniqueLinearEquiv Real Real Unit.unit)
      ((data.determinantFrameBasis parameter).repr
        (data.determinantFrame parameter)) = 1
  have hFrame :
      data.determinantFrameBasis parameter Unit.unit =
        data.determinantFrame parameter := by
    unfold determinantFrameBasis
    rw [FiniteDimensional.basisSingleton_apply]
  rw [← hFrame, Module.Basis.repr_self]
  simp

/-- Named coordinate reconstructs every real Fredholm-line vector exactly. -/
theorem determinantFrameCoordinateEquiv_symm_apply
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (coordinate : Real) :
    (data.determinantFrameCoordinateEquiv parameter).symm coordinate =
      coordinate • data.determinantFrame parameter := by
  apply (data.determinantFrameCoordinateEquiv parameter).injective
  simp [data.determinantFrameCoordinateEquiv_frame]

/-- Public canonical real Fredholm-coordinate checkpoint. -/
theorem self_adjoint_fredholm_named_coordinate_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter,
      data.determinantFrameCoordinateEquiv parameter
          (data.determinantFrame parameter) = 1) ∧
    (∀ parameter coordinate,
      (data.determinantFrameCoordinateEquiv parameter).symm coordinate =
        coordinate • data.determinantFrame parameter) :=
  ⟨data.determinantFrameCoordinateEquiv_frame,
    data.determinantFrameCoordinateEquiv_symm_apply⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
