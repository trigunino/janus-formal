import Mathlib.LinearAlgebra.TensorProduct.Map
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexification4D

/-!
# Parameter transport of the actual complexified Fredholm line

The real Fredholm determinant fibres already carry genuine linear equivalences
between parameters.  Scalar extension along `Real -> Complex` transports those
equivalences to the complexified determinant fibres without introducing a new
choice of frame or a second family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmComplexTransport4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Scalar extension of the actual Fredholm-fibre transport. -/
def complexifiedDeterminantTransport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.complexifiedDeterminantLine first ≃ₗ[Real]
      data.complexifiedDeterminantLine second :=
  LinearEquiv.lTensor Complex (data.determinantTransport first second)

/-- On pure tensors, complexified transport acts only on the actual Fredholm
factor. -/
@[simp]
theorem complexifiedDeterminantTransport_tmul
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) (coordinate : Complex)
    (value : data.determinantLine first) :
    data.complexifiedDeterminantTransport first second
        (TensorProduct.tmul Real coordinate value) =
      TensorProduct.tmul Real coordinate
        (data.determinantTransport first second value) := by
  simp [complexifiedDeterminantTransport]

/-- Every scalar-extended Fredholm transport is bijective. -/
theorem complexifiedDeterminantTransport_bijective
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    Function.Bijective (data.complexifiedDeterminantTransport first second) :=
  (data.complexifiedDeterminantTransport first second).bijective

/-- Basepoint transport gives a genuine trivialization of each complexified
Fredholm fibre as a real vector space. -/
def complexifiedDeterminantBaseTrivialization
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.complexifiedDeterminantLine 0 ≃ₗ[Real]
      data.complexifiedDeterminantLine parameter :=
  data.complexifiedDeterminantTransport 0 parameter

/-- Public scalar-extension transport checkpoint. -/
theorem self_adjoint_fredholm_complex_transport_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    ∀ first second,
      Function.Bijective (data.complexifiedDeterminantTransport first second) :=
  data.complexifiedDeterminantTransport_bijective

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmComplexTransport4D
end JanusFormal
