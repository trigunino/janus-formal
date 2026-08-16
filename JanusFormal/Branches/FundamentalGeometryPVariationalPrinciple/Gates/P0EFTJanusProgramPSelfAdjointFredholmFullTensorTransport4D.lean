import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorCollapseFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexFrameFlatness4D

/-!
# Canonical transport of the full Fredholm--zeta determinant fibre

The full determinant fibre is canonically equivalent to the complexified finite
Fredholm line because the reduced invertible determinant factor is the scalar
line.  Conjugating the complex-linear finite Fredholm transport by this collapse
constructs a genuine complex-linear transport between full determinant fibres.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFullTensorTransport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexLinearTransport4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexFrameFlatness4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
open P0EFTJanusProgramPFullTensorCollapseFormula4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Complex-linear transport between the genuine full determinant fibres. -/
def fullTensorDeterminantTransport
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.fullTensorDeterminantLine first ≃ₗ[Complex]
      data.fullTensorDeterminantLine second :=
  (data.fullTensorDeterminantCollapse first).trans
    ((data.complexLinearDeterminantTransport first second).trans
      (data.fullTensorDeterminantCollapse second).symm)

/-- Full transport preserves every fixed zeta coordinate in the canonical
Fredholm frame. -/
theorem fullTensorDeterminantTransport_section
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) (coordinate : Complex) :
    data.fullTensorDeterminantTransport first second
        (data.fullTensorDeterminantSection first coordinate) =
      data.fullTensorDeterminantSection second coordinate := by
  apply (data.fullTensorDeterminantCollapse second).injective
  simp [fullTensorDeterminantTransport,
    data.complexLinearDeterminantTransport_section,
    fullTensorCollapse_formula]

/-- Basepoint trivialization of the genuine full determinant family. -/
def fullTensorDeterminantBaseTrivialization
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.fullTensorDeterminantLine 0 ≃ₗ[Complex]
      data.fullTensorDeterminantLine parameter :=
  data.fullTensorDeterminantTransport 0 parameter

/-- The basepoint trivialization transports a fixed coordinate exactly. -/
theorem fullTensorDeterminantBaseTrivialization_section
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (coordinate : Complex) :
    data.fullTensorDeterminantBaseTrivialization parameter
        (data.fullTensorDeterminantSection 0 coordinate) =
      data.fullTensorDeterminantSection parameter coordinate :=
  data.fullTensorDeterminantTransport_section 0 parameter coordinate

/-- Public full determinant transport checkpoint. -/
theorem self_adjoint_fredholm_full_tensor_transport_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ first second coordinate,
      data.fullTensorDeterminantTransport first second
          (data.fullTensorDeterminantSection first coordinate) =
        data.fullTensorDeterminantSection second coordinate) ∧
    (∀ parameter coordinate,
      data.fullTensorDeterminantBaseTrivialization parameter
          (data.fullTensorDeterminantSection 0 coordinate) =
        data.fullTensorDeterminantSection parameter coordinate) :=
  ⟨data.fullTensorDeterminantTransport_section,
    data.fullTensorDeterminantBaseTrivialization_section⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmFullTensorTransport4D
end JanusFormal
