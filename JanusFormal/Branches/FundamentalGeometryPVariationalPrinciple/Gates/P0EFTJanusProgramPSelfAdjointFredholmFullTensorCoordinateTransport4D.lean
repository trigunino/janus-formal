import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullComplexCoordinate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorTransport4D

/-!
# Canonical-coordinate laws of full determinant transport

The full determinant transport preserves each canonical scalar section.  Since
every vector in the one-dimensional full fibre is uniquely reconstructed from
its canonical complex coordinate, this determines the whole transport and
makes its identity/composition laws immediate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFullTensorCoordinateTransport4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPSelfAdjointFredholmFullComplexCoordinate4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorTransport4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Transport preserves the canonical complex coordinate of every full-line
vector. -/
theorem fullTensorDeterminantTransport_coordinate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real)
    (value : data.fullTensorDeterminantLine first) :
    data.fullTensorDeterminantCoordinateEquiv second
        (data.fullTensorDeterminantTransport first second value) =
      data.fullTensorDeterminantCoordinateEquiv first value := by
  rw [← data.fullTensorDeterminantCoordinateEquiv_symm_apply first
    (data.fullTensorDeterminantCoordinateEquiv first value)]
  rw [data.fullTensorDeterminantTransport_section]
  simp

/-- Full determinant transport is the identity when source and target
parameters coincide. -/
@[simp]
theorem fullTensorDeterminantTransport_self
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.fullTensorDeterminantTransport parameter parameter =
      LinearEquiv.refl Complex _ := by
  ext value
  apply (data.fullTensorDeterminantCoordinateEquiv parameter).injective
  rw [data.fullTensorDeterminantTransport_coordinate]
  rfl

/-- Exact composition law of the genuine full determinant transports. -/
theorem fullTensorDeterminantTransport_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.fullTensorDeterminantTransport second third).comp
        (data.fullTensorDeterminantTransport first second) =
      data.fullTensorDeterminantTransport first third := by
  ext value
  apply (data.fullTensorDeterminantCoordinateEquiv third).injective
  simp only [LinearEquiv.comp_apply]
  rw [data.fullTensorDeterminantTransport_coordinate]
  rw [data.fullTensorDeterminantTransport_coordinate]
  rw [data.fullTensorDeterminantTransport_coordinate]

/-- Basepoint trivialization is coordinate-preserving on every vector, not only
on canonical zeta sections. -/
theorem fullTensorDeterminantBaseTrivialization_coordinate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real)
    (value : data.fullTensorDeterminantLine 0) :
    data.fullTensorDeterminantCoordinateEquiv parameter
        (data.fullTensorDeterminantBaseTrivialization parameter value) =
      data.fullTensorDeterminantCoordinateEquiv 0 value :=
  data.fullTensorDeterminantTransport_coordinate 0 parameter value

/-- Public coordinate-compatible full transport checkpoint. -/
theorem self_adjoint_fredholm_full_tensor_coordinate_transport_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ first second value,
      data.fullTensorDeterminantCoordinateEquiv second
          (data.fullTensorDeterminantTransport first second value) =
        data.fullTensorDeterminantCoordinateEquiv first value) ∧
    (∀ parameter,
      data.fullTensorDeterminantTransport parameter parameter =
        LinearEquiv.refl Complex _) ∧
    (∀ first second third,
      (data.fullTensorDeterminantTransport second third).comp
          (data.fullTensorDeterminantTransport first second) =
        data.fullTensorDeterminantTransport first third) :=
  ⟨data.fullTensorDeterminantTransport_coordinate,
    data.fullTensorDeterminantTransport_self,
    data.fullTensorDeterminantTransport_trans⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmFullTensorCoordinateTransport4D
end JanusFormal
