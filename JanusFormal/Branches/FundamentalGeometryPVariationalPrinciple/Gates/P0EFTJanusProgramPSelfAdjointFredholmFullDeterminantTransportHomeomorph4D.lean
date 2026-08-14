import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTopologicalBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorCoordinateTransport4D

/-!
# Topological transport of full determinant fibres

The algebraic full determinant transport preserves the canonical complex
coordinate exactly.  Therefore, for the transported fibre topologies, it is the
homeomorphism obtained by passing through `Complex` with the identity map.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTransportHomeomorph4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000
noncomputable section

open Topology
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTopologicalBundle4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorTransport4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCoordinateTransport4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Canonical homeomorphism between two full determinant fibres. -/
noncomputable def fullTensorDeterminantTransportHomeomorph
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.FullDeterminantFiber first ≃ₜ data.FullDeterminantFiber second :=
  (data.fullTensorDeterminantCoordinateHomeomorph first).trans
    (data.fullTensorDeterminantCoordinateHomeomorph second).symm

/-- The topological transport is exactly the existing complex-linear Fredholm
transport. -/
theorem fullTensorDeterminantTransportHomeomorph_apply
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real)
    (value : data.FullDeterminantFiber first) :
    data.fullTensorDeterminantTransportHomeomorph first second value =
      data.fullTensorDeterminantTransport first second value := by
  apply (data.fullTensorDeterminantCoordinateEquiv second).injective
  simp [fullTensorDeterminantTransportHomeomorph,
    data.fullTensorDeterminantTransport_coordinate]

/-- Topological transport preserves every canonical scalar section. -/
theorem fullTensorDeterminantTransportHomeomorph_section
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) (coordinate : Complex) :
    data.fullTensorDeterminantTransportHomeomorph first second
        (data.fullTensorDeterminantSection first coordinate) =
      data.fullTensorDeterminantSection second coordinate := by
  rw [data.fullTensorDeterminantTransportHomeomorph_apply]
  exact data.fullTensorDeterminantTransport_section first second coordinate

/-- The homeomorphic transports compose exactly. -/
theorem fullTensorDeterminantTransportHomeomorph_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.fullTensorDeterminantTransportHomeomorph first second).trans
        (data.fullTensorDeterminantTransportHomeomorph second third) =
      data.fullTensorDeterminantTransportHomeomorph first third := by
  ext value
  simp [fullTensorDeterminantTransportHomeomorph]

/-- Public topological transport checkpoint. -/
theorem self_adjoint_fredholm_full_determinant_transport_homeomorph_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ first second value,
      data.fullTensorDeterminantTransportHomeomorph first second value =
        data.fullTensorDeterminantTransport first second value) ∧
    (∀ first second third,
      (data.fullTensorDeterminantTransportHomeomorph first second).trans
          (data.fullTensorDeterminantTransportHomeomorph second third) =
        data.fullTensorDeterminantTransportHomeomorph first third) :=
  ⟨data.fullTensorDeterminantTransportHomeomorph_apply,
    data.fullTensorDeterminantTransportHomeomorph_trans⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTransportHomeomorph4D
end JanusFormal
