import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameBasisIndependence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorCollapseFormula4D

/-!
# Basis independence of the full self-adjoint Fredholm--zeta tensor line

The full determinant line uses the canonical Fredholm `Hom` frame and one
reduced complex coordinate.  Since the Fredholm frame is the self-adjoint
`det coker ≃ det ker` equivalence itself, simultaneous changes of matching
kernel/cokernel volumes cancel before the reduced zeta factor is introduced.

This file records that cancellation and the resulting interpretation of the
full tensor coordinate: all nontrivial scalar dependence of a full section
`fullTensorDeterminantSection a z` is the reduced coordinate `z`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFullTensorBasisIndependence4D
end P0EFTJanusProgramPSelfAdjointFredholmFullTensorBasisIndependence4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameBasisIndependence4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorCollapse4D
open P0EFTJanusProgramPFullTensorCollapseFormula4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Simultaneously scaling a kernel top vector and its canonically matching
cokernel vector is invisible to the choice of Fredholm frame: the frame simply
reproduces the scaled kernel vector. -/
theorem determinantFrame_matchingKernelVolume_smul
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (scalar : Real) :
    ∀ kernelVolume,
      data.determinantFrame parameter
          (scalar •
            (data.cokernelTopKernelTopEquiv parameter).symm kernelVolume) =
        scalar • kernelVolume := by
  intro kernelVolume
  rw [map_smul]
  rw [data.determinantFrame_matchingKernelVolume parameter]

/-- The complexified canonical frame remains `1 tensor determinantFrame`; no
kernel-volume normalization appears in its definition. -/
theorem complexifiedDeterminantFrame_is_canonical
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.complexifiedDeterminantFrame parameter =
      TensorProduct.tmul Real (1 : Complex) (data.determinantFrame parameter) :=
  rfl

/-- The full tensor section collapses to exactly its reduced complex coordinate
multiplying the canonical Fredholm frame.  This formula contains no named
kernel-volume factor. -/
theorem fullTensorSection_coordinate_only
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) (coordinate : Complex) :
    data.fullTensorDeterminantCollapse parameter
        (data.fullTensorDeterminantSection parameter coordinate) =
      coordinate • data.complexifiedDeterminantFrame parameter :=
  data.fullTensorCollapse_formula parameter coordinate

/-- Public full-tensor basis-independence checkpoint. -/
theorem self_adjoint_fredholm_full_tensor_basis_independence_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter kernelVolume,
      data.determinantFrame parameter
          ((data.cokernelTopKernelTopEquiv parameter).symm kernelVolume) =
        kernelVolume) ∧
    (∀ parameter coordinate,
      data.fullTensorDeterminantCollapse parameter
          (data.fullTensorDeterminantSection parameter coordinate) =
        coordinate • data.complexifiedDeterminantFrame parameter) :=
  ⟨data.determinantFrame_matchingKernelVolume,
    data.fullTensorSection_coordinate_only⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
