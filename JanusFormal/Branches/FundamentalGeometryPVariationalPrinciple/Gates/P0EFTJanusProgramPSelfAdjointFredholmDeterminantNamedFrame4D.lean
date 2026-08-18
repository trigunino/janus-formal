import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

/-!
# Named normalization of the self-adjoint Fredholm determinant frame

The self-adjoint equivalence `coker H ≃ ker H` lifts to an equivalence between
their top exterior powers.  Pulling the named kernel volume backwards defines a
canonical cokernel volume.  The canonical Fredholm frame then sends that source
volume exactly to the named kernel volume.

This fixes the real algebraic normalization of the finite-dimensional Fredholm
line before any complex zeta scalar is attached.
-/

namespace JanusFormal

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Exterior-power equivalence between actual cokernel and actual kernel. -/
def cokernelTopKernelTopEquiv
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.cokernelTop parameter ≃ₗ[Real] data.kernelTop parameter :=
  SelfAdjointFredholmDeterminantFamilyData.exteriorPowerEquiv
    (SelfAdjointFredholmDeterminantFamilyData.determinantDegree
      (ZeroMode := ZeroMode))
    (data.cokernelKernelEquiv parameter)

/-- Canonical source volume obtained by pulling the named kernel volume through
self-adjoint cokernel--kernel duality. -/
def cokernelNamedVolume
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) : data.cokernelTop parameter :=
  (cokernelTopKernelTopEquiv data parameter).symm
    (finiteKernelNamedVolume data.kernels parameter)

/-- The canonical Fredholm frame sends the named cokernel volume to the named
kernel volume. -/
theorem determinantFrame_cokernelNamedVolume
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.determinantFrame parameter (cokernelNamedVolume data parameter) =
      finiteKernelNamedVolume data.kernels parameter := by
  change
    cokernelTopKernelTopEquiv data parameter
        ((cokernelTopKernelTopEquiv data parameter).symm
          (finiteKernelNamedVolume data.kernels parameter)) =
      finiteKernelNamedVolume data.kernels parameter
  exact (cokernelTopKernelTopEquiv data parameter).apply_symm_apply _

/-- The named cokernel volume is nonzero. -/
theorem cokernelNamedVolume_ne_zero
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    cokernelNamedVolume data parameter ≠ 0 := by
  intro hZero
  have hMapped := congrArg (data.determinantFrame parameter) hZero
  rw [determinantFrame_cokernelNamedVolume data parameter, map_zero] at hMapped
  exact finiteKernelNamedVolume_ne_zero data.kernels parameter hMapped

/-- Public named normalization checkpoint. -/
theorem self_adjoint_fredholm_determinant_named_frame_gate
    (operator : Real → E →L[Real] E)
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter, cokernelNamedVolume data parameter ≠ 0) ∧
      (∀ parameter,
        data.determinantFrame parameter (cokernelNamedVolume data parameter) =
          finiteKernelNamedVolume data.kernels parameter) :=
  ⟨data.cokernelNamedVolume_ne_zero,
    data.determinantFrame_cokernelNamedVolume⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
