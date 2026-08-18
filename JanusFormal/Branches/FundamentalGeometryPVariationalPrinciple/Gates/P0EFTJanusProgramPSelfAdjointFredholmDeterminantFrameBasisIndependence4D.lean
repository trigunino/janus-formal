import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D

/-!
# Basis independence of the self-adjoint Fredholm determinant frame

For an index-zero self-adjoint operator the determinant line is

`Hom(det coker H, det ker H)`.

The preferred frame is the top-exterior equivalence induced by the canonical
self-adjoint identification of cokernel with kernel.  It is therefore not tied
to one chosen kernel volume.

Given any top kernel vector `v`, use its inverse image through the canonical
`det coker ≃ det ker` equivalence as the matching cokernel vector.  The Fredholm
frame maps that matching cokernel vector exactly to `v`.

Consequently a simultaneous change of kernel basis and the corresponding
self-adjoint cokernel basis introduces no scalar in the `Hom` determinant
frame.  Named bases remain useful for transports and nonvanishing witnesses,
but they do not define a second determinant-line frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameBasisIndependence4D
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameBasisIndependence4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- The determinant frame is literally the canonical top-exterior
cokernel-to-kernel equivalence, evaluated on an arbitrary cokernel vector. -/
theorem determinantFrame_apply_canonical
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    ∀ cokernelVolume,
      data.determinantFrame parameter cokernelVolume =
        data.cokernelTopKernelTopEquiv parameter cokernelVolume := by
  intro cokernelVolume
  rfl

/-- Any chosen top kernel vector is reproduced exactly by the Fredholm frame
when the cokernel vector is chosen through the inverse canonical self-adjoint
identification. -/
theorem determinantFrame_matchingKernelVolume
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    ∀ kernelVolume,
      data.determinantFrame parameter
          ((data.cokernelTopKernelTopEquiv parameter).symm kernelVolume) =
        kernelVolume := by
  intro kernelVolume
  rw [data.determinantFrame_apply_canonical parameter]
  exact (data.cokernelTopKernelTopEquiv parameter).apply_symm_apply kernelVolume

/-- Equivalently, every cokernel vector is recovered from its frame image by
the inverse canonical equivalence. -/
theorem matchingCokernelVolume_determinantFrame
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    ∀ cokernelVolume,
      (data.cokernelTopKernelTopEquiv parameter).symm
          (data.determinantFrame parameter cokernelVolume) =
        cokernelVolume := by
  intro cokernelVolume
  rw [data.determinantFrame_apply_canonical parameter]
  exact (data.cokernelTopKernelTopEquiv parameter).symm_apply_apply cokernelVolume

/-- Public basis-independence checkpoint.  The statement quantifies over every
top kernel vector, so no named volume is privileged by the actual Fredholm
frame. -/
theorem self_adjoint_fredholm_determinant_frame_basis_independence_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    ∀ parameter kernelVolume,
      data.determinantFrame parameter
          ((data.cokernelTopKernelTopEquiv parameter).symm kernelVolume) =
        kernelVolume :=
  data.determinantFrame_matchingKernelVolume

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
