import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameTransport4D

/-!
# Preservation of the canonical Fredholm frame

The top-exterior naturality square makes both the named cokernel volume and the
canonical Fredholm Hom-frame invariant under the already defined family
transport.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmFramePreservation4D
end P0EFTJanusProgramPSelfAdjointFredholmFramePreservation4D

namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantNamedFrame4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantFrameTransport4D

variable {E : Type*} {ZeroMode : Type}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- Cokernel top transport preserves the named source volume. -/
theorem cokernelTopTransport_namedVolume
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.cokernelTopTransport first second (cokernelNamedVolume data first) =
      cokernelNamedVolume data second := by
  apply (cokernelTopKernelTopEquiv data second).injective
  rw [data.cokernelTopKernelTopEquiv_transport]
  have hNamed :
      cokernelTopKernelTopEquiv data first (cokernelNamedVolume data first) =
        finiteKernelNamedVolume data.kernels first :=
    (cokernelTopKernelTopEquiv data first).apply_symm_apply _
  rw [hNamed]
  have hTarget :
      cokernelTopKernelTopEquiv data second (cokernelNamedVolume data second) =
        finiteKernelNamedVolume data.kernels second :=
    (cokernelTopKernelTopEquiv data second).apply_symm_apply _
  rw [hTarget]
  change
    finiteKernelDeterminantTransport data.kernels first second
        (finiteKernelNamedVolume data.kernels first) =
      finiteKernelNamedVolume data.kernels second
  exact finiteKernelDeterminantTransport_namedVolume data.kernels first second

/-- The actual Fredholm Hom-line transport preserves its canonical frame. -/
theorem determinantTransport_frame
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.determinantTransport first second (data.determinantFrame first) =
      data.determinantFrame second := by
  apply LinearMap.ext
  intro value
  unfold determinantTransport
  rw [LinearEquiv.arrowCongr_apply]
  have h := data.cokernelTopKernelTopEquiv_transport first second
    ((data.cokernelTopTransport first second).symm value)
  change
    data.kernelTopTransport first second
        (cokernelTopKernelTopEquiv data first
          ((data.cokernelTopTransport first second).symm value)) =
      cokernelTopKernelTopEquiv data second value
  simpa using h.symm

/-- Public canonical-frame preservation checkpoint. -/
theorem self_adjoint_fredholm_frame_preservation_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ first second,
      data.determinantTransport first second (data.determinantFrame first) =
        data.determinantFrame second) ∧
      (∀ first second,
        data.cokernelTopTransport first second (cokernelNamedVolume data first) =
          cokernelNamedVolume data second) :=
  ⟨data.determinantTransport_frame, data.cokernelTopTransport_namedVolume⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
end JanusFormal
