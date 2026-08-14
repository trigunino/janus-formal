import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexLinearTransport4D

/-!
# Flatness of the finite Fredholm frame under canonical family transport

The finite kernel/cokernel factor already carries a canonical coordinate
transport.  Since that transport preserves the real Fredholm frame, its scalar
extension preserves the complexified frame and every fixed complex coordinate.

Thus in this canonical trivialization the finite Fredholm factor contributes no
additional connection coefficient; all spectral variation lives in the reduced
zeta factor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmComplexFrameFlatness4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmFramePreservation4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexLinearTransport4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

/-- The canonical complexified Fredholm frame is parallel for the
coordinate-preserving finite-dimensional transport. -/
theorem complexLinearDeterminantTransport_frame
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    data.complexLinearDeterminantTransport first second
        (data.complexifiedDeterminantFrame first) =
      data.complexifiedDeterminantFrame second := by
  unfold complexifiedDeterminantFrame
  rw [data.complexLinearDeterminantTransport_tmul]
  rw [data.determinantTransport_frame]

/-- A fixed complex coordinate in the canonical Fredholm frame is transported
without any extra scalar factor. -/
theorem complexLinearDeterminantTransport_section
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) (coordinate : Complex) :
    data.complexLinearDeterminantTransport first second
        (data.complexifiedDeterminantSection first coordinate) =
      data.complexifiedDeterminantSection second coordinate := by
  unfold complexifiedDeterminantSection
  rw [map_smul, data.complexLinearDeterminantTransport_frame]

/-- Public finite-factor flatness checkpoint. -/
theorem self_adjoint_fredholm_complex_frame_flatness_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ first second,
      data.complexLinearDeterminantTransport first second
          (data.complexifiedDeterminantFrame first) =
        data.complexifiedDeterminantFrame second) ∧
    (∀ first second coordinate,
      data.complexLinearDeterminantTransport first second
          (data.complexifiedDeterminantSection first coordinate) =
        data.complexifiedDeterminantSection second coordinate) :=
  ⟨data.complexLinearDeterminantTransport_frame,
    data.complexLinearDeterminantTransport_section⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmComplexFrameFlatness4D
end JanusFormal
