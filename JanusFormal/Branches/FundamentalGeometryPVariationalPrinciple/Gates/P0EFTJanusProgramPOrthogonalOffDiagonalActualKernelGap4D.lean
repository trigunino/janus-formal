import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalOperatorGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPQuadraticGardingActualKernelGap4D

/-!
# Actual-kernel gap from one orthogonal decomposition and one off-diagonal form

This is the minimal generic finite-sector H12 packet developed on this branch:
finite actual kernel, one orthogonal coordinate decomposition of the complement,
five diagonal estimates, one canonical off-diagonal norm, and one physical
constant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOrthogonalOffDiagonalActualKernelGap4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalOperatorGarding4D
open P0EFTJanusProgramPQuadraticGardingActualKernelGap4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, NormedSpace Real (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Finite actual kernel and one-form sector control on the orthogonal
complement. -/
structure OrthogonalOffDiagonalActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  kernel_finite : FiniteDimensional Real operator.ker
  complementGarding :
    CandidateAFiveSectorOrthogonalOffDiagonalOperatorGardingData
      (Component := Component)
      (selfAdjointKernelComplementOperator operator hSelfAdjoint)

namespace OrthogonalOffDiagonalActualKernelGapData

/-- Generic quadratic actual-kernel packet. -/
def toQuadraticActualKernelGap
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : OrthogonalOffDiagonalActualKernelGapData
      (Component := Component) operator hSelfAdjoint) :
    QuadraticGardingActualKernelGapData operator hSelfAdjoint where
  kernel_finite := data.kernel_finite
  complementGarding := data.complementGarding.toQuadraticOperatorData Component

/-- Established actual-kernel gap. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : OrthogonalOffDiagonalActualKernelGapData
      (Component := Component) operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toQuadraticActualKernelGap Component |>.toGapData

/-- Public one-form actual-kernel checkpoint. -/
theorem orthogonal_offDiagonal_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : OrthogonalOffDiagonalActualKernelGapData
      (Component := Component) operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toGapData Component

end OrthogonalOffDiagonalActualKernelGapData

end
end P0EFTJanusProgramPOrthogonalOffDiagonalActualKernelGap4D
end JanusFormal
