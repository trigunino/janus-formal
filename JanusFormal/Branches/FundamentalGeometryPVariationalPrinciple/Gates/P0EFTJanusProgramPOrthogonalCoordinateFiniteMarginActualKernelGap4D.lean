import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOperatorGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointProjectionFiniteMarginActualKernelGap4D

/-!
# Actual-kernel gap from one orthogonal sector decomposition

A finite actual kernel and an orthogonal-coordinate lower bound on its
orthogonal complement form the H12 gap packet.  The five sector projectors are
generated internally from the coordinate equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOrthogonalCoordinateFiniteMarginActualKernelGap4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 2500000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOperatorGarding4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointProjectionFiniteMarginActualKernelGap4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, NormedSpace Real (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Finite actual kernel and orthogonal-coordinate control on its complement. -/
structure OrthogonalCoordinateFiniteMarginActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  kernel_finite : FiniteDimensional Real operator.ker
  orthogonalGarding : CandidateAFiveSectorOrthogonalOperatorGardingData
    (Component := Component)
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)

namespace OrthogonalCoordinateFiniteMarginActualKernelGapData

/-- Generate the previous self-adjoint-projection gap packet. -/
def toSelfAdjointProjectionGap
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : OrthogonalCoordinateFiniteMarginActualKernelGapData
      (Component := Component) operator hSelfAdjoint) :
    SelfAdjointProjectionFiniteMarginActualKernelGapData
      operator hSelfAdjoint where
  kernel_finite := data.kernel_finite
  projectionGarding :=
    data.orthogonalGarding.toSelfAdjointOperatorGarding Component

/-- Established actual-kernel gap. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : OrthogonalCoordinateFiniteMarginActualKernelGapData
      (Component := Component) operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toSelfAdjointProjectionGap Component |>.toGapData

/-- Public orthogonal-coordinate actual-kernel checkpoint. -/
theorem orthogonal_coordinate_finite_margin_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : OrthogonalCoordinateFiniteMarginActualKernelGapData
      (Component := Component) operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toGapData Component

end OrthogonalCoordinateFiniteMarginActualKernelGapData

end
end P0EFTJanusProgramPOrthogonalCoordinateFiniteMarginActualKernelGap4D
end JanusFormal
