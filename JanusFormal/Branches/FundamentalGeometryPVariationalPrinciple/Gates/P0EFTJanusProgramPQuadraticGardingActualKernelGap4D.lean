import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Actual-kernel gap from any quadratic Gårding certificate

This generic bridge separates the H12 functional analysis from the particular
five-sector construction.  A quadratic/operator certificate on `(ker H)ᗮ`,
together with finite-dimensionality of the actual kernel, is exactly an
`SelfAdjointKernelComplementGapData` packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPQuadraticGardingActualKernelGap4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Finite actual kernel and a quadratic Gårding certificate on its orthogonal
complement. -/
structure QuadraticGardingActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  kernel_finite : FiniteDimensional Real operator.ker
  complementGarding : QuadraticGardingOperatorData
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)

namespace QuadraticGardingActualKernelGapData

/-- Established actual-kernel gap packet. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : QuadraticGardingActualKernelGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint where
  kernel_finite := data.kernel_finite
  gap := data.complementGarding.margin
  gap_pos := data.complementGarding.margin_pos
  lowerBound := data.complementGarding.lowerBound

/-- Public generic H12 gap checkpoint. -/
theorem quadratic_garding_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : QuadraticGardingActualKernelGapData operator hSelfAdjoint) :
    Nonempty (SelfAdjointKernelComplementGapData operator hSelfAdjoint) :=
  ⟨data.toGapData⟩

end QuadraticGardingActualKernelGapData

end
end P0EFTJanusProgramPQuadraticGardingActualKernelGap4D
end JanusFormal
