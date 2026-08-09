import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteMarginActualKernelGap4D

/-!
# Actual-kernel gap from one projected principal Hessian

This façade hides the intermediate ten cross forms.  Give finite-dimensionality
of the actual kernel and the projected-principal operator Gårding packet on its
orthogonal complement; the established H12 gap packet follows.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrincipalFiniteMarginActualKernelGap4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorAdapter4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorGarding4D
open P0EFTJanusProgramPFiniteMarginActualKernelGap4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Actual finite kernel and one projected-principal finite-margin certificate
on its orthogonal complement. -/
structure PrincipalFiniteMarginActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  kernel_finite : FiniteDimensional Real operator.ker
  principalGarding : CandidateAFiveSectorPrincipalOperatorGardingData
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)

namespace PrincipalFiniteMarginActualKernelGapData

/-- Convert to the first finite-margin actual-kernel packet. -/
def toFiniteMarginActualKernelGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : PrincipalFiniteMarginActualKernelGapData operator hSelfAdjoint) :
    FiniteMarginActualKernelGapData operator hSelfAdjoint where
  kernel_finite := data.kernel_finite
  complementGarding := data.principalGarding.toCrossFormOperatorGardingData

/-- Established actual-kernel gap. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : PrincipalFiniteMarginActualKernelGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toFiniteMarginActualKernelGapData.toGapData

/-- Public direct checkpoint. -/
theorem principal_finite_margin_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : PrincipalFiniteMarginActualKernelGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toGapData

end PrincipalFiniteMarginActualKernelGapData

end
end P0EFTJanusProgramPPrincipalFiniteMarginActualKernelGap4D
end JanusFormal
