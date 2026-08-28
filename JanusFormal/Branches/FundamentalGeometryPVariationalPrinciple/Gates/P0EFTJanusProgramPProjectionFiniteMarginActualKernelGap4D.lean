import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorProjectionOperatorGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrincipalFiniteMarginActualKernelGap4D

/-!
# Actual-kernel gap from a positive five-sector projection resolution

The Pythagorean identity is generated from the projection resolution, then the
projected principal and physical margins give the norm lower bound on the true
kernel complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProjectionFiniteMarginActualKernelGap4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorProjectionOperatorGarding4D
open P0EFTJanusProgramPPrincipalFiniteMarginActualKernelGap4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Finite actual kernel and positive projected-sector control of its true
orthogonal complement. -/
structure ProjectionFiniteMarginActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  kernel_finite : FiniteDimensional Real operator.ker
  projectionGarding : CandidateAFiveSectorProjectionOperatorGardingData
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)

namespace ProjectionFiniteMarginActualKernelGapData

/-- Established projected-principal actual-kernel packet. -/
def toPrincipalFiniteMarginActualKernelGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : ProjectionFiniteMarginActualKernelGapData operator hSelfAdjoint) :
    PrincipalFiniteMarginActualKernelGapData operator hSelfAdjoint where
  kernel_finite := data.kernel_finite
  principalGarding := data.projectionGarding.toPrincipalOperatorGardingData

/-- Established H12 actual-kernel gap. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : ProjectionFiniteMarginActualKernelGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toPrincipalFiniteMarginActualKernelGapData.toGapData

/-- Public direct checkpoint. -/
def projection_finite_margin_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : ProjectionFiniteMarginActualKernelGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toGapData

end ProjectionFiniteMarginActualKernelGapData

end
end P0EFTJanusProgramPProjectionFiniteMarginActualKernelGap4D
end JanusFormal
