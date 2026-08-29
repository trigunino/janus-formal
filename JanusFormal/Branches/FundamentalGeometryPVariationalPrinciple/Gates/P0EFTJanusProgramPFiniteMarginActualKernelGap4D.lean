import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorCrossFormOperatorGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Actual-kernel gap from the finite Candidate-A coercive margin

The finite diagonal/cross/physical calculation is performed on the actual
orthogonal complement of the kernel.  Its operator lower bound is exactly the
remaining analytic field of `SelfAdjointKernelComplementGapData`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteMarginActualKernelGap4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorCrossFormOperatorGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorCrossFormPhysicalSmallness4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Finite actual kernel together with the explicit finite-margin estimate on
its true orthogonal complement. -/
structure FiniteMarginActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  kernel_finite : FiniteDimensional Real operator.ker
  complementGarding :
    CandidateAFiveSectorCrossFormOperatorGardingData
      (selfAdjointKernelComplementOperator operator hSelfAdjoint)

namespace FiniteMarginActualKernelGapData

/-- Convert the finite-margin proof directly to the established actual-kernel
gap packet. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : FiniteMarginActualKernelGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint where
  kernel_finite := data.kernel_finite
  gap := data.complementGarding.finiteMargin.margin
  gap_pos :=
    (CandidateAFiveSectorCrossFormPhysicalSmallnessData.candidateA_five_sector_cross_form_physical_smallness_gate
        data.complementGarding.finiteMargin).1
  lowerBound := data.complementGarding.lowerBound

/-- Public bridge from the finite sector calculation to H12's actual-kernel
gap, reduced Green and resolvent chain. -/
def finite_margin_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteMarginActualKernelGapData operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toGapData

end FiniteMarginActualKernelGapData

end
end P0EFTJanusProgramPFiniteMarginActualKernelGap4D
end JanusFormal
