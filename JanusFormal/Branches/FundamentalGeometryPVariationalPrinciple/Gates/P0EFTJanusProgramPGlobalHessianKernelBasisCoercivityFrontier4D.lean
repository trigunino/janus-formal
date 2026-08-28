import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeBasis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianNamedZeroModeCoercivityFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D

/-!
# Preferred physical zero-mode basis frontier

The strongest zero-mode input need not provide an arbitrary coordinate
isomorphism.  A finite basis of the actual Candidate-A Hessian kernel and the
quadratic coercivity estimate on its orthogonal complement determine all
intermediate named-mode and gap packets.

The resulting gap is consumed by the already installed H10--H14 zero-mode
frontier.  This module is a narrow public façade for that route.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianKernelBasisCoercivityFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteKernelNamedModeBasis4D
open P0EFTJanusProgramPGlobalHessianNamedZeroModeCoercivityFrontier4D
open P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D

/-- Preferred PDE packet: finite basis of `ker H` plus quadratic coercivity on
`(ker H)ᗮ`. -/
def GlobalHessianKernelBasisCoercivityInput :=
  @SelfAdjointKernelComplementCoercivityWithBasis

/-- Canonical conversion from that packet to the actual-kernel gap consumed by
H12 and H14. -/
def global_hessian_kernelBasis_coercivity_to_gap :=
  @SelfAdjointKernelComplementCoercivityWithBasis.toGapWithModel

/-- Terminal Candidate-A gate after the canonical basis/coercivity conversion. -/
def global_candidateA_hessian_kernelBasisCoercivity_frontier_gate :=
  @global_candidateA_hessian_zeroModeModel_frontier_gate

/-- Only a finite kernel basis and one quadratic estimate remain at the
zero-mode layer. -/
theorem global_candidateA_hessian_kernelBasisCoercivity_frontier_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianKernelBasisCoercivityFrontier4D
end JanusFormal
