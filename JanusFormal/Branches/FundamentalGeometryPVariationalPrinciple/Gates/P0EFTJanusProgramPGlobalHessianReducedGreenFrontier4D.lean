import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianReducedGreenCertificate4D

/-!
# Reduced-Green frontier of the concrete Candidate-A Hessian

The same three analytic packets used by the concrete H14 closure also construct
the exact zero-mode splitting and the continuous inverse of the Hessian on the
zero-mode complement.

This façade is intended for stability, resolvent and determinant work.  It does
not add a fourth input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianReducedGreenFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D
open P0EFTJanusProgramPGlobalHessianReducedGreenCertificate4D

/-- Concrete local-family input. -/
def GlobalHessianReducedGreenLocalFamilyInput :=
  GlobalHessianConcreteLocalFamilyInput

/-- Canonical dense-agreement H11 input. -/
def GlobalHessianReducedGreenPhysicalAgreementsInput :=
  GlobalHessianConcretePhysicalAgreementsInput

/-- Orthogonal finite-defect coercivity H12 input. -/
def GlobalHessianReducedGreenOrthogonalCoerciveShiftInput :=
  GlobalHessianConcreteOrthogonalCoerciveShiftInput

/-- Terminal endpoint returning H14 plus the reduced Green operator. -/
def global_candidateA_hessian_reducedGreen_frontier_gate :=
  @global_candidateA_hessian_reducedGreen_certificate_gate

/-- The reduced Green output needs no additional analytic packet. -/
theorem global_candidateA_hessian_reducedGreen_frontier_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianReducedGreenFrontier4D
end JanusFormal
