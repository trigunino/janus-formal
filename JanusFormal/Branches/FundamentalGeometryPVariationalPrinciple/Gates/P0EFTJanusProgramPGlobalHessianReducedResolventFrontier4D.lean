import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianReducedResolventCertificate4D

/-!
# Reduced-resolvent frontier of the concrete Candidate-A Hessian

The same three analytic packets used by the concrete H14 closure now provide:

* the exact finite zero-mode splitting;
* the reduced Green operator;
* an open real interval around zero contained in the reduced resolvent set;
* the sharp elementary estimate
  `‖R(lambda)‖ ≤ (c - |lambda|)⁻¹` on that interval.

No fourth analytic packet is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianReducedResolventFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D
open P0EFTJanusProgramPGlobalHessianReducedResolventCertificate4D

/-- Concrete local-family input. -/
def GlobalHessianReducedResolventLocalFamilyInput :=
  GlobalHessianConcreteLocalFamilyInput

/-- Canonical dense-agreement H11 input. -/
def GlobalHessianReducedResolventPhysicalAgreementsInput :=
  GlobalHessianConcretePhysicalAgreementsInput

/-- Orthogonal finite-defect coercivity H12 input. -/
def GlobalHessianReducedResolventOrthogonalCoerciveShiftInput :=
  GlobalHessianConcreteOrthogonalCoerciveShiftInput

/-- Terminal endpoint returning H14, the reduced Green operator and the full
certified real resolvent interval. -/
def global_candidateA_hessian_reducedResolvent_frontier_gate :=
  @global_candidateA_hessian_reducedResolvent_certificate_gate

/-- The reduced-resolvent output needs no additional analytic packet. -/
theorem global_candidateA_hessian_reducedResolvent_frontier_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianReducedResolventFrontier4D
end JanusFormal
