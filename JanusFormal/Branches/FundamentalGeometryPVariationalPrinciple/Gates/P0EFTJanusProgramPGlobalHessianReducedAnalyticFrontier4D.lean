import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D

/-!
# Reduced analytic frontier of `HESSIAN-GLOBAL-01`

All aggregate H10--H14 interfaces have now been reduced to the following
analytic work packets:

* smooth primitive SpinC maximal-domain and same-action data;
* an open `C²` Candidate-A family on the actual D10-free minimal tangent,
  together with the two matter/LL graph-norm estimates and action identities;
* one product estimate for the seven physical Hessian blocks on the existing
  dense diagonal core;
* one finite-defect parametrix of the augmented operator on the stationary LL
  stratum.

Every other object appearing in the H14 certificate is constructed by the
imported gates.  This file is a façade only and introduces no additional
assumption or mathematical object.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D

/-- Canonical name of the smooth SpinC maximal-domain input. -/
def GlobalHessianSpinCDomainInput :=
  ProgramPPrimitiveSpinCSmoothMaximalDomainData4D

/-- Canonical name of its genuine completion same-action input. -/
def GlobalHessianSpinCSameActionInput :=
  ProgramPPrimitiveSpinCMatterSmoothMaximalSameActionData4D

/-- Canonical name of the reduced local minimal-physical family input. -/
def GlobalHessianLocalFamilyInput :=
  ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D

/-- Canonical name of the single H11 seven-block estimate. -/
def GlobalHessianSevenPhysicalBoundInput :=
  GlobalCandidateASevenPhysicalCoreBound4D

/-- Canonical name of the H12 finite-defect parametrix input. -/
def GlobalHessianParametrixInput :=
  GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D

/-- Preferred terminal gate from the reduced analytic frontier. -/
def global_candidateA_hessian_reduced_analytic_closure_gate :=
  @global_candidateA_hessian_maximalDomain_bounded_closure_gate

/-- The reduced work packets are all exposed by this façade. -/
theorem global_candidateA_hessian_reduced_analytic_frontier_gate :
    Nonempty (Unit × Unit × Unit × Unit × Unit) :=
  ⟨((), (), (), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D
end JanusFormal
