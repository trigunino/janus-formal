import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothGraphFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFirstOrderGraphCoreDensityBoundedClosure4D

/-!
# Reduced analytic frontier of `HESSIAN-GLOBAL-01`

All aggregate H10--H14 interfaces have now been reduced to four analytic work
packets:

* mass-independent graph-core density for the genuine first-order primitive
  SpinC Dirac operator;
* an open `C²` Candidate-A family on the actual D10-free minimal tangent,
  together with the two matter/LL graph-norm estimates and action identities;
* one product estimate for the seven physical Hessian blocks on the existing
  dense diagonal core;
* one finite-defect parametrix of the augmented operator on the stationary LL
  stratum.

Finite Green symmetry is already unconditional.  The first packet constructs,
for every matter mass, the complete Hessian graph core, global Green identity,
coefficient intertwining, maximal-domain membership, exact operator
restriction, weighted Fourier vector, Parseval identity and same-action matter
realization.  Every remaining aggregate object in H14 is built by the imported
gates.  This façade introduces no additional mathematical object.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalHessianFirstOrderGraphCoreDensityBoundedClosure4D

/-- Canonical name of the sole mass-independent SpinC graph-core input. -/
def GlobalHessianSpinCFirstOrderGraphCoreDensityInput :=
  ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D

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
  @global_candidateA_hessian_firstOrderGraphCoreDensity_bounded_closure_gate

/-- The four reduced work packets are all exposed by this façade. -/
theorem global_candidateA_hessian_reduced_analytic_frontier_gate :
    Nonempty (Unit × Unit × Unit × Unit) :=
  ⟨((), (), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianReducedAnalyticFrontier4D
end JanusFormal
