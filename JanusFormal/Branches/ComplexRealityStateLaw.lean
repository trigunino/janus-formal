/- Branch head: complex-reality state-law program. -/

import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealitySourceFormulaCurationGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityEq131KKSProjectionGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCoadjointStateSpaceGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityKKSBoundaryDensityGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealitySigmaBoundaryProjectionGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityBoundaryVariationBasisGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityClosedBoundaryTwoCycleGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityActiveEmbeddingOrCompactPhaseGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityTwoExitEvaluationGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCandidateBoundaryPhaseSpaceGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCandidatePhaseSpaceMatrixGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityQuantumCandidateWorkbenchGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCombinedPhaseSpaceCandidateGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCP1FromJanusPTGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityAroundSigmaCP1HolonomyActionGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCombinedKKSPeriodGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityNoncentralSpinLiftSearchGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCombinedBranchVerdictGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityPrequantizationIntegralityGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityAlphaStateLawVerdictGate

namespace JanusFormal
namespace Branches
namespace ComplexRealityStateLaw

set_option autoImplicit false

structure BranchStatus where
  sourceFormulaCurationReady : Prop
  eq131KKSProjectionReady : Prop
  coadjointStateSpaceReady : Prop
  globalKKSOrbitNonzero : Prop
  sigmaBoundaryProjectionSymbolicReady : Prop
  sigmaBoundaryProjectionActiveReady : Prop
  boundaryVariationBasisSymbolicReady : Prop
  boundaryVariationBasisActiveReady : Prop
  topologicalCycleAuditReady : Prop
  kksBoundaryTwoCycleReady : Prop
  activeEmbeddingOrCompactPhaseRouteReady : Prop
  kksBoundaryDensityReady : Prop
  alphaGenerated : Prop

def complexRealityBranchFormalized (s : BranchStatus) : Prop :=
  s.sourceFormulaCurationReady /\
  s.eq131KKSProjectionReady /\
  s.coadjointStateSpaceReady /\
  s.globalKKSOrbitNonzero /\
  s.sigmaBoundaryProjectionSymbolicReady /\
  s.boundaryVariationBasisSymbolicReady /\
  s.topologicalCycleAuditReady /\
  Not s.sigmaBoundaryProjectionActiveReady /\
  Not s.boundaryVariationBasisActiveReady /\
  Not s.kksBoundaryTwoCycleReady /\
  Not s.activeEmbeddingOrCompactPhaseRouteReady /\
  Not s.kksBoundaryDensityReady /\
  Not s.alphaGenerated

theorem formalized_branch_still_does_not_predict_alpha
    (s : BranchStatus)
    (h : complexRealityBranchFormalized s) :
    Not s.alphaGenerated := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hNoAlpha⟩
  exact hNoAlpha

end ComplexRealityStateLaw
end Branches
end JanusFormal
