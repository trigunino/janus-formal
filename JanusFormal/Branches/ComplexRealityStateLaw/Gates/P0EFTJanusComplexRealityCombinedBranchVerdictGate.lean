import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityCombinedKKSPeriodGate
import JanusFormal.Branches.ComplexRealityStateLaw.Gates.P0EFTJanusComplexRealityNoncentralSpinLiftSearchGate

namespace JanusFormal
namespace P0EFTJanusComplexRealityCombinedBranchVerdictGate

set_option autoImplicit false

structure CombinedBranchVerdictGate where
  mathematicalCandidateSurvives : Prop
  janusPhysicalDerivationClosed : Prop
  alphaGenerated : Prop
  globalSpinorProjectionClosed : Prop
  noncentralSpinLiftForced : Prop
  sectorSelectionDerived : Prop
  alphaMapDerived : Prop

def verdictClosed (g : CombinedBranchVerdictGate) : Prop :=
  g.mathematicalCandidateSurvives /\
  Not g.janusPhysicalDerivationClosed /\
  Not g.alphaGenerated /\
  Not g.globalSpinorProjectionClosed /\
  Not g.noncentralSpinLiftForced /\
  Not g.sectorSelectionDerived /\
  Not g.alphaMapDerived

theorem surviving_math_candidate_is_not_alpha_law
    (g : CombinedBranchVerdictGate)
    (h : verdictClosed g) :
    Not g.alphaGenerated := by
  exact h.right.right.left

end P0EFTJanusComplexRealityCombinedBranchVerdictGate
end JanusFormal
