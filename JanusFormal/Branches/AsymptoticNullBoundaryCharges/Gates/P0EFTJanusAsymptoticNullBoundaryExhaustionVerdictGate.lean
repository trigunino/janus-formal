import JanusFormal.Branches.AsymptoticNullBoundaryCharges.Gates.P0EFTJanusAsymptoticNullBoundaryAlphaBridgeGate

namespace JanusFormal
namespace P0EFTJanusAsymptoticNullBoundaryExhaustionVerdictGate

set_option autoImplicit false

structure AsymptoticNullBoundaryChargesExhaustionVerdictGate where
  bmsRouteAudited : Prop
  newmanPenroseRouteAudited : Prop
  covariantPhaseSpaceRouteAudited : Prop
  boundaryMassChargeDerived : Prop
  alphaGeneratedNoFit : Prop

def allAsymptoticNullRoutesAudited (g : AsymptoticNullBoundaryChargesExhaustionVerdictGate) : Prop :=
  g.bmsRouteAudited /\ g.newmanPenroseRouteAudited /\ g.covariantPhaseSpaceRouteAudited

def exhaustedStillBlocked (g : AsymptoticNullBoundaryChargesExhaustionVerdictGate) : Prop :=
  allAsymptoticNullRoutesAudited g /\
  Not g.boundaryMassChargeDerived /\
  Not g.alphaGeneratedNoFit

theorem exhausted_null_symmetry_branch_still_blocks_alpha
    (g : AsymptoticNullBoundaryChargesExhaustionVerdictGate)
    (h : exhaustedStillBlocked g) :
    Not g.alphaGeneratedNoFit := by
  exact h.right.right

end P0EFTJanusAsymptoticNullBoundaryExhaustionVerdictGate
end JanusFormal
