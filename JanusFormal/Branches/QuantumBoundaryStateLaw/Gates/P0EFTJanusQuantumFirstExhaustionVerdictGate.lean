import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstVerdictGate
import JanusFormal.Branches.QuantumBoundaryStateLaw.Gates.P0EFTJanusQuantumFirstBoundaryMassOperatorNoGoGate

namespace JanusFormal
namespace P0EFTJanusQuantumFirstExhaustionVerdictGate

set_option autoImplicit false

structure QuantumFirstExhaustionVerdictGate where
  cp1RouteExhausted : Prop
  tqftRouteExhausted : Prop
  prequantizationRouteExhausted : Prop
  boundaryMassOperatorDerived : Prop
  primitiveSectorLawDerived : Prop
  noFitAlphaGenerated : Prop

def allQuantumFirstRoutesAudited (g : QuantumFirstExhaustionVerdictGate) : Prop :=
  g.cp1RouteExhausted /\ g.tqftRouteExhausted /\ g.prequantizationRouteExhausted

def exhaustedStillBlocked (g : QuantumFirstExhaustionVerdictGate) : Prop :=
  allQuantumFirstRoutesAudited g /\
  Not g.boundaryMassOperatorDerived /\
  Not g.primitiveSectorLawDerived /\
  Not g.noFitAlphaGenerated

theorem exhausted_branch_still_does_not_generate_alpha
    (g : QuantumFirstExhaustionVerdictGate)
    (h : exhaustedStillBlocked g) :
    Not g.noFitAlphaGenerated := by
  exact h.right.right.right

end P0EFTJanusQuantumFirstExhaustionVerdictGate
end JanusFormal
