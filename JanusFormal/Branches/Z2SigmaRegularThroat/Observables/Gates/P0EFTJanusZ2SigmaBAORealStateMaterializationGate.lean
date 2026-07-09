import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaPhysicalInputsToScaleFreeBAOChi2Gate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAORealStateMaterializationGate

set_option autoImplicit false

structure BAORealStateMaterializationGate where
  activeCoreZ2Sigma : Prop
  physicalInputsGatePassed : Prop
  baoChi2Evaluated : Prop
  realActiveInputsMissing : Prop
  fixtureResultIsNotPhysicalResult : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4Forbidden : Prop
  observationalH0FitForbidden : Prop
  observationalCurvatureFitForbidden : Prop
  gatePassed : Prop

def ready (g : BAORealStateMaterializationGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.physicalInputsGatePassed /\
  g.baoChi2Evaluated /\
  Not g.realActiveInputsMissing /\
  Not g.fixtureResultIsNotPhysicalResult /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4Forbidden /\
  g.observationalH0FitForbidden /\
  g.observationalCurvatureFitForbidden

theorem ready_requires_real_active_inputs
    (g : BAORealStateMaterializationGate)
    (h : ready g) :
    Not g.realActiveInputsMissing := by
  exact h.2.2.2.1

theorem fixture_result_cannot_promote_real_state
    (g : BAORealStateMaterializationGate)
    (_hFixture : g.fixtureResultIsNotPhysicalResult) :
    Not (ready g) := by
  intro h
  exact h.2.2.2.2.1 _hFixture

end P0EFTJanusZ2SigmaBAORealStateMaterializationGate
end JanusFormal
