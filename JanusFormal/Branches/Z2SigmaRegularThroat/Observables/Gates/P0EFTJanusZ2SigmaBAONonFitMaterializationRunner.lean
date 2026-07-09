import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaBAORealStateMaterializationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAONonFitMaterializationRunner

set_option autoImplicit false

structure BAONonFitMaterializationRunner where
  activeCoreZ2Sigma : Prop
  materializationStepsRan : Prop
  realStateGateRan : Prop
  baoChi2Evaluated : Prop
  realStateGatePassed : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4Forbidden : Prop
  observationalH0FitForbidden : Prop
  observationalCurvatureFitForbidden : Prop

def ready (r : BAONonFitMaterializationRunner) : Prop :=
  r.activeCoreZ2Sigma /\
  r.materializationStepsRan /\
  r.realStateGateRan /\
  r.baoChi2Evaluated /\
  r.realStateGatePassed /\
  r.compressedPlanckLCDMForbidden /\
  r.archivedZ4Forbidden /\
  r.observationalH0FitForbidden /\
  r.observationalCurvatureFitForbidden

theorem ready_requires_real_state_gate_passed
    (r : BAONonFitMaterializationRunner)
    (h : ready r) :
    r.realStateGatePassed := by
  exact h.2.2.2.2.1

theorem ready_forbids_compressed_inputs
    (r : BAONonFitMaterializationRunner)
    (h : ready r) :
    r.compressedPlanckLCDMForbidden /\ r.archivedZ4Forbidden := by
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

end P0EFTJanusZ2SigmaBAONonFitMaterializationRunner
end JanusFormal
