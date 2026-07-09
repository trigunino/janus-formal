import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4GRBaselineReductionGate

namespace JanusFormal
namespace P0EFTJanusZ4ControlledDeviationGate

set_option autoImplicit false

structure ControlledDeviationGate where
  cambGRSafeBaselineUsed : Prop
  channelDeltasTagged : Prop
  sourceLevelDeltaRequiredForPhysics : Prop
  spectrumLevelDeltaDebugOnly : Prop
  rawNativeLOSUsedForPlanck : Prop
  lambdaZeroIdentityPassed : Prop
  continuityPassed : Prop
  officialPlanckAllowedForDeltaBackend : Prop

def deltaBackendSafe (g : ControlledDeviationGate) : Prop :=
  g.cambGRSafeBaselineUsed /\
  g.channelDeltasTagged /\
  g.lambdaZeroIdentityPassed /\
  g.continuityPassed /\
  Not g.rawNativeLOSUsedForPlanck

theorem safe_delta_backend_allows_planck_gate
    (g : ControlledDeviationGate)
    (hPolicy : deltaBackendSafe g -> g.officialPlanckAllowedForDeltaBackend)
    (h : deltaBackendSafe g) :
    g.officialPlanckAllowedForDeltaBackend := by
  exact hPolicy h

theorem raw_native_los_blocks_planck_delta_backend
    (g : ControlledDeviationGate)
    (hPolicy : g.officialPlanckAllowedForDeltaBackend -> Not g.rawNativeLOSUsedForPlanck)
    (hRaw : g.rawNativeLOSUsedForPlanck) :
    Not g.officialPlanckAllowedForDeltaBackend := by
  intro h
  exact (hPolicy h) hRaw

theorem source_level_required_for_physical_delta
    (g : ControlledDeviationGate)
    (h : g.sourceLevelDeltaRequiredForPhysics) :
    g.sourceLevelDeltaRequiredForPhysics := by
  exact h

end P0EFTJanusZ4ControlledDeviationGate
end JanusFormal
