import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CompleteGRLimitShapeGate

namespace JanusFormal
namespace P0EFTJanusZ4SolverInputManifestGate

set_option autoImplicit false

structure SolverInputManifestGate where
  hiddenDefaultInputs : Prop
  fixedCsvTheory : Prop
  globalLSChannelCalibration : Prop
  z4InitialModeUnspecified : Prop
  projectionUnspecified : Prop
  minusMicrophysicsUnspecified : Prop
  clOrCphiConventionUnknown : Prop
  solverInputManifestPassed : Prop
  z4ObservedPlanckInterpretationAllowed : Prop
  candidatePromotionAllowed : Prop
  fullPlanckValidation : Prop

def blockedByManifest (g : SolverInputManifestGate) : Prop :=
  (g.hiddenDefaultInputs \/
    g.fixedCsvTheory \/
    g.globalLSChannelCalibration \/
    g.z4InitialModeUnspecified \/
    g.projectionUnspecified \/
    g.minusMicrophysicsUnspecified \/
    g.clOrCphiConventionUnknown) /\
  Not g.solverInputManifestPassed /\
  Not g.z4ObservedPlanckInterpretationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.fullPlanckValidation

theorem manifest_blocker_forbids_planck_interpretation
    (g : SolverInputManifestGate)
    (h : blockedByManifest g) :
    Not g.z4ObservedPlanckInterpretationAllowed /\ Not g.fullPlanckValidation := by
  rcases h with âŸ¨_, _, hInterpret, _, hFullâŸ©
  exact âŸ¨hInterpret, hFullâŸ©

end P0EFTJanusZ4SolverInputManifestGate
end JanusFormal
