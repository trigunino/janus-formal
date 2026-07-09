namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveInputsToScaleFreeBAOChi2Gate

set_option autoImplicit false

structure ActiveInputsToScaleFreeBAOChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  requiredInputManifestsAvailable : Prop
  countertermRadialReductionReady : Prop
  atomicPreflightPassed : Prop
  backgroundScalarManifestWritten : Prop
  flrwComponentManifestWritten : Prop
  earlyPlasmaManifestWritten : Prop
  baoComponentManifestWritten : Prop
  scaleFreeBAOInputManifestWritten : Prop
  activeScaleFreeBAOInputValid : Prop
  scaleFreeBAOEvaluation : Prop
  baoChi2Evaluated : Prop
  gammaDragOverH0Available : Prop
  officialDimensionalBAOGateUnblocked : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def activeInputsToScaleFreeBAOChi2Closed
    (g : ActiveInputsToScaleFreeBAOChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.requiredInputManifestsAvailable /\
  g.countertermRadialReductionReady /\
  g.atomicPreflightPassed /\
  g.backgroundScalarManifestWritten /\
  g.flrwComponentManifestWritten /\
  g.earlyPlasmaManifestWritten /\
  g.baoComponentManifestWritten /\
  g.scaleFreeBAOInputManifestWritten /\
  g.activeScaleFreeBAOInputValid /\
  g.scaleFreeBAOEvaluation /\
  g.baoChi2Evaluated /\
  g.gammaDragOverH0Available /\
  Not g.officialDimensionalBAOGateUnblocked /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem active_inputs_scale_free_keeps_dimensional_official_bao_blocked
    (g : ActiveInputsToScaleFreeBAOChi2Gate)
    (hClosed : activeInputsToScaleFreeBAOChi2Closed g) :
    Not g.officialDimensionalBAOGateUnblocked := by
  rcases hClosed with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hDimensionalBlocked, _, _, _, _⟩
  exact hDimensionalBlocked

theorem active_inputs_scale_free_forbids_planck_z4_h0_fit
    (g : ActiveInputsToScaleFreeBAOChi2Gate)
    (hClosed : activeInputsToScaleFreeBAOChi2Closed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

theorem active_inputs_scale_free_requires_counterterm_reduction
    (g : ActiveInputsToScaleFreeBAOChi2Gate)
    (hClosed : activeInputsToScaleFreeBAOChi2Closed g) :
    g.countertermRadialReductionReady := by
  rcases hClosed with ⟨_, _, hCounterterm, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  exact hCounterterm

end P0EFTJanusZ2SigmaActiveInputsToScaleFreeBAOChi2Gate
end JanusFormal
