namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveInputsToScaleFreePrimitiveChi2Gate

set_option autoImplicit false

structure ActiveInputsToScaleFreePrimitiveChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  backgroundInputManifestAvailable : Prop
  flrwInputManifestAvailable : Prop
  earlyPlasmaInputManifestAvailable : Prop
  countertermRadialReductionReady : Prop
  atomicPreflightPassed : Prop
  componentManifestWritten : Prop
  splitPrimitiveManifestsWritten : Prop
  canonicalPrimitiveManifestWritten : Prop
  scaleFreeBAOInputsWritten : Prop
  desiDR2Chi2Evaluated : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def activeInputsAvailable
    (g : ActiveInputsToScaleFreePrimitiveChi2Gate) : Prop :=
  g.backgroundInputManifestAvailable /\
  g.flrwInputManifestAvailable /\
  g.earlyPlasmaInputManifestAvailable /\
  g.countertermRadialReductionReady

def primitiveChainReady
    (g : ActiveInputsToScaleFreePrimitiveChi2Gate) : Prop :=
  g.componentManifestWritten /\
  g.splitPrimitiveManifestsWritten /\
  g.canonicalPrimitiveManifestWritten /\
  g.scaleFreeBAOInputsWritten

def observationPolicyClosed
    (g : ActiveInputsToScaleFreePrimitiveChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed

theorem atomic_preflight_requires_all_active_inputs
    (g : ActiveInputsToScaleFreePrimitiveChi2Gate)
    (_hPreflight : g.atomicPreflightPassed)
    (hImplies : g.atomicPreflightPassed -> activeInputsAvailable g) :
    activeInputsAvailable g := by
  exact hImplies _hPreflight

theorem chi2_requires_primitive_chain
    (g : ActiveInputsToScaleFreePrimitiveChi2Gate)
    (_hChi2 : g.desiDR2Chi2Evaluated)
    (hImplies : g.desiDR2Chi2Evaluated -> primitiveChainReady g) :
    primitiveChainReady g := by
  exact hImplies _hChi2

theorem policy_forbids_legacy_inputs
    (g : ActiveInputsToScaleFreePrimitiveChi2Gate)
    (hClosed : observationPolicyClosed g) :
    Not g.compressedPlanckLCDMUsed /\
    Not g.archivedZ4Used /\
    Not g.observationalH0FitUsed := by
  rcases hClosed with ⟨_, hNoPlanck, hNoZ4, hNoH0⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

theorem active_inputs_require_counterterm_reduction
    (g : ActiveInputsToScaleFreePrimitiveChi2Gate)
    (hInputs : activeInputsAvailable g) :
    g.countertermRadialReductionReady := by
  exact hInputs.2.2.2

end P0EFTJanusZ2SigmaActiveInputsToScaleFreePrimitiveChi2Gate
end JanusFormal
