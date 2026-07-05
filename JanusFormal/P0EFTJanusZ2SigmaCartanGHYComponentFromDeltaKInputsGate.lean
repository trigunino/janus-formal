namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYComponentFromDeltaKInputsGate

set_option autoImplicit false

structure CartanGHYComponentFromDeltaKInputsGate where
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  aGridDeclared : Prop
  deltaKsOfAReady : Prop
  deltaKtauOfAReady : Prop
  z2OrientationSignDeclared : Prop
  activeKappaRhoCrit0Ready : Prop
  deltaKProvenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  deltaKInputWriterFrontierDeclared : Prop
  backgroundScalarFrontierDeclared : Prop
  nearestCartanComponentFrontierDeclared : Prop
  nearestCartanComponentFrontierDiagnosticOnly : Prop
  cartanGHYComponentOutputWritten : Prop

def canWriteCartanGHYComponents
    (g : CartanGHYComponentFromDeltaKInputsGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.aGridDeclared /\
  g.deltaKsOfAReady /\
  g.deltaKtauOfAReady /\
  g.z2OrientationSignDeclared /\
  g.activeKappaRhoCrit0Ready /\
  g.deltaKProvenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.deltaKInputWriterFrontierDeclared /\
  g.backgroundScalarFrontierDeclared /\
  g.nearestCartanComponentFrontierDeclared /\
  g.nearestCartanComponentFrontierDiagnosticOnly

theorem cartan_components_require_deltaK_and_normalization
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (h : canWriteCartanGHYComponents g) :
    g.deltaKsOfAReady /\ g.deltaKtauOfAReady /\ g.activeKappaRhoCrit0Ready := by
  rcases h with ⟨_, _, _, hKs, hKtau, _, hNorm, _⟩
  exact ⟨hKs, hKtau, hNorm⟩

theorem cartan_components_forbid_legacy_inputs
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (h : canWriteCartanGHYComponents g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hPlanck, hZ4, _⟩
  exact ⟨hPlanck, hZ4⟩

theorem cartan_component_declares_upstream_frontiers
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (h : canWriteCartanGHYComponents g) :
    g.deltaKInputWriterFrontierDeclared /\
    g.backgroundScalarFrontierDeclared /\
    g.nearestCartanComponentFrontierDeclared /\
    g.nearestCartanComponentFrontierDiagnosticOnly := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hDeltaK, hBackground, hNearest, hDiag⟩
  exact ⟨hDeltaK, hBackground, hNearest, hDiag⟩

end P0EFTJanusZ2SigmaCartanGHYComponentFromDeltaKInputsGate
end JanusFormal
