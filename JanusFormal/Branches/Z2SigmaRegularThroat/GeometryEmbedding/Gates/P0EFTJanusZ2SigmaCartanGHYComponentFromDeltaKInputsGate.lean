namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYComponentFromDeltaKInputsGate

set_option autoImplicit false

structure CartanGHYComponentFromDeltaKInputsGate where
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  aGridDeclared : Prop
  rSigmaOverEllCollarReady : Prop
  absoluteRSigmaSolutionReady : Prop
  ratioOnlyCannotWriteDeltaK : Prop
  deltaKsOfAReady : Prop
  deltaKtauOfAReady : Prop
  z2OrientationSignDeclared : Prop
  activeKappaRhoCrit0Ready : Prop
  zeroDeltaKNormalizationIndependent : Prop
  deltaKProvenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  rSigmaRatioFrontierDeclared : Prop
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
  (g.activeKappaRhoCrit0Ready \/ g.zeroDeltaKNormalizationIndependent) /\
  g.deltaKProvenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.rSigmaRatioFrontierDeclared /\
  g.deltaKInputWriterFrontierDeclared /\
  g.backgroundScalarFrontierDeclared /\
  g.nearestCartanComponentFrontierDeclared /\
  g.nearestCartanComponentFrontierDiagnosticOnly

theorem cartan_components_require_deltaK_and_normalization
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (h : canWriteCartanGHYComponents g) :
    g.deltaKsOfAReady /\ g.deltaKtauOfAReady /\
    (g.activeKappaRhoCrit0Ready \/ g.zeroDeltaKNormalizationIndependent) := by
  rcases h with ⟨_, _, _, hKs, hKtau, _, hNorm, _, _, _, _, _, _, _, _, _⟩
  exact ⟨hKs, hKtau, hNorm⟩

theorem zero_deltaK_branch_can_skip_critical_normalization
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (h : canWriteCartanGHYComponents g)
    (hNoNorm : Not g.activeKappaRhoCrit0Ready) :
    g.zeroDeltaKNormalizationIndependent := by
  exact Or.resolve_left
    (cartan_components_require_deltaK_and_normalization g h).right.right
    hNoNorm

theorem ratio_only_does_not_supply_deltaK
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (_hRatioOnly : g.ratioOnlyCannotWriteDeltaK)
    (hNoDeltaKs : Not g.deltaKsOfAReady) :
    Not (canWriteCartanGHYComponents g) := by
  intro h
  exact hNoDeltaKs (cartan_components_require_deltaK_and_normalization g h).left

theorem cartan_components_forbid_legacy_inputs
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (h : canWriteCartanGHYComponents g) :
    g.compressedPlanckLCDMForbidden /\ g.archivedZ4ReuseForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hPlanck, hZ4, _, _, _, _, _, _⟩
  exact ⟨hPlanck, hZ4⟩

theorem cartan_component_declares_upstream_frontiers
    (g : CartanGHYComponentFromDeltaKInputsGate)
    (h : canWriteCartanGHYComponents g) :
    g.rSigmaRatioFrontierDeclared /\
    g.deltaKInputWriterFrontierDeclared /\
    g.backgroundScalarFrontierDeclared /\
    g.nearestCartanComponentFrontierDeclared /\
    g.nearestCartanComponentFrontierDiagnosticOnly := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hRatio, hDelta, hBack, hFront, hDiag⟩
  exact ⟨hRatio, hDelta, hBack, hFront, hDiag⟩

end P0EFTJanusZ2SigmaCartanGHYComponentFromDeltaKInputsGate
end JanusFormal
