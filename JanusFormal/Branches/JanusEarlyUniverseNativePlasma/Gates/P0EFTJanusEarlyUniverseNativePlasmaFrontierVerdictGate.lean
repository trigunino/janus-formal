namespace JanusFormal
namespace P0EFTJanusEarlyUniverseNativePlasmaFrontierVerdictGate

set_option autoImplicit false

structure EarlyUniverseNativePlasmaFrontierVerdictGate where
  eq40MicrophysicsClosed : Prop
  maxwellRadiationExtensionClosed : Prop
  sahaVisibilityScalingClosed : Prop
  symbolicDragEquationClosed : Prop
  soundHorizonContractClosed : Prop
  numericBAOBlocked : Prop
  highPowerPhotonClockTransportRouteOpen : Prop
  attachedEarlyBranchRouteOpen : Prop
  boundaryStateLawForNRouteOpen : Prop
  lambdaCDMRulerImportForbidden : Prop
  alphaFitRepairForbidden : Prop

def frontierVerdictReady
    (g : EarlyUniverseNativePlasmaFrontierVerdictGate) : Prop :=
  g.eq40MicrophysicsClosed /\
  g.maxwellRadiationExtensionClosed /\
  g.sahaVisibilityScalingClosed /\
  g.symbolicDragEquationClosed /\
  g.soundHorizonContractClosed /\
  g.numericBAOBlocked /\
  g.highPowerPhotonClockTransportRouteOpen /\
  g.attachedEarlyBranchRouteOpen /\
  g.boundaryStateLawForNRouteOpen /\
  g.lambdaCDMRulerImportForbidden /\
  g.alphaFitRepairForbidden

theorem native_plasma_frontier_has_three_surviving_routes
    (g : EarlyUniverseNativePlasmaFrontierVerdictGate)
    (hReady : frontierVerdictReady g) :
    g.highPowerPhotonClockTransportRouteOpen /\
      g.attachedEarlyBranchRouteOpen /\
      g.boundaryStateLawForNRouteOpen /\
      g.numericBAOBlocked := by
  rcases hReady with ⟨_, _, _, _, _, hBAO, hClock, hEarly, hBoundary, _, _⟩
  exact And.intro hClock (And.intro hEarly (And.intro hBoundary hBAO))

end P0EFTJanusEarlyUniverseNativePlasmaFrontierVerdictGate
end JanusFormal
