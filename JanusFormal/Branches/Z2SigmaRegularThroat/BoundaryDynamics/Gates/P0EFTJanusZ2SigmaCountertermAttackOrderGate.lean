import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermAttackOrderGate

set_option autoImplicit false

structure CountertermAttackOrderGate where
  residualChannelFrontierImported : Prop
  tetradResidualChannelImported : Prop
  activeEmbeddingReadinessImported : Prop
  throatRadiusSolutionFrontierImported : Prop
  attackOrderIsDiagnosticOnly : Prop
  circularRadiusCountertermDependencyChecked : Prop
  lctProfileCurrentlyRequiresRadiusValues : Prop
  nonCircularTraceRouteRequired : Prop
  symbolicLocalCountertermRouteDeclared : Prop
  noCountertermChannelDropped : Prop
  noFitShortcut : Prop
  noLegacyZ4Import : Prop
  nearestChannelIdentified : Prop
  tetradChannelIsNearestNotReady : Prop
  radiusCountertermCircularDependencyDetected : Prop
  activeEmbeddingReady : Prop
  rSigmaSolutionCertificateReady : Prop
  symbolicLocalCountertermRouteReady : Prop
  traceValuesFromFullSigmaActionReady : Prop
  radialProfileFromResidualContractionsNonCircular : Prop
  countertermAttackOrderReady : Prop

def countertermAttackOrderLedgerDeclared
    (g : CountertermAttackOrderGate) : Prop :=
  g.residualChannelFrontierImported /\
  g.tetradResidualChannelImported /\
  g.activeEmbeddingReadinessImported /\
  g.throatRadiusSolutionFrontierImported /\
  g.attackOrderIsDiagnosticOnly /\
  g.circularRadiusCountertermDependencyChecked /\
  g.lctProfileCurrentlyRequiresRadiusValues /\
  g.nonCircularTraceRouteRequired /\
  g.symbolicLocalCountertermRouteDeclared /\
  g.noCountertermChannelDropped /\
  g.noFitShortcut /\
  g.noLegacyZ4Import

def countertermAttackOrderGatePassed
    (g : CountertermAttackOrderGate) : Prop :=
  countertermAttackOrderLedgerDeclared g /\
  g.nearestChannelIdentified /\
  g.tetradChannelIsNearestNotReady /\
  g.radiusCountertermCircularDependencyDetected /\
  g.symbolicLocalCountertermRouteReady /\
  g.traceValuesFromFullSigmaActionReady /\
  g.radialProfileFromResidualContractionsNonCircular /\
  g.activeEmbeddingReady /\
  g.rSigmaSolutionCertificateReady /\
  g.countertermAttackOrderReady

theorem attack_order_requires_symbolic_local_counterterm_route
    (g : CountertermAttackOrderGate)
    (h : countertermAttackOrderGatePassed g) :
    g.symbolicLocalCountertermRouteReady := by
  exact h.2.2.2.2.1

theorem attack_order_requires_non_circular_trace_values
    (g : CountertermAttackOrderGate)
    (h : countertermAttackOrderGatePassed g) :
    g.traceValuesFromFullSigmaActionReady := by
  exact h.2.2.2.2.2.1

theorem missing_symbolic_local_counterterm_route_blocks_attack_order
    (g : CountertermAttackOrderGate)
    (hMissing : Not g.symbolicLocalCountertermRouteReady) :
    Not (countertermAttackOrderGatePassed g) := by
  intro hReady
  exact hMissing (attack_order_requires_symbolic_local_counterterm_route g hReady)

theorem missing_non_circular_trace_values_blocks_attack_order
    (g : CountertermAttackOrderGate)
    (hMissing : Not g.traceValuesFromFullSigmaActionReady) :
    Not (countertermAttackOrderGatePassed g) := by
  intro hReady
  exact hMissing (attack_order_requires_non_circular_trace_values g hReady)

theorem diagnostic_nearest_tetrad_does_not_close_attack_order
    (g : CountertermAttackOrderGate)
    (hNotReady : Not g.countertermAttackOrderReady) :
    Not (countertermAttackOrderGatePassed g) := by
  intro hReady
  exact hNotReady hReady.2.2.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaCountertermAttackOrderGate
end JanusFormal
