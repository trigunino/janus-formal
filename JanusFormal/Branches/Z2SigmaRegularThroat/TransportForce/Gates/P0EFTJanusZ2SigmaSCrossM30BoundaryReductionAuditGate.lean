import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaSCrossTransportSourceAcceptanceGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSCrossM30BoundaryReductionAuditGate

set_option autoImplicit false

structure SCrossM30BoundaryReductionAuditGate where
  janusTwoLayerActionSourceAvailable : Prop
  janusBivariationSourceAvailable : Prop
  genericBoundaryVariationBibliographyAvailable : Prop
  genericJunctionBibliographyAvailable : Prop
  explicitSSbarToSigmaPullbackFound : Prop
  explicitSigmaSupportOrDeltaDistributionFound : Prop
  explicitPhiLTransportFromM30Found : Prop
  explicitCountertermDensityFromM30Found : Prop
  conditionalBulkToSigmaForceFormulaDerived : Prop
  strictZ2BulkForceCancels : Prop
  canReduceM30InteractionTermsToSigmaCounterterm : Prop

def janusSourceContextAvailable
    (g : SCrossM30BoundaryReductionAuditGate) : Prop :=
  g.janusTwoLayerActionSourceAvailable /\
  g.janusBivariationSourceAvailable /\
  g.genericBoundaryVariationBibliographyAvailable /\
  g.genericJunctionBibliographyAvailable

def m30SigmaReductionReady
    (g : SCrossM30BoundaryReductionAuditGate) : Prop :=
  janusSourceContextAvailable g /\
  g.explicitSSbarToSigmaPullbackFound /\
  g.explicitSigmaSupportOrDeltaDistributionFound /\
  g.explicitPhiLTransportFromM30Found /\
  g.explicitCountertermDensityFromM30Found /\
  g.conditionalBulkToSigmaForceFormulaDerived /\
  Not g.strictZ2BulkForceCancels /\
  g.canReduceM30InteractionTermsToSigmaCounterterm

def tunnelDefectActionRequiredForNonzeroCounterterm
    (g : SCrossM30BoundaryReductionAuditGate) : Prop :=
  janusSourceContextAvailable g /\
  g.conditionalBulkToSigmaForceFormulaDerived /\
  g.strictZ2BulkForceCancels /\
  Not g.canReduceM30InteractionTermsToSigmaCounterterm

theorem missing_sigma_pullback_blocks_m30_reduction
    (g : SCrossM30BoundaryReductionAuditGate)
    (hMissing : Not g.explicitSSbarToSigmaPullbackFound) :
    Not (m30SigmaReductionReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem missing_phi_l_transport_blocks_m30_reduction
    (g : SCrossM30BoundaryReductionAuditGate)
    (hMissing : Not g.explicitPhiLTransportFromM30Found) :
    Not (m30SigmaReductionReady g) := by
  intro hReady
  exact hMissing hReady.right.right.right.left

theorem strict_z2_bulk_cancellation_blocks_m30_counterterm
    (g : SCrossM30BoundaryReductionAuditGate)
    (hCancels : g.strictZ2BulkForceCancels) :
    Not (m30SigmaReductionReady g) := by
  intro hReady
  exact hReady.right.right.right.right.right.right.left hCancels

theorem nonzero_counterterm_requires_independent_tunnel_defect_action
    (g : SCrossM30BoundaryReductionAuditGate)
    (hReq : tunnelDefectActionRequiredForNonzeroCounterterm g) :
    g.strictZ2BulkForceCancels /\
      Not g.canReduceM30InteractionTermsToSigmaCounterterm := by
  exact And.intro hReq.right.right.left hReq.right.right.right

end P0EFTJanusZ2SigmaSCrossM30BoundaryReductionAuditGate
end JanusFormal
