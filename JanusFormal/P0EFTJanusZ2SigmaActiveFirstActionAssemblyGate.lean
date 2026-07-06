import JanusFormal.P0EFTJanusLegacyZ4ArchivePolicyGate
import JanusFormal.P0EFTJanusSigmaBoundaryActionSupportGate
import JanusFormal.P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermBoundaryActionFunctionalGate
import JanusFormal.P0EFTJanusZ2SigmaTransportMapDerivationGate
import JanusFormal.P0EFTJanusZ2SigmaSameSectorStressConservationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveFirstActionAssemblyGate

set_option autoImplicit false

structure ActiveFirstActionAssemblyGate where
  legacyZ4ArchivePolicyImported : Prop
  z4ActionReuseForbidden : Prop
  activeCoreIsZ2TunnelSigma : Prop
  sigmaBoundaryActionImported : Prop
  plusMinusMatterActionImported : Prop
  countertermBoundaryActionImported : Prop
  transportMapDerivationImported : Prop
  sameSectorStressConservationImported : Prop
  bulkGravityPlusDeclared : Prop
  bulkGravityMinusDeclared : Prop
  sigmaBoundaryTermDeclared : Prop
  plusMatterTermDeclared : Prop
  minusMatterTermDeclared : Prop
  countertermTermDeclared : Prop
  transportCrossTermDeclared : Prop
  noObservationalFit : Prop
  activeFirstActionSkeletonWritten : Prop
  sigmaBoundaryActionClosed : Prop
  plusMatterActionReady : Prop
  minusMatterActionReady : Prop
  countertermBoundaryActionClosed : Prop
  transportBridgeDeclared : Prop
  crossActionSourceAccepted : Prop
  crossActionNewAxiomNotAdopted : Prop
  activeFirstActionAssembled : Prop

def activeFirstActionLedgerDeclared
    (g : ActiveFirstActionAssemblyGate) : Prop :=
  g.legacyZ4ArchivePolicyImported /\
  g.z4ActionReuseForbidden /\
  g.activeCoreIsZ2TunnelSigma /\
  g.sigmaBoundaryActionImported /\
  g.plusMinusMatterActionImported /\
  g.countertermBoundaryActionImported /\
  g.transportMapDerivationImported /\
  g.sameSectorStressConservationImported /\
  g.bulkGravityPlusDeclared /\
  g.bulkGravityMinusDeclared /\
  g.sigmaBoundaryTermDeclared /\
  g.plusMatterTermDeclared /\
  g.minusMatterTermDeclared /\
  g.countertermTermDeclared /\
  g.transportCrossTermDeclared /\
  g.noObservationalFit /\
  g.activeFirstActionSkeletonWritten

def activeFirstActionReady
    (g : ActiveFirstActionAssemblyGate) : Prop :=
  activeFirstActionLedgerDeclared g /\
  g.sigmaBoundaryActionClosed /\
  g.plusMatterActionReady /\
  g.minusMatterActionReady /\
  g.countertermBoundaryActionClosed /\
  g.transportBridgeDeclared /\
  g.crossActionSourceAccepted /\
  g.crossActionNewAxiomNotAdopted /\
  g.activeFirstActionAssembled

theorem active_first_action_forbids_z4_reuse
    (g : ActiveFirstActionAssemblyGate)
    (hLedger : activeFirstActionLedgerDeclared g) :
    g.z4ActionReuseForbidden /\ g.activeCoreIsZ2TunnelSigma := by
  exact And.intro hLedger.right.left hLedger.right.right.left

theorem active_first_action_ready_feeds_matter_actions
    (g : ActiveFirstActionAssemblyGate)
    (hReady : activeFirstActionReady g) :
    g.plusMatterActionReady /\ g.minusMatterActionReady := by
  exact And.intro hReady.right.right.left hReady.right.right.right.left

theorem missing_plus_matter_action_blocks_active_first_action
    (g : ActiveFirstActionAssemblyGate)
    (hMissing : Not g.plusMatterActionReady) :
    Not (activeFirstActionReady g) := by
  intro hReady
  exact hMissing hReady.right.right.left

theorem missing_cross_action_source_blocks_active_first_action
    (g : ActiveFirstActionAssemblyGate)
    (hMissing : Not g.crossActionSourceAccepted) :
    Not (activeFirstActionReady g) := by
  intro hReady
  exact hMissing hReady.right.right.right.right.right.right.left

end P0EFTJanusZ2SigmaActiveFirstActionAssemblyGate
end JanusFormal
