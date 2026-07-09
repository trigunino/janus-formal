import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaSameSectorStressConservationGate
import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusPlusSectorMaxwellRadiationActionGate

namespace JanusFormal
namespace P0EFTJanusPlusSectorPhotonStressConservationGate

set_option autoImplicit false

structure PlusSectorPhotonStressConservationGate where
  positivePhotonGeodesicAnchor : Prop
  distinctGeodesicFamilyAnchor : Prop
  sameSectorStressConservationScaffoldImported : Prop
  plusSectorPhotonActionDeclared : Prop
  minimalCouplingToGPlus : Prop
  photonDiffeomorphismNoetherIdentityDeclared : Prop
  photonEomReady : Prop
  noCrossSectorPhotonExchangeDeclared : Prop
  plusSectorPhotonStressConditionallyConserved : Prop
  plusSectorPhotonStressConservedWithinExtension : Prop
  plusSectorPhotonStressPaperNative : Prop

def photonNoetherLedgerDeclared
    (g : PlusSectorPhotonStressConservationGate) : Prop :=
  g.positivePhotonGeodesicAnchor /\
  g.distinctGeodesicFamilyAnchor /\
  g.sameSectorStressConservationScaffoldImported /\
  g.photonDiffeomorphismNoetherIdentityDeclared

def photonStressConservationReady
    (g : PlusSectorPhotonStressConservationGate) : Prop :=
  photonNoetherLedgerDeclared g /\
  g.plusSectorPhotonActionDeclared /\
  g.minimalCouplingToGPlus /\
  g.photonEomReady /\
  g.noCrossSectorPhotonExchangeDeclared /\
  g.plusSectorPhotonStressConservedWithinExtension /\
  Not g.plusSectorPhotonStressPaperNative

theorem missing_photon_action_blocks_unconditional_conservation
    (g : PlusSectorPhotonStressConservationGate)
    (hMissing : Not g.plusSectorPhotonActionDeclared) :
    Not (photonStressConservationReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem conditional_noether_route_is_not_unconditional_closure
    (g : PlusSectorPhotonStressConservationGate)
    (hCond : g.plusSectorPhotonStressConditionallyConserved)
    (hPaperExternal : Not g.plusSectorPhotonStressPaperNative) :
    g.plusSectorPhotonStressConditionallyConserved /\
      Not g.plusSectorPhotonStressPaperNative := by
  exact And.intro hCond hPaperExternal

end P0EFTJanusPlusSectorPhotonStressConservationGate
end JanusFormal
