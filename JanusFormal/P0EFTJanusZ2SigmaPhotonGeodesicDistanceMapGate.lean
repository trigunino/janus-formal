import JanusFormal.P0EFTJanusZ2SigmaBackgroundEquationDerivationGate
import JanusFormal.P0EFTJanusZ2SigmaDistanceBAOBibliographyGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPhotonGeodesicDistanceMapGate

set_option autoImplicit false

structure Z2SigmaPhotonGeodesicDistanceMapGate where
  backgroundEquationsDerived : Prop
  distanceBibliographyChecked : Prop
  visiblePhotonMetricProjectionDeclared : Prop
  photonNullGeodesicOnVisibleProjection : Prop
  sigmaCrossingMapDeclared : Prop
  affineRedshiftMapDerived : Prop
  photonNumberConservationGuardDeclared : Prop
  etheringtonGuardAvailable : Prop
  hubbleDistanceDerived : Prop
  transverseComovingDistanceDerived : Prop
  angularDiameterDistanceDerived : Prop
  luminosityDistanceDerived : Prop
  sigmaPhotonGeodesicMapDerived : Prop

def photonDistanceLockClosed
    (g : Z2SigmaPhotonGeodesicDistanceMapGate) : Prop :=
  g.backgroundEquationsDerived /\
  g.distanceBibliographyChecked /\
  g.visiblePhotonMetricProjectionDeclared /\
  g.photonNullGeodesicOnVisibleProjection /\
  g.sigmaCrossingMapDeclared /\
  g.affineRedshiftMapDerived /\
  g.photonNumberConservationGuardDeclared /\
  g.etheringtonGuardAvailable /\
  g.hubbleDistanceDerived /\
  g.transverseComovingDistanceDerived /\
  g.angularDiameterDistanceDerived /\
  g.luminosityDistanceDerived

theorem photon_distance_lock_derives_sigma_map
    (g : Z2SigmaPhotonGeodesicDistanceMapGate)
    (hLock : photonDistanceLockClosed g)
    (hImplies : photonDistanceLockClosed g -> g.sigmaPhotonGeodesicMapDerived) :
    g.sigmaPhotonGeodesicMapDerived := by
  exact hImplies hLock

end P0EFTJanusZ2SigmaPhotonGeodesicDistanceMapGate
end JanusFormal
