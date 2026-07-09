import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusBoundaryHilbertNSelectorRequirementsGate
import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealityCombinedKKSPeriodGate

namespace JanusFormal
namespace P0EFTJanusBoundaryHilbertSectorSelectionFrontierGate

set_option autoImplicit false

structure BoundaryHilbertSectorSelectionFrontierGate where
  requiredNEquals1001 : Prop
  projectiveCoverNEquals2 : Prop
  projectiveCoverCannotSelectRequiredN : Prop
  cp1SpinJ500CanRepresentRequiredN : Prop
  kksLevel1000CanRepresentRequiredN : Prop
  csOrU1FluxLevelCanRepresentRequiredN : Prop
  spinNetworkOrAreaPuncturesCanRepresentRequiredN : Prop
  globalCP1SectorSelectionDerived : Prop
  kksLevelSelectionDerived : Prop
  fluxPrimitiveSectorDerived : Prop
  areaPunctureLawDerived : Prop
  NMapsToAminAndPhotonRulerDerived : Prop

def noFitBoundaryHilbertSelectorReady
    (g : BoundaryHilbertSectorSelectionFrontierGate) : Prop :=
  g.requiredNEquals1001 /\
  (g.globalCP1SectorSelectionDerived \/
   g.kksLevelSelectionDerived \/
   g.fluxPrimitiveSectorDerived \/
   g.areaPunctureLawDerived) /\
  g.NMapsToAminAndPhotonRulerDerived

def currentBoundaryHilbertFrontier
    (g : BoundaryHilbertSectorSelectionFrontierGate) : Prop :=
  g.requiredNEquals1001 /\
  g.projectiveCoverNEquals2 /\
  g.projectiveCoverCannotSelectRequiredN /\
  g.cp1SpinJ500CanRepresentRequiredN /\
  g.kksLevel1000CanRepresentRequiredN /\
  g.csOrU1FluxLevelCanRepresentRequiredN /\
  g.spinNetworkOrAreaPuncturesCanRepresentRequiredN /\
  Not g.globalCP1SectorSelectionDerived /\
  Not g.kksLevelSelectionDerived /\
  Not g.fluxPrimitiveSectorDerived /\
  Not g.areaPunctureLawDerived

theorem current_frontier_blocks_no_fit_selector
    (g : BoundaryHilbertSectorSelectionFrontierGate)
    (hFrontier : currentBoundaryHilbertFrontier g) :
    Not (noFitBoundaryHilbertSelectorReady g) := by
  intro hReady
  rcases hFrontier with ⟨_, _, _, _, _, _, _, hNoCP1, hNoKKS, hNoFlux, hNoArea⟩
  rcases hReady.right.left with hCP1 | hKKS | hFlux | hArea
  · exact hNoCP1 hCP1
  · exact hNoKKS hKKS
  · exact hNoFlux hFlux
  · exact hNoArea hArea

end P0EFTJanusBoundaryHilbertSectorSelectionFrontierGate
end JanusFormal
