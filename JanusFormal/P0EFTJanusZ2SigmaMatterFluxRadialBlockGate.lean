import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate
import JanusFormal.P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxRadialBlockGate

set_option autoImplicit false

structure MatterFluxRadialBlockGate where
  thinShellFluxBibliographyChecked : Prop
  normalTangentFluxFormulaReady : Prop
  radialFluxVariationDeclared : Prop
  transparencyBranchDeclared : Prop
  matterFluxRouteDecisionGateDeclared : Prop
  activeBulkStressProjectionRequired : Prop
  z2FluxOrientationDeclared : Prop
  observationalFitForbidden : Prop
  eMatterFluxBlockDeclared : Prop
  transparencyConditionDerived : Prop
  activeFluxOfAReady : Prop
  eMatterFluxRadialBlockReduced : Prop

def matterFluxRadialLedgerDeclared
    (g : MatterFluxRadialBlockGate) : Prop :=
  g.thinShellFluxBibliographyChecked /\
  g.normalTangentFluxFormulaReady /\
  g.radialFluxVariationDeclared /\
  g.transparencyBranchDeclared /\
  g.matterFluxRouteDecisionGateDeclared /\
  g.activeBulkStressProjectionRequired /\
  g.z2FluxOrientationDeclared /\
  g.observationalFitForbidden /\
  g.eMatterFluxBlockDeclared

def matterFluxRadialBlockReduced
    (g : MatterFluxRadialBlockGate) : Prop :=
  matterFluxRadialLedgerDeclared g /\
  (g.transparencyConditionDerived \/ g.activeFluxOfAReady) /\
  g.eMatterFluxRadialBlockReduced

theorem matter_flux_reduction_requires_transparency_or_flux
    (g : MatterFluxRadialBlockGate)
    (hReady : matterFluxRadialBlockReduced g) :
    g.transparencyConditionDerived \/ g.activeFluxOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaMatterFluxRadialBlockGate
end JanusFormal
