import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxFLRWObligationGate

set_option autoImplicit false

structure MatterFluxFLRWObligationGate where
  thinShellFluxBibliographyChecked : Prop
  sigmaEmbeddingDataAvailable : Prop
  bulkStressTensorsDeclared : Prop
  normalTangentFluxFormulaReady : Prop
  transparencyConditionDeclared : Prop
  z2FluxOrientationDeclared : Prop
  visibleMatterFluxComponentDeclared : Prop
  flrwMatterFluxReduced : Prop
  matterFluxRhoPOfAReady : Prop

def matterFluxMethodReady
    (g : MatterFluxFLRWObligationGate) : Prop :=
  g.thinShellFluxBibliographyChecked /\
  g.sigmaEmbeddingDataAvailable /\
  g.bulkStressTensorsDeclared /\
  g.normalTangentFluxFormulaReady /\
  g.transparencyConditionDeclared /\
  g.z2FluxOrientationDeclared /\
  g.visibleMatterFluxComponentDeclared

def matterFluxFLRWClosureReady
    (g : MatterFluxFLRWObligationGate) : Prop :=
  matterFluxMethodReady g /\
  g.flrwMatterFluxReduced /\
  g.matterFluxRhoPOfAReady

theorem matter_flux_closure_requires_flux_reduction
    (g : MatterFluxFLRWObligationGate)
    (hReady : matterFluxFLRWClosureReady g) :
    g.flrwMatterFluxReduced := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaMatterFluxFLRWObligationGate
end JanusFormal
