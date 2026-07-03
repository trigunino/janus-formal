import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate
import JanusFormal.P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate

set_option autoImplicit false

structure BoundarySpinorRestrictionGate where
  hypersurfaceSpinorRestrictionBibliographyChecked : Prop
  activeSigmaEmbeddingImported : Prop
  plusMinusSpinorBundleDataGateDeclared : Prop
  plusBoundaryRestrictionDeclared : Prop
  minusBoundaryRestrictionDeclared : Prop
  sigmaBoundarySpinorPairDeclared : Prop
  observationalFitForbidden : Prop
  activeSigmaEmbeddingReady : Prop
  plusSpinorBundleReady : Prop
  minusSpinorBundleReady : Prop
  plusBoundaryRestrictionReady : Prop
  minusBoundaryRestrictionReady : Prop
  sigmaBoundarySpinorDataReady : Prop

def boundarySpinorRestrictionLedgerDeclared
    (g : BoundarySpinorRestrictionGate) : Prop :=
  g.hypersurfaceSpinorRestrictionBibliographyChecked /\
  g.activeSigmaEmbeddingImported /\
  g.plusMinusSpinorBundleDataGateDeclared /\
  g.plusBoundaryRestrictionDeclared /\
  g.minusBoundaryRestrictionDeclared /\
  g.sigmaBoundarySpinorPairDeclared /\
  g.observationalFitForbidden

def boundarySpinorRestrictionReady
    (g : BoundarySpinorRestrictionGate) : Prop :=
  boundarySpinorRestrictionLedgerDeclared g /\
  g.activeSigmaEmbeddingReady /\
  g.plusSpinorBundleReady /\
  g.minusSpinorBundleReady /\
  g.plusBoundaryRestrictionReady /\
  g.minusBoundaryRestrictionReady /\
  g.sigmaBoundarySpinorDataReady

theorem boundary_spinor_restriction_requires_embedding
    (g : BoundarySpinorRestrictionGate)
    (hReady : boundarySpinorRestrictionReady g) :
    g.activeSigmaEmbeddingReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
end JanusFormal
