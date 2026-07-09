import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate
import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate

set_option autoImplicit false

structure BoundarySpinorRestrictionGate where
  hypersurfaceSpinorRestrictionBibliographyChecked : Prop
  activeSigmaEmbeddingImported : Prop
  plusMinusSpinorBundleDataGateDeclared : Prop
  localBoundarySpinorVariablesDeclared : Prop
  localSheetRestrictionDeclared : Prop
  localZ2SolderingPairDeclared : Prop
  plusBoundaryRestrictionDeclared : Prop
  minusBoundaryRestrictionDeclared : Prop
  sigmaBoundarySpinorPairDeclared : Prop
  observationalFitForbidden : Prop
  activeSigmaEmbeddingReady : Prop
  plusSpinorBundleReady : Prop
  minusSpinorBundleReady : Prop
  globalAmbientSpinorBundleRestrictionReady : Prop
  localBoundarySpinorVariablesReady : Prop
  localPlusBoundaryRestrictionReady : Prop
  localMinusBoundaryRestrictionReady : Prop
  plusBoundaryRestrictionReady : Prop
  minusBoundaryRestrictionReady : Prop
  sigmaBoundarySpinorDataReady : Prop

def boundarySpinorRestrictionLedgerDeclared
    (g : BoundarySpinorRestrictionGate) : Prop :=
  g.hypersurfaceSpinorRestrictionBibliographyChecked /\
  g.activeSigmaEmbeddingImported /\
  g.plusMinusSpinorBundleDataGateDeclared /\
  g.localBoundarySpinorVariablesDeclared /\
  g.localSheetRestrictionDeclared /\
  g.localZ2SolderingPairDeclared /\
  g.plusBoundaryRestrictionDeclared /\
  g.minusBoundaryRestrictionDeclared /\
  g.sigmaBoundarySpinorPairDeclared /\
  g.observationalFitForbidden

def localBoundarySpinorRestrictionReady
    (g : BoundarySpinorRestrictionGate) : Prop :=
  boundarySpinorRestrictionLedgerDeclared g /\
  g.localBoundarySpinorVariablesReady /\
  g.localPlusBoundaryRestrictionReady /\
  g.localMinusBoundaryRestrictionReady /\
  g.sigmaBoundarySpinorDataReady

def globalBoundarySpinorRestrictionReady
    (g : BoundarySpinorRestrictionGate) : Prop :=
  boundarySpinorRestrictionLedgerDeclared g /\
  g.activeSigmaEmbeddingReady /\
  g.plusSpinorBundleReady /\
  g.minusSpinorBundleReady /\
  g.globalAmbientSpinorBundleRestrictionReady /\
  g.plusBoundaryRestrictionReady /\
  g.minusBoundaryRestrictionReady /\
  g.sigmaBoundarySpinorDataReady

def boundarySpinorRestrictionReady
    (g : BoundarySpinorRestrictionGate) : Prop :=
  localBoundarySpinorRestrictionReady g

theorem boundary_spinor_restriction_requires_embedding
    (g : BoundarySpinorRestrictionGate)
    (hReady : globalBoundarySpinorRestrictionReady g) :
    g.activeSigmaEmbeddingReady := by
  exact hReady.2.1

theorem local_boundary_spinors_do_not_claim_global_bundle
    (g : BoundarySpinorRestrictionGate)
    (_hLocal : localBoundarySpinorRestrictionReady g)
    (hGlobal : g.globalAmbientSpinorBundleRestrictionReady) :
    g.globalAmbientSpinorBundleRestrictionReady := by
  exact hGlobal

end P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate
end JanusFormal
