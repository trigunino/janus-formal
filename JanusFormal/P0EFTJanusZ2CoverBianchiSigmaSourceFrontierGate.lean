namespace JanusFormal
namespace P0EFTJanusZ2CoverBianchiSigmaSourceFrontierGate

set_option autoImplicit false

structure Z2CoverBianchiSigmaSourceFrontierGate where
  projectedEquationsReady : Prop
  pairedBianchiBalanceReady : Prop
  crossMeasureTransportReady : Prop
  sigmaSourceAvailable : Prop
  sigmaAlphaHAvailable : Prop
  surfaceHKCoefficientsAvailable : Prop
  surfaceHKGeometryAvailable : Prop
  bianchiClosureReady : Prop
  noRhoEffShortcut : Prop
  noNegativeThermodynamicDensityPostulate : Prop
  noZ4MonodromyUse : Prop

def currentZ2CoverLedgerReady
    (g : Z2CoverBianchiSigmaSourceFrontierGate) : Prop :=
  g.projectedEquationsReady /\
  g.pairedBianchiBalanceReady /\
  g.crossMeasureTransportReady /\
  g.noRhoEffShortcut /\
  g.noNegativeThermodynamicDensityPostulate /\
  g.noZ4MonodromyUse

def sigmaSourceDependencyOpen
    (g : Z2CoverBianchiSigmaSourceFrontierGate) : Prop :=
  Not g.sigmaSourceAvailable /\
  Not g.sigmaAlphaHAvailable /\
  Not g.surfaceHKCoefficientsAvailable /\
  Not g.surfaceHKGeometryAvailable

theorem missing_sigma_source_blocks_bianchi_closure
    (g : Z2CoverBianchiSigmaSourceFrontierGate)
    (hMissing : Not g.sigmaSourceAvailable)
    (hClosureNeedsSigma : g.bianchiClosureReady -> g.sigmaSourceAvailable) :
    Not g.bianchiClosureReady := by
  intro hClosed
  exact hMissing (hClosureNeedsSigma hClosed)

theorem sigma_alpha_h_requires_surface_hk_inputs
    (g : Z2CoverBianchiSigmaSourceFrontierGate)
    (hAlphaNeedsHK :
      g.sigmaAlphaHAvailable ->
        g.surfaceHKCoefficientsAvailable /\ g.surfaceHKGeometryAvailable)
    (hAlpha : g.sigmaAlphaHAvailable) :
    g.surfaceHKCoefficientsAvailable /\ g.surfaceHKGeometryAvailable := by
  exact hAlphaNeedsHK hAlpha

theorem current_frontier_is_not_full_closure
    (g : Z2CoverBianchiSigmaSourceFrontierGate)
    (hLedger : currentZ2CoverLedgerReady g)
    (hMissing : Not g.sigmaSourceAvailable)
    (hClosureNeedsSigma : g.bianchiClosureReady -> g.sigmaSourceAvailable) :
    currentZ2CoverLedgerReady g /\ Not g.bianchiClosureReady := by
  exact And.intro hLedger
    (missing_sigma_source_blocks_bianchi_closure g hMissing hClosureNeedsSigma)

end P0EFTJanusZ2CoverBianchiSigmaSourceFrontierGate
end JanusFormal
