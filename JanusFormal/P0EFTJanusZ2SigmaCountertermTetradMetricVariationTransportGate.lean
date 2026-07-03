import JanusFormal.P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradMetricVariationTransportGate

set_option autoImplicit false

structure CountertermTetradMetricVariationTransportGate where
  tetradVariationTransportGateImported : Prop
  tetradMetricIdentityBibliographyChecked : Prop
  inducedMetricFormulaDeclared : Prop
  coframeVariationBasisDeclared : Prop
  z2OrientationNoEffectOnMetricDeclared : Prop
  noMetricOnlyShortcut : Prop
  deltaHFormulaDeclared : Prop
  deltaHInAllowedBasis : Prop
  inducedMetricVariationTransportReady : Prop

def tetradMetricVariationLedgerDeclared
    (g : CountertermTetradMetricVariationTransportGate) : Prop :=
  g.tetradVariationTransportGateImported /\
  g.tetradMetricIdentityBibliographyChecked /\
  g.inducedMetricFormulaDeclared /\
  g.coframeVariationBasisDeclared /\
  g.z2OrientationNoEffectOnMetricDeclared /\
  g.noMetricOnlyShortcut /\
  g.deltaHFormulaDeclared

def tetradMetricVariationTransportReady
    (g : CountertermTetradMetricVariationTransportGate) : Prop :=
  tetradMetricVariationLedgerDeclared g /\
  g.deltaHInAllowedBasis /\
  g.inducedMetricVariationTransportReady

theorem metric_transport_requires_delta_h_formula
    (g : CountertermTetradMetricVariationTransportGate)
    (hReady : tetradMetricVariationTransportReady g) :
    g.deltaHFormulaDeclared := by
  exact hReady.1.2.2.2.2.2.2

theorem metric_transport_feeds_tetrad_transport
    (g : CountertermTetradMetricVariationTransportGate)
    (hReady : tetradMetricVariationTransportReady g) :
    g.inducedMetricVariationTransportReady := by
  exact hReady.2.2

end P0EFTJanusZ2SigmaCountertermTetradMetricVariationTransportGate
end JanusFormal
