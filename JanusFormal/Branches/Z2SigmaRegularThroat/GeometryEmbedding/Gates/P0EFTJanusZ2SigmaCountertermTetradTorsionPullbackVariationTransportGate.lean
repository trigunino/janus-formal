import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGate

set_option autoImplicit false

structure CountertermTetradTorsionPullbackVariationTransportGate where
  tetradVariationTransportGateImported : Prop
  torsionPullbackOnSigmaGateImported : Prop
  orientedPullbackVariationCommutationImported : Prop
  cartanStructureEquationBibliographyChecked : Prop
  independentConnectionBranchDeclared : Prop
  torsionFormulaDeclared : Prop
  deltaEToDeltaTorsionFormulaDeclared : Prop
  sigmaPullbackCommutationDeclared : Prop
  z2OrientationTransportDeclared : Prop
  noFittedTorsionVariationCoefficient : Prop
  torsionPullbackReady : Prop
  pullbackCommutationReady : Prop
  deltaEToDeltaTorsionFormulaProved : Prop
  torsionPullbackVariationInAllowedBasis : Prop
  torsionPullbackVariationTransportReady : Prop

def tetradTorsionPullbackVariationLedgerDeclared
    (g : CountertermTetradTorsionPullbackVariationTransportGate) : Prop :=
  g.tetradVariationTransportGateImported /\
  g.torsionPullbackOnSigmaGateImported /\
  g.orientedPullbackVariationCommutationImported /\
  g.cartanStructureEquationBibliographyChecked /\
  g.independentConnectionBranchDeclared /\
  g.torsionFormulaDeclared /\
  g.deltaEToDeltaTorsionFormulaDeclared /\
  g.sigmaPullbackCommutationDeclared /\
  g.z2OrientationTransportDeclared /\
  g.noFittedTorsionVariationCoefficient

def tetradTorsionPullbackVariationReady
    (g : CountertermTetradTorsionPullbackVariationTransportGate) : Prop :=
  tetradTorsionPullbackVariationLedgerDeclared g /\
  g.torsionPullbackReady /\
  g.pullbackCommutationReady /\
  g.deltaEToDeltaTorsionFormulaProved /\
  g.torsionPullbackVariationInAllowedBasis /\
  g.torsionPullbackVariationTransportReady

theorem tetrad_torsion_transport_requires_cartan_formula
    (g : CountertermTetradTorsionPullbackVariationTransportGate)
    (hReady : tetradTorsionPullbackVariationReady g) :
    g.deltaEToDeltaTorsionFormulaDeclared := by
  exact hReady.1.2.2.2.2.2.2.1

theorem tetrad_torsion_transport_feeds_tetrad_transport
    (g : CountertermTetradTorsionPullbackVariationTransportGate)
    (hReady : tetradTorsionPullbackVariationReady g) :
    g.torsionPullbackVariationTransportReady := by
  exact hReady.2.2.2.2.2

end P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGate
end JanusFormal
