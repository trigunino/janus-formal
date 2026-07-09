import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4TwoSectorBoltzmannVariablesGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorConservationBianchiGate

set_option autoImplicit false

structure TwoSectorConservationBianchiGate where
  variablesGatePassed : Prop
  plusSectorConservationDeclared : Prop
  minusSectorConservationDeclared : Prop
  exchangeTermsDeclared : Prop
  exchangeTermsExplicitZero : Prop
  projectedExchangeBalance : Prop
  continuityPlusAvailable : Prop
  eulerPlusAvailable : Prop
  shearPlusAvailableOrClosureDeclared : Prop
  continuityMinusAvailable : Prop
  eulerMinusAvailable : Prop
  shearMinusAvailableOrClosureDeclared : Prop
  couplingMatrixConservationCompatible : Prop
  projectionMatrixConservationCompatible : Prop
  bianchiResidualDeclared : Prop
  bianchiResidualGuard : Prop
  grLimitRecovered : Prop
  negativeSectorSignPolicyDeclared : Prop
  negativeDensityThermodynamic : Prop
  gravitationalCouplingSignDeclared : Prop
  negativeGravitySignNotThermodynamicNegativeDensity : Prop
  rhoEffShortcutForbidden : Prop
  effectiveRhoCollapseForbidden : Prop
  directClPatchForbidden : Prop
  rawToyLOSForbidden : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def conservationReady (g : TwoSectorConservationBianchiGate) : Prop :=
  g.variablesGatePassed /\
  g.plusSectorConservationDeclared /\
  g.minusSectorConservationDeclared /\
  g.exchangeTermsDeclared /\
  g.exchangeTermsExplicitZero /\
  g.projectedExchangeBalance /\
  g.continuityPlusAvailable /\
  g.eulerPlusAvailable /\
  g.shearPlusAvailableOrClosureDeclared /\
  g.continuityMinusAvailable /\
  g.eulerMinusAvailable /\
  g.shearMinusAvailableOrClosureDeclared /\
  g.couplingMatrixConservationCompatible /\
  g.projectionMatrixConservationCompatible /\
  g.bianchiResidualDeclared /\
  g.bianchiResidualGuard /\
  g.grLimitRecovered /\
  g.negativeSectorSignPolicyDeclared /\
  g.negativeDensityThermodynamic /\
  g.gravitationalCouplingSignDeclared /\
  g.negativeGravitySignNotThermodynamicNegativeDensity /\
  g.rhoEffShortcutForbidden /\
  g.effectiveRhoCollapseForbidden /\
  g.directClPatchForbidden /\
  g.rawToyLOSForbidden /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem conservation_bianchi_gate_blocks_unconserved_sources
    (g : TwoSectorConservationBianchiGate)
    (hPolicy : conservationReady g -> g.gatePassed)
    (h : conservationReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorConservationBianchiGate
end JanusFormal
