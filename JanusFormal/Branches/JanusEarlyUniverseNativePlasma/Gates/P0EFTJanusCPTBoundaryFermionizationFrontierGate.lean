import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusM31ExteriorPowerConsistencyAuditGate

namespace JanusFormal
namespace P0EFTJanusCPTBoundaryFermionizationFrontierGate

set_option autoImplicit false

structure CPTBoundaryFermionizationFrontierGate where
  resolvedTunnelPinLiftReady : Prop
  z2SigmaSpinorProjectionReady : Prop
  unitNormalCliffordActionReady : Prop
  projectedChargeReductionReady : Prop
  globalFermionOccupationNumberFixed : Prop
  threeCPTOperatorsOnBoundaryHilbert : Prop
  operatorsAreCAROrCliffordGenerators : Prop
  chargeConjugationAsBoundaryModeDerived : Prop
  cptModesOccupiable : Prop
  exteriorStatisticsDerived : Prop
  lambda4SectorSelected : Prop

def cptFermionizationDerived
    (g : CPTBoundaryFermionizationFrontierGate) : Prop :=
  g.threeCPTOperatorsOnBoundaryHilbert /\
  g.operatorsAreCAROrCliffordGenerators /\
  g.chargeConjugationAsBoundaryModeDerived /\
  g.cptModesOccupiable /\
  g.exteriorStatisticsDerived /\
  g.lambda4SectorSelected

def cptFermionizationFrontier
    (g : CPTBoundaryFermionizationFrontierGate) : Prop :=
  g.resolvedTunnelPinLiftReady /\
  g.z2SigmaSpinorProjectionReady /\
  g.unitNormalCliffordActionReady /\
  g.projectedChargeReductionReady /\
  Not g.globalFermionOccupationNumberFixed /\
  Not g.operatorsAreCAROrCliffordGenerators /\
  Not g.chargeConjugationAsBoundaryModeDerived /\
  Not g.exteriorStatisticsDerived

theorem pin_projection_not_enough_for_cpt_fermionization
    (g : CPTBoundaryFermionizationFrontierGate)
    (hFrontier : cptFermionizationFrontier g) :
    Not (cptFermionizationDerived g) := by
  intro h
  exact hFrontier.2.2.2.2.2.1 h.2.1

end P0EFTJanusCPTBoundaryFermionizationFrontierGate
end JanusFormal
