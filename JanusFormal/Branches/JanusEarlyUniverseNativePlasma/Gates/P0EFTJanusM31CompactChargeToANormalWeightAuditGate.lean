import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusAnormalWeightOriginCandidateMatrixGate

namespace JanusFormal
namespace P0EFTJanusM31CompactChargeToANormalWeightAuditGate

set_option autoImplicit false

structure M31CompactChargeToANormalWeightAuditGate where
  CompactChargeDimensionsDeclared : Prop
  ChargePTCSignActionDeclared : Prop
  ChargeQuantizationMotivated : Prop
  ChargeLatticeActsOnC11Derived : Prop
  NormalRedshiftANormalDerived : Prop
  FourDissociatedC11WeightsDerived : Prop

def M31CompactChargeANormalClosed
    (g : M31CompactChargeToANormalWeightAuditGate) : Prop :=
  g.CompactChargeDimensionsDeclared /\
  g.ChargeLatticeActsOnC11Derived /\
  g.NormalRedshiftANormalDerived /\
  g.FourDissociatedC11WeightsDerived

def M31CompactChargeANormalFrontier
    (g : M31CompactChargeToANormalWeightAuditGate) : Prop :=
  g.CompactChargeDimensionsDeclared /\
  g.ChargePTCSignActionDeclared /\
  g.ChargeQuantizationMotivated /\
  Not g.ChargeLatticeActsOnC11Derived /\
  Not g.NormalRedshiftANormalDerived /\
  Not g.FourDissociatedC11WeightsDerived

theorem compact_charge_labels_do_not_alone_close_anormal
    (g : M31CompactChargeToANormalWeightAuditGate)
    (hFrontier : M31CompactChargeANormalFrontier g) :
    Not (M31CompactChargeANormalClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.1

end P0EFTJanusM31CompactChargeToANormalWeightAuditGate
end JanusFormal
