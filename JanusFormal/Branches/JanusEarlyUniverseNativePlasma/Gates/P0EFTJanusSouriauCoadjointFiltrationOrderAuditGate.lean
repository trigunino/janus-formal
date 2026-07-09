import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSouriauTorsorC11NoCarryBridgeGate

namespace JanusFormal
namespace P0EFTJanusSouriauCoadjointFiltrationOrderAuditGate

set_option autoImplicit false

structure SouriauCoadjointFiltrationOrderAuditGate where
  QPMFiltrationDerived : Prop
  FiltrationDimensionEquals11 : Prop
  BlockProfileLevelsEqual15 : Prop
  FullComponentOrderDerived : Prop
  Orders1001Sym4States : Prop

def SouriauFiltrationOrderingClosed
    (g : SouriauCoadjointFiltrationOrderAuditGate) : Prop :=
  g.QPMFiltrationDerived /\
  g.FullComponentOrderDerived /\
  g.Orders1001Sym4States

def SouriauFiltrationOrderingFrontier
    (g : SouriauCoadjointFiltrationOrderAuditGate) : Prop :=
  g.QPMFiltrationDerived /\
  g.FiltrationDimensionEquals11 /\
  g.BlockProfileLevelsEqual15 /\
  Not g.FullComponentOrderDerived /\
  Not g.Orders1001Sym4States

theorem qpm_filtration_is_too_coarse_for_sym4_1001
    (g : SouriauCoadjointFiltrationOrderAuditGate)
    (hFrontier : SouriauFiltrationOrderingFrontier g) :
    Not (SouriauFiltrationOrderingClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.1

end P0EFTJanusSouriauCoadjointFiltrationOrderAuditGate
end JanusFormal
