import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusSouriauCoadjointFiltrationOrderAuditGate

namespace JanusFormal
namespace P0EFTJanusIsotropyPreservingANormalOrderingObstructionGate

set_option autoImplicit false

structure IsotropyPreservingANormalOrderingObstructionGate where
  SpatialTripletsRemainDegenerate : Prop
  IsotropicBlockProfilesEqual70 : Prop
  FullSym4LevelsEqual1001 : Prop
  Orders1001WhileIsotropic : Prop
  BoundaryMicrostateAveragingDerived : Prop

def IsotropicANormalOrderingClosed
    (g : IsotropyPreservingANormalOrderingObstructionGate) : Prop :=
  g.SpatialTripletsRemainDegenerate /\
  g.Orders1001WhileIsotropic /\
  g.BoundaryMicrostateAveragingDerived

def IsotropicANormalOrderingFrontier
    (g : IsotropyPreservingANormalOrderingObstructionGate) : Prop :=
  g.SpatialTripletsRemainDegenerate /\
  g.IsotropicBlockProfilesEqual70 /\
  g.FullSym4LevelsEqual1001 /\
  Not g.Orders1001WhileIsotropic /\
  Not g.BoundaryMicrostateAveragingDerived

theorem isotropic_triplet_degeneracy_blocks_1001_ordering
    (g : IsotropyPreservingANormalOrderingObstructionGate)
    (hFrontier : IsotropicANormalOrderingFrontier g) :
    Not (IsotropicANormalOrderingClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.1

end P0EFTJanusIsotropyPreservingANormalOrderingObstructionGate
end JanusFormal
