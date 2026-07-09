import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusM31ExteriorPowerConsistencyAuditGate

namespace JanusFormal
namespace P0EFTJanusM31SymmetricPowerBoundarySectorCandidateGate

set_option autoImplicit false

structure M31SymmetricPowerBoundarySectorCandidateGate where
  M31JanusLieDimension11 : Prop
  M31TranslationDimension4 : Prop
  sym4C11Equals1001 : Prop
  usesCPTLabelsAsModes : Prop
  boundaryBosonicStatisticsDerived : Prop
  degree4SectorSelected : Prop
  sym4MapsToAmin : Prop
  sym4MapsToPhotonRuler : Prop

def sym4CandidateReady
    (g : M31SymmetricPowerBoundarySectorCandidateGate) : Prop :=
  g.M31JanusLieDimension11 /\
  g.M31TranslationDimension4 /\
  g.sym4C11Equals1001 /\
  Not g.usesCPTLabelsAsModes

def sym4BoundaryStateLawDerived
    (g : M31SymmetricPowerBoundarySectorCandidateGate) : Prop :=
  sym4CandidateReady g /\
  g.boundaryBosonicStatisticsDerived /\
  g.degree4SectorSelected /\
  g.sym4MapsToAmin /\
  g.sym4MapsToPhotonRuler

theorem sym4_candidate_without_statistics_not_state_law
    (g : M31SymmetricPowerBoundarySectorCandidateGate)
    (hNoStats : Not g.boundaryBosonicStatisticsDerived) :
    Not (sym4BoundaryStateLawDerived g) := by
  intro h
  exact hNoStats h.right.left

end P0EFTJanusM31SymmetricPowerBoundarySectorCandidateGate
end JanusFormal
