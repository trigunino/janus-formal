import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusIsotropyPreservingANormalOrderingObstructionGate

namespace JanusFormal
namespace P0EFTJanusBoundaryMicrostateIsotropicAverageCandidateGate

set_option autoImplicit false

structure BoundaryMicrostateIsotropicAverageCandidateGate where
  Sym4MicrostateCountEquals1001 : Prop
  IsotropicMacroProfileCountEquals70 : Prop
  BoundaryDensityMatrixSO3InvariantDerived : Prop
  VisibleObservablesDependOnlyOnTripletAverages : Prop
  EarlyRulerUsesMicrostateCountDerived : Prop

def BoundaryMicrostateAverageClosed
    (g : BoundaryMicrostateIsotropicAverageCandidateGate) : Prop :=
  g.Sym4MicrostateCountEquals1001 /\
  g.BoundaryDensityMatrixSO3InvariantDerived /\
  g.VisibleObservablesDependOnlyOnTripletAverages /\
  g.EarlyRulerUsesMicrostateCountDerived

def BoundaryMicrostateAverageFrontier
    (g : BoundaryMicrostateIsotropicAverageCandidateGate) : Prop :=
  g.Sym4MicrostateCountEquals1001 /\
  g.IsotropicMacroProfileCountEquals70 /\
  Not g.BoundaryDensityMatrixSO3InvariantDerived /\
  Not g.EarlyRulerUsesMicrostateCountDerived

theorem hidden_microstate_count_needs_state_law
    (g : BoundaryMicrostateIsotropicAverageCandidateGate)
    (hFrontier : BoundaryMicrostateAverageFrontier g) :
    Not (BoundaryMicrostateAverageClosed g) := by
  intro h
  exact hFrontier.2.2.1 h.2.1

end P0EFTJanusBoundaryMicrostateIsotropicAverageCandidateGate
end JanusFormal
