import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusAnormalSym4SpectralConditionGate

namespace JanusFormal
namespace P0EFTJanusAnormalWeightOriginCandidateMatrixGate

set_option autoImplicit false

structure ANormalWeightOriginCandidateMatrixGate where
  ScalarBoundaryChargeRejected : Prop
  PublishedM31BlockWeightsRejected : Prop
  TopologicalCycleOnlyRejected : Prop
  GenericBaseFiveWeightsRejectedAsUnanchored : Prop
  ActivePTSigmaNormalConnectionRouteOpen : Prop
  BoundaryModularStateRouteOpen : Prop
  FourDissociatedJanusWeightsDerived : Prop

def ANormalWeightOriginClosed
    (g : ANormalWeightOriginCandidateMatrixGate) : Prop :=
  g.ActivePTSigmaNormalConnectionRouteOpen /\
  g.FourDissociatedJanusWeightsDerived

def ANormalWeightOriginFrontier
    (g : ANormalWeightOriginCandidateMatrixGate) : Prop :=
  g.ScalarBoundaryChargeRejected /\
  g.PublishedM31BlockWeightsRejected /\
  g.TopologicalCycleOnlyRejected /\
  g.GenericBaseFiveWeightsRejectedAsUnanchored /\
  g.ActivePTSigmaNormalConnectionRouteOpen /\
  g.BoundaryModularStateRouteOpen /\
  Not g.FourDissociatedJanusWeightsDerived

theorem remaining_routes_do_not_close_without_janus_weights
    (g : ANormalWeightOriginCandidateMatrixGate)
    (hFrontier : ANormalWeightOriginFrontier g) :
    Not (ANormalWeightOriginClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2.2 h.2

end P0EFTJanusAnormalWeightOriginCandidateMatrixGate
end JanusFormal
