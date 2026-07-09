import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusNormalConnectionToSym4AnormalBridgeGate

namespace JanusFormal
namespace P0EFTJanusActiveNormalConnectionPrimitivesAvailabilityGate

set_option autoImplicit false

structure ActiveNormalConnectionPrimitivesAvailabilityGate where
  SigmaUnitFrameAvailable : Prop
  UnitFrameIsLocalOnly : Prop
  ActiveCollarEmbeddingAvailable : Prop
  PartialUNormalFrameAvailable : Prop
  AmbientConnectionUAvailable : Prop
  ActiveOmegaPerpMaterializable : Prop

def ActiveNormalConnectionPrimitivesClosed
    (g : ActiveNormalConnectionPrimitivesAvailabilityGate) : Prop :=
  g.ActiveCollarEmbeddingAvailable /\
  g.PartialUNormalFrameAvailable /\
  g.AmbientConnectionUAvailable /\
  g.ActiveOmegaPerpMaterializable

def ActiveNormalConnectionPrimitivesFrontier
    (g : ActiveNormalConnectionPrimitivesAvailabilityGate) : Prop :=
  g.SigmaUnitFrameAvailable /\
  g.UnitFrameIsLocalOnly /\
  Not g.ActiveCollarEmbeddingAvailable /\
  Not g.PartialUNormalFrameAvailable /\
  Not g.AmbientConnectionUAvailable /\
  Not g.ActiveOmegaPerpMaterializable

theorem local_unit_frame_does_not_close_active_omega
    (g : ActiveNormalConnectionPrimitivesAvailabilityGate)
    (hFrontier : ActiveNormalConnectionPrimitivesFrontier g) :
    Not (ActiveNormalConnectionPrimitivesClosed g) := by
  intro h
  exact hFrontier.2.2.1 h.1

end P0EFTJanusActiveNormalConnectionPrimitivesAvailabilityGate
end JanusFormal
