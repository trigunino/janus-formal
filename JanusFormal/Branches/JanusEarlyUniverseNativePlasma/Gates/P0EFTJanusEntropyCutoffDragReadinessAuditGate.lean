import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusEntropyCutoffToNativeSoundHorizonBridgeGate

namespace JanusFormal
namespace P0EFTJanusEntropyCutoffDragReadinessAuditGate

set_option autoImplicit false

structure EntropyCutoffDragReadinessAuditGate where
  EntropyCutoffAvailable : Prop
  CionFromCodataFirasAvailable : Prop
  PhotonDensityNormalizationAvailable : Prop
  BaryonNormalizationAvailable : Prop
  NativeHJAvailable : Prop
  DragPredictionExecutable : Prop

def EntropyCutoffDragReady
    (g : EntropyCutoffDragReadinessAuditGate) : Prop :=
  g.EntropyCutoffAvailable /\
  g.CionFromCodataFirasAvailable /\
  g.PhotonDensityNormalizationAvailable /\
  g.BaryonNormalizationAvailable /\
  g.NativeHJAvailable /\
  g.DragPredictionExecutable

def EntropyCutoffDragFrontier
    (g : EntropyCutoffDragReadinessAuditGate) : Prop :=
  g.EntropyCutoffAvailable /\
  g.CionFromCodataFirasAvailable /\
  g.PhotonDensityNormalizationAvailable /\
  Not g.BaryonNormalizationAvailable /\
  Not g.NativeHJAvailable /\
  Not g.DragPredictionExecutable

theorem photon_inputs_do_not_make_drag_executable
    (g : EntropyCutoffDragReadinessAuditGate)
    (hFrontier : EntropyCutoffDragFrontier g) :
    Not (EntropyCutoffDragReady g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusEntropyCutoffDragReadinessAuditGate
end JanusFormal
