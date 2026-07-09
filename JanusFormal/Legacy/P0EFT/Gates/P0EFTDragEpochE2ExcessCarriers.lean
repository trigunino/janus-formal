namespace JanusFormal
namespace P0EFTDragEpochE2ExcessCarriers

set_option autoImplicit false

structure DragEpochE2ExcessCarriers where
  soundHorizonDragTargetEncoded : Prop
  homogeneousA6SpinCarrierRejected : Prop
  radiationLikeHolstPlasmaCarrierSelected : Prop
  radiationLikeHolstPlasmaDerived : Prop

def dragCarrierDiagnosticReady (d : DragEpochE2ExcessCarriers) : Prop :=
  d.soundHorizonDragTargetEncoded /\
  d.homogeneousA6SpinCarrierRejected /\
  d.radiationLikeHolstPlasmaCarrierSelected

def dragCarrierNoFitReady (d : DragEpochE2ExcessCarriers) : Prop :=
  dragCarrierDiagnosticReady d /\
  d.radiationLikeHolstPlasmaDerived

theorem carrier_diagnostic_selects_plasma_route
    (d : DragEpochE2ExcessCarriers)
    (hSound : d.soundHorizonDragTargetEncoded)
    (hReject : d.homogeneousA6SpinCarrierRejected)
    (hSelect : d.radiationLikeHolstPlasmaCarrierSelected) :
    dragCarrierDiagnosticReady d := by
  exact And.intro hSound (And.intro hReject hSelect)

theorem missing_plasma_derivation_blocks_no_fit
    (d : DragEpochE2ExcessCarriers)
    (hMissing : Not d.radiationLikeHolstPlasmaDerived) :
    Not (dragCarrierNoFitReady d) := by
  intro h
  exact hMissing h.right

end P0EFTDragEpochE2ExcessCarriers
end JanusFormal
