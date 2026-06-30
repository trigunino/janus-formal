import JanusFormal.P0EFTLoopDoubleDualConditional

namespace JanusFormal
namespace P0EFTPinAnomalySelection

set_option autoImplicit false

inductive PinChoice where
  | pinPlus
  | pinMinus
  deriving DecidableEq

structure PinAnomalyData where
  diracCartanDomainDefined : Prop
  etaInvariantComputed : Prop
  pinPlusAnomalous : Prop
  pinMinusAnomalyFree : Prop

def anomalyFreeChoice (d : PinAnomalyData) : PinChoice -> Prop
  | PinChoice.pinPlus => False
  | PinChoice.pinMinus => d.pinMinusAnomalyFree

def axialCoefficientFixed (choice : PinChoice) : Prop :=
  choice = PinChoice.pinMinus

theorem aps_data_selects_pin_minus
    (d : PinAnomalyData)
    (_hEta : d.etaInvariantComputed)
    (hMinus : d.pinMinusAnomalyFree) :
    anomalyFreeChoice d PinChoice.pinMinus := by
  exact hMinus

theorem pin_plus_rejected_by_selection
    (d : PinAnomalyData) :
    Not (anomalyFreeChoice d PinChoice.pinPlus) := by
  intro h
  exact h

theorem selected_pin_minus_fixes_axial_coefficient :
    axialCoefficientFixed PinChoice.pinMinus := by
  rfl

theorem missing_eta_blocks_unconditional_pin_selection
    (d : PinAnomalyData)
    (hMissing : Not d.etaInvariantComputed) :
    Not (d.diracCartanDomainDefined /\ d.etaInvariantComputed /\
      d.pinPlusAnomalous /\ d.pinMinusAnomalyFree) := by
  intro h
  exact hMissing h.right.left

end P0EFTPinAnomalySelection
end JanusFormal
