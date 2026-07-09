import JanusFormal.Legacy.P0EFT.Gates.P0EFTVlasovTorsionCoupling

namespace JanusFormal
namespace P0EFTSpinlessMomentsSlipTarget

set_option autoImplicit false

structure SpinlessMomentsSlip where
  densityMomentWritten : Prop
  continuityConditionallyClosed : Prop
  fluxEulerStructured : Prop
  pressurePiMomentsDefined : Prop
  piIsotropyNotAssumed : Prop
  slipFormulaEncoded : Prop
  slipFormulaDerivedFromJumps : Prop
  lensingGrowthSourcesClosed : Prop

def spinlessMomentsStructured (s : SpinlessMomentsSlip) : Prop :=
  s.densityMomentWritten /\
  s.continuityConditionallyClosed /\
  s.fluxEulerStructured /\
  s.pressurePiMomentsDefined /\
  s.piIsotropyNotAssumed

def spinlessObservableSourcesClosed (s : SpinlessMomentsSlip) : Prop :=
  spinlessMomentsStructured s /\
  s.slipFormulaEncoded /\
  s.slipFormulaDerivedFromJumps /\
  s.lensingGrowthSourcesClosed

theorem spinless_moments_are_structured_without_pi_zero_assumption
    (s : SpinlessMomentsSlip)
    (hDensity : s.densityMomentWritten)
    (hCont : s.continuityConditionallyClosed)
    (hFlux : s.fluxEulerStructured)
    (hPi : s.pressurePiMomentsDefined)
    (hNoIso : s.piIsotropyNotAssumed) :
    spinlessMomentsStructured s := by
  exact And.intro hDensity
    (And.intro hCont
      (And.intro hFlux
        (And.intro hPi hNoIso)))

theorem missing_slip_derivation_blocks_observables
    (s : SpinlessMomentsSlip)
    (hMissing : Not s.slipFormulaDerivedFromJumps) :
    Not (spinlessObservableSourcesClosed s) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTSpinlessMomentsSlipTarget
end JanusFormal
