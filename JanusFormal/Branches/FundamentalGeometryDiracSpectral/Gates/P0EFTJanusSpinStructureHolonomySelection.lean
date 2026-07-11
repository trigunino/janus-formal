import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpinStructureHolonomySelection

set_option autoImplicit false

/-- Spin structures on the compact circle. -/
inductive CircleSpinStructure where
  | periodic
  | antiperiodic
  deriving DecidableEq, Repr

/-- Fractional momentum shift contributed by the spin structure. -/
def spinShift : CircleSpinStructure → ℝ
  | CircleSpinStructure.periodic => 0
  | CircleSpinStructure.antiperiodic => 1 / 2

/-- Combined fermionic holonomy in a fixed real representative. -/
def combinedHolonomy
    (spin : CircleSpinStructure) (gaugeHolonomy : ℝ) : ℝ :=
  spinShift spin + gaugeHolonomy

/-- Periodic spin structure converts selected total half holonomy to gauge half holonomy. -/
theorem periodic_total_half_selects_gauge_half
    (gaugeHolonomy : ℝ)
    (hSelected :
      combinedHolonomy CircleSpinStructure.periodic gaugeHolonomy = 1 / 2) :
    gaugeHolonomy = 1 / 2 := by
  simpa [combinedHolonomy, spinShift] using hSelected

/-- Antiperiodic spin structure converts selected total half holonomy to zero gauge holonomy. -/
theorem antiperiodic_total_half_selects_zero_gauge_holonomy
    (gaugeHolonomy : ℝ)
    (hSelected :
      combinedHolonomy CircleSpinStructure.antiperiodic gaugeHolonomy = 1 / 2) :
    gaugeHolonomy = 0 := by
  unfold combinedHolonomy spinShift at hSelected
  linarith

/-- The two spin structures need different gauge representatives for the same spectrum. -/
theorem selected_gauge_representatives_are_distinct :
    (1 / 2 : ℝ) ≠ 0 := by
  norm_num

/--
The determinant selects a combined fermionic boundary condition.  A global Pin
lift and its restriction to the throat circle must determine the spin structure
before the selected gauge holonomy is interpreted physically.
-/
structure SpinHolonomyClosureStatus where
  globalPinStructureConstructed : Prop
  pinRestrictionToThroatDerived : Prop
  circleSpinStructureDerived : Prop
  gaugeHolonomyDefinedModuloIntegers : Prop
  combinedFermionHolonomyDerived : Prop
  determinantSelectsCombinedHalf : Prop
  physicalGaugeRepresentativeDerived : Prop
  largeGaugeEquivalenceChecked : Prop


def spinHolonomyClosure (s : SpinHolonomyClosureStatus) : Prop :=
  s.globalPinStructureConstructed /\
  s.pinRestrictionToThroatDerived /\
  s.circleSpinStructureDerived /\
  s.gaugeHolonomyDefinedModuloIntegers /\
  s.combinedFermionHolonomyDerived /\
  s.determinantSelectsCombinedHalf /\
  s.physicalGaugeRepresentativeDerived /\
  s.largeGaugeEquivalenceChecked

end P0EFTJanusSpinStructureHolonomySelection
end JanusFormal
