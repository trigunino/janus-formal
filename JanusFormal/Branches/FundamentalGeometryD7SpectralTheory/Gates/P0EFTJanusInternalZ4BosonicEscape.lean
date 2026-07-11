import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusZ4StatisticsSelection
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusMinimalZ4AnomalyContent

namespace JanusFormal
namespace P0EFTJanusInternalZ4BosonicEscape

set_option autoImplicit false

open P0EFTJanusZ4StatisticsSelection
open P0EFTJanusMinimalZ4AnomalyContent
open P0EFTJanusPeriodicQuarterCompetition

/--
A field may carry two distinct order-four phases:

* `pinPhase`, constrained by `g_Pin^2=(-1)^F`;
* `internalPhase`, belonging to an independent internal `Z4`.

The determinant boundary condition sees the sum of the two additive phases.
-/
structure ProductZ4Charge where
  pinPhase : PinZ4Phase
  internalPhase : PinZ4Phase

/-- Total phase seen around the compact circle. -/
def totalPhase (charge : ProductZ4Charge) : PinZ4Phase :=
  charge.pinPhase + charge.internalPhase

/-- Statistics constrains only the central Pin phase. -/
def ProductZ4Compatible
    (statistics : FieldStatistics)
    (charge : ProductZ4Charge) : Prop :=
  PinZ4Compatible statistics charge.pinPhase

/-- A boson with trivial Pin phase and internal quarter charge. -/
def bosonicInternalQuarterCharge : ProductZ4Charge :=
  { pinPhase := periodicPhase
    internalPhase := quarterPhase }

/-- This field is fully compatible with bosonic statistics. -/
@[simp] theorem bosonic_internal_quarter_is_pin_compatible :
    ProductZ4Compatible FieldStatistics.boson
      bosonicInternalQuarterCharge := by
  native_decide

/-- Yet its total determinant phase is an exact quarter turn. -/
@[simp] theorem bosonic_internal_quarter_has_total_quarter_phase :
    totalPhase bosonicInternalQuarterCharge = quarterPhase := by
  native_decide

/-- The internal construction is genuinely different from assigning the central Pin quarter phase. -/
@[simp] theorem bosonic_internal_quarter_has_nonquarter_pin_phase :
    bosonicInternalQuarterCharge.pinPhase ≠ quarterPhase := by
  native_decide

/-- Five bosonic internal-quarter components. -/
def fiveBosonicInternalQuarterCharges
    (_index : Fin 5) : ProductZ4Charge :=
  bosonicInternalQuarterCharge

/-- Every component is bosonic-Pin-compatible and has total quarter holonomy. -/
theorem five_bosonic_internal_quarter_components_are_consistent :
    ∀ index : Fin 5,
      ProductZ4Compatible FieldStatistics.boson
        (fiveBosonicInternalQuarterCharges index) /\
      totalPhase (fiveBosonicInternalQuarterCharges index) = quarterPhase := by
  intro index
  exact ⟨bosonic_internal_quarter_is_pin_compatible,
    bosonic_internal_quarter_has_total_quarter_phase⟩

/-- The same-sign bosonic determinant algebra recovers the one-to-five stationary root. -/
@[simp] theorem internal_z4_bosonic_one_five_root :
    stationarityPolynomial 1 5 (1 / 3) = 0 := by
  exact third_is_one_to_five_stationary

/-- PT doubling preserves the same stationary root. -/
@[simp] theorem internal_z4_bosonic_two_ten_root :
    stationarityPolynomial 2 10 (1 / 3) = 0 := by
  rw [one_five_and_two_ten_stationarity_equivalent]
  exact internal_z4_bosonic_one_five_root

/--
The direct Pin-quarter and internal-quarter interpretations are exclusive for a
boson: the former violates the central statistics law, whereas the latter is
compatible.
-/
theorem bosonic_quarter_requires_independent_internal_z4 :
    Not (PinZ4Compatible FieldStatistics.boson quarterPhase) /\
      ProductZ4Compatible FieldStatistics.boson
        bosonicInternalQuarterCharge /\
      totalPhase bosonicInternalQuarterCharge = quarterPhase := by
  exact ⟨quarter_phase_is_not_bosonic,
    bosonic_internal_quarter_is_pin_compatible,
    bosonic_internal_quarter_has_total_quarter_phase⟩

/--
This construction rescues the determinant signs of the arithmetic `1:5`
candidate, but only by introducing a new internal symmetry not implied by the
Pin lift itself.  Its principal bundle, geometric origin, rank-five
representation and action on the bimetric/world-volume fields remain explicit
research obligations.
-/
structure InternalZ4BosonicPhysicalStatus where
  independentInternalZ4BundleConstructed : Prop
  internalQuarterHolonomyDerived : Prop
  commutingWithPinLiftProved : Prop
  rankFiveBosonicRepresentationDerived : Prop
  onePeriodicBosonicSectorDerived : Prop
  determinantSignsComputed : Prop
  ptDoublingWithoutDoubleCountingProved : Prop
  fullGaugeGhostComplexIncluded : Prop
  stableOneThirdRootSurvivesFullSpectrum : Prop
  finiteCountertermsFixedMicroscopically : Prop


def internalZ4BosonicPhysicalClosure
    (s : InternalZ4BosonicPhysicalStatus) : Prop :=
  s.independentInternalZ4BundleConstructed /\
  s.internalQuarterHolonomyDerived /\
  s.commutingWithPinLiftProved /\
  s.rankFiveBosonicRepresentationDerived /\
  s.onePeriodicBosonicSectorDerived /\
  s.determinantSignsComputed /\
  s.ptDoublingWithoutDoubleCountingProved /\
  s.fullGaugeGhostComplexIncluded /\
  s.stableOneThirdRootSurvivesFullSpectrum /\
  s.finiteCountertermsFixedMicroscopically

end P0EFTJanusInternalZ4BosonicEscape
end JanusFormal
