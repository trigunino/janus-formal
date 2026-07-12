import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpinTwoDimensionalityAudit

set_option autoImplicit false

/-- Standard physical polarization count for a massive spin-two field in dimension `d`. -/
def massiveSpinTwoPolarizationsIn
    (spacetimeDimension : ℕ) : ℕ :=
  ((spacetimeDimension + 1) * (spacetimeDimension - 2)) / 2

/-- Standard physical polarization count for a massless spin-two field in dimension `d`. -/
def masslessSpinTwoPolarizationsIn
    (spacetimeDimension : ℕ) : ℕ :=
  (spacetimeDimension * (spacetimeDimension - 3)) / 2

@[simp] theorem massive_spin_two_in_three_dimensions_has_two_polarizations :
    massiveSpinTwoPolarizationsIn 3 = 2 := by
  norm_num [massiveSpinTwoPolarizationsIn]

@[simp] theorem massive_spin_two_in_four_dimensions_has_five_polarizations :
    massiveSpinTwoPolarizationsIn 4 = 5 := by
  norm_num [massiveSpinTwoPolarizationsIn]

@[simp] theorem massless_spin_two_in_three_dimensions_has_no_local_polarizations :
    masslessSpinTwoPolarizationsIn 3 = 0 := by
  norm_num [masslessSpinTwoPolarizationsIn]

@[simp] theorem massless_spin_two_in_four_dimensions_has_two_polarizations :
    masslessSpinTwoPolarizationsIn 4 = 2 := by
  norm_num [masslessSpinTwoPolarizationsIn]

/-- A determinant interpreted intrinsically on the three-dimensional throat cannot obtain weight five from one massive spin-two field. -/
structure ThroatMassiveSpinTwoWeightClaim where
  determinantDimension : ℕ
  determinantWeight : ℕ
  intrinsicThroatDimension : determinantDimension = 3
  onePhysicalMassiveSpinTwo :
    determinantWeight =
      massiveSpinTwoPolarizationsIn determinantDimension
  claimedWeightFive : determinantWeight = 5

/-- The one-field, intrinsic-three-dimensional, weight-five interpretation is inconsistent. -/
theorem no_intrinsic_throat_single_spin_two_weight_five :
    Not (∃ _s : ThroatMassiveSpinTwoWeightClaim, True) := by
  rintro ⟨s, _⟩
  have hWeightTwo : s.determinantWeight = 2 := by
    rw [s.onePhysicalMassiveSpinTwo,
      s.intrinsicThroatDimension]
    exact massive_spin_two_in_three_dimensions_has_two_polarizations
  have hWeightFive : s.determinantWeight = 5 := s.claimedWeightFive
  rw [hWeightTwo] at hWeightFive
  norm_num at hWeightFive

/-- The number five is instead the four-dimensional bulk massive-spin-two count. -/
theorem five_is_bulk_four_dimensional_spin_two_count :
    massiveSpinTwoPolarizationsIn 4 = 5 :=
  massive_spin_two_in_four_dimensions_has_five_polarizations

/--
Therefore a weight-five determinant on `S2 x S1` has only three honest
interpretations:

1. five independent/internal world-volume components;
2. a bulk four-dimensional determinant reduced to the throat with a proved
   boundary spectral map;
3. an effective gauge/ghost supertrace whose net weight is five.

It cannot be justified merely by citing one physical massive spin-two field on
the three-dimensional world-volume.
-/
structure WeightFiveDimensionalExitStatus where
  rankFiveWorldvolumeMultipletDerived : Prop
  bulkFourDimensionalDeterminantReduced : Prop
  gaugeGhostSupertraceWeightFiveDerived : Prop
  atLeastOneDimensionalExitDerived : Prop
  noDimensionMixingOrDoubleCountingProved : Prop


def weightFiveDimensionalAuditClosed
    (s : WeightFiveDimensionalExitStatus) : Prop :=
  (s.rankFiveWorldvolumeMultipletDerived \/
    s.bulkFourDimensionalDeterminantReduced \/
    s.gaugeGhostSupertraceWeightFiveDerived) /\
  s.atLeastOneDimensionalExitDerived /\
  s.noDimensionMixingOrDoubleCountingProved

end P0EFTJanusSpinTwoDimensionalityAudit
end JanusFormal
