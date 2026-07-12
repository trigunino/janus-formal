import Mathlib

namespace JanusFormal
namespace P0EFTJanusMinimalChernSimonsLevelSelector

set_option autoImplicit false

/-- A positive Chern--Simons level minimal among all positive integer levels. -/
structure MinimalPositiveLevel where
  level : ℕ
  levelPositive : 0 < level
  minimalPositive : ∀ m : ℕ, 0 < m → level ≤ m

/-- The least positive integer level is exactly one. -/
theorem minimal_positive_level_is_one
    (s : MinimalPositiveLevel) :
    s.level = 1 := by
  have hLe : s.level ≤ 1 := s.minimalPositive 1 (by norm_num)
  omega

/-- PT-paired primitive levels are `+1` and `-1`. -/
structure PTPairedPrimitiveLevels where
  positiveLevel : ℕ
  negativeLevel : ℤ
  positiveLevelData : MinimalPositiveLevel
  samePositiveLevel : positiveLevel = positiveLevelData.level
  ptPairing : negativeLevel = -(positiveLevel : ℤ)


theorem paired_levels_are_plus_minus_one
    (s : PTPairedPrimitiveLevels) :
    s.positiveLevel = 1 /\ s.negativeLevel = -1 := by
  have hPositive : s.positiveLevel = 1 := by
    rw [s.samePositiveLevel]
    exact minimal_positive_level_is_one s.positiveLevelData
  constructor
  · exact hPositive
  · rw [s.ptPairing, hPositive]
    norm_num

/-- The total paired Chern--Simons level cancels. -/
theorem paired_primitive_levels_cancel
    (s : PTPairedPrimitiveLevels) :
    (s.positiveLevel : ℤ) + s.negativeLevel = 0 := by
  rw [s.ptPairing]
  omega

/--
A physical minimum-level theorem requires the effective action to increase with
`|k|` within the anomaly-allowed positive sectors; this ordering is not supplied
by integrality alone.
-/
structure LevelSelectionClosureStatus where
  anomalyAllowedPositiveLevelsDerived : Prop
  zeroLevelExcluded : Prop
  effectiveActionMonotoneInLevelMagnitude : Prop
  leastActionSectorExists : Prop
  primitivePositiveLevelSelected : Prop
  ptPairedNegativeLevelDerived : Prop


def levelSelectionClosed (s : LevelSelectionClosureStatus) : Prop :=
  s.anomalyAllowedPositiveLevelsDerived /\
  s.zeroLevelExcluded /\
  s.effectiveActionMonotoneInLevelMagnitude /\
  s.leastActionSectorExists /\
  s.primitivePositiveLevelSelected /\
  s.ptPairedNegativeLevelDerived

end P0EFTJanusMinimalChernSimonsLevelSelector
end JanusFormal
