import Mathlib

namespace JanusFormal
namespace P0EFTJanusZ4ShiftedLeeHierarchy

set_option autoImplicit false

/--
Quarter-shifted logarithmic period.  The numerator is interpreted modulo four
only after choosing the physical Pin/Z4 sector.
-/
def shiftedLeePeriod
    (piConstant : ℝ)
    (integerLevel quarterNumerator : ℕ) : ℝ :=
  2 * piConstant *
    ((integerLevel : ℝ) + (quarterNumerator : ℝ) / 4)

/-- Moving by one Z4 sector shifts the period by `pi/2`. -/
theorem shifted_period_successor
    (piConstant : ℝ)
    (integerLevel quarterNumerator : ℕ) :
    shiftedLeePeriod piConstant integerLevel (quarterNumerator + 1) =
      shiftedLeePeriod piConstant integerLevel quarterNumerator +
        piConstant / 2 := by
  unfold shiftedLeePeriod
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- Four quarter shifts equal one full integral Lee level. -/
theorem four_quarter_shifts_equal_next_integer_level
    (piConstant : ℝ)
    (integerLevel quarterNumerator : ℕ) :
    shiftedLeePeriod piConstant integerLevel (quarterNumerator + 4) =
      shiftedLeePeriod piConstant (integerLevel + 1) quarterNumerator := by
  unfold shiftedLeePeriod
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- Planck- or bulk-anchored scale attached to the shifted period. -/
noncomputable def shiftedAlphaScale
    (uvLength piConstant : ℝ)
    (integerLevel quarterNumerator : ℕ) : ℝ :=
  uvLength / 2 *
    Real.exp (shiftedLeePeriod piConstant integerLevel quarterNumerator)

/-- Adjacent Z4 sectors differ by `exp(pi/2)`. -/
theorem adjacent_z4_sectors_have_quarter_exponential_spacing
    (uvLength piConstant : ℝ)
    (integerLevel quarterNumerator : ℕ) :
    shiftedAlphaScale uvLength piConstant integerLevel
        (quarterNumerator + 1) =
      Real.exp (piConstant / 2) *
        shiftedAlphaScale uvLength piConstant integerLevel quarterNumerator := by
  unfold shiftedAlphaScale
  rw [shifted_period_successor, Real.exp_add]
  ring

/-- Four sector steps reproduce the next integral level exactly. -/
theorem four_z4_steps_equal_next_integer_scale
    (uvLength piConstant : ℝ)
    (integerLevel quarterNumerator : ℕ) :
    shiftedAlphaScale uvLength piConstant integerLevel
        (quarterNumerator + 4) =
      shiftedAlphaScale uvLength piConstant (integerLevel + 1)
        quarterNumerator := by
  unfold shiftedAlphaScale
  rw [four_quarter_shifts_equal_next_integer_level]

/-- The four genuine representatives of the Z4 sector. -/
def IsCanonicalZ4Sector (quarterNumerator : ℕ) : Prop :=
  quarterNumerator < 4

/--
The Z4 refinement reduces the spacing between neighboring sectors from
`exp(2*pi)` to `exp(pi/2)`, but it still needs a theorem selecting the integral
level and the Z4 residue.
-/
structure Z4ShiftedHierarchyStatus where
  leeClassQuantized : Prop
  pinLiftedZ4Constructed : Prop
  quarterShiftFromEtaInvariantDerived : Prop
  canonicalSectorSelected : Prop
  integerLevelSelected : Prop
  uvAnchorDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaDerived : Prop


def z4ShiftedHierarchyClosed
    (s : Z4ShiftedHierarchyStatus) : Prop :=
  s.leeClassQuantized /\
  s.pinLiftedZ4Constructed /\
  s.quarterShiftFromEtaInvariantDerived /\
  s.canonicalSectorSelected /\
  s.integerLevelSelected /\
  s.uvAnchorDerived /\
  s.noObservedScaleImported /\
  s.absoluteAlphaDerived

end P0EFTJanusZ4ShiftedLeeHierarchy
end JanusFormal
