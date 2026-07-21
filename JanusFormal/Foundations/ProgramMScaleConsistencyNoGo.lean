import Mathlib.Tactic

/-!
# MF-MAN-012: dimensionless scale consistency does not resolve the conflict

The constants are the exact independent calibrations from the first
MF-MAN-010 volume/time conflict.
-/

namespace JanusFormal.ProgramM

def scaleConsistency (density chainToTimeSquared : ℚ) : ℚ :=
  2 * density * chainToTimeSquared

theorem firstConflict_timePreferred_consistency :
    scaleConsistency (2 / 3) (9 / 4) = 3 := by
  norm_num [scaleConsistency]

theorem firstConflict_volumePreferred_consistency :
    scaleConsistency (3 / 4) 2 = 3 := by
  norm_num [scaleConsistency]

theorem firstConflict_consistency_equal :
    scaleConsistency (2 / 3) (9 / 4) = scaleConsistency (3 / 4) 2 := by
  norm_num [scaleConsistency]

theorem firstConflict_fails_exact_asymptotic_identity :
    scaleConsistency (2 / 3) (9 / 4) ≠ 1 ∧
      scaleConsistency (3 / 4) 2 ≠ 1 := by
  norm_num [scaleConsistency]

end JanusFormal.ProgramM
