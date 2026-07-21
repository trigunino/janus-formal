import Mathlib.Tactic

/-!
# MF-MAN-011: no unit-free scalar choice in the finite volume/time conflict

The exact residuals come from the first MF-MAN-010 witness.  The theorem does
not interpret either diagnostic physically; it records the extra convention
introduced by a weighted scalar loss.
-/

namespace JanusFormal.ProgramM

def weightedDiagnosticLoss (weight volumeLoss timeLoss : ℚ) : ℚ :=
  weight * volumeLoss + (1 - weight) * timeLoss

def volumePreferredVolumeLoss : ℚ := 119 / 32
def volumePreferredTimeLoss : ℚ := 22
def timePreferredVolumeLoss : ℚ := 37 / 9
def timePreferredTimeLoss : ℚ := 43 / 4

theorem finiteWitness_volume_prefers_volumeCandidate :
    volumePreferredVolumeLoss < timePreferredVolumeLoss := by
  norm_num [volumePreferredVolumeLoss, timePreferredVolumeLoss]

theorem finiteWitness_time_prefers_timeCandidate :
    timePreferredTimeLoss < volumePreferredTimeLoss := by
  norm_num [volumePreferredTimeLoss, timePreferredTimeLoss]

/-- A weighted sum chooses the volume-preferred candidate exactly after an
externally supplied threshold. -/
theorem finiteWitness_weighted_volumeCandidate_iff (weight : ℚ) :
    weightedDiagnosticLoss weight volumePreferredVolumeLoss
        volumePreferredTimeLoss <
      weightedDiagnosticLoss weight timePreferredVolumeLoss
        timePreferredTimeLoss ↔
      3240 / 3353 < weight := by
  norm_num [weightedDiagnosticLoss, volumePreferredVolumeLoss,
    volumePreferredTimeLoss, timePreferredVolumeLoss,
    timePreferredTimeLoss]
  constructor <;> intro h <;> linarith

/-- With a 99% nominal volume weight, the unscaled loss selects the
volume-preferred candidate. -/
theorem finiteWitness_unscaled_selects_volumeCandidate :
    weightedDiagnosticLoss (99 / 100) volumePreferredVolumeLoss
        volumePreferredTimeLoss <
      weightedDiagnosticLoss (99 / 100) timePreferredVolumeLoss
        timePreferredTimeLoss := by
  norm_num [weightedDiagnosticLoss, volumePreferredVolumeLoss,
    volumePreferredTimeLoss, timePreferredVolumeLoss,
    timePreferredTimeLoss]

/-- Expressing the time loss in units scaled by 100 reverses that choice while
the underlying pair of candidates is unchanged. -/
theorem finiteWitness_rescaled_selects_timeCandidate :
    weightedDiagnosticLoss (99 / 100) timePreferredVolumeLoss
        (100 * timePreferredTimeLoss) <
      weightedDiagnosticLoss (99 / 100) volumePreferredVolumeLoss
        (100 * volumePreferredTimeLoss) := by
  norm_num [weightedDiagnosticLoss, volumePreferredVolumeLoss,
    volumePreferredTimeLoss, timePreferredVolumeLoss,
    timePreferredTimeLoss]

end JanusFormal.ProgramM
