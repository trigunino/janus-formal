import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusHolonomyDeterminantNoGo
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusZ4HolonomyEtaGap

namespace JanusFormal
namespace P0EFTJanusPairedZ4DeterminantNoGo

set_option autoImplicit false

open P0EFTJanusHolonomyDeterminantNoGo
open P0EFTJanusZ4HolonomyEtaGap

/-- PT-related folds have the same positive determinant magnitude mode. -/
structure PairedQuarterMode where
  positiveFold : PositiveQuarterMode
  negativeFold : PositiveQuarterMode
  equalWeight : negativeFold.weight = positiveFold.weight
  equalRadialMagnitude : negativeFold.radial = positiveFold.radial

/-- The paired determinant derivative is twice the one-fold derivative. -/
theorem paired_quarter_derivative_doubles
    (mode : PairedQuarterMode) :
    quarterModeLogDerivative mode.positiveFold +
        quarterModeLogDerivative mode.negativeFold =
      2 * quarterModeLogDerivative mode.positiveFold := by
  have hMode : mode.negativeFold = mode.positiveFold := by
    cases mode.positiveFold with
    | mk positiveWeight positiveRadial hPositiveWeight hPositiveRadial =>
      cases mode.negativeFold with
      | mk negativeWeight negativeRadial hNegativeWeight hNegativeRadial =>
        simp_all
  rw [hMode]
  ring

/-- Hence the PT pair is still strictly monotone in determinant magnitude. -/
theorem paired_quarter_derivative_strictly_negative
    (mode : PairedQuarterMode) :
    quarterModeLogDerivative mode.positiveFold +
        quarterModeLogDerivative mode.negativeFold < 0 := by
  rw [paired_quarter_derivative_doubles mode]
  have hOne := quarter_mode_log_derivative_negative mode.positiveFold
  nlinarith

/-- Flipping to the overall fermionic sign reverses but does not remove monotonicity. -/
theorem paired_fermionic_quarter_derivative_strictly_positive
    (mode : PairedQuarterMode) :
    0 < -(
      quarterModeLogDerivative mode.positiveFold +
        quarterModeLogDerivative mode.negativeFold) := by
  exact neg_pos.mpr (paired_quarter_derivative_strictly_negative mode)

/--
Parity-odd eta values cancel between opposite monopole charges, while the
parity-even determinant slopes add with the same sign.
-/
theorem eta_cancels_while_determinant_slope_adds
    (chernNumber : ℤ)
    (mode : PairedQuarterMode) :
    chiralReducedEtaModel chernNumber (1 / 4) +
        chiralReducedEtaModel (-chernNumber) (1 / 4) = 0 /\
      quarterModeLogDerivative mode.positiveFold +
        quarterModeLogDerivative mode.negativeFold < 0 := by
  constructor
  · exact pt_paired_chiral_eta_cancels chernNumber (1 / 4)
  · exact paired_quarter_derivative_strictly_negative mode

/--
This closes a decisive no-go: the two PT-related primitive `Z4` fermion towers
can cancel the eta/anomaly phase, but their determinant magnitude cannot by
itself generate the spectral-isotropy vacuum or a finite circle modulus.  A
second holonomy/statistics sector, interaction, or local geometric potential is
mathematically required.
-/
structure PairedZ4CompletionStatus where
  globalPinLiftDerived : Prop
  pairedEtaCancellationRegularized : Prop
  pairedDeterminantMagnitudeDerived : Prop
  monotoneRunawayProved : Prop
  additionalCompetingSectorDerived : Prop
  fullRenormalizedPotentialBoundedBelow : Prop
  finiteModulusMinimumDerived : Prop
  alphaLockRecoveredAtMinimum : Prop


def pairedZ4CompletionClosed
    (s : PairedZ4CompletionStatus) : Prop :=
  s.globalPinLiftDerived /\
  s.pairedEtaCancellationRegularized /\
  s.pairedDeterminantMagnitudeDerived /\
  s.monotoneRunawayProved /\
  s.additionalCompetingSectorDerived /\
  s.fullRenormalizedPotentialBoundedBelow /\
  s.finiteModulusMinimumDerived /\
  s.alphaLockRecoveredAtMinimum

end P0EFTJanusPairedZ4DeterminantNoGo
end JanusFormal
