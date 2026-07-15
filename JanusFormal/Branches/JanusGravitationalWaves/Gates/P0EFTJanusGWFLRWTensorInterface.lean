import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWMinkowskiTensorGate
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusProportionalBimetricEquations

namespace JanusFormal
namespace P0EFTJanusGWFLRWTensorInterface

set_option autoImplicit false

noncomputable section

open P0EFTJanusPositiveBimetricLinearSpectrum
open P0EFTJanusProportionalBimetricEquations
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Conditional constraint-reduced TT equation on a common-time FLRW chart.
Its derivation from the complete Janus/P action is deliberately not assumed by
the definition. -/
def flrwTensorOperatorPlus
    (planckPlusSquared relativeMass hubble physicalWaveSquared
      hPlus hMinus hPlusDot hPlusDDot : ℝ) : ℝ :=
  hPlusDDot + 3 * hubble * hPlusDot + physicalWaveSquared * hPlus +
    weightedMassOperatorPlus
      planckPlusSquared relativeMass hPlus hMinus

def flrwTensorOperatorMinus
    (planckMinusSquared relativeMass hubble physicalWaveSquared
      hPlus hMinus hMinusDot hMinusDDot : ℝ) : ℝ :=
  hMinusDDot + 3 * hubble * hMinusDot + physicalWaveSquared * hMinus +
    weightedMassOperatorMinus
      planckMinusSquared relativeMass hPlus hMinus

/-- On the dynamically locked proportional branch, equal TT perturbations obey
the same massless FLRW wave operator in both sectors. -/
theorem diagonal_flrw_mode_is_common_and_massless
    (planckPlusSquared planckMinusSquared relativeMass hubble
      physicalWaveSquared h hDot hDDot : ℝ) :
    flrwTensorOperatorPlus planckPlusSquared relativeMass hubble
        physicalWaveSquared h h hDot hDDot =
      hDDot + 3 * hubble * hDot + physicalWaveSquared * h ∧
    flrwTensorOperatorMinus planckMinusSquared relativeMass hubble
        physicalWaveSquared h h hDot hDDot =
      hDDot + 3 * hubble * hDot + physicalWaveSquared * h := by
  constructor <;>
    simp [flrwTensorOperatorPlus, flrwTensorOperatorMinus,
      weightedMassOperatorPlus, weightedMassOperatorMinus]

/-- A positive PT-flat Bianchi factor forces the common Hubble rate required by
the proportional FLRW tensor interface. -/
theorem pt_flat_branch_supplies_common_hubble
    (beta1 beta2 plusHubble minusHubble : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2)
    (hConstraint :
      bianchiFactor (ptFlatCoefficients beta1 beta2) 1 *
        (plusHubble - minusHubble) = 0) :
    plusHubble = minusHubble :=
  pt_flat_bianchi_locks_expansions beta1 beta2 plusHubble minusHubble
    hBeta1 hBeta2 hConstraint

/-- Exact dependency ledger for promoting the conditional FLRW operator to a
derived Janus prediction. -/
structure PCompletionInputs where
  completeRenormalizedAction : Prop
  physicalFLRWBackgroundSolvesEulerLagrange : Prop
  secondVariationOnThatBackground : Prop
  lapseShiftConstraintsEliminated : Prop
  tensorKineticNormalizationDerived : Prop
  tensorMassMatrixDerived : Prop
  visibleMatterMetricDerived : Prop
  detectorResponseDerived : Prop

def pInputsReady (s : PCompletionInputs) : Prop :=
  s.completeRenormalizedAction ∧
  s.physicalFLRWBackgroundSolvesEulerLagrange ∧
  s.secondVariationOnThatBackground ∧
  s.lapseShiftConstraintsEliminated ∧
  s.tensorKineticNormalizationDerived ∧
  s.tensorMassMatrixDerived ∧
  s.visibleMatterMetricDerived ∧
  s.detectorResponseDerived

/-- The current algebra closes a conditional proportional-FLRW interface, not
the derivation of its coefficients from P. -/
structure ConditionalFLRWClosure where
  proportionalBackground : Prop
  commonHubbleDerived : Prop
  diagonalEquationReduced : Prop
  relativeEquationReduced : Prop
  pCompletion : PCompletionInputs

def conditionalInterfaceClosed (s : ConditionalFLRWClosure) : Prop :=
  s.proportionalBackground ∧
  s.commonHubbleDerived ∧
  s.diagonalEquationReduced ∧
  s.relativeEquationReduced

def physicalGW01FLRWClosed (s : ConditionalFLRWClosure) : Prop :=
  conditionalInterfaceClosed s ∧ pInputsReady s.pCompletion

theorem missing_complete_p_action_blocks_physical_gw01
    (s : ConditionalFLRWClosure)
    (hMissing : ¬s.pCompletion.completeRenormalizedAction) :
    ¬physicalGW01FLRWClosed s := by
  intro hClosed
  exact hMissing hClosed.2.1

end
end P0EFTJanusGWFLRWTensorInterface
end JanusFormal
