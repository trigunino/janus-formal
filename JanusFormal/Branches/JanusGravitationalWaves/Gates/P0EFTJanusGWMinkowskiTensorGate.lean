import JanusFormal.Experimental.JanusPLinearizedEinsteinTTDispersion
import JanusFormal.Experimental.JanusPTensorFourierConstraintReducedBridge

namespace JanusFormal
namespace P0EFTJanusGWMinkowskiTensorGate

set_option autoImplicit false

noncomputable section

open P0EFTJanusPositiveBimetricLinearSpectrum
open P0EFTJanusLinearizedEinsteinBianchiSymbol
open JanusPLinearizedEinsteinTTDispersion
open JanusPTensorFourierConstraintReducedBridge

/-- Squared frequency of the common TT channel. -/
def diagonalFrequencySquared (waveNumber : ℝ) : ℝ := waveNumber ^ 2

/-- Squared frequency of the weighted relative TT channel. -/
def relativeFrequencySquared
    (planckPlusSquared planckMinusSquared relativeMass waveNumber : ℝ) : ℝ :=
  waveNumber ^ 2 +
    weightedRelativeEigenvalue
      planckPlusSquared planckMinusSquared relativeMass

/-- The explicit Einstein principal symbol fixes the common TT light cone. -/
theorem diagonal_tt_dispersion_from_einstein_symbol
    (omega waveNumber amplitude : ℝ) (hAmplitude : amplitude ≠ 0) :
    linearizedEinsteinSymbol (waveCovector omega waveNumber)
        (ttPolarization amplitude) 1 2 = 0 ↔
      omega ^ 2 = diagonalFrequencySquared waveNumber := by
  simpa [diagonalFrequencySquared] using
    vacuum_tt_symbol_eq_zero_iff_dispersion
      omega waveNumber amplitude hAmplitude

/-- The P interaction Hessian and the two positive Einstein weights give the
weighted relative TT eigenfrequency. -/
theorem relative_tt_spatial_eigenvalue
    (planckPlusSquared planckMinusSquared relativeMass waveNumber h : ℝ)
    (hPlus : planckPlusSquared ≠ 0)
    (hMinus : planckMinusSquared ≠ 0) :
    tensorFourierOperatorPlus planckPlusSquared relativeMass waveNumber
        (planckMinusSquared * h) (-planckPlusSquared * h) =
      relativeFrequencySquared planckPlusSquared planckMinusSquared
          relativeMass waveNumber * (planckMinusSquared * h) ∧
    tensorFourierOperatorMinus planckMinusSquared relativeMass waveNumber
        (planckMinusSquared * h) (-planckPlusSquared * h) =
      relativeFrequencySquared planckPlusSquared planckMinusSquared
          relativeMass waveNumber * (-planckPlusSquared * h) := by
  simpa [relativeFrequencySquared] using
    weighted_relative_tensor_dispersion
      planckPlusSquared planckMinusSquared relativeMass waveNumber h
      hPlus hMinus

/-- Positive kinetic weights and positive relative interaction mass exclude a
tachyonic relative TT frequency on the Minkowski branch. -/
theorem relative_tt_frequency_squared_positive
    (planckPlusSquared planckMinusSquared relativeMass waveNumber : ℝ)
    (hPlanckPlus : 0 < planckPlusSquared)
    (hPlanckMinus : 0 < planckMinusSquared)
    (hMass : 0 < relativeMass) :
    0 < relativeFrequencySquared planckPlusSquared planckMinusSquared
      relativeMass waveNumber := by
  simpa [relativeFrequencySquared] using
    weighted_relative_tensor_frequency_positive
      planckPlusSquared planckMinusSquared relativeMass waveNumber
      hPlanckPlus hPlanckMinus hMass

/-- Exact current boundary of GW01: Minkowski TT is closed, whereas FLRW,
source projection and detector coupling remain separate obligations. -/
structure GW01Status where
  minkowskiEinsteinTTSymbolDerived : Prop
  relativeInteractionHessianDerived : Prop
  diagonalMasslessDispersionDerived : Prop
  relativeMassiveDispersionDerived : Prop
  positiveTensorKineticWeightsDerived : Prop
  flrwTensorActionDerived : Prop
  visibleMatterDetectorCouplingDerived : Prop

def minkowskiTTClosed (s : GW01Status) : Prop :=
  s.minkowskiEinsteinTTSymbolDerived ∧
  s.relativeInteractionHessianDerived ∧
  s.diagonalMasslessDispersionDerived ∧
  s.relativeMassiveDispersionDerived ∧
  s.positiveTensorKineticWeightsDerived

def fullGW01Closed (s : GW01Status) : Prop :=
  minkowskiTTClosed s ∧
  s.flrwTensorActionDerived ∧
  s.visibleMatterDetectorCouplingDerived

theorem minkowski_does_not_close_full_gw01
    (s : GW01Status)
    (hFLRW : ¬s.flrwTensorActionDerived) :
    ¬fullGW01Closed s := by
  intro hFull
  exact hFLRW hFull.2.1

end
end P0EFTJanusGWMinkowskiTensorGate
end JanusFormal
