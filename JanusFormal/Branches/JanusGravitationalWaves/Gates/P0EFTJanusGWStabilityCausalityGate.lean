import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWFLRWTensorInterface
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusCosmologicalHiguchiGate

namespace JanusFormal
namespace P0EFTJanusGWStabilityCausalityGate

set_option autoImplicit false

noncomputable section

open P0EFTJanusCosmologicalHiguchiGate

/-- Squared group velocity for `omega²=k²+m²`, avoiding a square-root
convention at `omega=0`. -/
def massiveGroupVelocitySquared (waveNumber massSquared : ℝ) : ℝ :=
  waveNumber ^ 2 / (waveNumber ^ 2 + massSquared)

/-- A positive mass gap makes the relative TT mode strictly subluminal at every
finite wave number. -/
theorem massive_group_velocity_strictly_between_zero_and_one
    (waveNumber massSquared : ℝ)
    (hMass : 0 < massSquared) :
    0 ≤ massiveGroupVelocitySquared waveNumber massSquared ∧
      massiveGroupVelocitySquared waveNumber massSquared < 1 := by
  have hDenom : 0 < waveNumber ^ 2 + massSquared :=
    add_pos_of_nonneg_of_pos (sq_nonneg waveNumber) hMass
  constructor
  · exact div_nonneg (sq_nonneg waveNumber) (le_of_lt hDenom)
  · unfold massiveGroupVelocitySquared
    rw [div_lt_one hDenom]
    linarith

/-- The massless diagonal TT mode propagates exactly on the unit light cone for
nonzero wave number. -/
theorem diagonal_group_velocity_squared_is_one
    (waveNumber : ℝ) (hWave : waveNumber ≠ 0) :
    massiveGroupVelocitySquared waveNumber 0 = 1 := by
  unfold massiveGroupVelocitySquared
  simpa using (div_self (pow_ne_zero 2 hWave))

/-- The massive group velocity approaches the light cone algebraically: its
deficit is exactly `m²/(k²+m²)`. -/
theorem massive_group_velocity_deficit
    (waveNumber massSquared : ℝ)
    (hDenom : waveNumber ^ 2 + massSquared ≠ 0) :
    1 - massiveGroupVelocitySquared waveNumber massSquared =
      massSquared / (waveNumber ^ 2 + massSquared) := by
  unfold massiveGroupVelocitySquared
  field_simp
  ring

/-- Nonnegative mass excludes a tachyonic Fourier frequency. -/
theorem massive_dispersion_nonnegative
    (waveNumber massSquared : ℝ) (hMass : 0 ≤ massSquared) :
    0 ≤ waveNumber ^ 2 + massSquared :=
  add_nonneg (sq_nonneg waveNumber) hMass

/-- A strictly positive Higuchi gap places the effective massive mode above
the de Sitter helicity-zero boundary. This remains conditional on P deriving
the effective mass and background Hubble rate. -/
theorem positive_higuchi_gate_implies_mass_above_boundary
    (effectiveMassSquared hubbleSquared : ℝ)
    (hGap : 0 < higuchiGap effectiveMassSquared hubbleSquared) :
    2 * hubbleSquared < effectiveMassSquared := by
  unfold higuchiGap at hGap
  linarith

structure GW02Status where
  positiveTensorKineticWeights : Prop
  nonnegativeRelativeMassSquared : Prop
  minkowskiNoTachyonDerived : Prop
  finiteMomentumSubluminalityDerived : Prop
  diagonalLuminalityDerived : Prop
  effectiveFLRWMassDerivedFromP : Prop
  physicalHubbleHistoryDerivedFromP : Prop
  uniformHiguchiGapDerived : Prop

def reducedMinkowskiGW02Closed (s : GW02Status) : Prop :=
  s.positiveTensorKineticWeights ∧
  s.nonnegativeRelativeMassSquared ∧
  s.minkowskiNoTachyonDerived ∧
  s.finiteMomentumSubluminalityDerived ∧
  s.diagonalLuminalityDerived

def physicalFLRWGW02Closed (s : GW02Status) : Prop :=
  reducedMinkowskiGW02Closed s ∧
  s.effectiveFLRWMassDerivedFromP ∧
  s.physicalHubbleHistoryDerivedFromP ∧
  s.uniformHiguchiGapDerived

theorem missing_p_background_blocks_physical_gw02
    (s : GW02Status)
    (hMissing : ¬s.physicalHubbleHistoryDerivedFromP) :
    ¬physicalFLRWGW02Closed s := by
  intro hClosed
  exact hMissing hClosed.2.2.1

end
end P0EFTJanusGWStabilityCausalityGate
end JanusFormal
