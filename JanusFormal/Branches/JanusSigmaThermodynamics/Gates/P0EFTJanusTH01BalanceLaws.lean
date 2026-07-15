import Mathlib

namespace JanusFormal
namespace P0EFTJanusTH01BalanceLaws

set_option autoImplicit false

/-- Total energy-rate residual for the two sectors and `Sigma`. -/
def totalEnergyRate
    (plusRate minusRate sigmaRate externalPower : ℝ) : ℝ :=
  plusRate + minusRate + sigmaRate - externalPower

theorem closed_exchange_conserves_total_energy
    (flux : ℝ) :
    totalEnergyRate (-flux) flux 0 0 = 0 := by
  simp [totalEnergyRate]

theorem sigma_storage_restores_balance
    (plusRate minusRate : ℝ) :
    totalEnergyRate plusRate minusRate (-(plusRate + minusRate)) 0 = 0 := by
  unfold totalEnergyRate
  ring

/-- Local irreversible entropy production `J X`. -/
def entropyProduction (flux force : ℝ) : ℝ := flux * force

theorem aligned_flux_force_produces_nonnegative_entropy
    (flux force : ℝ) (hFlux : 0 ≤ flux) (hForce : 0 ≤ force) :
    0 ≤ entropyProduction flux force :=
  mul_nonneg hFlux hForce

/-- Gravity-sign reversal must not be encoded as negative thermodynamic
density or entropy by definition. -/
structure TH01Inputs where
  plusEnergyCurrent : ℝ → ℝ
  minusEnergyCurrent : ℝ → ℝ
  sigmaStoredEnergy : ℝ → ℝ
  plusEntropyCurrent : ℝ → ℝ
  minusEntropyCurrent : ℝ → ℝ
  gravitationalSignSeparatedFromThermodynamicSign : Prop
  localBalanceDerivedFromAction : Prop

end P0EFTJanusTH01BalanceLaws
end JanusFormal
