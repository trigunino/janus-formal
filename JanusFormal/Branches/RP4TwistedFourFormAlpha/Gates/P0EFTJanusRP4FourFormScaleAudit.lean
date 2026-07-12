import Mathlib

namespace JanusFormal
namespace P0EFTJanusRP4FourFormScaleAudit

set_option autoImplicit false

/-- Comoving energy associated with a homogeneous density and scale factor. -/
def comovingEnergy (rho a : ℝ) : ℝ := rho * a ^ 3

/--
A constant vacuum-like density makes its comoving energy scale as the cube of
the scale factor.  This is the algebraic obstruction to identifying a standard
four-form vacuum density directly with the conserved dust-like `E` used in the
published Janus exact solution.
-/
theorem constant_density_comoving_scaling (rho a s : ℝ) :
    comovingEnergy rho (s * a) = s ^ 3 * comovingEnergy rho a := by
  unfold comovingEnergy
  ring

/--
If the initial comoving energy is nonzero and the rescaling is nontrivial at
cubic order, a constant density cannot keep the comoving energy fixed.
-/
theorem constant_density_not_dust_conserved
    (rho a s : ℝ)
    (hEnergy : comovingEnergy rho a ≠ 0)
    (hScale : s ^ 3 ≠ 1) :
    comovingEnergy rho (s * a) ≠ comovingEnergy rho a := by
  rw [constant_density_comoving_scaling]
  intro hEqual
  have hFactor : (s ^ 3 - 1) * comovingEnergy rho a = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hFactor with hScaleZero | hEnergyZero
  · apply hScale
    nlinarith
  · exact hEnergy hEnergyZero

/--
Algebraic data left after reducing a round fixed-flux Einstein saddle.

`volumeCoefficient` is the coefficient `v` in `Vol = v * L^4`; for a round
`RP^4`, `v = 4*pi^2/3`.  The balance equation is kept explicit because deriving
its sign and normalization from a Janus Euclidean action is a separate physical
obligation.
-/
structure FixedFluxEinsteinSaddle where
  radius : ℝ
  kappa : ℝ
  volumeCoefficient : ℝ
  chargeUnit : ℝ
  flux : ℤ
  radiusPositive : 0 < radius
  volumeCoefficientPositive : 0 < volumeCoefficient
  balance :
    6 * volumeCoefficient ^ 2 * radius ^ 6 =
      kappa * (((flux : ℝ) * chargeUnit) ^ 2)

/-- The explicit sixth-power radius law encoded by the fixed-flux balance. -/
def radiusSixthPowerLaw (s : FixedFluxEinsteinSaddle) : Prop :=
  s.radius ^ 6 =
    s.kappa * (((s.flux : ℝ) * s.chargeUnit) ^ 2) /
      (6 * s.volumeCoefficient ^ 2)

/-- Once the fixed-flux Einstein balance is derived, it determines `L^6`. -/
theorem balance_determines_radius_sixth_power
    (s : FixedFluxEinsteinSaddle) :
    radiusSixthPowerLaw s := by
  unfold radiusSixthPowerLaw
  have hVolume : s.volumeCoefficient ≠ 0 :=
    ne_of_gt s.volumeCoefficientPositive
  have hDenominator : 6 * s.volumeCoefficient ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hVolume)
  apply (eq_div_iff hDenominator).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using s.balance

/--
The advance closes the integer/primitive part but deliberately separates the
remaining dimensionful and Lorentzian obligations.
-/
structure RP4TwistedFourFormScaleStatus where
  orientationTwistedTopClassAvailable : Prop
  primitiveFluxMagnitudeOneProved : Prop
  fixedFluxEinsteinBalanceDerived : Prop
  janusChargeUnitDerived : Prop
  fourFormToPublishedDustEnergyMapDerived : Prop
  lorentzianContinuationDerived : Prop
  alphaSquaredOverLFixedNoFit : Prop

def mathematicalAdvanceClosed
    (s : RP4TwistedFourFormScaleStatus) : Prop :=
  s.orientationTwistedTopClassAvailable /\
  s.primitiveFluxMagnitudeOneProved /\
  s.fixedFluxEinsteinBalanceDerived


def fullNoFitScaleClosed
    (s : RP4TwistedFourFormScaleStatus) : Prop :=
  mathematicalAdvanceClosed s /\
  s.janusChargeUnitDerived /\
  s.fourFormToPublishedDustEnergyMapDerived /\
  s.lorentzianContinuationDerived /\
  s.alphaSquaredOverLFixedNoFit


theorem missing_dust_energy_map_blocks_full_scale_closure
    (s : RP4TwistedFourFormScaleStatus)
    (hMissing : Not s.fourFormToPublishedDustEnergyMapDerived) :
    Not (fullNoFitScaleClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

end P0EFTJanusRP4FourFormScaleAudit
end JanusFormal
