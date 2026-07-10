import Mathlib
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusRP4TwistedFluxPrimitiveSelector

namespace JanusFormal
namespace P0EFTJanusDustCurrentThreeFormBridge

set_option autoImplicit false

/--
The leading barotropic fluid EFT can be written as `F(b)`.  The affine choice
`F(b) = -m*b` is pressureless dust: `rho = -F = m*b` and
`p = F - b*F_b = 0`.
-/
def affineDustLagrangian (massUnit b : ℝ) : ℝ := -(massUnit * b)

def affineDustEnergyDensity (massUnit b : ℝ) : ℝ :=
  -affineDustLagrangian massUnit b

def affineDustPressure (massUnit b : ℝ) : ℝ :=
  affineDustLagrangian massUnit b - b * (-massUnit)

/-- The affine perfect-fluid action has exactly the dust equation of state. -/
theorem affine_fluid_is_pressureless_dust (massUnit b : ℝ) :
    affineDustEnergyDensity massUnit b = massUnit * b /\
      affineDustPressure massUnit b = 0 := by
  constructor <;> unfold affineDustEnergyDensity affineDustPressure affineDustLagrangian
  · ring
  · ring

/-- Homogeneous conserved number density on a three-dimensional spatial slice. -/
def homogeneousNumberDensity (charge scaleFactor : ℝ) : ℝ :=
  charge / scaleFactor ^ 3

/-- Dust energy density carried by the conserved current. -/
def homogeneousDustDensity
    (massUnit charge scaleFactor : ℝ) : ℝ :=
  massUnit * homogeneousNumberDensity charge scaleFactor

/--
Unlike a vacuum-like four-form density, the dust-current density gives the
published conserved scaling `a^3*rho = m*N`.
-/
theorem dust_current_gives_constant_comoving_energy
    (massUnit charge scaleFactor : ℝ)
    (hScale : scaleFactor ≠ 0) :
    scaleFactor ^ 3 * homogeneousDustDensity massUnit charge scaleFactor =
      massUnit * charge := by
  unfold homogeneousDustDensity homogeneousNumberDensity
  field_simp [pow_ne_zero 3 hScale]

/-- Integer current sector and its exact global dust energy. -/
def quantizedDustEnergy (massUnit : ℝ) (charge : ℤ) : ℝ :=
  massUnit * (charge : ℝ)

@[simp] theorem negative_primitive_charge_energy (massUnit : ℝ) :
    quantizedDustEnergy massUnit (-1) = -massUnit := by
  simp [quantizedDustEnergy]

@[simp] theorem positive_primitive_charge_energy (massUnit : ℝ) :
    quantizedDustEnergy massUnit 1 = massUnit := by
  simp [quantizedDustEnergy]

/--
A separate transgression/anomaly law is required to identify the twisted RP4
flux integer with the spatial dust-current integer.  Once that law preserves
magnitude, the primitive theorem transports to the dust sector.
-/
structure TwistedFluxToDustCharge where
  fluxSector :
    P0EFTJanusRP4TwistedFluxPrimitiveSelector.TwistedFluxSector
  dustCharge : ℤ
  chargeMagnitudeTransport :
    dustCharge.natAbs = fluxSector.flux.natAbs

/-- Primitive twisted flux implies primitive dust-current magnitude. -/
theorem transported_dust_charge_is_primitive
    (t : TwistedFluxToDustCharge) :
    t.dustCharge.natAbs = 1 := by
  calc
    t.dustCharge.natAbs = t.fluxSector.flux.natAbs :=
      t.chargeMagnitudeTransport
    _ = 1 :=
      P0EFTJanusRP4TwistedFluxPrimitiveSelector.minimal_odd_flux_is_primitive
        t.fluxSector

/--
For the negative primitive dust sector, the bounce/throat bridge map fixes the
required mass unit relative to the bridge mass:

`4*pi*m_J = 3*M_bridge`.
-/
theorem negative_primitive_mass_unit_bridge_relation
    (piConstant massUnit globalEnergy bridgeMass : ℝ)
    (hPrimitiveEnergy : globalEnergy = -massUnit)
    (hBridgeMap : 4 * piConstant * globalEnergy + 3 * bridgeMass = 0) :
    4 * piConstant * massUnit = 3 * bridgeMass := by
  nlinarith

/--
The mathematically corrected carrier separates the pieces that were conflated
in the direct four-form attempt.
-/
structure DustCurrentClosureStatus where
  comovingScalarFieldsDefined : Prop
  identicallyConservedThreeFormCurrentDerived : Prop
  affineDustActionDerived : Prop
  integerCurrentSectorDerived : Prop
  twistedFluxToDustTransgressionDerived : Prop
  primitiveNegativeSectorSelected : Prop
  janusMassUnitDerived : Prop
  globalEnergyMapDerived : Prop


def dustCurrentMapClosed (s : DustCurrentClosureStatus) : Prop :=
  s.comovingScalarFieldsDefined /\
  s.identicallyConservedThreeFormCurrentDerived /\
  s.affineDustActionDerived /\
  s.integerCurrentSectorDerived /\
  s.twistedFluxToDustTransgressionDerived /\
  s.primitiveNegativeSectorSelected /\
  s.janusMassUnitDerived /\
  s.globalEnergyMapDerived

end P0EFTJanusDustCurrentThreeFormBridge
end JanusFormal
