import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusD7AbsoluteAlphaSynthesis
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusBimetricZ4MassRadiusLock

namespace JanusFormal
namespace P0EFTJanusMinimalTwoTenD7Candidate

set_option autoImplicit false

open P0EFTJanusD7AbsoluteAlphaSynthesis
open P0EFTJanusBimetricZ4MassRadiusLock

/--
Concrete terminal candidate obtained by combining:

* one shared massless spin-two tower and two PT-related massive towers, whose
  effective weights are `2:10 = 1:5`;
* the stable determinant root `exp(-m L T)=1/3`, hence `x_*=log 3`;
* the conditional spectral modulus `T^2=2*pi^2`;
* the D7 RG/charge/radius synthesis.
-/
structure MinimalTwoTenD7Candidate extends D7AbsoluteAlphaSynthesis where
  stationaryProductIsLogThree : stationaryProduct = Real.log 3
  circleModulusSquared : circleModulus ^ 2 = 2 * Real.pi ^ 2
  piConvention : piConstant = Real.pi

/-- Convert the D7 candidate to the previously proved mass-radius lock. -/
def asOneFiveMassRadiusLock
    (s : MinimalTwoTenD7Candidate) : OneFiveMassRadiusLock :=
  { physicalMass := s.generatedMass
    geometricLength := s.geometricLength
    circleModulus := s.circleModulus
    alphaSquaredLength := s.alphaSquaredLength
    physicalMassPositive := s.generatedMassPositive
    geometricLengthPositive := s.geometricLengthPositive
    circleModulusPositive := s.circleModulusPositive
    alphaSquaredLengthPositive := s.alphaSquaredLengthPositive
    determinantMinimum := by
      have hVacuum := s.spectralVacuumLaw
      rw [s.stationaryProductIsLogThree] at hVacuum
      calc
        s.generatedMass * s.geometricLength * s.circleModulus =
            s.generatedMass * s.circleModulus * s.alphaSquaredLength := by
          rw [s.alphaGeometryLock]
          ring
        _ = Real.log 3 := hVacuum
    spectralModulus := s.circleModulusSquared
    alphaEqualsGeometry := s.alphaGeometryLock }

/-- The generated mass and the Janus radius obey the exact dimensionless target. -/
theorem minimal_generated_mass_alpha_target
    (s : MinimalTwoTenD7Candidate) :
    2 * Real.pi ^ 2 *
        (s.generatedMass * s.alphaSquaredLength) ^ 2 =
      (Real.log 3) ^ 2 := by
  exact one_five_physical_mass_alpha_target
    (asOneFiveMassRadiusLock s)

/-- The mass entering the determinant must be lighter than the inverse radius. -/
theorem minimal_generated_mass_is_strictly_light
    (s : MinimalTwoTenD7Candidate) :
    (s.generatedMass * s.alphaSquaredLength) ^ 2 < 1 / 2 := by
  rw [s.alphaGeometryLock]
  exact one_five_mass_is_strictly_light
    (asOneFiveMassRadiusLock s)

/-- The first positive primitive-monopole sphere excitation cannot be the stabilizing mass. -/
theorem first_sphere_dirac_excitation_cannot_generate_minimum
    (s : MinimalTwoTenD7Candidate)
    (hFirstSphereMass :
      (s.generatedMass * s.alphaSquaredLength) ^ 2 = 2) : False := by
  rw [s.alphaGeometryLock] at hFirstSphereMass
  exact first_sphere_dirac_mass_cannot_satisfy_one_five_lock
    (asOneFiveMassRadiusLock s) hFirstSphereMass

/-- Terminal squared UV/alpha hierarchy with both `x_*` and `T` eliminated. -/
theorem minimal_uv_alpha_squared_law
    (s : MinimalTwoTenD7Candidate) :
    2 * Real.pi ^ 2 *
        (s.uvMass * s.alphaSquaredLength) ^ 2 =
      (Real.log 3) ^ 2 *
        Real.exp s.hierarchyExponent ^ 2 := by
  have hHierarchy := terminal_alpha_hierarchy_law
    s.toD7AbsoluteAlphaSynthesis
  rw [s.stationaryProductIsLogThree] at hHierarchy
  have hSquared := congrArg (fun value : ℝ => value ^ 2) hHierarchy
  calc
    2 * Real.pi ^ 2 *
        (s.uvMass * s.alphaSquaredLength) ^ 2 =
      s.circleModulus ^ 2 *
        (s.uvMass * s.alphaSquaredLength) ^ 2 := by
      rw [s.circleModulusSquared]
    _ = (s.uvMass * s.circleModulus *
          s.alphaSquaredLength) ^ 2 := by ring
    _ = (Real.log 3 * Real.exp s.hierarchyExponent) ^ 2 :=
      hSquared
    _ = (Real.log 3) ^ 2 *
        Real.exp s.hierarchyExponent ^ 2 := by ring

/-- Terminal charge hierarchy after eliminating the circle modulus. -/
theorem minimal_charge_uv_hierarchy_law
    (s : MinimalTwoTenD7Candidate) :
    4 * s.llChargeUnit * (Real.log 3) ^ 2 *
        Real.exp s.hierarchyExponent ^ 2 =
      2 * Real.pi ^ 2 * s.uvMass ^ 2 := by
  have hCharge := terminal_charge_hierarchy_law
    s.toD7AbsoluteAlphaSynthesis
  rw [s.stationaryProductIsLogThree] at hCharge
  calc
    4 * s.llChargeUnit * (Real.log 3) ^ 2 *
        Real.exp s.hierarchyExponent ^ 2 =
      (s.uvMass * s.circleModulus) ^ 2 := hCharge
    _ = s.uvMass ^ 2 * s.circleModulus ^ 2 := by ring
    _ = 2 * Real.pi ^ 2 * s.uvMass ^ 2 := by
      rw [s.circleModulusSquared]
      ring

/-- Two candidates with the same RG product and UV mass predict the same radius. -/
theorem same_minimal_microscopic_data_fix_same_alpha
    (first second : MinimalTwoTenD7Candidate)
    (hUV : first.uvMass = second.uvMass)
    (hProduct :
      first.betaCouplingProduct = second.betaCouplingProduct) :
    first.alphaSquaredLength = second.alphaSquaredLength := by
  have hPi : first.piConstant = second.piConstant := by
    rw [first.piConvention, second.piConvention]
  have hStationary :
      first.stationaryProduct = second.stationaryProduct := by
    rw [first.stationaryProductIsLogThree,
      second.stationaryProductIsLogThree]
  have hModulusSquares :
      first.circleModulus ^ 2 = second.circleModulus ^ 2 := by
    rw [first.circleModulusSquared, second.circleModulusSquared]
  have hRootFactor :
      (first.circleModulus - second.circleModulus) *
        (first.circleModulus + second.circleModulus) = 0 := by
    nlinarith [hModulusSquares]
  have hModulus : first.circleModulus = second.circleModulus := by
    rcases mul_eq_zero.mp hRootFactor with hDifference | hSum
    · linarith
    · have hPositive :
          0 < first.circleModulus + second.circleModulus :=
        add_pos first.circleModulusPositive second.circleModulusPositive
      exact False.elim ((ne_of_gt hPositive) hSum)
  exact same_terminal_data_fix_same_alpha
    first.toD7AbsoluteAlphaSynthesis
    second.toD7AbsoluteAlphaSynthesis
    hUV hProduct hPi hModulus hStationary

/--
The candidate removes the previously free `x_*` and `T`, but remains physical
only if the bimetric/ghost determinant really produces weights `2:10` and if RG
or bulk matching derives `uvMass` and the beta/coupling product without fitting
`A`.
-/
structure MinimalTwoTenPhysicalStatus where
  sharedMasslessTowerDerived : Prop
  twoPTMassiveTowersDerived : Prop
  gaugeGhostWeightsComputed : Prop
  effectiveWeightsTwoToTenDerived : Prop
  stableOneThirdRootDerived : Prop
  spectralModulusDerived : Prop
  generatedMassIdentifiedWithBimetricMode : Prop
  betaFunctionComputed : Prop
  uvCouplingFixedMicroscopically : Prop
  independentUVMassDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop
  chargeCompatibilityDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaDerivedNoFit : Prop


def minimalTwoTenPhysicalClosure
    (s : MinimalTwoTenPhysicalStatus) : Prop :=
  s.sharedMasslessTowerDerived /\
  s.twoPTMassiveTowersDerived /\
  s.gaugeGhostWeightsComputed /\
  s.effectiveWeightsTwoToTenDerived /\
  s.stableOneThirdRootDerived /\
  s.spectralModulusDerived /\
  s.generatedMassIdentifiedWithBimetricMode /\
  s.betaFunctionComputed /\
  s.uvCouplingFixedMicroscopically /\
  s.independentUVMassDerived /\
  s.finiteCountertermsFixedMicroscopically /\
  s.chargeCompatibilityDerived /\
  s.noObservedScaleImported /\
  s.absoluteAlphaDerivedNoFit

end P0EFTJanusMinimalTwoTenD7Candidate
end JanusFormal
