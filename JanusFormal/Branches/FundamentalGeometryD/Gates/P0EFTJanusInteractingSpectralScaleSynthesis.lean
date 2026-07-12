import Mathlib

namespace JanusFormal
namespace P0EFTJanusInteractingSpectralScaleSynthesis

set_option autoImplicit false

/--
Terminal data for the only currently viable Program-D absolute-scale route:

* interactions or bulk matching generate a physical mass `m_dyn`;
* the renormalized nonlocal action fixes the dimensionless product
  `x_* = m_dyn * L * T`;
* the Dirac/LL/bimetric compatibility chain fixes `A=L` and
  `4*q_LL*L^2=1`.
-/
structure InteractingSpectralScale where
  generatedMass : ℝ
  circleModulus : ℝ
  stationaryProduct : ℝ
  geometricLength : ℝ
  alphaSquaredLength : ℝ
  llChargeUnit : ℝ
  generatedMassPositive : 0 < generatedMass
  circleModulusPositive : 0 < circleModulus
  stationaryProductPositive : 0 < stationaryProduct
  geometricLengthPositive : 0 < geometricLength
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  llChargePositive : 0 < llChargeUnit
  nonlocalVacuumLaw :
    generatedMass * geometricLength * circleModulus = stationaryProduct
  alphaGeometryLock :
    alphaSquaredLength = geometricLength
  chargeGeometryLock :
    4 * llChargeUnit * geometricLength ^ 2 = 1

/-- The absolute Janus length obeys `m_dyn*T*A=x_*`. -/
theorem absolute_alpha_product_law
    (s : InteractingSpectralScale) :
    s.generatedMass * s.circleModulus * s.alphaSquaredLength =
      s.stationaryProduct := by
  rw [s.alphaGeometryLock]
  nlinarith [s.nonlocalVacuumLaw]

/-- Division form of the absolute prediction. -/
theorem absolute_alpha_division_law
    (s : InteractingSpectralScale) :
    s.alphaSquaredLength =
      s.stationaryProduct /
        (s.generatedMass * s.circleModulus) := by
  have hProduct := absolute_alpha_product_law s
  have hNonzero :
      s.generatedMass * s.circleModulus ≠ 0 :=
    mul_ne_zero
      (ne_of_gt s.generatedMassPositive)
      (ne_of_gt s.circleModulusPositive)
  apply (eq_div_iff hNonzero).2
  nlinarith [hProduct]

/-- The LL charge is fixed in a division-free form by the generated mass and vacuum product. -/
theorem generated_mass_fixes_charge_law
    (s : InteractingSpectralScale) :
    4 * s.llChargeUnit * s.stationaryProduct ^ 2 =
      (s.generatedMass * s.circleModulus) ^ 2 := by
  have hVacuum := s.nonlocalVacuumLaw
  calc
    4 * s.llChargeUnit * s.stationaryProduct ^ 2 =
        4 * s.llChargeUnit *
          (s.generatedMass * s.geometricLength * s.circleModulus) ^ 2 := by
      rw [← hVacuum]
    _ = (s.generatedMass * s.circleModulus) ^ 2 *
          (4 * s.llChargeUnit * s.geometricLength ^ 2) := by
      ring
    _ = (s.generatedMass * s.circleModulus) ^ 2 := by
      rw [s.chargeGeometryLock]
      ring

/-- The primitive squared LL flux law follows from the unsquared positive lock. -/
theorem primitive_ll_flux_law
    (s : InteractingSpectralScale) :
    16 * s.llChargeUnit ^ 2 * s.alphaSquaredLength ^ 4 = 1 := by
  have hAlphaCharge :
      4 * s.llChargeUnit * s.alphaSquaredLength ^ 2 = 1 := by
    rw [s.alphaGeometryLock]
    exact s.chargeGeometryLock
  calc
    16 * s.llChargeUnit ^ 2 * s.alphaSquaredLength ^ 4 =
        (4 * s.llChargeUnit * s.alphaSquaredLength ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hAlphaCharge]; norm_num

/-- Equal generated mass, modulus and dimensionless vacuum product fix the same absolute alpha. -/
theorem same_microscopic_spectral_data_fix_same_alpha
    (first second : InteractingSpectralScale)
    (hMass : first.generatedMass = second.generatedMass)
    (hModulus : first.circleModulus = second.circleModulus)
    (hProduct : first.stationaryProduct = second.stationaryProduct) :
    first.alphaSquaredLength = second.alphaSquaredLength := by
  have hFirst := absolute_alpha_product_law first
  have hSecond := absolute_alpha_product_law second
  rw [hMass, hModulus, hProduct] at hFirst
  have hPositive :
      0 < second.generatedMass * second.circleModulus :=
    mul_pos second.generatedMassPositive second.circleModulusPositive
  nlinarith [hFirst, hSecond]

/-- Without a generated physical mass, the dimensionless spectral vacuum cannot determine a length. -/
structure DimensionlessVacuumOnly where
  circleModulus : ℝ
  stationaryProduct : ℝ
  alphaSquaredLength : ℝ

/-- Common rescaling orbit when no mass anchor is supplied. -/
def rescaleDimensionlessVacuum
    (s : DimensionlessVacuumOnly)
    (scale : ℝ) : DimensionlessVacuumOnly :=
  { circleModulus := s.circleModulus
    stationaryProduct := s.stationaryProduct
    alphaSquaredLength := scale * s.alphaSquaredLength }

/-- The dimensionless data are unchanged by rescaling the candidate absolute length. -/
theorem dimensionless_data_invariant_under_length_rescaling
    (s : DimensionlessVacuumOnly)
    (scale : ℝ) :
    (rescaleDimensionlessVacuum s scale).circleModulus = s.circleModulus /\
    (rescaleDimensionlessVacuum s scale).stationaryProduct =
      s.stationaryProduct := by
  exact ⟨rfl, rfl⟩

/--
The absolute-scale program closes only when both components are derived:
nonlocal spectral stabilization supplies `x_*`, and an interacting/bulk sector
supplies the dimensionful mass.  Neither part is sufficient alone.
-/
structure InteractingSpectralClosureStatus where
  interactingQuantumTheoryConstructed : Prop
  generatedMassDerivedNoFit : Prop
  fullRenormalizedNonlocalActionDerived : Prop
  stableStationaryProductDerived : Prop
  circleModulusDerived : Prop
  diracLLBimetricLockDerived : Prop
  bulkBoundaryChargeCompatibilityDerived : Prop
  absoluteAlphaDerivedNoFit : Prop


def interactingSpectralClosure
    (s : InteractingSpectralClosureStatus) : Prop :=
  s.interactingQuantumTheoryConstructed /\
  s.generatedMassDerivedNoFit /\
  s.fullRenormalizedNonlocalActionDerived /\
  s.stableStationaryProductDerived /\
  s.circleModulusDerived /\
  s.diracLLBimetricLockDerived /\
  s.bulkBoundaryChargeCompatibilityDerived /\
  s.absoluteAlphaDerivedNoFit

end P0EFTJanusInteractingSpectralScaleSynthesis
end JanusFormal
