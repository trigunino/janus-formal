import Mathlib

namespace JanusFormal
namespace P0EFTJanusAuxiliaryMetricSpectralLock

set_option autoImplicit false

/--
Compatibility data between the canonical first scalar mode of `S2_L` and the
primitive LL auxiliary-flux normalization.
-/
structure AuxiliaryMetricSpectralData where
  geometricLength : ℝ
  sphereFirstEigenvalue : ℝ
  llChargeUnit : ℝ
  spectralChargeCoefficient : ℝ
  geometricLengthPositive : 0 < geometricLength
  sphereEigenvaluePositive : 0 < sphereFirstEigenvalue
  llChargeUnitPositive : 0 < llChargeUnit
  spectralCoefficientPositive : 0 < spectralChargeCoefficient
  sphereModeLaw :
    sphereFirstEigenvalue * geometricLength ^ 2 = 2
  primitiveAuxiliaryFluxNormalization :
    4 * llChargeUnit * geometricLength ^ 2 = 1
  chargeFromSphereMode :
    llChargeUnit = spectralChargeCoefficient * sphereFirstEigenvalue

/-- The LL auxiliary metric computes the spectral coefficient as `1/8`. -/
theorem auxiliary_metric_fixes_one_eighth_coefficient
    (s : AuxiliaryMetricSpectralData) :
    8 * s.spectralChargeCoefficient = 1 := by
  have hChargeLength :
      s.llChargeUnit * s.geometricLength ^ 2 =
        2 * s.spectralChargeCoefficient := by
    calc
      s.llChargeUnit * s.geometricLength ^ 2 =
          (s.spectralChargeCoefficient * s.sphereFirstEigenvalue) *
            s.geometricLength ^ 2 := by rw [s.chargeFromSphereMode]
      _ = s.spectralChargeCoefficient *
          (s.sphereFirstEigenvalue * s.geometricLength ^ 2) := by ring
      _ = 2 * s.spectralChargeCoefficient := by
        rw [s.sphereModeLaw]
        ring
  nlinarith [s.primitiveAuxiliaryFluxNormalization, hChargeLength]

/-- Ordinary notation for the same coefficient. -/
theorem spectral_charge_coefficient_eq_one_eighth
    (s : AuxiliaryMetricSpectralData) :
    s.spectralChargeCoefficient = 1 / 8 := by
  have h := auxiliary_metric_fixes_one_eighth_coefficient s
  norm_num at h ⊢
  linarith

/-- Positive primitive flux normalization is equivalent to its squared form. -/
theorem primitive_linear_flux_implies_squared_flux
    (s : AuxiliaryMetricSpectralData) :
    16 * s.llChargeUnit ^ 2 * s.geometricLength ^ 4 = 1 := by
  calc
    16 * s.llChargeUnit ^ 2 * s.geometricLength ^ 4 =
        (4 * s.llChargeUnit * s.geometricLength ^ 2) ^ 2 := by ring
    _ = 1 := by
      rw [s.primitiveAuxiliaryFluxNormalization]
      norm_num

/--
Thus, once the exact-solution length is identified with the throat radius, the
spectral lock, LL primitive flux and bimetric radius match become mutually
consistent rather than three independent normalizations.
-/
structure UnifiedSpectralLLBimetricStatus where
  sphereSpectrumDerived : Prop
  auxiliaryMetricA0OneEighthDerived : Prop
  primitiveMonopoleFluxDerived : Prop
  spectralCoefficientOneEighthDerived : Prop
  alphaEqualsThroatRadiusDerived : Prop
  allNormalizationsMatched : Prop


def unifiedSpectralLLBimetricClosed
    (s : UnifiedSpectralLLBimetricStatus) : Prop :=
  s.sphereSpectrumDerived /\
  s.auxiliaryMetricA0OneEighthDerived /\
  s.primitiveMonopoleFluxDerived /\
  s.spectralCoefficientOneEighthDerived /\
  s.alphaEqualsThroatRadiusDerived /\
  s.allNormalizationsMatched

end P0EFTJanusAuxiliaryMetricSpectralLock
end JanusFormal
