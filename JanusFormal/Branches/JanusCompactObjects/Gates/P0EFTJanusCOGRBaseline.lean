import Mathlib

namespace JanusFormal
namespace P0EFTJanusCOGRBaseline

set_option autoImplicit false

noncomputable section

/-- Geometric compactness `C=2M/R`. -/
def compactness (mass radius : ℝ) : ℝ := 2 * mass / radius

/-- Exterior Schwarzschild surface redshift factor `1+z`. -/
def surfaceRedshiftFactor (compactnessValue : ℝ) : ℝ :=
  1 / Real.sqrt (1 - compactnessValue)

/-- Schwarzschild photon sphere and critical impact parameter. -/
def photonSphereRadius (mass : ℝ) : ℝ := 3 * mass
def criticalImpactParameter (mass : ℝ) : ℝ := 3 * Real.sqrt 3 * mass

theorem photon_sphere_outside_surface_when_ultracompact
    (mass radius : ℝ)
    (hCompact : radius < 3 * mass) :
    radius < photonSphereRadius mass := by
  simpa [photonSphereRadius] using hCompact

/-- The denominator controlling the constant-density central pressure vanishes
at the Buchdahl compactness. -/
def centralPressureDenominatorFromSurfaceRoot (surfaceRoot : ℝ) : ℝ :=
  3 * surfaceRoot - 1

theorem buchdahl_root_has_zero_pressure_denominator :
    centralPressureDenominatorFromSurfaceRoot (1 / 3 : ℝ) = 0 := by
  norm_num [centralPressureDenominatorFromSurfaceRoot]

/-- An image-intensity ratio does not determine a wavelength ratio without an
injective calibrated forward map. -/
structure RedshiftInferenceInputs where
  sameSpectralFeatureIdentified : Prop
  emitterFrequencyKnown : Prop
  covariantRadiativeTransferDerived : Prop
  syntheticVisibilityPipelineDerived : Prop
  reconstructionStatisticCalibrated : Prop

def ehtSpectralRedshiftReady (s : RedshiftInferenceInputs) : Prop :=
  s.sameSpectralFeatureIdentified ∧
  s.emitterFrequencyKnown ∧
  s.covariantRadiativeTransferDerived ∧
  s.syntheticVisibilityPipelineDerived ∧
  s.reconstructionStatisticCalibrated

theorem missing_spectral_feature_blocks_redshift_inference
    (s : RedshiftInferenceInputs)
    (hMissing : ¬s.sameSpectralFeatureIdentified) :
    ¬ehtSpectralRedshiftReady s := by
  intro hReady
  exact hMissing hReady.1

end
end P0EFTJanusCOGRBaseline
end JanusFormal
