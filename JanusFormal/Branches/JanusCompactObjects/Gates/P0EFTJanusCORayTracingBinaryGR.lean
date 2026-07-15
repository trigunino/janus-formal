import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCOGRBaseline

namespace JanusFormal
namespace P0EFTJanusCORayTracingBinaryGR

set_option autoImplicit false

noncomputable section

/-- Schwarzschild null radial polynomial in `u=1/r`. -/
def nullRadialPolynomial (mass impact u : ℝ) : ℝ :=
  1 / impact ^ 2 - u ^ 2 + 2 * mass * u ^ 3

/-- The photon-sphere inverse radius is a stationary point of the null
effective potential derivative `-2u+6Mu²`. -/
theorem photon_sphere_stationary
    (mass : ℝ) (hMass : mass ≠ 0) :
    -2 * (1 / (3 * mass)) +
      6 * mass * (1 / (3 * mass)) ^ 2 = 0 := by
  field_simp
  ring

def periastronAdvance
    (totalMass semiMajorAxis eccentricity : ℝ) : ℝ :=
  6 * Real.pi * totalMass /
    (semiMajorAxis * (1 - eccentricity ^ 2))

theorem periastron_advance_positive
    (totalMass semiMajorAxis eccentricity : ℝ)
    (hMass : 0 < totalMass) (hAxis : 0 < semiMajorAxis)
    (hEccentricity : eccentricity ^ 2 < 1) :
    0 < periastronAdvance totalMass semiMajorAxis eccentricity := by
  unfold periastronAdvance
  positivity

/-- Peters-Mathews eccentricity enhancement numerator. -/
def eccentricityEnhancementNumerator (eccentricity : ℝ) : ℝ :=
  1 + 73 * eccentricity ^ 2 / 24 + 37 * eccentricity ^ 4 / 96

theorem eccentricity_enhancement_numerator_positive (eccentricity : ℝ) :
    0 < eccentricityEnhancementNumerator eccentricity := by
  unfold eccentricityEnhancementNumerator
  positivity

/-- Separation between GR baselines and future Janus corrections. -/
structure CO0506Status where
  nullGeodesicReferenceValidated : Prop
  surfaceCaptureClassifierValidated : Prop
  periastronReferenceValidated : Prop
  shapiroReferenceValidated : Prop
  orbitalDecayReferenceValidated : Prop
  iscoReferenceValidated : Prop
  janusExteriorMetricDerived : Prop
  janusBinaryRadiationLawDerived : Prop

def grReferenceClosed (s : CO0506Status) : Prop :=
  s.nullGeodesicReferenceValidated ∧
  s.surfaceCaptureClassifierValidated ∧
  s.periastronReferenceValidated ∧
  s.shapiroReferenceValidated ∧
  s.orbitalDecayReferenceValidated ∧
  s.iscoReferenceValidated

def janusPredictionClosed (s : CO0506Status) : Prop :=
  grReferenceClosed s ∧
  s.janusExteriorMetricDerived ∧
  s.janusBinaryRadiationLawDerived

end
end P0EFTJanusCORayTracingBinaryGR
end JanusFormal
