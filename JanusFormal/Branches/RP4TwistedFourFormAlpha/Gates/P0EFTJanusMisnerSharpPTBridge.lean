import Mathlib

namespace JanusFormal
namespace P0EFTJanusMisnerSharpPTBridge

set_option autoImplicit false

/-- Homogeneous signed density associated with the conserved mass constant. -/
noncomputable def homogeneousSignedDensity
    (globalMass scaleFactor : ℝ) : ℝ :=
  globalMass / scaleFactor ^ 3

/-- Areal radius of a finite comoving sphere. -/
def finiteSphereArealRadius (scaleFactor radialCoordinate : ℝ) : ℝ :=
  scaleFactor * radialCoordinate

/-- Misner--Sharp mass of a homogeneous finite sphere. -/
noncomputable def homogeneousMisnerSharpMass
    (piConstant globalMass scaleFactor radialCoordinate : ℝ) : ℝ :=
  (4 * piConstant / 3) *
    homogeneousSignedDensity globalMass scaleFactor *
    finiteSphereArealRadius scaleFactor radialCoordinate ^ 3

/--
For nonzero scale factor, the homogeneous Misner--Sharp mass depends only on the
conserved mass constant and the comoving volume factor `r^3`.
-/
theorem homogeneous_misner_sharp_reduces_to_global_mass
    (piConstant globalMass scaleFactor radialCoordinate : ℝ)
    (hScale : scaleFactor ≠ 0) :
    3 * homogeneousMisnerSharpMass
        piConstant globalMass scaleFactor radialCoordinate =
      4 * piConstant * globalMass * radialCoordinate ^ 3 := by
  unfold homogeneousMisnerSharpMass homogeneousSignedDensity
    finiteSphereArealRadius
  field_simp [pow_ne_zero 3 hScale]

/--
Finite-sphere bridge data.  The sole Janus-specific sign input is
`bridgeMass = -signedMisnerSharpMass`: the positive bridge mass is the PT
magnitude of the negative signed quasi-local mass.
-/
structure PTMisnerSharpBridge where
  alphaSquaredLength : ℝ
  radialCoordinate : ℝ
  boundaryRadius : ℝ
  lightSpeedSquared : ℝ
  piConstant : ℝ
  gravitationalConstant : ℝ
  globalMassConstant : ℝ
  signedMisnerSharpMass : ℝ
  bridgeMass : ℝ
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  radialCoordinatePositive : 0 < radialCoordinate
  lightSpeedSquaredPositive : 0 < lightSpeedSquared
  gravitationalConstantNonzero : gravitationalConstant ≠ 0
  arealRadiusLaw :
    boundaryRadius = alphaSquaredLength * radialCoordinate
  sourceScaleLaw :
    3 * lightSpeedSquared * alphaSquaredLength =
      -8 * piConstant * gravitationalConstant * globalMassConstant
  misnerSharpLaw :
    3 * signedMisnerSharpMass =
      4 * piConstant * globalMassConstant * radialCoordinate ^ 3
  ptMassReversal :
    bridgeMass = -signedMisnerSharpMass
  horizonCompactnessLaw :
    lightSpeedSquared * boundaryRadius =
      2 * gravitationalConstant * bridgeMass

/-- PT reversal converts the signed Misner--Sharp law into the bridge law. -/
theorem pt_reversal_derives_bridge_mass_law
    (m : PTMisnerSharpBridge) :
    3 * m.bridgeMass =
      -4 * m.piConstant * m.globalMassConstant *
        m.radialCoordinate ^ 3 := by
  calc
    3 * m.bridgeMass = -(3 * m.signedMisnerSharpMass) := by
      rw [m.ptMassReversal]
      ring
    _ = -(4 * m.piConstant * m.globalMassConstant *
          m.radialCoordinate ^ 3) := by
      rw [m.misnerSharpLaw]
    _ = -4 * m.piConstant * m.globalMassConstant *
          m.radialCoordinate ^ 3 := by ring

/--
The source scale, Misner--Sharp mass and horizon compactness force the finite
matching sphere to have `r = 1`.
-/
theorem horizon_compactness_selects_unit_radial_coordinate
    (m : PTMisnerSharpBridge) :
    m.radialCoordinate = 1 := by
  have hHorizon := m.horizonCompactnessLaw
  rw [m.arealRadiusLaw] at hHorizon
  have hBridge := pt_reversal_derives_bridge_mass_law m
  have hPolynomial :
      3 * m.lightSpeedSquared * m.alphaSquaredLength *
        m.radialCoordinate -
      3 * m.lightSpeedSquared * m.alphaSquaredLength *
        m.radialCoordinate ^ 3 = 0 := by
    linear_combination
      3 * hHorizon +
      2 * m.gravitationalConstant * hBridge -
      m.radialCoordinate ^ 3 * m.sourceScaleLaw
  have hFactor :
      (3 * m.lightSpeedSquared * m.alphaSquaredLength) *
        (m.radialCoordinate - m.radialCoordinate ^ 3) = 0 := by
    calc
      (3 * m.lightSpeedSquared * m.alphaSquaredLength) *
          (m.radialCoordinate - m.radialCoordinate ^ 3) =
          3 * m.lightSpeedSquared * m.alphaSquaredLength *
            m.radialCoordinate -
          3 * m.lightSpeedSquared * m.alphaSquaredLength *
            m.radialCoordinate ^ 3 := by ring
      _ = 0 := hPolynomial
  have hCoefficientNonzero :
      3 * m.lightSpeedSquared * m.alphaSquaredLength ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt m.lightSpeedSquaredPositive))
      (ne_of_gt m.alphaSquaredLengthPositive)
  have hRadialPolynomial :
      m.radialCoordinate - m.radialCoordinate ^ 3 = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hCoefficientNonzero
  have hRadialFactor :
      m.radialCoordinate * (1 - m.radialCoordinate ^ 2) = 0 := by
    nlinarith [hRadialPolynomial]
  have hRadialNonzero : m.radialCoordinate ≠ 0 :=
    ne_of_gt m.radialCoordinatePositive
  have hUnitSquare : 1 - m.radialCoordinate ^ 2 = 0 :=
    (mul_eq_zero.mp hRadialFactor).resolve_left hRadialNonzero
  nlinarith [m.radialCoordinatePositive, hUnitSquare]

/-- The selected finite sphere has boundary radius equal to `alpha^2`. -/
theorem selected_boundary_radius_eq_alpha_squared_length
    (m : PTMisnerSharpBridge) :
    m.boundaryRadius = m.alphaSquaredLength := by
  rw [m.arealRadiusLaw, horizon_compactness_selects_unit_radial_coordinate m]
  ring

/-- The bridge/global mass relation follows from Misner--Sharp plus PT. -/
theorem global_mass_to_bridge_mass_map
    (m : PTMisnerSharpBridge) :
    4 * m.piConstant * m.globalMassConstant + 3 * m.bridgeMass = 0 := by
  have hBridge := pt_reversal_derives_bridge_mass_law m
  rw [horizon_compactness_selects_unit_radial_coordinate m] at hBridge
  norm_num at hBridge
  linarith

/--
The previously free signed finite-boundary law is reduced to two standard/local
inputs and one Janus sign input.
-/
structure PhysicalStatus where
  homogeneousMisnerSharpFormulaDerived : Prop
  ptMassReversalDerivedFromBimetricAction : Prop
  horizonCompactnessDerivedFromNullJunction : Prop
  noObservedScaleImported : Prop


def physicalPTBridgeClosed (s : PhysicalStatus) : Prop :=
  s.homogeneousMisnerSharpFormulaDerived /\
  s.ptMassReversalDerivedFromBimetricAction /\
  s.horizonCompactnessDerivedFromNullJunction /\
  s.noObservedScaleImported

end P0EFTJanusMisnerSharpPTBridge
end JanusFormal
