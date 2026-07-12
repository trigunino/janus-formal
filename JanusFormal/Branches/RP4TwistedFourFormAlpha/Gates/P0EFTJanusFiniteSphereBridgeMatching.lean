import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteSphereBridgeMatching

set_option autoImplicit false

/--
Algebraic data for matching a finite sphere in the published `k = -1` FLRW
branch to a Schwarzschild-type PT bridge.

`alphaSquaredLength` is the positive length denoted `alpha^2` in the 2018 exact
solution.  The field `signedSectorMassLaw` is the genuinely new physical input:
it asserts that the positive bridge mass is obtained from the magnitude/sign-
reversed quasi-local mass of the negative total Janus sector.  This law is not
silently derived from ordinary one-metric GR.
-/
structure FiniteSphereBridgeMatching where
  alphaSquaredLength : ℝ
  radialCoordinate : ℝ
  sphereArealRadius : ℝ
  bridgeRadius : ℝ
  lightSpeedSquared : ℝ
  piConstant : ℝ
  gravitationalConstant : ℝ
  globalMassConstant : ℝ
  bridgeMass : ℝ
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  radialCoordinatePositive : 0 < radialCoordinate
  bridgeRadiusPositive : 0 < bridgeRadius
  lightSpeedSquaredNonzero : lightSpeedSquared ≠ 0
  arealRadiusLaw :
    sphereArealRadius = alphaSquaredLength * radialCoordinate
  sourceScaleLaw :
    3 * lightSpeedSquared * alphaSquaredLength =
      -8 * piConstant * gravitationalConstant * globalMassConstant
  signedSectorMassLaw :
    3 * bridgeMass =
      -4 * piConstant * globalMassConstant * radialCoordinate ^ 3
  schwarzschildRadiusLaw :
    lightSpeedSquared * bridgeRadius =
      2 * gravitationalConstant * bridgeMass
  boundaryIsBridgeHorizon :
    sphereArealRadius = bridgeRadius

/--
The source normalization, signed quasi-local mass law and Schwarzschild law
imply `R_s = alpha^2 * r^3`.
-/
theorem bridge_radius_eq_alpha_times_r_cubed
    (m : FiniteSphereBridgeMatching) :
    m.bridgeRadius =
      m.alphaSquaredLength * m.radialCoordinate ^ 3 := by
  have hScaled :
      3 * m.lightSpeedSquared * m.bridgeRadius =
        3 * m.lightSpeedSquared *
          (m.alphaSquaredLength * m.radialCoordinate ^ 3) := by
    linear_combination
      3 * m.schwarzschildRadiusLaw +
      2 * m.gravitationalConstant * m.signedSectorMassLaw -
      m.radialCoordinate ^ 3 * m.sourceScaleLaw
  have hFactor :
      (3 * m.lightSpeedSquared) *
        (m.bridgeRadius -
          m.alphaSquaredLength * m.radialCoordinate ^ 3) = 0 := by
    nlinarith [hScaled]
  have hCoefficient : 3 * m.lightSpeedSquared ≠ 0 :=
    mul_ne_zero (by norm_num) m.lightSpeedSquaredNonzero
  have hDifference :
      m.bridgeRadius -
        m.alphaSquaredLength * m.radialCoordinate ^ 3 = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hCoefficient
  linarith

/--
Horizon matching selects the dimensionless FLRW boundary coordinate `r = 1`;
it is not an arbitrary coordinate normalization once all matching laws above are
assumed.
-/
theorem horizon_matching_selects_unit_radial_coordinate
    (m : FiniteSphereBridgeMatching) :
    m.radialCoordinate = 1 := by
  have hRadius := bridge_radius_eq_alpha_times_r_cubed m
  have hPolynomial :
      m.alphaSquaredLength * m.radialCoordinate =
        m.alphaSquaredLength * m.radialCoordinate ^ 3 := by
    calc
      m.alphaSquaredLength * m.radialCoordinate =
          m.sphereArealRadius := m.arealRadiusLaw.symm
      _ = m.bridgeRadius := m.boundaryIsBridgeHorizon
      _ = m.alphaSquaredLength * m.radialCoordinate ^ 3 := hRadius
  have hFirstFactor :
      m.alphaSquaredLength *
        (m.radialCoordinate - m.radialCoordinate ^ 3) = 0 := by
    nlinarith [hPolynomial]
  have hAlphaNonzero : m.alphaSquaredLength ≠ 0 :=
    ne_of_gt m.alphaSquaredLengthPositive
  have hRadialPolynomial :
      m.radialCoordinate - m.radialCoordinate ^ 3 = 0 :=
    (mul_eq_zero.mp hFirstFactor).resolve_left hAlphaNonzero
  have hSecondFactor :
      m.radialCoordinate * (1 - m.radialCoordinate ^ 2) = 0 := by
    nlinarith [hRadialPolynomial]
  have hRadialNonzero : m.radialCoordinate ≠ 0 :=
    ne_of_gt m.radialCoordinatePositive
  have hUnitSquare : 1 - m.radialCoordinate ^ 2 = 0 :=
    (mul_eq_zero.mp hSecondFactor).resolve_left hRadialNonzero
  nlinarith [m.radialCoordinatePositive]

/-- The finite-sphere matching fixes the exact-solution length to the bridge radius. -/
theorem alpha_squared_length_eq_bridge_radius
    (m : FiniteSphereBridgeMatching) :
    m.alphaSquaredLength = m.bridgeRadius := by
  have hRadius := bridge_radius_eq_alpha_times_r_cubed m
  have hUnit := horizon_matching_selects_unit_radial_coordinate m
  rw [hUnit] at hRadius
  norm_num at hRadius
  exact hRadius.symm

/-- Consequently the dimensionless ratio `alpha^2 / R_s` is one. -/
theorem alpha_squared_over_bridge_radius_eq_one
    (m : FiniteSphereBridgeMatching) :
    m.alphaSquaredLength / m.bridgeRadius = 1 := by
  rw [alpha_squared_length_eq_bridge_radius m]
  exact div_self (ne_of_gt m.bridgeRadiusPositive)

/--
The same matching fixes the 2018 mass constant relative to the positive bridge
mass: `4*pi*E_global + 3*M_bridge = 0`.
-/
theorem global_mass_to_bridge_mass_map
    (m : FiniteSphereBridgeMatching) :
    4 * m.piConstant * m.globalMassConstant + 3 * m.bridgeMass = 0 := by
  have hMass := m.signedSectorMassLaw
  rw [horizon_matching_selects_unit_radial_coordinate m] at hMass
  norm_num at hMass
  linarith

/--
This is a conditional closure: the algebra is complete, while the signed-sector
quasi-local mass law and the null junction must still be derived from the active
Janus bimetric action.
-/
structure PhysicalDerivationStatus where
  bimetricQuasiLocalMassDefined : Prop
  signedSectorMassLawDerived : Prop
  nullJunctionEquationsDerived : Prop
  finiteBoundaryIsHorizonDerived : Prop
  noImportedObservedScale : Prop


def physicalFiniteSphereClosure
    (s : PhysicalDerivationStatus) : Prop :=
  s.bimetricQuasiLocalMassDefined /\
  s.signedSectorMassLawDerived /\
  s.nullJunctionEquationsDerived /\
  s.finiteBoundaryIsHorizonDerived /\
  s.noImportedObservedScale

end P0EFTJanusFiniteSphereBridgeMatching
end JanusFormal
