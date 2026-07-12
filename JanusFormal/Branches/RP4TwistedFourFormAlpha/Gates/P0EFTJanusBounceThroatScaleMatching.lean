import Mathlib

namespace JanusFormal
namespace P0EFTJanusBounceThroatScaleMatching

set_option autoImplicit false

/--
Metric matching data at a reflection-symmetric bounce.  `alphaSquaredLength` is
the positive length denoted `alpha^2` in the 2018 exact solution.  The equality
of squared scale factors is the coordinate-free content of matching two induced
metrics written with the same normalized reference metric.
-/
structure BounceThroatMetricMatching where
  alphaSquaredLength : ℝ
  throatRadius : ℝ
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  throatRadiusPositive : 0 < throatRadius
  inducedMetricScaleMatch : alphaSquaredLength ^ 2 = throatRadius ^ 2

/-- Positivity removes the spurious negative root of the metric-scale equation. -/
theorem alpha_squared_length_eq_throat_radius
    (m : BounceThroatMetricMatching) :
    m.alphaSquaredLength = m.throatRadius := by
  have hFactor :
      (m.alphaSquaredLength - m.throatRadius) *
        (m.alphaSquaredLength + m.throatRadius) = 0 := by
    nlinarith [m.inducedMetricScaleMatch]
  rcases mul_eq_zero.mp hFactor with hDifference | hSum
  · linarith
  · have hPositive :
        0 < m.alphaSquaredLength + m.throatRadius :=
      add_pos m.alphaSquaredLengthPositive m.throatRadiusPositive
    exfalso
    exact (ne_of_gt hPositive) hSum

/-- The dimensionless exact-solution/throat ratio is one under metric matching. -/
theorem alpha_squared_over_throat_eq_one
    (m : BounceThroatMetricMatching) :
    m.alphaSquaredLength / m.throatRadius = 1 := by
  rw [alpha_squared_length_eq_throat_radius m]
  exact div_self (ne_of_gt m.throatRadiusPositive)

/-- A PT-odd scalar second fundamental form must vanish on the fixed surface. -/
theorem pt_odd_extrinsic_curvature_vanishes
    (extrinsicCurvature : ℝ)
    (hPT : extrinsicCurvature = -extrinsicCurvature) :
    extrinsicCurvature = 0 := by
  linarith

/--
The extra hypothesis required to identify the local throat radius with the
single global projective radius.  Tubular surgery does not supply this equality
from topology alone.
-/
structure ProjectiveSingleRadiusMatching where
  metricMatching : BounceThroatMetricMatching
  projectiveRadius : ℝ
  projectiveRadiusPositive : 0 < projectiveRadius
  throatEqualsProjectiveRadius :
    metricMatching.throatRadius = projectiveRadius

/-- A one-radius projective tunnel fixes `alpha^2 / L_projective = 1`. -/
theorem alpha_squared_over_projective_radius_eq_one
    (m : ProjectiveSingleRadiusMatching) :
    m.metricMatching.alphaSquaredLength / m.projectiveRadius = 1 := by
  have hAlpha :
      m.metricMatching.alphaSquaredLength = m.projectiveRadius :=
    (alpha_squared_length_eq_throat_radius m.metricMatching).trans
      m.throatEqualsProjectiveRadius
  rw [hAlpha]
  exact div_self (ne_of_gt m.projectiveRadiusPositive)

/--
Combine the 2018 source normalization with the Schwarzschild bridge law.  The
relations are stored without division:

* `3*c^2*alpha^2 = -8*pi*G*E_global`;
* `c^2*R_s = 2*G*M_bridge`.
-/
structure SourceBridgeMatching where
  metricMatching : BounceThroatMetricMatching
  lightSpeedSquared : ℝ
  piConstant : ℝ
  gravitationalConstant : ℝ
  globalEnergy : ℝ
  bridgeMass : ℝ
  gravitationalConstantNonzero : gravitationalConstant ≠ 0
  sourceScaleLaw :
    3 * lightSpeedSquared * metricMatching.alphaSquaredLength =
      -8 * piConstant * gravitationalConstant * globalEnergy
  schwarzschildRadiusLaw :
    lightSpeedSquared * metricMatching.throatRadius =
      2 * gravitationalConstant * bridgeMass

/--
Once the same radius is used on both sides, the missing map is fixed:

`4*pi*E_global + 3*M_bridge = 0`.

Thus `E_global = -(3/(4*pi))*M_bridge` in the 2018 mass-density convention.
-/
theorem source_energy_to_bridge_mass_map
    (m : SourceBridgeMatching) :
    4 * m.piConstant * m.globalEnergy + 3 * m.bridgeMass = 0 := by
  have hSource := m.sourceScaleLaw
  rw [alpha_squared_length_eq_throat_radius m.metricMatching] at hSource
  have hFactor :
      2 * m.gravitationalConstant *
        (4 * m.piConstant * m.globalEnergy + 3 * m.bridgeMass) = 0 := by
    nlinarith [hSource, m.schwarzschildRadiusLaw]
  have hTwoG : 2 * m.gravitationalConstant ≠ 0 :=
    mul_ne_zero (by norm_num) m.gravitationalConstantNonzero
  exact (mul_eq_zero.mp hFactor).resolve_left hTwoG

/-- LL-brane radius law in the geometrized convention already used by the repo. -/
structure LLBraneMatchedScale where
  metricMatching : BounceThroatMetricMatching
  piConstant : ℝ
  chiAbsInverseLength : ℝ
  llRadiusLaw :
    8 * piConstant * chiAbsInverseLength * metricMatching.throatRadius = 1

/-- The matched exact scale inherits the LL-brane tension-radius relation. -/
theorem alpha_squared_llbrane_law
    (m : LLBraneMatchedScale) :
    8 * m.piConstant * m.chiAbsInverseLength *
        m.metricMatching.alphaSquaredLength = 1 := by
  rw [alpha_squared_length_eq_throat_radius m.metricMatching]
  exact m.llRadiusLaw

/--
The remaining geometry obligation is explicit: the published `k=-1` exact
branch and the resolved projective/tunnel slice must be connected by an actual
matching hypersurface before the ratio theorem can be applied physically.
-/
structure GeometryMatchingFrontier where
  publishedOpenBranchTracked : Prop
  resolvedProjectiveBranchTracked : Prop
  matchingHypersurfaceConstructed : Prop
  commonNormalizedInducedMetricDerived : Prop
  ptOddExtrinsicCurvatureDerived : Prop
  noThinShellOrDeclaredShellLaw : Prop


def physicalGeometryMatchingClosed (g : GeometryMatchingFrontier) : Prop :=
  g.publishedOpenBranchTracked /\
  g.resolvedProjectiveBranchTracked /\
  g.matchingHypersurfaceConstructed /\
  g.commonNormalizedInducedMetricDerived /\
  g.ptOddExtrinsicCurvatureDerived /\
  g.noThinShellOrDeclaredShellLaw

end P0EFTJanusBounceThroatScaleMatching
end JanusFormal
