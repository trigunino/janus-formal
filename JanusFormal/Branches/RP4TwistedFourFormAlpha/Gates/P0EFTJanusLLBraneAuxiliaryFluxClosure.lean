import Mathlib

namespace JanusFormal
namespace P0EFTJanusLLBraneAuxiliaryFluxClosure

set_option autoImplicit false

/--
The `p = 2` LL-brane with the wrong-sign Maxwell choice
`L(F^2) = F^2 / 4`.

The world-volume measure equation gives `M = F^2/4`; the Virasoro-like
constraint gives `a0 = F^2/4`; and the Einstein-Rosen junction fixes `a0=1/8`.
-/
structure MinimalWrongSignMaxwellSector where
  fieldInvariant : ℝ
  measureIntegrationConstant : ℝ
  a0 : ℝ
  measureEquation :
    measureIntegrationConstant = fieldInvariant / 4
  auxiliaryMetricEquation :
    a0 = fieldInvariant / 4
  junctionA0 :
    a0 = 1 / 8

/-- The cited LL-brane action and junction fix the auxiliary invariant. -/
theorem field_invariant_eq_one_half
    (s : MinimalWrongSignMaxwellSector) :
    s.fieldInvariant = 1 / 2 := by
  nlinarith [s.auxiliaryMetricEquation, s.junctionA0]

/-- The non-Riemannian measure integration constant is fixed as well. -/
theorem measure_constant_eq_one_eighth
    (s : MinimalWrongSignMaxwellSector) :
    s.measureIntegrationConstant = 1 / 8 := by
  nlinarith [s.measureEquation, field_invariant_eq_one_half s]

/--
Normalized flux data on the spherical spatial section of the LL world-volume.
The cleared equation

`32 * F^2 * q_LL^2 * R_s^4 = n^2`

includes the induced/auxiliary metric relation `g_ij = 2*a0*gamma_ij` and the
factor two from contracting an antisymmetric two-form in two dimensions.
-/
structure SphericalAuxiliaryFlux where
  minimalSector : MinimalWrongSignMaxwellSector
  chargeUnit : ℝ
  throatRadius : ℝ
  fluxNumber : ℝ
  chargeUnitPositive : 0 < chargeUnit
  throatRadiusPositive : 0 < throatRadius
  primitiveFluxSquare : fluxNumber ^ 2 = 1
  auxiliaryMetricFluxNormalization :
    32 * minimalSector.fieldInvariant * chargeUnit ^ 2 *
      throatRadius ^ 4 = fluxNumber ^ 2

/-- With `F^2=1/2` and primitive flux, the radius law is exact. -/
theorem primitive_flux_radius_law
    (s : SphericalAuxiliaryFlux) :
    16 * s.chargeUnit ^ 2 * s.throatRadius ^ 4 = 1 := by
  have hField := field_invariant_eq_one_half s.minimalSector
  nlinarith [s.auxiliaryMetricFluxNormalization, s.primitiveFluxSquare]

/--
Adding the Einstein-Rosen LL-brane relation `8*pi*|chi|*R_s=1` eliminates the
radius and fixes the relation between the two remaining world-volume scales.
-/
structure LLTensionFluxMatching extends SphericalAuxiliaryFlux where
  piConstant : ℝ
  chiMagnitude : ℝ
  piConstantPositive : 0 < piConstant
  chiMagnitudePositive : 0 < chiMagnitude
  tensionRadiusLaw :
    8 * piConstant * chiMagnitude * throatRadius = 1

/--
The full classical LL system reduces to

`q_LL^2 = 256*pi^4*|chi|^4`.

Thus the auxiliary invariant is no longer free; one dimensionful charge unit
remains.  In positive variables this is equivalent to
`q_LL = 16*pi^2*|chi|^2` and `R_s = 1/(2*sqrt(q_LL))`.
-/
theorem charge_tension_relation
    (s : LLTensionFluxMatching) :
    s.chargeUnit ^ 2 =
      256 * s.piConstant ^ 4 * s.chiMagnitude ^ 4 := by
  have hFlux := primitive_flux_radius_law s.toSphericalAuxiliaryFlux
  have hTensionFourth :
      (8 * s.piConstant * s.chiMagnitude * s.throatRadius) ^ 4 = 1 := by
    rw [s.tensionRadiusLaw]
    norm_num
  have hFactor :
      s.throatRadius ^ 4 *
        (s.chargeUnit ^ 2 -
          256 * s.piConstant ^ 4 * s.chiMagnitude ^ 4) = 0 := by
    nlinarith [hFlux, hTensionFourth]
  have hRadiusFourthNonzero : s.throatRadius ^ 4 ≠ 0 :=
    pow_ne_zero 4 (ne_of_gt s.throatRadiusPositive)
  have hDifference :
      s.chargeUnit ^ 2 -
        256 * s.piConstant ^ 4 * s.chiMagnitude ^ 4 = 0 :=
    (mul_eq_zero.mp hFactor).resolve_left hRadiusFourthNonzero
  linarith

/-- The primitive flux law may be transported directly to the matched Janus scale. -/
theorem matched_alpha_charge_law
    (s : SphericalAuxiliaryFlux)
    (alphaSquaredLength : ℝ)
    (hMatch : alphaSquaredLength = s.throatRadius) :
    16 * s.chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1 := by
  rw [hMatch]
  exact primitive_flux_radius_law s

/--
What remains is now sharply isolated: deriving `q_LL` from the Janus action.
Calling it dimensionless would hide the scale problem; in this normalization it
carries the inverse-area scale needed to determine `R_s`.
-/
structure ChargeUnitDerivationStatus where
  compactWorldVolumeFluxCycleDerived : Prop
  fluxNormalizationFromActionDerived : Prop
  primitiveFluxSectorDerived : Prop
  auxiliaryInvariantOneHalfDerived : Prop
  chargeUnitDimensionsAudited : Prop
  chargeUnitMagnitudeDerivedNoFit : Prop
  absoluteThroatScaleDerivedNoFit : Prop


def absoluteLLScaleClosed
    (s : ChargeUnitDerivationStatus) : Prop :=
  s.compactWorldVolumeFluxCycleDerived /\
  s.fluxNormalizationFromActionDerived /\
  s.primitiveFluxSectorDerived /\
  s.auxiliaryInvariantOneHalfDerived /\
  s.chargeUnitDimensionsAudited /\
  s.chargeUnitMagnitudeDerivedNoFit /\
  s.absoluteThroatScaleDerivedNoFit


theorem missing_charge_unit_blocks_absolute_scale
    (s : ChargeUnitDerivationStatus)
    (hMissing : Not s.chargeUnitMagnitudeDerivedNoFit) :
    Not (absoluteLLScaleClosed s) := by
  intro h
  exact hMissing h.2.2.2.2.2.1

end P0EFTJanusLLBraneAuxiliaryFluxClosure
end JanusFormal
