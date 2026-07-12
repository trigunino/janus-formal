import Mathlib

namespace JanusFormal
namespace P0EFTJanusLLGaugeNormalizationScaleOrbit

set_option autoImplicit false

/-- Primitive LL auxiliary-flux radius law. -/
def PrimitiveFluxRadiusLaw (chargeUnit throatRadius : ℝ) : Prop :=
  16 * chargeUnit ^ 2 * throatRadius ^ 4 = 1

/--
A simultaneous change of gauge normalization and radius.  The cleared relation
`q' * s^2 = q` avoids treating a convention-dependent division as primitive.
-/
structure GaugeNormalizationRescaling where
  originalChargeUnit : ℝ
  originalRadius : ℝ
  scaleFactor : ℝ
  rescaledChargeUnit : ℝ
  rescaledRadius : ℝ
  scaleFactorNonzero : scaleFactor ≠ 0
  chargeNormalizationLaw :
    rescaledChargeUnit * scaleFactor ^ 2 = originalChargeUnit
  radiusRescalingLaw :
    rescaledRadius = scaleFactor * originalRadius

/-- The primitive flux law is invariant along the gauge-normalization scale orbit. -/
theorem primitive_flux_law_invariant_under_normalization_rescaling
    (s : GaugeNormalizationRescaling)
    (hOriginal :
      PrimitiveFluxRadiusLaw s.originalChargeUnit s.originalRadius) :
    PrimitiveFluxRadiusLaw s.rescaledChargeUnit s.rescaledRadius := by
  unfold PrimitiveFluxRadiusLaw at hOriginal ⊢
  calc
    16 * s.rescaledChargeUnit ^ 2 * s.rescaledRadius ^ 4 =
        16 *
          (s.rescaledChargeUnit * s.scaleFactor ^ 2) ^ 2 *
          s.originalRadius ^ 4 := by
      rw [s.radiusRescalingLaw]
      ring
    _ = 16 * s.originalChargeUnit ^ 2 * s.originalRadius ^ 4 := by
      rw [s.chargeNormalizationLaw]
    _ = 1 := hOriginal

/-- A nontrivial positive rescaling changes the physical radius. -/
theorem nontrivial_positive_rescaling_changes_radius
    (s : GaugeNormalizationRescaling)
    (hRadius : 0 < s.originalRadius)
    (hScalePositive : 0 < s.scaleFactor)
    (hScaleNontrivial : s.scaleFactor ≠ 1) :
    s.rescaledRadius ≠ s.originalRadius := by
  rw [s.radiusRescalingLaw]
  intro hEqual
  have hFactor :
      (s.scaleFactor - 1) * s.originalRadius = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hFactor with hScale | hRadiusZero
  · apply hScaleNontrivial
    linarith
  · exact (ne_of_gt hRadius) hRadiusZero

/--
Therefore compactness and integrality alone do not fix `q_LL`: the kinetic/WZ
normalization of the world-volume field must be derived from the action.
-/
structure PhysicalGaugeNormalizationStatus where
  compactU1BundleDerived : Prop
  firstChernIntegerDerived : Prop
  auxiliaryKineticCoefficientDerived : Prop
  largeGaugeTransformationPeriodDerived : Prop
  bulkWessZuminoChargeNormalizationDerived : Prop
  conventionIndependentChargeUnitDerived : Prop


def physicalGaugeNormalizationClosed
    (s : PhysicalGaugeNormalizationStatus) : Prop :=
  s.compactU1BundleDerived /\
  s.firstChernIntegerDerived /\
  s.auxiliaryKineticCoefficientDerived /\
  s.largeGaugeTransformationPeriodDerived /\
  s.bulkWessZuminoChargeNormalizationDerived /\
  s.conventionIndependentChargeUnitDerived

end P0EFTJanusLLGaugeNormalizationScaleOrbit
end JanusFormal
