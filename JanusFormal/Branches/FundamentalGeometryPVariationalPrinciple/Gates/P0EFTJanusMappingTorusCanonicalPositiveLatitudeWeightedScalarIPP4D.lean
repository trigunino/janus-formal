import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D

/-!
# Positive-latitude weighted scalar IPP

The proved positive-latitude change of variables has the exact density
`cos normal ^ 2`.  This gate inserts that same density into the already
concrete one-dimensional latitude integration by parts.  It also expresses
the normal derivative pointwise in the local-gradient basis of an existing
total holonomic patch.

This is a collar/fiber result.  The latitude parameter space is
`(S² × time) × normal`, not the `Vector4` domain of one holonomic chart, so no
single integrated Euclidean chart identity is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusPositiveLatitudeJacobian4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The real density whose `ENNReal.ofReal` is the proved latitude
Jacobian. -/
def canonicalPositiveLatitudeWeight (normal : Real) : Real :=
  Real.cos normal ^ 2

/-- Exact identification with the density in the radial-polar change of
variables. -/
theorem canonicalPositiveLatitudeJacobian_eq_weight
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalPositiveLatitudeJacobian (base.1, normal) =
      ENNReal.ofReal (canonicalPositiveLatitudeWeight normal) := by
  rfl

/-- Density-weighted normal current on one actual canonical latitude
fiber. -/
def canonicalPositiveLatitudeWeightedNormalCurrent
    (field : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalPositiveLatitudeWeight normal *
    canonicalLatitudeDerivative period hPeriod field base normal

/-- The corresponding weighted normal divergence. -/
def canonicalPositiveLatitudeWeightedNormalDivergence
    (field : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  deriv (canonicalPositiveLatitudeWeightedNormalCurrent
    period hPeriod field base) normal

theorem canonicalPositiveLatitudeWeightedNormalCurrent_contDiff
    (field : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) :
    ContDiff Real ∞
      (canonicalPositiveLatitudeWeightedNormalCurrent
        period hPeriod field base) := by
  change ContDiff Real ∞ (fun normal : Real =>
    Real.cos normal ^ 2 *
      canonicalLatitudeDerivative period hPeriod field base normal)
  exact (Real.contDiff_cos.pow 2).mul
    (canonicalLatitudeDerivative_contDiff period hPeriod field base)

theorem canonicalPositiveLatitudeWeightedNormalCurrent_hasDerivAt
    (field : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) :
    HasDerivAt
      (canonicalPositiveLatitudeWeightedNormalCurrent
        period hPeriod field base)
      (canonicalPositiveLatitudeWeightedNormalDivergence
        period hPeriod field base normal) normal :=
  ((canonicalPositiveLatitudeWeightedNormalCurrent_contDiff
      period hPeriod field base).differentiable (by simp)).differentiableAt.hasDerivAt

theorem canonicalPositiveLatitudeWeightedNormalDivergence_continuous
    (field : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) :
    Continuous
      (canonicalPositiveLatitudeWeightedNormalDivergence
        period hPeriod field base) := by
  unfold canonicalPositiveLatitudeWeightedNormalDivergence
  exact (canonicalPositiveLatitudeWeightedNormalCurrent_contDiff
    period hPeriod field base).continuous_deriv (by simp)

/-- Kinetic pairing with exactly the positive-latitude Jacobian density. -/
def canonicalPositiveLatitudeWeightedScalarKineticFiber
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) : Real :=
  ∫ normal in (0 : Real)..1,
    canonicalPositiveLatitudeWeightedNormalCurrent
        period hPeriod field base normal *
      canonicalLatitudeDerivative period hPeriod variation base normal

/-- Weighted Euler term produced by the normal IPP. -/
def canonicalPositiveLatitudeWeightedScalarEulerFiber
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) : Real :=
  -(∫ normal in (0 : Real)..1,
    canonicalPositiveLatitudeWeightedNormalDivergence
        period hPeriod field base normal *
      canonicalLatitudeValue period hPeriod variation base normal)

/-- Oriented endpoint flux of the weighted normal current. -/
def canonicalPositiveLatitudeWeightedScalarBoundaryFiber
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalPositiveLatitudeWeightedNormalCurrent period hPeriod field base 1 *
      canonicalLatitudeValue period hPeriod variation base 1 -
    canonicalPositiveLatitudeWeightedNormalCurrent period hPeriod field base 0 *
      canonicalLatitudeValue period hPeriod variation base 0

/-- Exact weighted IPP on every positive canonical latitude fiber. -/
theorem canonicalPositiveLatitudeWeightedScalarKineticFiber_eq_euler_add_boundary
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) :
    canonicalPositiveLatitudeWeightedScalarKineticFiber
        period hPeriod field variation base =
      canonicalPositiveLatitudeWeightedScalarEulerFiber
          period hPeriod field variation base +
        canonicalPositiveLatitudeWeightedScalarBoundaryFiber
          period hPeriod field variation base := by
  have hIPP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : Real)) (b := 1)
    (u := canonicalPositiveLatitudeWeightedNormalCurrent
      period hPeriod field base)
    (v := canonicalLatitudeValue period hPeriod variation base)
    (u' := canonicalPositiveLatitudeWeightedNormalDivergence
      period hPeriod field base)
    (v' := canonicalLatitudeDerivative period hPeriod variation base)
    (fun normal _ =>
      canonicalPositiveLatitudeWeightedNormalCurrent_hasDerivAt
        period hPeriod field base normal)
    (fun normal _ =>
      canonicalLatitudeValue_hasDerivAt period hPeriod variation base normal)
    ((canonicalPositiveLatitudeWeightedNormalDivergence_continuous
      period hPeriod field base).intervalIntegrable 0 1)
    ((canonicalLatitudeDerivative_continuous
      period hPeriod variation base).intervalIntegrable 0 1)
  unfold canonicalPositiveLatitudeWeightedScalarKineticFiber
    canonicalPositiveLatitudeWeightedScalarEulerFiber
    canonicalPositiveLatitudeWeightedScalarBoundaryFiber
  rw [hIPP]
  ring

/-- Measured weighted IPP over the actual round-`S²`/fundamental-time base,
without splitting the two output integrals. -/
theorem canonicalPositiveLatitudeMeasuredWeightedScalarKinetic_eq_integral_euler_add_boundary
    (field variation : SmoothScalarField period hPeriod) :
    (∫ base,
      canonicalPositiveLatitudeWeightedScalarKineticFiber
        period hPeriod field variation base
      ∂(canonicalLatitudeBaseMeasure period)) =
      ∫ base,
        (canonicalPositiveLatitudeWeightedScalarEulerFiber
            period hPeriod field variation base +
          canonicalPositiveLatitudeWeightedScalarBoundaryFiber
            period hPeriod field variation base)
        ∂(canonicalLatitudeBaseMeasure period) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalPositiveLatitudeWeightedScalarKineticFiber_eq_euler_add_boundary
      period hPeriod field variation base

/-- At each collar point, the normal derivative occurring in the weighted
IPP is exactly a finite sum of the local Frechet gradients in one of the
already constructed total holonomic patches.  The patch is point-dependent;
no unproved measurable global choice is made. -/
theorem exists_holonomicPatch_canonicalLatitudeDerivative_eq_localGradientSum
    (field : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) :
    ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4),
      patch.coordinateMap coordinate =
          quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal ∧
      canonicalLatitudeDerivative period hPeriod field base normal =
        ∑ index : Index4,
          (patch.frame coordinate).repr
              (canonicalLatitudeNormalVector period hPeriod base normal) index *
            localScalarGradient period hPeriod field patch coordinate index := by
  let point := quotientNormalLatitude period hPeriod
    (canonicalLatitudeAnchor period hPeriod base) normal
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  refine ⟨patch, coordinate, hCoordinate, ?_⟩
  rw [canonicalLatitudeDerivative_eq_mvfderiv_normal]
  change scalarDifferential period hPeriod field point
      (canonicalLatitudeNormalVector period hPeriod base normal) = _
  calc
    _ = scalarDifferential period hPeriod field
        (patch.coordinateMap coordinate)
        (canonicalLatitudeNormalVector period hPeriod base normal) := by
      rw [hCoordinate]
    _ = _ :=
      scalarDifferential_eq_sum_frameCoordinate_mul_localScalarGradient
        period hPeriod field patch coordinate
          (canonicalLatitudeNormalVector period hPeriod base normal)

end

end P0EFTJanusMappingTorusCanonicalPositiveLatitudeWeightedScalarIPP4D
end JanusFormal
