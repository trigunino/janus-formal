import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarEnergyCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzScalarStressCovariance4D

/-!
# Canonical collar scalar stress-energy current

The intrinsic D8 metric lowers the genuine latitude normal to a unit
covector.  Evaluating the already defined Lorentz scalar stress on the
normal-projected collar jet identifies its normal-normal component with one
half of the canonical collar energy.  Its conservation is only the local
one-dimensional consequence of the collar Euler equation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeScalarStressEnergyCurrent4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarEnergyCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzScalarStressCovariance4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Metric dual of the genuine latitude tangent for the intrinsic D8 metric. -/
def canonicalLatitudeNormalCovector
    (base : CanonicalLatitudeBase) (normal : Real) :
    TangentSpace coverModelWithCorners
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal) →L[Real] Real :=
  (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical
      (quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal)
      (canonicalLatitudeNormalVector period hPeriod base normal)

/-- The normal-projected differential of the scalar collar jet. -/
def canonicalLatitudeCollarDifferential
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    TangentSpace coverModelWithCorners
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal) →L[Real] Real :=
  canonicalLatitudeDerivative period hPeriod field base normal •
    canonicalLatitudeNormalCovector period hPeriod base normal

theorem canonicalLatitudeNormalCovector_apply_normal
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeNormalCovector period hPeriod base normal
        (canonicalLatitudeNormalVector period hPeriod base normal) = 1 := by
  unfold canonicalLatitudeNormalCovector
  have hFlat := congrArg
    (fun linearMap =>
      linearMap (canonicalLatitudeNormalVector period hPeriod base normal))
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical_eq_tensor
      (quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal))
  exact (DFunLike.congr_fun hFlat
    (canonicalLatitudeNormalVector period hPeriod base normal)).trans
      (intrinsicMetric_canonicalLatitudeNormalVector_self period hPeriod base normal)

theorem normalCovector_inverseMetricContraction_self
    (base : CanonicalLatitudeBase) (normal : Real) :
    fiberInverseMetricContraction period hPeriod
        ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal))
        (canonicalLatitudeNormalCovector period hPeriod base normal)
        (canonicalLatitudeNormalCovector period hPeriod base normal) = 1 := by
  simp [fiberInverseMetricContraction, canonicalLatitudeNormalCovector]
  simpa [canonicalLatitudeNormalCovector] using
    canonicalLatitudeNormalCovector_apply_normal period hPeriod base normal

theorem normalCovector_inverseMetricContraction_collarDifferential
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    fiberInverseMetricContraction period hPeriod
        ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal))
        (canonicalLatitudeNormalCovector period hPeriod base normal)
        (canonicalLatitudeCollarDifferential period hPeriod field base normal) =
      canonicalLatitudeDerivative period hPeriod field base normal := by
  simp [fiberInverseMetricContraction, canonicalLatitudeNormalCovector,
    canonicalLatitudeCollarDifferential]
  have hUnit := canonicalLatitudeNormalCovector_apply_normal period hPeriod base normal
  rw [show
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal)
        (canonicalLatitudeNormalVector period hPeriod base normal))
      (canonicalLatitudeNormalVector period hPeriod base normal) = 1 by
        simpa [canonicalLatitudeNormalCovector] using hUnit]
  ring

theorem collarDifferential_inverseMetricContraction_self
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    fiberInverseMetricContraction period hPeriod
        ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal))
        (canonicalLatitudeCollarDifferential period hPeriod field base normal)
        (canonicalLatitudeCollarDifferential period hPeriod field base normal) =
      canonicalLatitudeDerivative period hPeriod field base normal ^ 2 := by
  simp [fiberInverseMetricContraction, canonicalLatitudeNormalCovector,
    canonicalLatitudeCollarDifferential]
  have hUnit := canonicalLatitudeNormalCovector_apply_normal period hPeriod base normal
  rw [show
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal)
        (canonicalLatitudeNormalVector period hPeriod base normal))
      (canonicalLatitudeNormalVector period hPeriod base normal) = 1 by
        simpa [canonicalLatitudeNormalCovector] using hUnit]
  ring

/-- Normal-normal component of the general Lorentz scalar stress evaluated on
the scalar jet restricted to the canonical latitude direction. -/
def canonicalLatitudeScalarNormalStressPairing
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  fiberContravariantScalarStress period hPeriod
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical
      (quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal))
    massSquared (canonicalLatitudeValue period hPeriod field base normal)
    (canonicalLatitudeCollarDifferential period hPeriod field base normal)
    (canonicalLatitudeNormalCovector period hPeriod base normal)
    (canonicalLatitudeNormalCovector period hPeriod base normal)

/-- The convention used by `canonicalLatitudeScalarEnergyCurrent` is twice
the standard energy density, hence twice the normal-normal stress component. -/
theorem canonicalLatitudeScalarEnergyCurrent_eq_two_normalStressPairing
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared field base normal =
      2 * canonicalLatitudeScalarNormalStressPairing period hPeriod
        massSquared field base normal := by
  unfold canonicalLatitudeScalarNormalStressPairing
  rw [fiberContravariantScalarStress, fiberScalarLagrangian,
    normalCovector_inverseMetricContraction_collarDifferential,
    normalCovector_inverseMetricContraction_self,
    collarDifferential_inverseMetricContraction_self]
  unfold canonicalLatitudeScalarEnergyCurrent
  ring

/-- Local normal conservation of the canonical stress component under the
collar Euler equation.  No four-dimensional divergence theorem is used. -/
theorem canonicalLatitudeScalarNormalStressPairing_hasDerivAt_zero_of_euler
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (base : CanonicalLatitudeBase) (normal : Real) :
    CanonicalLatitudeScalarHasDerivAt
      (canonicalLatitudeScalarNormalStressPairing period hPeriod
        massSquared field base) 0 normal := by
  have hEnergy :=
    canonicalLatitudeScalarEnergyCurrent_hasDerivAt_zero_of_euler period
      hPeriod massSquared field hField base normal
  unfold CanonicalLatitudeScalarHasDerivAt at hEnergy ⊢
  have hFunction :
      canonicalLatitudeScalarNormalStressPairing period hPeriod
          massSquared field base =
        fun coordinate => (1 / 2 : Real) *
          canonicalLatitudeScalarEnergyCurrent period hPeriod massSquared
            field base coordinate := by
    funext coordinate
    rw [canonicalLatitudeScalarEnergyCurrent_eq_two_normalStressPairing]
    ring
  rw [hFunction]
  simpa using hEnergy.const_mul (1 / 2 : Real)

theorem canonicalLatitudeScalarNormalStressPairing_eq_of_euler
    (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (base : CanonicalLatitudeBase) (first second : Real) :
    canonicalLatitudeScalarNormalStressPairing period hPeriod massSquared
        field base first =
      canonicalLatitudeScalarNormalStressPairing period hPeriod massSquared
        field base second := by
  have hEnergy := canonicalLatitudeScalarEnergyCurrent_eq_of_euler period
    hPeriod massSquared field hField base first second
  rw [canonicalLatitudeScalarEnergyCurrent_eq_two_normalStressPairing,
    canonicalLatitudeScalarEnergyCurrent_eq_two_normalStressPairing] at hEnergy
  linarith

end

end P0EFTJanusMappingTorusCanonicalLatitudeScalarStressEnergyCurrent4D
end JanusFormal
