import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricVolumeDensityHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-!
# Frame-free relative Lorentz-volume Hessian density

The invariant pairing already available for smooth general Lorentz metrics
defines the trace `tr(g⁻¹h)` and the polarized determinant Hessian density

`ρ_g (1 / 4 * tr(g⁻¹h) * tr(g⁻¹k) -
       1 / 2 * tr(g⁻¹h g⁻¹k))`.

These spacetime functions are continuous and hence integrable against the
finite intrinsic reference measure on the compact quotient.  The resulting
integral is symmetric in the two tensor slots.

This gate globalizes the algebraic density formula.  It does not put a
topology or a chart on the space of Lorentz metrics, and therefore makes no
Fréchet-differentiability claim in the metric variable.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolumeHessian4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-! ## Global invariant trace and determinant-variation densities -/

/-- The invariant trace `tr(g⁻¹h)`, expressed using the existing
general-metric tensor pairing. -/
def globalRelativeMetricVolumeTraceAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  generalMetricTensorPairingAt period hPeriod metric variation metric.tensor point

theorem globalRelativeMetricVolumeTraceAt_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Continuous (globalRelativeMetricVolumeTraceAt
      period hPeriod metric variation) :=
  generalMetricTensorPairingAt_continuous
    period hPeriod metric variation metric.tensor

/-- Relative first-volume-variation density
`ρ_g * (1 / 2) * tr(g⁻¹h)`. -/
def globalRelativeMetricVolumeFirstVariationDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  globalMetricVolumeRatio period hPeriod metric point *
    ((1 / 2 : Real) *
      globalRelativeMetricVolumeTraceAt
        period hPeriod metric variation point)

theorem globalRelativeMetricVolumeFirstVariationDensity_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Continuous (globalRelativeMetricVolumeFirstVariationDensity
      period hPeriod metric variation) := by
  exact
    (globalMetricVolumeRatio_continuous period hPeriod metric).mul
      (continuous_const.mul
        (globalRelativeMetricVolumeTraceAt_continuous
          period hPeriod metric variation))

/-- Polarized relative Hessian density of the Lorentz-volume factor. -/
def globalRelativeMetricVolumeHessianDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  globalMetricVolumeRatio period hPeriod metric point *
    ((1 / 4 : Real) *
        (globalRelativeMetricVolumeTraceAt period hPeriod metric first point *
          globalRelativeMetricVolumeTraceAt period hPeriod metric second point) -
      (1 / 2 : Real) *
        generalMetricTensorPairingAt
          period hPeriod metric first second point)

theorem globalRelativeMetricVolumeHessianDensity_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalRelativeMetricVolumeHessianDensity
        period hPeriod metric first second point =
      globalRelativeMetricVolumeHessianDensity
        period hPeriod metric second first point := by
  unfold globalRelativeMetricVolumeHessianDensity
  rw [generalMetricTensorPairingAt_symmetric
    period hPeriod metric first second point]
  ring

theorem globalRelativeMetricVolumeHessianDensity_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Continuous (globalRelativeMetricVolumeHessianDensity
      period hPeriod metric first second) := by
  have hFirst :=
    globalRelativeMetricVolumeTraceAt_continuous
      period hPeriod metric first
  have hSecond :=
    globalRelativeMetricVolumeTraceAt_continuous
      period hPeriod metric second
  have hPairing :=
    generalMetricTensorPairingAt_continuous
      period hPeriod metric first second
  exact
    (globalMetricVolumeRatio_continuous period hPeriod metric).mul
      ((continuous_const.mul (hFirst.mul hSecond)).sub
        (continuous_const.mul hPairing))

/-! ## Compact-quotient integrability -/

theorem globalRelativeMetricVolumeFirstVariationDensity_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Integrable
      (globalRelativeMetricVolumeFirstVariationDensity
        period hPeriod metric variation)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (globalRelativeMetricVolumeFirstVariationDensity_continuous
    period hPeriod metric variation).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem globalRelativeMetricVolumeHessianDensity_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Integrable
      (globalRelativeMetricVolumeHessianDensity
        period hPeriod metric first second)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (globalRelativeMetricVolumeHessianDensity_continuous
    period hPeriod metric first second).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-! ## Integrated symmetric pairing -/

/-- Integral of the polarized relative volume Hessian density. -/
def integratedRelativeMetricVolumeHessian
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  ∫ point,
    globalRelativeMetricVolumeHessianDensity
      period hPeriod metric first second point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

theorem integratedRelativeMetricVolumeHessian_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    integratedRelativeMetricVolumeHessian
        period hPeriod metric first second =
      integratedRelativeMetricVolumeHessian
        period hPeriod metric second first := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    globalRelativeMetricVolumeHessianDensity_symmetric
      period hPeriod metric first second point

end

end P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolumeHessian4D
end JanusFormal
