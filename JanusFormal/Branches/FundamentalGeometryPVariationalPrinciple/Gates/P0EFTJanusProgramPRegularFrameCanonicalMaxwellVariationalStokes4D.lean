import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellCartanVariation4D

/-! # Concrete global Stokes identity for the authentic Maxwell variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalStokes4D

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellCartanVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Euler density selected directly by the authentic first variation and the
concrete canonical divergence. -/
def regularFrameCanonicalMaxwellVariationalEulerPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  regularFrameCanonicalMaxwellFluxEulerPairing period hPeriod metric potential
      variation point +
    regularFrameCanonicalMaxwellAnholonomyPairing period hPeriod metric
      potential variation point

/-- Exact pointwise Euler-boundary decomposition of the genuine Maxwell
first variation. -/
theorem regularMaxwellFirstVariationField_eq_variationalEuler_sub_divergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) point =
      regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
          potential variation point -
        canonicalTenFlowDivergence period hPeriod metric
          (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
            potential variation) point := by
  rw [regularMaxwellFirstVariationField_eq_neg_derivative_add_anholonomy,
    regularFrameCanonicalMaxwellBoundaryCurrent_divergence_split]
  unfold regularFrameCanonicalMaxwellVariationalEulerPairing
  ring

theorem regularFrameCanonicalMaxwellVariationalEulerPairing_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    Integrable
      (regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
        potential variation)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  have hFirst : Integrable
      (regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation))
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    (regularMaxwellFirstVariationField period hPeriod metric
      (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
        potential variation)).contMDiff_toFun.continuous
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDivergence := canonicalTenFlowDivergence_integrable period hPeriod metric
    (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric potential
      variation)
  apply (hFirst.add hDivergence).congr
  filter_upwards [] with point
  change
    regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) point +
        canonicalTenFlowDivergence period hPeriod metric
          (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
            potential variation) point =
      regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
        potential variation point
  rw [regularMaxwellFirstVariationField_eq_variationalEuler_sub_divergence]
  ring

/-- The concrete boundary current has zero total flux, so the integrated
authentic variation is exactly its derived Euler pairing. -/
theorem intrinsicMaxwellFirstVariation_eq_integral_variationalEuler
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ point,
        regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
          potential variation point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold intrinsicMaxwellFirstVariation
  calc
    _ = ∫ point,
          (regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod
              metric potential variation point -
            canonicalTenFlowDivergence period hPeriod metric
              (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
                potential variation) point)
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
      integral_congr_ae (Filter.Eventually.of_forall fun point =>
        regularMaxwellFirstVariationField_eq_variationalEuler_sub_divergence
          period hPeriod metric potential variation point)
    _ = (∫ point,
          regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod
            metric potential variation point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) -
        ∫ point,
          canonicalTenFlowDivergence period hPeriod metric
            (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
              potential variation) point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
      rw [integral_sub
        (regularFrameCanonicalMaxwellVariationalEulerPairing_integrable period
          hPeriod metric potential variation)
        (canonicalTenFlowDivergence_integrable period hPeriod metric
          (regularFrameCanonicalMaxwellBoundaryCurrent period hPeriod metric
            potential variation))]
    _ = _ := by
      rw [canonicalTenFlowDivergence_integral_eq_zero period hPeriod metric]
      ring

/-- Gate marker: both former abstract Maxwell Stokes obligations are replaced
by one concrete current and an exact action-level identity. -/
theorem regular_frame_canonical_maxwell_variational_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ point,
        regularFrameCanonicalMaxwellVariationalEulerPairing period hPeriod metric
          potential variation point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicMaxwellFirstVariation_eq_integral_variationalEuler period hPeriod
    metric potential variation

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalStokes4D
end JanusFormal
